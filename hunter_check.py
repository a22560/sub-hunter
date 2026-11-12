#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import asyncio
import base64
import json
import os
import re
import shutil
import subprocess
import time
import urllib.parse
from collections import Counter
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

import aiohttp
import yaml

# ==================== 可调核心参数 ====================
MAX_CANDIDATES_TO_TEST = 2200   # 单次送入真机内核测速的最大去重候选数
TEST_TIMEOUT_MS = 5000          # Mihomo 单节点握手+测速超时上限 (毫秒)
MAX_ACCEPT_DELAY_MS = 3200      # 保留的最大延迟 (兼顾美国服务器跨洋测香港/日本节点的往返耗时)
TEST_CONCURRENCY = 70           # 并发真连接测速数
TEST_TARGET_URL = "https://www.gstatic.com/generate_204"
MIHOMO_API = "http://127.0.0.1:19090"

GITHUB_SEARCH_KEYWORDS = [
    "v2ray sub free",
    "v2rayaggregator",
    "free nodes clash v2ray",
]

TG_CHANNELS = [
    "freev2rays",
    "v2raycollect",
    "ShadowProxy66",
    "PrivateVPNs",
    "OutlineVpnOfficial",
]

SEED_URLS = [
    "https://nodefree.githubrowcontent.com/{YYYY}/{MM}/{YYYY}{MM}{DD}.txt",
    "https://raw.githubusercontent.com/barry-far/V2ray-Configs/main/Sub1.txt",
    "https://raw.githubusercontent.com/barry-far/V2ray-Configs/main/Sub2.txt",
    "https://raw.githubusercontent.com/Pawdroid/Free-servers/main/sub",
    "https://raw.githubusercontent.com/aiboboxx/v2rayfree/main/v2",
    "https://raw.githubusercontent.com/mfuu/v2ray/master/v2ray",
    "https://raw.githubusercontent.com/mahdibland/V2RayAggregator/master/sub/sub_merge_base64.txt",
]

FETCH_ROUTES = [
    lambda u: u,
    lambda u: f"https://api.codetabs.com/v1/proxy?quest={urllib.parse.quote(u, safe='')}",
    lambda u: f"https://api.allorigins.win/raw?url={urllib.parse.quote(u, safe='')}",
]

URI_PATTERN = re.compile(
    r"(?:vmess|vless|trojan|ss|ssr|hy2|hysteria2|tuic)://[A-Za-z0-9+/_=-]+[^\s<>\"'`\\]*",
    re.IGNORECASE,
)
SECOND_HOP_PATTERN = re.compile(
    r"https?://[^\s<>\"'`\\]+(?:/api/v1/client/subscribe\?token=[A-Za-z0-9]+|/sub\?[^\s<>\"'`\\]+|/[^\s<>\"'`\\]*sub[^\s<>\"'`\\]*\.(?:txt|yaml|yml))(?![A-Za-z0-9])",
    re.IGNORECASE,
)
AD_REMARK_PATTERN = re.compile(
    r"剩余流量|套餐到期|距离下次重置|已过期|流量已用尽|官网|防失联|群组|频道|请更新订阅|购买套餐|到期时间|备用地址",
    re.IGNORECASE,
)
FAKE_HOSTS = {"127.0.0.1", "0.0.0.0", "localhost", "1.1.1.1", "8.8.8.8", "example.com"}


# ==================== 编解码与解析工具 ====================
def b64_decode_safe(s: str) -> Optional[str]:
    cleaned = re.sub(r"\s+", "", s).replace("-", "+").replace("_", "/")
    if len(cleaned) < 16 or not re.fullmatch(r"[A-Za-z0-9+/=]+", cleaned):
        return None
    cleaned += "=" * ((4 - len(cleaned) % 4) % 4)
    try:
        return base64.b64decode(cleaned).decode("utf-8", errors="ignore")
    except Exception:
        return None


def b64_encode_str(s: str) -> str:
    return base64.b64encode(s.encode("utf-8")).decode("ascii")


def b64_encode_urlsafe_nopad(s: str) -> str:
    return base64.urlsafe_b64encode(s.encode("utf-8")).decode("ascii").rstrip("=")


def expand_date_urls(tpl: str) -> List[str]:
    if "{YYYY}" not in tpl and "{MM}" not in tpl and "{DD}" not in tpl:
        return [tpl]
    now = datetime.now(timezone.utc)
    return [
        tpl.replace("{YYYY}", d.strftime("%Y"))
        .replace("{MM}", d.strftime("%m"))
        .replace("{DD}", d.strftime("%d"))
        for d in (now, now - timedelta(days=1))
    ]


def clash_dict_to_uri(p: dict) -> Optional[str]:
    if not isinstance(p, dict):
        return None
    ptype = str(p.get("type", "")).lower().strip()
    server = str(p.get("server", "")).strip()
    port = str(p.get("port", "")).strip()
    name = urllib.parse.quote(str(p.get("name", f"{ptype}-{server}")).strip())
    if not server or not port or server.lower() in FAKE_HOSTS:
        return None

    if ptype == "trojan" and p.get("password"):
        sni = p.get("sni") or p.get("servername") or ""
        q = f"security=tls&allowInsecure=1&sni={urllib.parse.quote(str(sni))}" if sni else "security=tls&allowInsecure=1"
        return f"trojan://{urllib.parse.quote(str(p['password']))}@{server}:${port}?{q}#{name}".replace("${port}", port)

    if ptype == "ss" and p.get("cipher") and p.get("password"):
        userinfo = b64_encode_urlsafe_nopad(f"{p['cipher']}:{p['password']}")
        return f"ss://{userinfo}@{server}:{port}#{name}"

    if ptype == "vless" and p.get("uuid"):
        net = p.get("network", "tcp")
        tls_enabled = bool(p.get("tls"))
        ropts = p.get("reality-opts") or {}
        sec = "reality" if ropts else ("tls" if tls_enabled else "none")
        sni = p.get("servername") or p.get("sni") or ""
        params = {"encryption": "none", "security": sec, "type": net}
        if sec == "tls":
            params["allowInsecure"] = "1"
        if sni:
            params["sni"] = str(sni)
        if p.get("client-fingerprint"):
            params["fp"] = str(p["client-fingerprint"])
        if p.get("flow"):
            params["flow"] = str(p["flow"])
        if ropts.get("public-key"):
            params["pbk"] = str(ropts["public-key"])
        if ropts.get("short-id"):
            params["sid"] = str(ropts["short-id"])
        ws_opts = p.get("ws-opts") or {}
        if net == "ws":
            if ws_opts.get("path"):
                params["path"] = str(ws_opts["path"])
            headers = ws_opts.get("headers") or {}
            if headers.get("Host"):
                params["host"] = str(headers["Host"])
        qs = urllib.parse.urlencode(params)
        return f"vless://{p['uuid']}@{server}:{port}?{qs}#{name}"

    if ptype == "vmess" and p.get("uuid"):
        ws_opts = p.get("ws-opts") or {}
        headers = ws_opts.get("headers") or {}
        vobj = {
            "v": "2",
            "ps": urllib.parse.unquote(name),
            "add": server,
            "port": str(port),
            "id": str(p["uuid"]),
            "aid": str(p.get("alterId", 0)),
            "net": str(p.get("network", "tcp")),
            "type": "none",
            "host": str(headers.get("Host", p.get("servername", ""))),
            "path": str(ws_opts.get("path", "")),
            "tls": "tls" if p.get("tls") else "",
            "sni": str(p.get("servername", "")),
        }
        return "vmess://" + b64_encode_str(json.dumps(vobj, ensure_ascii=False))

    if ptype in ("hysteria2", "hy2") and p.get("password"):
        params = {"insecure": "1"}
        if p.get("sni"):
            params["sni"] = str(p["sni"])
        if p.get("obfs"):
            params["obfs"] = str(p["obfs"])
            if p.get("obfs-password"):
                params["obfs-password"] = str(p["obfs-password"])
        qs = urllib.parse.urlencode(params)
        return f"hysteria2://{urllib.parse.quote(str(p['password']))}@{server}:{port}?{qs}#{name}"

    if ptype == "tuic" and p.get("uuid") and p.get("password"):
        params = {"congestion_control": str(p.get("congestion-controller", "bbr")), "allow_insecure": "1"}
        if p.get("sni"):
            params["sni"] = str(p["sni"])
        if p.get("alpn"):
            alpn_val = ",".join(p["alpn"]) if isinstance(p["alpn"], list) else str(p["alpn"])
            params["alpn"] = alpn_val
        qs = urllib.parse.urlencode(params)
        auth = f"{urllib.parse.quote(str(p['uuid']))}:{urllib.parse.quote(str(p['password']))}"
        return f"tuic://{auth}@{server}:{port}?{qs}#{name}"

    return None


def parse_clash_yaml(text: str) -> List[str]:
    if "proxies:" not in text:
        return []
    uris = []
    try:
        data = yaml.safe_load(text)
        if isinstance(data, dict) and isinstance(data.get("proxies"), list):
            for item in data["proxies"]:
                u = clash_dict_to_uri(item)
                if u:
                    uris.append(u)
    except Exception:
        pass
    return uris


def harvest_from_text(raw: str) -> Tuple[List[str], List[str]]:
    if not raw or len(raw) < 12:
        return [], []
    norm = re.sub(r"<br\s*/?>", "\n", raw, flags=re.I)
    norm = re.sub(r"</(?:div|p|li|tr|code|pre)>", "\n", norm, flags=re.I)
    norm = re.sub(r"<[^>]+>", " ", norm)
    norm = norm.replace("&amp;", "&").replace("&#35;", "#").replace("&quot;", '"')

    sub_links = [
        u.rstrip(").,;'\"\\]>")
        for u in SECOND_HOP_PATTERN.findall(norm)
        if not re.search(r"t\.me|telegram\.org", u, re.I)
    ]

    nodes = [n.rstrip(").,;'\"\\]>") for n in URI_PATTERN.findall(norm)]
    if not nodes:
        dec = b64_decode_safe(raw)
        if dec:
            nodes.extend(n.strip() for n in URI_PATTERN.findall(dec))
            nodes.extend(parse_clash_yaml(dec))
    nodes.extend(parse_clash_yaml(norm))
    return nodes, list(dict.fromkeys(sub_links))


# ==================== 节点清洗、打标与重写 ====================
def inspect_and_rewrite_candidate(uri: str, tag_id: str) -> Optional[Tuple[str, str, str]]:
    m = re.match(r"^([a-z0-9]+)://(.+)$", uri.strip(), re.I)
    if not m:
        return None
    proto = m.group(1).lower()
    body = m.group(2)

    if proto == "vmess":
        dec = b64_decode_safe(body.split("#")[0])
        if not dec:
            return None
        try:
            obj = json.loads(dec)
            host = str(obj.get("add", "")).strip().lower()
            port = int(obj.get("port", 0))
            orig_name = str(obj.get("ps", "")).strip() or f"VMess-{host}"
            if not host or host in FAKE_HOSTS or not (1 <= port <= 65535):
                return None
            if AD_REMARK_PATTERN.search(orig_name):
                return None
            fp = f"vmess://{host}:{port}:{obj.get('id','')}:{obj.get('net','')}:{obj.get('path','')}"
            obj["ps"] = tag_id
            tagged_uri = "vmess://" + b64_encode_str(json.dumps(obj, ensure_ascii=False))
            return fp, tagged_uri, orig_name
        except Exception:
            return None

    if proto == "ssr":
        dec = b64_decode_safe(body.split("#")[0])
        if not dec or ":" not in dec:
            return None
        parts = dec.split("/?", 1)
        main_part = parts[0]
        segs = main_part.split(":")
        if len(segs) < 6:
            return None
        host = segs[0].lower()
        try:
            port = int(segs[1])
        except ValueError:
            return None
        if host in FAKE_HOSTS or not (1 <= port <= 65535):
            return None
        qs = urllib.parse.parse_qs(parts[1]) if len(parts) > 1 else {}
        orig_name = f"SSR-{host}"
        if "remarks" in qs and qs["remarks"]:
            r_dec = b64_decode_safe(qs["remarks"][0])
            if r_dec:
                orig_name = r_dec.strip()
        if AD_REMARK_PATTERN.search(orig_name):
            return None
        qs["remarks"] = [b64_encode_urlsafe_nopad(tag_id)]
        flat_q = "&".join(f"{k}={v[0]}" for k, v in qs.items() if v)
        tagged_ssr = "ssr://" + b64_encode_urlsafe_nopad(f"{main_part}/?{flat_q}")
        return f"ssr://{main_part}", tagged_ssr, orig_name

    norm_proto = "hysteria2" if proto == "hy2" else proto
    if "#" in body:
        main_part, raw_remark = body.split("#", 1)
        orig_name = urllib.parse.unquote(raw_remark).strip()
    else:
        main_part, orig_name = body, ""

    if orig_name and AD_REMARK_PATTERN.search(orig_name):
        return None

    addr_part = main_part.split("?")[0].rstrip("/")
    if "@" not in addr_part and norm_proto == "ss":
        dec_ss = b64_decode_safe(addr_part)
        if dec_ss and "@" in dec_ss:
            addr_part = dec_ss
    host_port = addr_part.rsplit("@", 1)[-1]
    pm = re.search(r":(\d{1,5})$", host_port)
    if pm:
        port = int(pm.group(1))
        host = host_port[: -len(pm.group(0))].strip("[]").lower()
        if not host or host in FAKE_HOSTS or not (1 <= port <= 65535):
            return None
        if not orig_name:
            orig_name = f"{norm_proto.upper()}-{host}"
    else:
        return None

    tagged_uri = f"{norm_proto}://{main_part.strip()}#{tag_id}"
    return f"{norm_proto}://{main_part.strip()}", tagged_uri, orig_name


def apply_final_remark(tagged_uri: str, final_remark: str) -> str:
    clean_label = re.sub(r"[\r\n#]+", " ", final_remark).strip()[:46]
    if tagged_uri.startswith("vmess://"):
        dec = b64_decode_safe(tagged_uri[8:])
        if dec:
            obj = json.loads(dec)
            obj["ps"] = clean_label
            return "vmess://" + b64_encode_str(json.dumps(obj, ensure_ascii=False))
    if tagged_uri.startswith("ssr://"):
        dec = b64_decode_safe(tagged_uri[6:])
        if dec and "/?" in dec:
            main_part, q_part = dec.split("/?", 1)
            qs = urllib.parse.parse_qs(q_part)
            qs["remarks"] = [b64_encode_urlsafe_nopad(clean_label)]
            flat_q = "&".join(f"{k}={v[0]}" for k, v in qs.items() if v)
            return "ssr://" + b64_encode_urlsafe_nopad(f"{main_part}/?{flat_q}")
    base = tagged_uri.split("#", 1)[0]
    return f"{base}#{urllib.parse.quote(clean_label)}"


# ==================== 多通道并发异步网络抓取 ====================
async def race_fetch_text(session: aiohttp.ClientSession, url: str) -> Optional[str]:
    async def try_one(target_url: str) -> str:
        async with session.get(target_url, timeout=aiohttp.ClientTimeout(total=10)) as resp:
            if resp.status != 200:
                raise RuntimeError(f"HTTP {resp.status}")
            txt = await resp.text(errors="ignore")
            if len(txt) < 12:
                raise RuntimeError("Empty")
            return txt

    tasks = [asyncio.create_task(try_one(route(url))) for route in FETCH_ROUTES]
    try:
        while tasks:
            done, pending = await asyncio.wait(tasks, return_when=asyncio.FIRST_COMPLETED)
            tasks = list(pending)
            for d in done:
                if not d.exception() and d.result():
                    for p in tasks:
                        p.cancel()
                    return d.result()
    finally:
        for t in tasks:
            t.cancel()
    return None


async def discover_github_sources(session: aiohttp.ClientSession) -> List[str]:
    headers = {"Accept": "application/vnd.github+json", "User-Agent": "NodeHunterBot/3.1"}
    gh_token = os.getenv("GITHUB_TOKEN", "").strip()
    if gh_token:
        headers["Authorization"] = f"Bearer {gh_token}"

    since = (datetime.now(timezone.utc) - timedelta(days=10)).strftime("%Y-%m-%d")
    found: Set[str] = set()

    for kw in GITHUB_SEARCH_KEYWORDS:
        q = urllib.parse.quote(f"{kw} pushed:>{since}")
        api_url = f"https://api.github.com/search/repositories?q={q}&sort=updated&order=desc&per_page=4"
        try:
            async with session.get(api_url, headers=headers, timeout=aiohttp.ClientTimeout(total=10)) as resp:
                if resp.status != 200:
                    continue
                data = await resp.json()
        except Exception:
            continue

        for repo in (data.get("items") or [])[:4]:
            full_name = repo.get("full_name")
            branch = repo.get("default_branch", "main")
            tree_url = f"https://api.github.com/repos/{full_name}/git/trees/{branch}?recursive=1"
            try:
                async with session.get(tree_url, headers=headers, timeout=aiohttp.ClientTimeout(total=10)) as tresp:
                    if tresp.status != 200:
                        continue
                    tdata = await tresp.json()
            except Exception:
                continue

            matched = 0
            for f in tdata.get("tree") or []:
                path = f.get("path", "")
                size = f.get("size", 0)
                if (
                    f.get("type") == "blob"
                    and 400 < size < 1_500_000
                    and not re.search(r"(readme|license|package|\.(py|js|go|sh|md|html|json))$", path, re.I)
                    and re.search(r"(sub|v2ray|clash|node|merge|base64|free|all)[^/]*\.(txt|yaml|yml|conf|sub)$", path, re.I)
                ):
                    found.add(f"https://raw.githubusercontent.com/{full_name}/{branch}/{path}")
                    matched += 1
                    if matched >= 2:
                        break
    print(f"[GitHub 雷达] 动态发现 {len(found)} 个近期活跃订阅源")
    return list(found)


# ==================== Mihomo 真机内核握手测速（兼容 v1.19.26+ Provider API） ====================
async def test_nodes_with_mihomo(mihomo_bin: Path, tagged_uris: List[str]) -> Dict[str, int]:
    work_dir = Path("./mihomo_work")
    if work_dir.exists():
        shutil.rmtree(work_dir)
    work_dir.mkdir(parents=True, exist_ok=True)

    b64_payload = b64_encode_str("\n".join(tagged_uris))
    (work_dir / "candidates.txt").write_text(b64_payload, encoding="utf-8")

    mihomo_cfg = {
        "mixed-port": 17890,
        "allow-lan": False,
        "mode": "rule",
        "log-level": "warning",
        "ipv6": False,
        "unified-delay": True,
        "tcp-concurrent": True,
        "external-controller": "127.0.0.1:19090",
        "dns": {
            "enable": True,
            "ipv6": False,
            "nameserver": ["8.8.8.8", "1.1.1.1"],
            "proxy-server-nameserver": ["8.8.8.8", "1.1.1.1"],
        },
        "proxy-providers": {
            "hunter_pool": {
                "type": "file",
                "path": "./candidates.txt",
                "health-check": {
                    "enable": True,
                    "url": TEST_TARGET_URL,
                    "interval": 3600,
                    "timeout": TEST_TIMEOUT_MS,
                    "lazy": True,
                    "expected-status": "200/204",
                },
                "override": {
                    "skip-cert-verify": True,
                    "udp": True,
                },
            }
        },
        "proxy-groups": [
            {
                "name": "HUNTER_SELECT",
                "type": "select",
                "use": ["hunter_pool"],
            }
        ],
        "rules": ["MATCH,DIRECT"],
    }
    cfg_path = work_dir / "config.yaml"
    cfg_path.write_text(yaml.safe_dump(mihomo_cfg, sort_keys=False), encoding="utf-8")

    err_log_path = work_dir / "mihomo_stderr.log"
    err_fp = open(err_log_path, "w", encoding="utf-8")
    proc = subprocess.Popen(
        [str(mihomo_bin.resolve()), "-d", str(work_dir.resolve()), "-f", str(cfg_path.resolve())],
        stdout=subprocess.DEVNULL,
        stderr=err_fp,
    )

    alive_delays: Dict[str, int] = {}
    status_counter: Counter = Counter()

    try:
        conn = aiohttp.TCPConnector(limit=TEST_CONCURRENCY + 20)
        async with aiohttp.ClientSession(connector=conn) as session:
            ready = False
            for _ in range(35):
                try:
                    async with session.get(f"{MIHOMO_API}/version", timeout=aiohttp.ClientTimeout(total=1)) as r:
                        if r.status == 200:
                            ver = await r.json()
                            print(f"[Mihomo 内核] 启动就绪，当前版本: {ver.get('version', 'unknown')}")
                            ready = True
                            break
                except Exception:
                    pass
                await asyncio.sleep(0.3)

            if not ready:
                err_fp.flush()
                err_txt = err_log_path.read_text(encoding="utf-8", errors="ignore")[-800:]
                print(f"[Mihomo 测速] 错误：控制接口未就绪，内核日志: {err_txt}")
                return {}

            await session.put(f"{MIHOMO_API}/providers/proxies/hunter_pool")
            await asyncio.sleep(0.6)
            async with session.get(f"{MIHOMO_API}/providers/proxies/hunter_pool") as resp:
                pdata = await resp.json()
                loaded_names = [
                    p["name"]
                    for p in (pdata.get("proxies") or [])
                    if str(p.get("name", "")).startswith("NODE_")
                ]

            total_loaded = len(loaded_names)
            print(f"[Mihomo 测速] 内核成功装载 {total_loaded} 个合法节点，开始并发 204 真连接验活...")
            if total_loaded == 0:
                return {}

            encoded_target = urllib.parse.quote(TEST_TARGET_URL, safe="")

            # 自动探测新版 Provider 专属测速路由 vs 旧版全局路由
            use_provider_route = True
            probe_name = urllib.parse.quote(loaded_names[0], safe="")
            probe_url = f"{MIHOMO_API}/providers/proxies/hunter_pool/{probe_name}/healthcheck?url={encoded_target}&timeout=3000"
            try:
                async with session.get(probe_url, timeout=aiohttp.ClientTimeout(total=5)) as pr:
                    if pr.status == 404:
                        use_provider_route = False
                        print("[路由自适应] 检测到旧版路由模式，切换至 /proxies/{name}/delay")
                    else:
                        print(f"[路由自适应] 命中新版 Provider 测速接口 (探测状态码 HTTP {pr.status})")
            except Exception:
                pass

            sem = asyncio.Semaphore(TEST_CONCURRENCY)
            completed = 0

            async def check_one(node_name: str):
                nonlocal completed
                q_name = urllib.parse.quote(node_name, safe="")
                if use_provider_route:
                    url = f"{MIHOMO_API}/providers/proxies/hunter_pool/{q_name}/healthcheck?url={encoded_target}&timeout={TEST_TIMEOUT_MS}"
                else:
                    url = f"{MIHOMO_API}/proxies/{q_name}/delay?url={encoded_target}&timeout={TEST_TIMEOUT_MS}"

                async with sem:
                    try:
                        async with session.get(url, timeout=aiohttp.ClientTimeout(total=(TEST_TIMEOUT_MS / 1000) + 3)) as r:
                            status_counter[f"HTTP_{r.status}"] += 1
                            if r.status == 200:
                                j = await r.json()
                                delay = int(j.get("delay", 0))
                                if 0 < delay <= MAX_ACCEPT_DELAY_MS:
                                    alive_delays[node_name] = delay
                    except asyncio.TimeoutError:
                        status_counter["CLIENT_TIMEOUT"] += 1
                    except Exception:
                        status_counter["CLIENT_ERR"] += 1
                    finally:
                        completed += 1
                        if completed % 400 == 0 or completed == total_loaded:
                            print(f"[测速进度] {completed} / {total_loaded} 已测 | 当前真连接存活: {len(alive_delays)} 个")

            await asyncio.gather(*(check_one(n) for n in loaded_names))
            print(f"[测速状态码分布] {dict(status_counter)}")
    finally:
        err_fp.close()
        proc.terminate()
        try:
            proc.wait(timeout=4)
        except Exception:
            proc.kill()
        shutil.rmtree(work_dir, ignore_errors=True)

    return alive_delays


def generate_clash_client_yaml(b64_sub_rel_note: str) -> str:
    repo = os.getenv("GITHUB_REPOSITORY", "yourname/yourrepo")
    branch = os.getenv("GITHUB_REF_NAME", "main")
    raw_sub_url = f"https://raw.githubusercontent.com/{repo}/{branch}/sub/sub_base64.txt"

    cfg = {
        "mixed-port": 7890,
        "allow-lan": True,
        "mode": "rule",
        "log-level": "info",
        "unified-delay": True,
        "tcp-concurrent": True,
        "proxy-providers": {
            "VerifiedNodes": {
                "type": "http",
                "url": raw_sub_url,
                "interval": 3600,
                "path": "./providers/verified_nodes.yaml",
                "health-check": {
                    "enable": True,
                    "interval": 300,
                    "url": "https://www.gstatic.com/generate_204",
                },
                "override": {
                    "skip-cert-verify": True,
                    "udp": True,
                },
            }
        },
        "proxy-groups": [
            {
                "name": "🚀 节点选择",
                "type": "select",
                "proxies": ["⚡ 自动最优", "🛡️ 故障转移"],
                "use": ["VerifiedNodes"],
            },
            {
                "name": "⚡ 自动最优",
                "type": "url-test",
                "use": ["VerifiedNodes"],
                "url": "https://www.gstatic.com/generate_204",
                "interval": 300,
                "tolerance": 50,
            },
            {
                "name": "🛡️ 故障转移",
                "type": "fallback",
                "use": ["VerifiedNodes"],
                "url": "https://www.gstatic.com/generate_204",
                "interval": 300,
            },
        ],
        "rules": [
            "GEOIP,LAN,DIRECT,no-resolve",
            "GEOIP,CN,DIRECT",
            "MATCH,🚀 节点选择",
        ],
    }
    header = f"# 自动更新真机验活配置 ({b64_sub_rel_note})\n"
    return header + yaml.safe_dump(cfg, allow_unicode=True, sort_keys=False)


# ==================== 主流水线入口 ====================
async def main():
    t_start = time.time()
    connector = aiohttp.TCPConnector(limit=30, ssl=False)
    visited_urls: Set[str] = set()
    raw_nodes: List[str] = []
    second_hop_urls: Set[str] = set()

    async with aiohttp.ClientSession(
        connector=connector,
        headers={"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) Chrome/126.0.0.0"},
    ) as session:
        targets: List[str] = []
        gh_urls = await discover_github_sources(session)
        targets.extend(gh_urls)
        targets.extend(f"https://t.me/s/{ch}" for ch in TG_CHANNELS)
        for s in SEED_URLS:
            targets.extend(expand_date_urls(s))

        unique_targets = []
        for u in targets:
            if u not in visited_urls:
                visited_urls.add(u)
                unique_targets.append(u)

        print(f"[一跳抓取] 共集结 {len(unique_targets)} 个全网源，启动多通道并发抓取...")
        sem = asyncio.Semaphore(10)

        async def fetch_job(u: str):
            async with sem:
                txt = await race_fetch_text(session, u)
                if not txt:
                    return
                nodes, hops = harvest_from_text(txt)
                raw_nodes.extend(nodes)
                for h in hops:
                    if h not in visited_urls:
                        second_hop_urls.add(h)

        await asyncio.gather(*(fetch_job(u) for u in unique_targets))

        if second_hop_urls:
            hop_list = list(second_hop_urls)[:20]
            print(f"[二跳爬虫] 顺藤摸瓜继续抓取新发现的 {len(hop_list)} 条二级外链订阅...")
            for h in hop_list:
                visited_urls.add(h)
            await asyncio.gather(*(fetch_job(u) for u in hop_list))

    print(f"[清洗去重] 原始共抓到 {len(raw_nodes)} 条毛坯记录，开始指纹去重与广告过滤...")
    seen_fp: Set[str] = set()
    id_map: Dict[str, Tuple[str, str]] = {}
    tagged_list: List[str] = []

    for uri in raw_nodes:
        if len(tagged_list) >= MAX_CANDIDATES_TO_TEST:
            break
        tag_id = f"NODE_{len(tagged_list):05d}"
        res = inspect_and_rewrite_candidate(uri, tag_id)
        if not res:
            continue
        fp, tagged_uri, orig_remark = res
        if fp in seen_fp:
            continue
        seen_fp.add(fp)
        id_map[tag_id] = (tagged_uri, orig_remark)
        tagged_list.append(tagged_uri)

    print(f"[候选就绪] 过滤假节点与重复项后，共 {len(tagged_list)} 个独立节点送入 Mihomo 内核测速")

    mihomo_bin = Path("./mihomo")
    if mihomo_bin.exists() and tagged_list:
        alive_delays = await test_nodes_with_mihomo(mihomo_bin, tagged_list)
    else:
        print("[警告] 未检测到 ./mihomo 二进制文件，跳过真连接测速")
        alive_delays = {k: 999 for k in id_map}

    sorted_alive = sorted(alive_delays.items(), key=lambda kv: kv[1])
    final_uris: List[str] = []
    for tag_id, delay_ms in sorted_alive:
        tagged_uri, orig_remark = id_map[tag_id]
        clean_orig = re.sub(r"^⚡\d+ms\s*\|\s*", "", orig_remark).strip()
        final_uris.append(apply_final_remark(tagged_uri, f"⚡{delay_ms}ms | {clean_orig}"))

    out_dir = Path("./sub")
    out_dir.mkdir(parents=True, exist_ok=True)
    now_str = datetime.now(timezone(timedelta(hours=8))).strftime("%Y-%m-%d %H:%M:%S CST")

    if final_uris:
        plain_text = "\n".join(final_uris)
        (out_dir / "sub_plain.txt").write_text(plain_text + "\n", encoding="utf-8")
        (out_dir / "sub_base64.txt").write_text(b64_encode_str(plain_text), encoding="utf-8")
        (out_dir / "clash.yaml").write_text(
            generate_clash_client_yaml(f"更新于 {now_str} · 存活 {len(final_uris)} 节点"),
            encoding="utf-8",
        )
        elapsed = round(time.time() - t_start, 1)
        print(f"[大功告成] 耗时 {elapsed}s | 真连接存活节点: {len(final_uris)} / {len(tagged_list)} | 已写入 sub/ 目录")
    else:
        print("[未更新] 本轮测速未筛出存活节点，保留上一轮历史可用订阅文件不覆盖")


if __name__ == "__main__":
    asyncio.run(main())