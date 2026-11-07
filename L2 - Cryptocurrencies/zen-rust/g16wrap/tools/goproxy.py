# Build a file-based GOPROXY from GitHub clones (proxy.golang.org is unreachable here).
# usage: python3 goproxy.py <proxy_dir> <go.sum> [<go.sum> ...]
import os, re, subprocess, sys, json, io, zipfile
PROXY = sys.argv[1]; CACHE = os.path.join(os.path.dirname(PROXY), "gitcache")
os.makedirs(CACHE, exist_ok=True)
VANITY = {"golang.org/x/": "github.com/golang/", "rsc.io/": "github.com/rsc/"}
GOPKG = {"gopkg.in/yaml.v2": "github.com/go-yaml/yaml", "gopkg.in/yaml.v3": "github.com/go-yaml/yaml", "gopkg.in/check.v1": "github.com/go-check/check"}
def repo_of(mod):
    if mod in GOPKG: return GOPKG[mod], ""
    for k, v in VANITY.items():
        if mod.startswith(k): mod = v + mod[len(k):]
    parts = mod.split("/")
    repo = "/".join(parts[:3]); sub = "/".join(parts[3:])
    return repo, sub
def git(repo_dir, *a, inp=None):
    return subprocess.run(["git", "-C", repo_dir, *a], capture_output=True, check=True, input=inp).stdout
def ensure(repo):
    d = os.path.join(CACHE, repo.replace("/", "_"))
    if not os.path.exists(d):
        subprocess.run(["git", "clone", "-q", "--bare", "--filter=blob:none", "https://" + repo, d], check=True)
    return d
def commit_for(d, ver, sub):
    m = re.match(r".*[-.](\d{14})-([0-9a-f]{12})$", ver.replace("+incompatible", ""))
    if m: return git(d, "rev-parse", m.group(2) + "^{commit}").decode().strip()
    v = ver.replace("+incompatible", "")
    for tag in ([sub + "/" + v] if sub and not re.fullmatch(r"v\d+", sub) else []) + [v]:
        try: return git(d, "rev-parse", tag + "^{commit}").decode().strip()
        except subprocess.CalledProcessError: pass
    raise Exception(f"no tag {v} in {d}")
def build(mod, ver):
    out = os.path.join(PROXY, mod.lower() if False else escape(mod), "@v")
    if os.path.exists(os.path.join(out, ver + ".zip")): return
    repo, sub = repo_of(mod)
    d = ensure(repo)
    c = commit_for(d, ver, sub)
    # module root: sub dir if it has a go.mod, else repo root (major-version-suffix-in-root case)
    files = git(d, "ls-tree", "-r", "--name-only", c).decode().splitlines()
    root = sub if sub and (sub + "/go.mod") in files else ""
    if sub and not root and not re.fullmatch(r"v\d+", sub) and mod not in GOPKG:
        root = sub
    pre = (root + "/") if root else ""
    gomod = (pre + "go.mod")
    modtxt = git(d, "show", f"{c}:{gomod}") if gomod in files else f"module {mod}\n".encode()
    # nested modules to exclude
    nested = {os.path.dirname(f) for f in files if f.endswith("/go.mod") and f.startswith(pre) and f != gomod}
    t = git(d, "show", "-s", "--format=%cI", c).decode().strip()
    os.makedirs(out, exist_ok=True)
    buf = io.BytesIO(); z = zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED)
    tar = subprocess.run(["git", "-C", d, "archive", "--format=zip", c] + ([root] if root else []), capture_output=True, check=True).stdout
    src = zipfile.ZipFile(io.BytesIO(tar))
    for info in src.infolist():
        n = info.filename
        if n.endswith("/") or not n.startswith(pre): continue
        if any(n.startswith(x + "/") for x in nested): continue
        rel = n[len(pre):]
        if "vendor/" in rel: continue
        z.writestr(f"{mod}@{ver}/{rel}", src.read(n))
    z.close()
    open(os.path.join(out, ver + ".zip"), "wb").write(buf.getvalue())
    open(os.path.join(out, ver + ".mod"), "wb").write(modtxt)
    json.dump({"Version": ver, "Time": t}, open(os.path.join(out, ver + ".info"), "w"))
    lst = os.path.join(out, "list"); vs = set(open(lst).read().split()) if os.path.exists(lst) else set(); vs.add(ver)
    open(lst, "w").write("\n".join(sorted(vs)) + "\n")
    print("ok", mod, ver, flush=True)
def escape(p): return re.sub(r"[A-Z]", lambda m: "!" + m.group(0).lower(), p)
if __name__ == "__main__":
    want = set()
    for f in sys.argv[2:]:
        for line in open(f):
            p = line.split()
            if len(p) >= 2: want.add((p[0], p[1].replace("/go.mod", "")))
    for mod, ver in sorted(want):
        try: build(mod, ver)
        except Exception as ex: print("FAIL", mod, ver, ex, flush=True)
