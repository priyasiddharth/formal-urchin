#!/usr/bin/env python3
"""Live conformance run: regenerate everything the suite consumes from the
Rust sources with the PINNED tools, then run the Lean suite on it.

For every manifest entry whose source exists (prep/, local/, or the
unprepped corpus file):
  1. Miri verdict (scripts/miri_local.sh) — compared to the manifest's
     `expected` block (verdict, and line where one is pinned).
  2. Charon artifact (scripts/gen_charon.sh) into .live/charon/.
  3. Certificate (scripts/gen_cert.sh), for entries that carry one.
  4. Drift: the fresh artifact/certificate against the committed one under
     charon/ (Charon's `dest_file` and its run-to-run `short_names` order
     are ignored).
Then `sb_conformance` runs on .live/charon, plain and --osea.

Exit status is nonzero when, for a SUPPORTED entry, Miri disagrees with the
manifest, Charon or the certificate run fails, a fresh file drifts from the
committed one, or either suite run fails. Unsupported entries are reported
but never fail the run.

  scripts/live.py                 # everything
  scripts/live.py --filter zst    # entries whose id contains `zst`
  scripts/live.py --update        # also copy fresh artifacts/certificates
                                  # over the committed ones (then commit)

Tools come from scripts/bootstrap_tools.sh (run it first).
"""
import argparse
import concurrent.futures as cf
import json
import os
import re
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.dirname(HERE)
LIVE = os.path.join(HERE, ".live")
TOOLCHAIN = os.environ.get("MIRI_TOOLCHAIN", "miri")


def sh(args, **kw):
    return subprocess.run(args, cwd=HERE, capture_output=True, text=True, **kw)


def source_of(e):
    """Path (relative to conformance/) of the Rust file the entry runs."""
    if e.get("prep"):
        return e["prep"]
    if e["id"].startswith("local/"):
        return e["id"] + ".rs"
    return e.get("source")


def miri_verdict(src, env, report_out=None):
    if report_out:
        env = dict(env, MIRI_REPORT_OUT=report_out)
    r = sh(["scripts/miri_local.sh", src], env=env)
    out = r.stdout.strip().splitlines()
    line = out[-1] if out else ""
    m = re.match(r"^[^:]+: ub line=(\d*) :: (.*)$", line)
    if m:
        return {"verdict": "ub", "line": int(m.group(1)) if m.group(1) else None,
                "msg": m.group(2)}
    if re.match(r"^[^:]+: ok$", line):
        return {"verdict": "ok"}
    if re.match(r"^[^:]+: panic", line):
        return {"verdict": "panic", "msg": line}
    return {"verdict": "error", "msg": (line + " " + r.stderr.strip()[:300]).strip()}


def normalized(path):
    j = json.load(open(path))
    t = j.get("translated")
    if isinstance(t, dict):
        t.get("options", {}).pop("dest_file", None)
        if isinstance(t.get("short_names"), list):
            t["short_names"].sort(key=lambda x: json.dumps(x, sort_keys=True))
    return j


def run_entry(e, env):
    t0 = time.time()
    res = run_entry_(e, env)
    res["secs"] = time.time() - t0
    return res


def run_entry_(e, env):
    src = source_of(e)
    # an xfail-model entry is checked against Miri like a supported one;
    # only the MODEL's verdict is the documented divergence
    res = {"id": e["id"], "supported": e["status"] in ("supported", "xfail-model"),
           "problems": [],
           "notes": []}
    if not src or not os.path.exists(os.path.join(HERE, src)):
        res["notes"].append(f"no source ({src})")
        if res["supported"]:
            res["problems"].append(f"source missing: {src}")
        return res

    # 1. Miri — on UB its own account of it goes to `<artifact>.miri.txt`
    # beside the artifact (the harness's reason check reads it)
    art0 = e.get("artifact")
    report_rel = art0[:-len(".ullbc.json")] + ".miri.txt" if art0 and art0.endswith(".ullbc.json") else None
    report_fresh = os.path.join(LIVE, "charon", report_rel) if report_rel else None
    if report_fresh:
        os.makedirs(os.path.dirname(report_fresh), exist_ok=True)
        if os.path.exists(report_fresh):
            os.remove(report_fresh)
    mv = miri_verdict(src, env, report_fresh)
    res["miri"] = mv
    exp = e.get("expected") or {}
    if mv["verdict"] != exp.get("verdict"):
        res["problems"].append(f"miri says {mv['verdict']}, manifest expects "
                               f"{exp.get('verdict')}: {mv.get('msg', '')}"[:300])
    elif "line" in exp and mv.get("line") != exp["line"]:
        res["problems"].append(f"miri UB line {mv.get('line')}, manifest pins {exp['line']}")

    # 2. Charon
    art = e.get("artifact")
    if not art:
        res["notes"].append("no artifact in the manifest")
        return res
    stem = os.path.basename(src)[:-3]
    out_dir = os.path.join(LIVE, "charon", os.path.dirname(art))
    os.makedirs(out_dir, exist_ok=True)
    produced = os.path.join(out_dir, stem + ".ullbc.json")
    fresh = os.path.join(LIVE, "charon", art)
    r = sh(["scripts/gen_charon.sh", src], env=dict(env, CHARON_OUT=out_dir))
    if r.returncode != 0 or not os.path.exists(produced):
        err = [l for l in r.stderr.splitlines() if "error" in l.lower()]
        res["problems"].append("charon failed: " + (err[0] if err else r.stderr[-200:]).strip())
        return res
    # Miri's UB report, drift-checked like the artifact
    if report_fresh and os.path.exists(report_fresh):
        committed_r = os.path.join(HERE, "charon", report_rel)
        if not os.path.exists(committed_r) or open(committed_r).read() != open(report_fresh).read():
            res.setdefault("drift", []).append(report_rel)
    if produced != fresh:
        os.replace(produced, fresh)
    committed = os.path.join(HERE, "charon", art)
    if not os.path.exists(committed):
        res["notes"].append("new artifact (none committed)")
        res.setdefault("drift", []).append(art)
    elif normalized(fresh) != normalized(committed):
        res.setdefault("drift", []).append(art)

    # 3. Certificate
    cert = e.get("certificate")
    if cert:
        r = sh(["scripts/gen_cert.sh", src],
               env=dict(env, CERT_CHARON_DIR=os.path.dirname(fresh)))
        fresh_cert = os.path.join(LIVE, "charon", cert)
        if os.path.join(os.path.dirname(fresh), stem + ".cert.json") != fresh_cert:
            os.replace(os.path.join(os.path.dirname(fresh), stem + ".cert.json"), fresh_cert)
        if r.returncode != 0 or not os.path.exists(fresh_cert):
            res["problems"].append("certificate failed: " + r.stderr.strip()[-300:])
        else:
            committed = os.path.join(HERE, "charon", cert)
            if not os.path.exists(committed) or json.load(open(fresh_cert)) != json.load(open(committed)):
                res.setdefault("drift", []).append(cert)
    return res


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--filter", default="")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    ap.add_argument("--update", action="store_true",
                    help="copy fresh supported artifacts/certificates into charon/")
    ap.add_argument("--no-suite", action="store_true", help="skip the Lean suite")
    a = ap.parse_args()

    manifest = json.load(open(os.path.join(HERE, "manifest.json")))
    entries = [e for e in manifest["tests"] if a.filter in e["id"]]

    # The pin guard: the Miri doing the judging must be the submodule's.
    # the TOOL pin: PIN's miri_tool_commit (upstream Miri plus our
    # observation-only certificate-event patch; vendor/miri adds
    # tests/formal-urchin on top)
    rev = next(l.split(":", 1)[1].strip() for l in open(os.path.join(HERE, "PIN"))
               if l.startswith("miri_tool_commit:"))
    ver = subprocess.run(["cargo", f"+{TOOLCHAIN}", "miri", "--version"],
                         capture_output=True, text=True).stdout.strip()
    if f"({rev[:10]} " not in ver:
        sys.exit(f"live: `cargo +{TOOLCHAIN} miri` is {ver or 'missing'}, not the pinned "
                 f"{rev[:10]}; run scripts/bootstrap_tools.sh")
    print(f"live: {ver}; {len(entries)} entries, {a.jobs} jobs", flush=True)

    shutil.rmtree(os.path.join(LIVE, "charon"), ignore_errors=True)
    os.makedirs(os.path.join(LIVE, "charon"), exist_ok=True)
    # resolved once, so the parallel Miri runs never touch cargo-miri
    env = dict(os.environ,
               MIRI_SYSROOT=os.path.join(HERE, ".tools", "miri-sysroot"),
               MIRI_BIN=subprocess.run(["rustup", "which", "--toolchain", TOOLCHAIN, "miri"],
                                       capture_output=True, text=True, check=True).stdout.strip())
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        results = list(ex.map(lambda e: run_entry(e, env), entries))

    failed = False
    report = []
    for r in results:
        drift = r.get("drift", [])
        tag = "SUP" if r["supported"] else "uns"
        mv = r.get("miri", {})
        miri = mv.get("verdict", "-") + (f"@{mv['line']}" if mv.get("line") else "")
        status = "ok"
        if r["problems"] or (drift and r["supported"] and not a.update):
            status = "FAIL" if r["supported"] else "note"
        if status == "FAIL":
            failed = True
        detail = r["problems"] + [f"drift: {d}" for d in drift] + r["notes"]
        report.append(f"{status:4} {tag} {r['id']:<60} {r['secs']:5.1f}s miri={miri}  "
                      + " | ".join(detail))
    os.makedirs(LIVE, exist_ok=True)
    with open(os.path.join(LIVE, "report.txt"), "w") as f:
        f.write("\n".join(report) + "\n")
    for line in report:
        if not line.startswith("ok"):
            print(line)
    sup = [r for r in results if r["supported"]]
    agree = sum(1 for r in sup if "miri" in r and not any(p.startswith("miri") for p in r["problems"]))
    ndrift = sum(1 for r in sup if r.get("drift"))
    print(f"live: Miri agrees with the manifest on {agree}/{len(sup)} supported entries; "
          f"{ndrift} supported entries drift from the committed artifacts "
          f"(report: conformance/.live/report.txt)")

    if a.update:
        for r in results:
            if not r["supported"]:
                continue
            for rel in r.get("drift", []):
                dst = os.path.join(HERE, "charon", rel)
                os.makedirs(os.path.dirname(dst), exist_ok=True)
                shutil.copyfile(os.path.join(LIVE, "charon", rel), dst)
                print(f"live: updated charon/{rel}")

    if not a.no_suite:
        if subprocess.run(["lake", "build", "sb_conformance"], cwd=REPO).returncode != 0:
            sys.exit("live: lake build sb_conformance failed")
        base = ["lake", "exe", "sb_conformance", "--manifest", os.path.join(HERE, "manifest.json"),
                "--charon-dir", os.path.join(LIVE, "charon")]
        if a.filter:
            base += ["--filter", a.filter]
        for extra in ([], ["--osea"]):
            print(f"live: sb_conformance {' '.join(extra) or '(mirlite)'}", flush=True)
            if subprocess.run(base + extra, cwd=REPO).returncode != 0:
                failed = True
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
