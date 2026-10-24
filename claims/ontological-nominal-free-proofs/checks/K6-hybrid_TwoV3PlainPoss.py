"""Thread F check (strict, full-name matching) for Programme.F.TwoV3PlainPoss.

Embeds the Lean file (sha256-pinned), compiles it against the read-only library at /library, and
runs v4's detector (HybridAudit: `#hybrid_audit` witness mode and `#hybrid_all` whole-term mode)
on the module, matching FULLY QUALIFIED names (cf. sk's P6: the library wrapper compares short
names). Asserts:
  1. the file compiles with no error and no sorry; `#print axioms` shows no sorryAx;
  2. no named theorem is hybrid, inheriting, or whole-term (EXTRA) flagged, and whole-term mode reports;
  3. negative control: a control module in the same namespace that re-exports the original
     (hybrid) library theorem is flagged under its full name, so the matcher is live.
Exits 0 only if all hold.
"""
import hashlib, os, re, subprocess, sys, tempfile

SRC = "import OpenQuestions.Ax1GenTwoVariant3PlainPoss\n/-! # Thread F: hybrid-free `MC_unconditional` in `Ax1GenTwoVariant3PlainPoss`\n\nv4 proves `MC_unconditional` from `OneWorld` (point properties, nominals).  The module's own\n`MC_Two` has the identical statement and a hybrid-free proof (through `G_ex_Two`, which v4's\ndetector certifies), so it is reused here. -/\n\nnamespace Programme.F.TwoV3PlainPoss\n\ntheorem MC_unconditional_hf : type_of% @MC_unconditional := MC_Two\n\nexample : type_of% @MC_unconditional_hf = type_of% @MC_unconditional := rfl\n\nend Programme.F.TwoV3PlainPoss\n\n#print axioms Programme.F.TwoV3PlainPoss.MC_unconditional_hf\n"
SHA = "02b157e36a0259e1a0ad1d03149460532a1519d2f71aa5d1dacc05341f909df3"
MOD = "Programme.F.TwoV3PlainPoss"
NAMES = ['Programme.F.TwoV3PlainPoss.MC_unconditional_hf']
CONTROL = 'MC_unconditional'   # name of a hybrid library theorem in the imported module


def compile_mod(d, mod, src, env):
    rel = mod.replace('.', '/')
    f = os.path.join(d, rel + ".lean"); os.makedirs(os.path.dirname(f), exist_ok=True)
    open(f, "w").write(src)
    o = os.path.join(d, ".lake/build/lib/lean", rel + ".olean"); os.makedirs(os.path.dirname(o), exist_ok=True)
    r = subprocess.run(["lean", "-R", d, "-o", o, f], capture_output=True, text=True, env=env, timeout=900, cwd=d)
    return r.returncode, r.stdout + r.stderr


def audit(d, mod, env):
    checks = "".join(f"#print axioms {n}\n" for n in NAMES) if mod == MOD else ""
    f = os.path.join(d, "H.lean")
    open(f, "w").write(f"import HybridAudit\nimport {mod}\n{checks}#hybrid_audit {mod}\n#hybrid_all {mod}\n")
    r = subprocess.run(["lean", f], capture_output=True, text=True, env=env, timeout=1500, cwd=d)
    out = r.stdout + r.stderr
    flagged = set(re.findall(r"^([A-Za-z_][\w'.]*):\s*\n\s+\[", out, re.M))
    m = re.search(r"inherit hybridness through their proofs: \[(.*?)\]", out, re.S)
    if m:
        flagged |= {x.strip() for x in m.group(1).split(",") if x.strip()}
    flagged |= set(re.findall(r"^EXTRA ([A-Za-z_][\w'.]*):", out, re.M))
    return r.returncode, out, flagged


def main():
    assert hashlib.sha256(SRC.encode()).hexdigest() == SHA, "embedded source changed"
    lib = os.environ.get("LIBRARY", "/library")
    with tempfile.TemporaryDirectory() as d:
        env = dict(os.environ, LEAN_PATH=os.path.join(lib, ".lake/build/lib/lean") + ":" +
                   os.path.join(d, ".lake/build/lib/lean"))
        rc, log = compile_mod(d, MOD, SRC, env)
        print(log[-3000:])
        assert rc == 0 and "error" not in log, "Lean compilation failed"
        assert "sorry" not in log, "sorry in build log"
        rc, out, flagged = audit(d, MOD, env)
        print(out[-5000:])
        assert rc == 0, "detector run failed"
        assert "sorryAx" not in out
        assert re.search(rf"^== wholeterm {re.escape(MOD)}:", out, re.M), "whole-term mode did not report"
        bad = [n for n in NAMES if n in flagged]
        assert not bad, f"flagged: {bad}"
        if CONTROL:
            imp = re.search(r"^import (\S+)", SRC, re.M).group(1)
            cmod = MOD + "Ctl"; ns = NAMES[0].rsplit('.', 1)[0]
            csrc = f"import {imp}\nnamespace {ns}\ntheorem ctl : type_of% @{CONTROL} := {CONTROL}\nend {ns}\n"
            rc, log = compile_mod(d, cmod, csrc, env)
            assert rc == 0, "control failed to compile: " + log
            rc, out, flagged = audit(d, cmod, env)
            assert ns + ".ctl" in flagged, "negative control not flagged: matcher is dead\n" + out[-2000:]
            print("control", ns + ".ctl", "flagged as expected")
    print("PASS (full-name match):", NAMES)
    return 0


if __name__ == "__main__":
    sys.exit(main())
