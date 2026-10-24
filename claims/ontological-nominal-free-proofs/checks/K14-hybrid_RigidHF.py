"""Thread F check (strict, full-name matching) for Programme.F.RigidHF.

Embeds the Lean file (sha256-pinned), compiles it against the read-only library at /library, and
runs v4's detector (HybridAudit: `#hybrid_audit` witness mode and `#hybrid_all` whole-term mode)
on the module, matching FULLY QUALIFIED names (cf. sk's P6: the library wrapper compares short
names). Asserts:
  1. the file compiles with no error and no sorry; `#print axioms` shows no sorryAx;
  2. no named theorem is hybrid, inheriting, or whole-term (EXTRA) flagged, and whole-term mode reports;
  2b. (if FORBID) the transitive constant closure of each proof avoids every F_WORKLIST name of
     the module, ACTUAL-only hybrids included (stricter than the detector, whose closure ignores ACTUAL);
  3. negative control: a control module in the same namespace that re-exports the original
     (hybrid) library theorem is flagged under its full name, so the matcher is live.
Exits 0 only if all hold.
"""
import hashlib, os, re, subprocess, sys, tempfile

SRC = "import OpenQuestions.Ax1GenRigidVariant2\n/-! # Thread F: hybrid-free `L_R` in `Ax1GenRigidVariant2`, no condition on positivity\n\nProof idea due to th (board P68, `agents/th/lean/Programme/F/Rigid.lean`); re-stated here in a\nseparate namespace for the strict full-name check.  v4's object-language witness `PosGlobal`\n(`A(P ψ)`) was only known to work under `RigidPos`.  For every `ψ` the guarded property\n`λx. P ψ →ᵐ ψ x` is globally positive (`Ax2a`, `Ax2b`, `Ax4`) and agrees with `ψ` wherever `ψ` is\npositive, which gives the missing half of `ConjR G PosGlobal`.  Logic **K**, no frame condition. -/\n\nnamespace Programme.F.RigidHF\n\n/-- `λx. P ψ →ᵐ ψ x` is positive at every world. -/\ntheorem guard_pos_hf (ψ : e → σ) : PosGlobal (fun x => P ψ →ᵐ ψ x) :=\n  posGlobal_of fun u =>\n    Classical.byCases\n      (fun hP : P ψ u => Ax4 ψ _ u ⟨hP, fun _ _ _ _ hy _ => hy⟩)\n      (fun hP : ¬ P ψ u => Ax4 (~ᵐψ) _ u ⟨(Ax2a' ψ u).1 hP, fun v hv _ _ _ hPv =>\n        absurd ⟨hPv, Ax2b _ u ((Ax2a' ψ u).1 hP) v hv⟩ (Ax2a ψ v).2⟩)\n\n/-- Hybrid-free proof of the module's `L_R` (same statement, via `type_of%`). -/\ntheorem L_R_hf : type_of% @L_R := fun h w =>\n  h PosGlobal G w\n    ⟨fun _ hψ => posGlobal_at hψ w,\n     fun v _hv _z _hz =>\n       ⟨fun hG ψ hψ => hG ψ (posGlobal_at hψ v),\n        fun hall ψ hPv => hall _ (guard_pos_hf ψ) hPv⟩⟩\n\nexample : type_of% @L_R_hf = type_of% @L_R := rfl\n\nend Programme.F.RigidHF\n\n#print axioms Programme.F.RigidHF.L_R_hf\n#print axioms Programme.F.RigidHF.guard_pos_hf\n"
SHA = "3cd19f904d0fd247af5296ce1fbcaa7a268365b63136e52356d4ffd0df604931"
MOD = "Programme.F.RigidHF"
NAMES = ['Programme.F.RigidHF.guard_pos_hf', 'Programme.F.RigidHF.L_R_hf']
CONTROL = 'L_R'   # name of a hybrid library theorem in the imported module
FORBID = ['L_R', 'RigidPos', 'RigidPos_of_link', 'pos_link', 'Link', 'L_R_rigidpos']     # F_WORKLIST names of the module (hybrid incl. ACTUAL-only, inheriting)

CLOSURE = """
open Lean Elab Command in
elab "#pr_closure " n:ident : command => do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[n.getId]
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      let mut cs := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
      for d in cs do
        if !seen.contains d then todo := todo.push d
  let names := seen.toList.map toString
  logInfo m!"CLOSURE {n.getId} := {names}"
"""


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
    clos = (CLOSURE + "".join(f"#pr_closure {n}\n" for n in NAMES)) if (mod == MOD and FORBID) else ""
    open(f, "w").write(f"import HybridAudit\nimport {mod}\n{checks}{clos}#hybrid_audit {mod}\n#hybrid_all {mod}\n")
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
        if FORBID:
            for n in NAMES:
                m = re.search(rf"CLOSURE {re.escape(n)} := \[(.*?)\]", out, re.S)
                assert m, f"no closure for {n}"
                cl = {x.strip() for x in m.group(1).split(",")}
                hit = sorted(cl & set(FORBID))
                assert not hit, f"{n} reaches worklist names {hit}"
            print("closure scan clean for", len(NAMES), "theorems against", FORBID)
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
