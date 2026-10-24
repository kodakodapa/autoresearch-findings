"""Thread F check (strict, full-name matching) for Programme.F.TwoV3Plain.

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

SRC = "import OpenQuestions.Ax1GenTwoVariant3Plain\n/-! # Thread F: hybrid-free `Ax1Gen_of_Two` and `Two_equivalent` in `Ax1GenTwoVariant3Plain`\n\nv4's proof of `Ax1Gen_of_Two` goes through `R_Id` (modal collapse at the nominal\n`fun u => u = w`).  Here the singleton and empty instances are carried to every successor by\nmodal collapse at object-language sentences built from `Φ` and the single member `ψ₀`:\n`Φ ψ₀` and `∀ᵐ ψ, Φ ψ →ᵐ ψ =ᵐ ψ₀` (singleton), `∀ᵐ ψ, ¬ᵐ Φ ψ` (empty).  Collapse itself is the\nmodule's `MC_Two_unconditional`, which the detector certifies.  No frame condition, no nominal. -/\n\nnamespace Programme.F.TwoV3Plain\n\n/-- Hybrid-free proof of the module's `Ax1Gen_of_Two` (same statement, via `type_of%`). -/\ntheorem Ax1Gen_of_Two_hf : type_of% @Ax1Gen_of_Two := by\n  intro Φ φ w ⟨pos, conj⟩\n  by_cases two : TwoMembers Φ w\n  · exact Ax1GenTwo Φ φ w ⟨⟨two, pos⟩, conj⟩\n  by_cases hex : (∃ᵐ ψ, Φ ψ) w\n  · obtain ⟨ψ₀, m0⟩ := hex\n    have uniq : (∀ᵐ ψ, Φ ψ →ᵐ (ψ =ᵐ ψ₀)) w := fun ψ hψ =>\n      Classical.byContradiction fun hne => two ⟨ψ, ψ₀, hψ, m0, hne⟩\n    have incl : (ψ₀ ⊃ᴺ φ) w := fun v rv y ay h =>\n      have uv := MC_Two_unconditional (∀ᵐ ψ, Φ ψ →ᵐ (ψ =ᵐ ψ₀)) w uniq v rv\n      (conj v rv y ay).2 (fun ψ hψ => by\n        have hψ0 : ψ = ψ₀ := uv ψ hψ\n        rw [hψ0]; exact h)\n    exact Ax4 ψ₀ φ w ⟨pos ψ₀ m0, incl⟩\n  · have none : (∀ᵐ ψ, ¬ᵐ (Φ ψ)) w := fun ψ hψ => hex ⟨ψ, hψ⟩\n    have incl : ((fun _ : e => ⊤ᵐ) ⊃ᴺ φ) w := fun v rv y ay _ =>\n      have nv := MC_Two_unconditional (∀ᵐ ψ, ¬ᵐ (Φ ψ)) w none v rv\n      (conj v rv y ay).2 (fun ψ hψ => (nv ψ hψ).elim)\n    exact Ax4 _ φ w ⟨PTop w, incl⟩\n\n/-- Hybrid-free proof of the module's `Two_equivalent` (same statement, via `type_of%`). -/\ntheorem Two_equivalent_hf : type_of% @Two_equivalent :=\n  ⟨fun _ => Ax1Gen_of_Two_hf, Two_weaker⟩\n\nexample : type_of% @Ax1Gen_of_Two_hf = type_of% @Ax1Gen_of_Two := rfl\nexample : type_of% @Two_equivalent_hf = type_of% @Two_equivalent := rfl\n\n/-- Hybrid-free `loc_of_conj`: no reflexivity.  Seriality gives a successor `v`; modal collapse\ncarries `z`'s actuality to `v` and the negation of the local equivalence (an `L`-sentence with\nthe individual `z` free) from `w` to `v`, where `conj` refutes it. -/\ntheorem loc_of_conj_hf : type_of% @loc_of_conj := by\n  intro φ Φ w z conj a\n  obtain ⟨v, rv⟩ := Serial w\n  have av : (∃ᴱ y, y =ᵐ z) v :=\n    MC_Two_unconditional (∃ᴱ y, y =ᵐ z) w ⟨z, a, rfl⟩ v rv\n  obtain ⟨y, ay, hyz⟩ := av\n  have hyz' : y = z := hyz\n  subst hyz'\n  refine Classical.byContradiction fun hn => ?_\n  exact MC_Two_unconditional (¬ᵐ(φ y ↔ᵐ (∀ᵐ ψ, Φ ψ →ᵐ ψ y))) w hn v rv (conj v rv y ay)\n\n/-- Hybrid-free `P_of_conj`. -/\ntheorem P_of_conj_hf : type_of% @P_of_conj := by\n  intro Φ φ w pos conj\n  exact Ax1Gen_of_Two_hf Φ φ w ⟨pos, conj⟩\n\n/-- Hybrid-free `ae_Two_nominal`: the module's own `ae_Two`. -/\ntheorem ae_Two_nominal_hf : type_of% @ae_Two_nominal := ae_Two\n\n/-- Hybrid-free `G_ex_Two_unconditional_nominal`. -/\ntheorem G_ex_Two_unconditional_nominal_hf : type_of% @G_ex_Two_unconditional_nominal :=\n  G_ex_Two ae_Two\n\n/-- Hybrid-free `only_top_and_empty_domain_False`: `ae_Two` refutes the empty domain. -/\ntheorem only_top_and_empty_domain_False_hf : type_of% @only_top_and_empty_domain_False := by\n  intro w _ empty\n  exact empty (ae_Two w)\n\n/-- Hybrid-free `only_top_and_empty_domain`. -/\ntheorem only_top_and_empty_domain_hf : type_of% @only_top_and_empty_domain := by\n  intro w _ empty\n  exact empty (ae_Two w)\n\nexample : type_of% @loc_of_conj_hf = type_of% @loc_of_conj := rfl\nexample : type_of% @P_of_conj_hf = type_of% @P_of_conj := rfl\nexample : type_of% @ae_Two_nominal_hf = type_of% @ae_Two_nominal := rfl\nexample : type_of% @G_ex_Two_unconditional_nominal_hf = type_of% @G_ex_Two_unconditional_nominal := rfl\nexample : type_of% @only_top_and_empty_domain_False_hf = type_of% @only_top_and_empty_domain_False := rfl\nexample : type_of% @only_top_and_empty_domain_hf = type_of% @only_top_and_empty_domain := rfl\n\nend Programme.F.TwoV3Plain\n\n#print axioms Programme.F.TwoV3Plain.Ax1Gen_of_Two_hf\n#print axioms Programme.F.TwoV3Plain.Two_equivalent_hf\n#print axioms Programme.F.TwoV3Plain.loc_of_conj_hf\n#print axioms Programme.F.TwoV3Plain.P_of_conj_hf\n#print axioms Programme.F.TwoV3Plain.ae_Two_nominal_hf\n#print axioms Programme.F.TwoV3Plain.G_ex_Two_unconditional_nominal_hf\n#print axioms Programme.F.TwoV3Plain.only_top_and_empty_domain_False_hf\n#print axioms Programme.F.TwoV3Plain.only_top_and_empty_domain_hf\n"
SHA = "c9f9c79d6482507216aa4c7646fa75a784a271464e633ee4ebc40740b4545f61"
MOD = "Programme.F.TwoV3Plain"
NAMES = ['Programme.F.TwoV3Plain.Ax1Gen_of_Two_hf', 'Programme.F.TwoV3Plain.Two_equivalent_hf', 'Programme.F.TwoV3Plain.loc_of_conj_hf', 'Programme.F.TwoV3Plain.P_of_conj_hf', 'Programme.F.TwoV3Plain.ae_Two_nominal_hf', 'Programme.F.TwoV3Plain.G_ex_Two_unconditional_nominal_hf', 'Programme.F.TwoV3Plain.only_top_and_empty_domain_False_hf', 'Programme.F.TwoV3Plain.only_top_and_empty_domain_hf']
CONTROL = 'Two_equivalent'   # name of a hybrid library theorem in the imported module
FORBID = ['AllExist', 'NoNecExist', 'OneWorld', 'OneWorld_abs', 'R_Id', 'Ax1Gen_of_Two', 'FrRefl_Two', 'G_ex_Two_unconditional_nominal', 'Id_Two', 'MC_OneWorld', 'P_of_conj', 'ReflR', 'Two_equivalent', 'ae_Two_nominal', 'loc_of_conj', 'only_top_and_empty_domain', 'only_top_and_empty_domain_False']     # F_WORKLIST names of the module (hybrid incl. ACTUAL-only, inheriting)

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
