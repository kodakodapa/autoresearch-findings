"""Thread F check (strict, full-name matching) for Programme.F.HOML3.

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

SRC = 'import OpenQuestions.GoedelVariantHOML3inS4oneFile\n/-! # Thread F: hybrid-free proofs for `GoedelVariantHOML3inS4oneFile`\n\nv4 proves `Th3`, `MC`, `EssDetermined`, `UniqueEss1`, ... through `NoNecExist` / `OneWorld`, whose\nwitnesses are nominals.  The module already holds hybrid-free `_K` lemmas (`G_ex`, `Serial`,\n`Reach_K`, `EssMemI_K`, `MC_K`, ...); here every flagged statement is re-proved from those.\nNew steps: `AllExist` with the witness `¬(∃ᴱ u, u = z)` in place of a bare `existsAt`\n(following th, P8), and `EssSupp` / `EssDetermined` for *arbitrary* worlds `v`, `u` (not only\nsuccessors) by `Reach_K` at the constant properties `φ y ∧ y ≠ x` and `¬ φ x`. -/\n\nnamespace Programme.F.HOML3\n\n/-- Pointwise `AllExist`; witness `fun z => z = y ∧ ¬(∃ᴱ u, u = z)`. -/\ntheorem AllExist_pt (w : i) (y : e) : y @ᵐ w :=\n  Classical.byContradiction fun ny =>\n    let ⟨g, _, hG⟩ := G_ex w\n    have Eg : E g w := hG E (Ax3 w)\n    let φ : e → σ := fun z => (z =ᵐ y) ∧ᵐ ¬ᵐ(∃ᴱ u, u =ᵐ z)\n    have ess : Ess φ g w := fun _ _ _ _ =>\n      ⟨fun h => (congrFun (congrFun h y) w ▸\n          (⟨rfl, fun ⟨_, hu, he⟩ => ny (he ▸ hu)⟩ : φ y w) : ⊥ᵐ w),\n       fun z hz ⟨_, hnz⟩ => (hnz ⟨z, hz, rfl⟩).elim⟩\n    let ⟨v, hv⟩ := Serial w\n    let ⟨z, hz, _, hnz⟩ := Eg φ ess v hv\n    hnz ⟨z, hz, rfl⟩\n\ntheorem AllExist_hf : type_of% @AllExist := AllExist_pt\n\ntheorem Th3_hf : type_of% @Th3 := Th3_K\ntheorem Th5_hf : type_of% @Th5 := Th5_K\ntheorem MC_hf : type_of% @MC := MC_K\ntheorem MCdual_hf : type_of% @MCdual := MCdual_K\ntheorem Triv_hf : type_of% @Triv := Triv_K\ntheorem UniqueEss3_hf : type_of% @UniqueEss3 := UniqueEss3_K\n\n/-- v4\'s `EssMemI_K` run on `AllExist_pt` instead of the library\'s `AllExistI`, whose\n`AllExist` carries an ACTUAL-flagged witness (sk, P46). -/\ntheorem EssMemI_pt {φ : e → σ} {x : e} {w : i} (h : Ess φ x w) : φ x w :=\n  Classical.byContradiction fun hn =>\n    let ⟨u, hu⟩ := Serial w\n    let ⟨hne, _⟩ := h (fun z => ¬ᵐ(φ z)) hn u hu\n    let ⟨v, hv, y, hy⟩ := Reach_K φ w hne\n    (h (fun z => ¬ᵐ(φ z)) hn v hv).2 y (AllExist_pt v y) hy hy\n\ntheorem EssMemI_hf : type_of% @EssMemI := EssMemI_pt\ntheorem EssMem_hf : type_of% @EssMem := fun _ _ _ h => EssMemI_pt h\ntheorem Ess_iff_Ess2_hf : type_of% @Ess_iff_Ess2 := fun _ _ _ =>\n  ⟨fun h => Ess2_of_Ess h (EssMemI_pt h), Ess_of_Ess2⟩\n\n/-- `EssSupp` at an arbitrary world `v`: were `z ≠ x`, the constant property\n"`φ z` and `z ≠ x`" would be non-empty, hence exemplified at a successor of `w` (`Reach_K`),\nby an actual being (`AllExist_pt`), against the essence clause for `fun y => y = x`. -/\ntheorem EssSupp_hf : type_of% @EssSupp := by\n  intro φ x w h z v _ pz\n  refine Classical.byContradiction fun hzx => ?_\n  let χ : e → σ := fun _ => φ z ∧ᵐ ¬ᵐ(z =ᵐ x)\n  have hne : χ ≠ (fun _ : e => ⊥ᵐ) := fun hc =>\n    (congrFun (congrFun hc z) v ▸ (⟨pz, hzx⟩ : χ z v) : ⊥ᵐ v)\n  obtain ⟨u, hu, _, hφ, hn⟩ := Reach_K χ w hne\n  exact hn ((h (fun y => y =ᵐ x) rfl u hu).2 z (AllExist_pt u z) hφ)\n\n/-- `EssDetermined`: `⊆` by `EssSupp_hf`; `⊇` because `φ x` holds at `w` (`EssMemI_pt`) and\nat every successor (`MC_K`), and a world where it fails would make the constant property\n`¬ φ x` non-empty, hence true at a successor (`Reach_K`). -/\ntheorem EssDetermined_hf : type_of% @EssDetermined := by\n  intro φ x w h\n  funext z u\n  refine propext ⟨fun hφ => EssSupp_hf h (AllExist_pt u z) hφ, fun hzx => ?_⟩\n  subst hzx\n  refine Classical.byContradiction fun hn => ?_\n  let χ : e → σ := fun _ => ¬ᵐ(φ z)\n  have hne : χ ≠ (fun _ : e => ⊥ᵐ) := fun hc =>\n    (congrFun (congrFun hc z) u ▸ (hn : χ z u) : ⊥ᵐ u)\n  obtain ⟨v, hv, _, hnv⟩ := Reach_K χ w hne\n  exact hnv (MC_K (φ z) w (EssMemI_pt h) v hv)\n\n/-- `UniqueEss1`, `UniqueEss2` from `EssDetermined_hf` (as v4 does from `EssDetermined`). -/\ntheorem UniqueEss1_hf : type_of% @UniqueEss1 :=\n  fun _ _ _ _ ⟨hφ, hψ⟩ _ _ _ _ => by\n    rw [EssDetermined_hf hφ, EssDetermined_hf hψ]; exact Iff.rfl\ntheorem UniqueEss2_hf : type_of% @UniqueEss2 :=\n  fun _ _ _ _ ⟨hφ, hψ⟩ _ _ _ hQ => by\n    rw [EssDetermined_hf hφ] at hQ; rw [EssDetermined_hf hψ]; exact hQ\n\nexample : type_of% @AllExist_hf = type_of% @AllExist := rfl\nexample : type_of% @Th3_hf = type_of% @Th3 := rfl\nexample : type_of% @Th5_hf = type_of% @Th5 := rfl\nexample : type_of% @MC_hf = type_of% @MC := rfl\nexample : type_of% @MCdual_hf = type_of% @MCdual := rfl\nexample : type_of% @Triv_hf = type_of% @Triv := rfl\nexample : type_of% @UniqueEss1_hf = type_of% @UniqueEss1 := rfl\nexample : type_of% @UniqueEss2_hf = type_of% @UniqueEss2 := rfl\nexample : type_of% @UniqueEss3_hf = type_of% @UniqueEss3 := rfl\nexample : type_of% @EssMemI_hf = type_of% @EssMemI := rfl\nexample : type_of% @EssMem_hf = type_of% @EssMem := rfl\nexample : type_of% @Ess_iff_Ess2_hf = type_of% @Ess_iff_Ess2 := rfl\nexample : type_of% @EssSupp_hf = type_of% @EssSupp := rfl\nexample : type_of% @EssDetermined_hf = type_of% @EssDetermined := rfl\n\nend Programme.F.HOML3\n\n#print axioms Programme.F.HOML3.AllExist_hf\n#print axioms Programme.F.HOML3.MC_hf\n#print axioms Programme.F.HOML3.UniqueEss2_hf\n#print axioms Programme.F.HOML3.EssDetermined_hf\n'
SHA = "20d690930ec93ffe26ea9bea00d6e7db71adc90a3f3ff65519a6eeedc02cc816"
MOD = "Programme.F.HOML3"
NAMES = ['Programme.F.HOML3.AllExist_hf', 'Programme.F.HOML3.Th3_hf', 'Programme.F.HOML3.Th5_hf', 'Programme.F.HOML3.MC_hf', 'Programme.F.HOML3.MCdual_hf', 'Programme.F.HOML3.Triv_hf', 'Programme.F.HOML3.UniqueEss3_hf', 'Programme.F.HOML3.EssMemI_hf', 'Programme.F.HOML3.EssMem_hf', 'Programme.F.HOML3.Ess_iff_Ess2_hf', 'Programme.F.HOML3.EssSupp_hf', 'Programme.F.HOML3.EssDetermined_hf', 'Programme.F.HOML3.UniqueEss1_hf', 'Programme.F.HOML3.UniqueEss2_hf']
CONTROL = 'Th3'   # name of a hybrid library theorem in the imported module
FORBID = ['AllExist', 'NoNecExist', 'OneWorld', 'EssDetermined', 'EssMem', 'EssMemI', 'EssSupp', 'Ess_iff_Ess2', 'MC', 'MCdual', 'Th3', 'Th5', 'Triv', 'UniqueEss1', 'UniqueEss2', 'UniqueEss3', 'AllExistI']     # F_WORKLIST names of the module (hybrid incl. ACTUAL-only, inheriting)

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
