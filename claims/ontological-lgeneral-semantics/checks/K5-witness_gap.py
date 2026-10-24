"""Witness-gap probe for v4's conjecture (arXiv 2609.36279v4, sec:criterion-open, before ex:separating).

Builds, against the read-only library at /library, a Lean module proving the separating sentence
A ∃p.(Atom p ∧ p) of ex:separating in the shallow embedding of OpenQuestions.Ax1GenTwoVariant2,
with the nominal `Eq w` used only as the argument of `congrFun` (an equational meta head), and runs
v4's detector (`/library/tools/hybrid_check.py`, witness and whole-term mode) on it.
Asserts: (1) the module builds, no sorry; (2) axioms are [i, propext, Classical.choice, Quot.sound];
(3) the detector reports PASS (0 flags in both modes) for the three theorems.
The sentence fails in an L-general model of variant 2 (run 2, prev-K102, library
Run2.StandardKB.separating_v2) and in v4's own finitary model (Separation.lean), so a PASS here
means the detector's acceptance does not imply truth in L-general models.
"""
import os, subprocess, sys, tempfile

SRC = r'''import OpenQuestions.Ax1GenTwoVariant2
namespace ThWitnessGap

def Dm (φ : σ) : σ := ∃ᵐ q : σ, ¬ᵐ q ∧ᵐ ((q ∧ᵐ φ) ≠ᵐ ⊥ᵐ)

def Body (p : σ) : σ := ((p ≠ᵐ ⊥ᵐ) ∧ᵐ ¬ᵐ ((p ∧ᵐ Dm p) ≠ᵐ ⊥ᵐ)) ∧ᵐ p

theorem nominal_body (w : i) : Body (Eq w) w := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, rfl⟩
  · exact (Eq.mp (congrFun h w) rfl : False)
  · apply h; funext v; apply propext; constructor
    · intro hv
      obtain ⟨hwv, hd⟩ := hv
      have hd' : ∃ q : σ, ¬ q v ∧ Mprimneg (Mand q (Eq w)) Mbot v := hd
      obtain ⟨q, hq, hq2⟩ := hd'
      apply hq2; funext u; apply propext; constructor
      · intro hu
        obtain ⟨hqu, hwu⟩ := hu
        exact (hq (Eq.mp (congrArg q (hwu.symm.trans hwv)) hqu)).elim
      · intro f; exact f.elim
    · intro f; exact f.elim

theorem separating : ⌊∃ᵐ p : σ, Body p⌋ := fun w =>
  Classical.byContradiction fun H =>
    Eq.mp (congrFun (funext fun p : σ => propext ⟨fun hp : Body p w => H ⟨p, hp⟩, False.elim⟩)
      (Eq w)) (nominal_body w)

def X : σ := ∃ᵐ p : σ, Body p

theorem separating_closed : ⌊X⌋ := fun w =>
  Classical.byContradiction fun H =>
    Eq.mp (congrFun (congrFun (funext fun p : σ => funext fun v => propext
        ⟨fun hp : Mand (Body p) (Mneg X) v => hp.2 ⟨p, hp.1⟩, False.elim⟩ :
          (fun p : σ => Mand (Body p) (Mneg X)) = fun _ => Mbot) (Eq w)) w)
      ⟨nominal_body w, H⟩

end ThWitnessGap
'''

def main():
    lib = "/library"
    with tempfile.TemporaryDirectory() as d:
        out = os.path.join(d, ".lake/build/lib/lean/ThProbe")
        os.makedirs(out)
        src = os.path.join(d, "ThProbe", "WitnessGap.lean")
        os.makedirs(os.path.dirname(src))
        open(src, "w").write(SRC + "\n#print axioms ThWitnessGap.separating_closed\n#print axioms ThWitnessGap.separating\n")
        env = dict(os.environ, LEAN_PATH=os.path.join(lib, ".lake/build/lib/lean"))
        r = subprocess.run(["lean", "--root=" + d, src, "-o", os.path.join(out, "WitnessGap.olean")],
                           capture_output=True, text=True, env=env, cwd=d, timeout=100)
        log = r.stdout + r.stderr
        print(log[-1500:])
        assert r.returncode == 0, "module failed to build"
        assert "sorry" not in log, "sorry used"
        ax = "[i, propext, Classical.choice, Quot.sound]"
        assert log.count("depends on axioms: " + ax) == 2, "unexpected axioms"
        r2 = subprocess.run([sys.executable, "-I", os.path.join(lib, "tools/hybrid_check.py"), "--path", d,
                             "ThProbe.WitnessGap", "ThWitnessGap.separating_closed",
                             "ThWitnessGap.separating", "ThWitnessGap.nominal_body"],
                            capture_output=True, text=True, cwd=d, timeout=110)
        print(r2.stdout[-1500:], r2.stderr[-500:])
        assert r2.returncode == 0 and "PASS" in r2.stdout, "detector flagged the probe"
        assert "witness-mode hybrid 0" in r2.stdout and "whole-term flagged 0, EXTRA 0" in r2.stdout
    print("OK: detector (both modes) accepts a proof of the separating sentence")

if __name__ == "__main__":
    main()
