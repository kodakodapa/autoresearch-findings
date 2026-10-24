"""Thread F check (strict, full-name matching) for Programme.F.TwoV3Th4.

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

SRC = "import OpenQuestions.Ax1GenTwoVariant3Th4\n/-! # Thread F: hybrid-free `G_ex_Two_hybrid` and `AllExist_Two` in `Ax1GenTwoVariant3Th4`\n\n`const` (every lifted proposition is constant) is proved exactly as in `Programme.F.TwoV3`, from\n`Ax1GenTwo`, `Ax2a`, `Ax2b`, `Ax3`, `Ax4` and no frame condition; with the postulated `Th4` it moves\nthe God-like being of a successor back to the world of evaluation.  `AllExist_Two` takes th's\nwitness `z = y ∧ ¬(∃ᴱ u, u = z)` (P8) in place of a bare `existsAt`. -/\n\nnamespace Programme.F.TwoV3Th4\n\nprivate theorem topEq : (~ᵐ(fun _ : e => ⊥ᵐ)) = (fun _ : e => ⊤ᵐ) := by funext x v; simp\n\nprivate theorem neBot {φ : e → σ} {x : e} {w : i} (h : φ x w) : φ ≠ (fun _ : e => ⊥ᵐ) :=\n  fun h' => (congrFun (congrFun h' x) w ▸ h : ⊥ᵐ w)\n\n/-- A positive non-empty property makes `⊤` positive. -/\nprivate theorem top_of {φ : e → σ} {w : i} (hφ : P φ w) (ne : φ ≠ (fun _ : e => ⊥ᵐ)) :\n    P (fun _ : e => ⊤ᵐ) w :=\n  Ax4 φ _ w ⟨hφ, fun _ _ => ⟨ne, fun _ _ _ => trivial⟩⟩\n\n/-- With `P G` and `¬ P ⊥` at `w`, a God-like being is actual at some successor of `w`. -/\nprivate theorem dia_G {w : i} (PG : P G w) (nb : ¬ P (fun _ : e => ⊥ᵐ) w) : (◇(∃ᴱ x, G x)) w :=\n  Classical.byContradiction fun hn =>\n    have Gne : G ≠ (fun _ : e => ⊥ᵐ) := fun h => nb (h ▸ PG)\n    nb (Ax4 G _ w ⟨PG, fun v hv => ⟨Gne, fun z hz hG => hn ⟨v, hv, z, hz, hG⟩⟩⟩)\n\n/-- At a world with an actual God-like `g`, every non-empty property is exemplified at some\nsuccessor (else it is a vacuous essence of `g`, against `E g u`). -/\nprivate theorem reach {g : e} {u : i} (hG : G g u) (χ : e → σ) (ne : χ ≠ (fun _ : e => ⊥ᵐ)) :\n    ∃ u1, u 𝗿 u1 ∧ ∃ y, χ y u1 :=\n  Classical.byContradiction fun hn =>\n    have Eg : E g u := hG E (Ax3 u)\n    have ess : Ess χ g u := fun _ _ v hv =>\n      ⟨ne, fun y _ hχ => (hn ⟨v, hv, y, hχ⟩).elim⟩\n    let ⟨v, hv⟩ := Serial u\n    let ⟨y, _, hχ⟩ := Eg χ ess v hv\n    hn ⟨v, hv, y, hχ⟩\n\n/-- **Every lifted proposition is constant**, hybrid-free and with no frame condition. -/\ntheorem const (q : σ) (w v : i) (hw : q w) : q v :=\n  Classical.byContradiction fun hv =>\n    let a : e := Classical.ofNonempty\n    let χ : e → σ := fun _ => q\n    let χn : e → σ := fun _ => ¬ᵐ q\n    have ne1 : χ ≠ (fun _ => ⊥ᵐ) := @neBot χ a w hw\n    have ne2 : χn ≠ (fun _ => ⊥ᵐ) := @neBot χn a v hv\n    -- at every world `⊤` is positive, `⊥` is not, and `P` has two members\n    have top : ∀ t, P (fun _ : e => ⊤ᵐ) t := fun t =>\n      ((Ax2a χ t).1).elim (fun h => top_of h ne1) (fun h => top_of h ne2)\n    have nb : ∀ t, ¬ P (fun _ : e => ⊥ᵐ) t := fun t hb => (Ax2a _ t).2 ⟨hb, topEq ▸ top t⟩\n    have two : ∀ t, TwoMembers P t := fun t =>\n      ((Ax2a χ t).1).elim\n        (fun h => ⟨_, χ, top t, h, fun h' => hv (Eq.mp (congrFun (congrFun h' a) v) trivial)⟩)\n        (fun h => ⟨_, ~ᵐχ, top t, h, fun h' => Eq.mp (congrFun (congrFun h' a) w) trivial hw⟩)\n    have PG : P G w := Ax1GenTwo P G w ⟨⟨two w, fun _ h => h⟩, fun _ _ _ _ => Iff.rfl⟩\n    let ⟨u, _, g, _, hG⟩ := dia_G PG (nb w)\n    let ⟨u1, r1, _, hq1⟩ := reach hG χn ne2\n    let ⟨u2, r2, _, hq2⟩ := reach hG χ ne1\n    let ⟨z1, _, hz1⟩ := Th2 g u hG u1 r1\n    let ⟨z2, _, hz2⟩ := Th2 g u hG u2 r2\n    (Classical.em (q u)).elim\n      (fun hu => hq1 (hz1 χ (Ax2b χ u (PosOfGod hG hu) u1 r1)))\n      (fun hu => hz2 χn (Ax2b χn u (PosOfGod hG hu) u2 r2) hq2)\n\ntheorem G_ex_Two_hybrid_hf : type_of% @G_ex_Two_hybrid := fun w =>\n  let ⟨v, _, hex⟩ := Th4 w\n  const _ v w hex\n\ntheorem AllExist_Two_pt (someNonGod : ∃ u z, (∃ᴱ y, G y) u ∧ ¬ G z u) (w : i) (y : e) :\n    y @ᵐ w :=\n  Classical.byContradiction fun ny =>\n    let ⟨g, _, hG⟩ := G_ex_Two someNonGod w\n    have Eg : E g w := hG E (Ax3 w)\n    let φ : e → σ := fun z => (z =ᵐ y) ∧ᵐ ¬ᵐ(∃ᴱ u, u =ᵐ z)\n    have ess : Ess φ g w := fun _ _ _ _ =>\n      ⟨fun h => (congrFun (congrFun h y) w ▸\n          (⟨rfl, fun ⟨_, hu, he⟩ => ny (he ▸ hu)⟩ : φ y w) : ⊥ᵐ w),\n       fun z hz ⟨_, hnz⟩ => (hnz ⟨z, hz, rfl⟩).elim⟩\n    let ⟨v, hv⟩ := Serial w\n    let ⟨z, hz, _, hnz⟩ := Eg φ ess v hv\n    hnz ⟨z, hz, rfl⟩\n\ntheorem AllExist_Two_hf : type_of% @AllExist_Two := AllExist_Two_pt\n\nexample : type_of% @G_ex_Two_hybrid_hf = type_of% @G_ex_Two_hybrid := rfl\nexample : type_of% @AllExist_Two_hf = type_of% @AllExist_Two := rfl\n\nend Programme.F.TwoV3Th4\n\n#print axioms Programme.F.TwoV3Th4.G_ex_Two_hybrid_hf\n#print axioms Programme.F.TwoV3Th4.AllExist_Two_hf\n"
SHA = "c1c0cb718fac25d406424156b93e709821c946200b5dbaa6760bd2ec92579753"
MOD = "Programme.F.TwoV3Th4"
NAMES = ['Programme.F.TwoV3Th4.G_ex_Two_hybrid_hf', 'Programme.F.TwoV3Th4.AllExist_Two_hf']
CONTROL = 'G_ex_Two_hybrid'   # name of a hybrid library theorem in the imported module


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
