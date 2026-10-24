"""Thread F check (strict, full-name matching) for Programme.F.OneV3.

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

SRC = 'import OpenQuestions.Ax1GenOneVariant3\n/-! # Thread F: hybrid-free proofs for `Ax1GenOneVariant3`\n\nv4 derives the second layer (`PTop_One_deriv`, `G_ex_One_deriv`, `One_gives_S`, ...) from\n`OneWorld`, whose proof uses the point properties `Pt x w` (nominals).  Its object-language shadow\nis `const`: every lifted proposition is constant, proved as in `Programme.F.TwoV3` with `L_One`\n(`Φ := P`) in place of `Ax1GenTwo`.  `AllActual_of_PBot` and `AllExist_One` replace the bare\n`existsAt` and `Pt` witnesses by `¬(∃ᴱ u, u = z)` and `z = y ∧ ¬(∃ᴱ u, u = z)`. -/\n\nnamespace Programme.F.OneV3\n\nprivate theorem topEq : (~ᵐ(fun _ : e => ⊥ᵐ)) = (fun _ : e => ⊤ᵐ) := by funext x v; simp\n\nprivate theorem neBot {φ : e → σ} {x : e} {w : i} (h : φ x w) : φ ≠ (fun _ : e => ⊥ᵐ) :=\n  fun h\' => (congrFun (congrFun h\' x) w ▸ h : ⊥ᵐ w)\n\n/-- A positive non-empty property makes `⊤` positive. -/\nprivate theorem top_of {φ : e → σ} {w : i} (hφ : P φ w) (ne : φ ≠ (fun _ : e => ⊥ᵐ)) :\n    P (fun _ : e => ⊤ᵐ) w :=\n  Ax4 φ _ w ⟨hφ, fun _ _ => ⟨ne, fun _ _ _ => trivial⟩⟩\n\n/-- With `P G` and `¬ P ⊥` at `w`, a God-like being is actual at some successor of `w`. -/\nprivate theorem dia_G {w : i} (PG : P G w) (nb : ¬ P (fun _ : e => ⊥ᵐ) w) : (◇(∃ᴱ x, G x)) w :=\n  Classical.byContradiction fun hn =>\n    have Gne : G ≠ (fun _ : e => ⊥ᵐ) := fun h => nb (h ▸ PG)\n    nb (Ax4 G _ w ⟨PG, fun v hv => ⟨Gne, fun z hz hG => hn ⟨v, hv, z, hz, hG⟩⟩⟩)\n\n/-- At a world with an actual God-like `g`, every non-empty property is exemplified at some\nsuccessor (else it is a vacuous essence of `g`, against `E g u`). -/\nprivate theorem reach {g : e} {u : i} (hG : G g u) (χ : e → σ) (ne : χ ≠ (fun _ : e => ⊥ᵐ)) :\n    ∃ u1, u 𝗿 u1 ∧ ∃ y, χ y u1 :=\n  Classical.byContradiction fun hn =>\n    have Eg : E g u := hG E (Ax3 u)\n    have ess : Ess χ g u := fun _ _ v hv =>\n      ⟨ne, fun y _ hχ => (hn ⟨v, hv, y, hχ⟩).elim⟩\n    let ⟨v, hv⟩ := Serial u\n    let ⟨y, _, hχ⟩ := Eg χ ess v hv\n    hn ⟨v, hv, y, hχ⟩\n\n/-- **Every lifted proposition is constant**, hybrid-free and with no frame condition. -/\ntheorem const (q : σ) (w v : i) (hw : q w) : q v :=\n  Classical.byContradiction fun hv =>\n    let a : e := Classical.ofNonempty\n    let χ : e → σ := fun _ => q\n    let χn : e → σ := fun _ => ¬ᵐ q\n    have ne1 : χ ≠ (fun _ => ⊥ᵐ) := @neBot χ a w hw\n    have ne2 : χn ≠ (fun _ => ⊥ᵐ) := @neBot χn a v hv\n    have top : P (fun _ : e => ⊤ᵐ) w :=\n      ((Ax2a χ w).1).elim (fun h => top_of h ne1) (fun h => top_of h ne2)\n    have nb : ¬ P (fun _ : e => ⊥ᵐ) w := fun hb => (Ax2a _ w).2 ⟨hb, topEq ▸ top⟩\n    let ⟨u, _, g, _, hG⟩ := dia_G (L_One w) nb\n    let ⟨u1, r1, _, hq1⟩ := reach hG χn ne2\n    let ⟨u2, r2, _, hq2⟩ := reach hG χ ne1\n    let ⟨_, _, hz1⟩ := Th2 g u hG u1 r1\n    let ⟨_, _, hz2⟩ := Th2 g u hG u2 r2\n    (Classical.em (q u)).elim\n      (fun hu => hq1 (hz1 χ (Ax2b χ u (PosOfGod hG hu) u1 r1)))\n      (fun hu => hz2 χn (Ax2b χn u (PosOfGod hG hu) u2 r2) hq2)\n\ntheorem MC_unconditional_hf : type_of% @MC_unconditional := fun φ w hφ v _ => const φ w v hφ\ntheorem MC_One_hf : type_of% @MC_One := fun φ w hφ v _ => const φ w v hφ\n\n/-- `AllActual_of_PBot` with "being non-actual" written `¬(∃ᴱ u, u = z)`. -/\ntheorem AllActual_of_PBot_hf : type_of% @AllActual_of_PBot := by\n  intro w pb\n  refine Classical.byContradiction fun h => ?_\n  let ν : e → σ := fun z => ¬ᵐ(∃ᴱ u, u =ᵐ z)\n  have Pν : P ν w := Ax1GenOne (fun ψ\' _ => ψ\' = (fun _ : e => ⊥ᵐ)) ν w\n    ⟨⟨⟨_, rfl⟩, fun _ hψ => hψ ▸ pb⟩,\n     fun _ _ z hz => ⟨fun hν => (hν ⟨z, hz, rfl⟩).elim, fun all _ => all (fun _ => ⊥ᵐ) rfl⟩⟩\n  have ne : ν ≠ (fun _ => ⊥ᵐ) := fun e => h fun z u =>\n    Classical.byContradiction fun hn =>\n      (congrFun (congrFun e z) u ▸ (fun ⟨_, hu, he⟩ => hn (he ▸ hu) : ν z u) : ⊥ᵐ u)\n  have all : ∀ ψ : e → σ, P ψ w := fun ψ =>\n    Ax4 ν ψ w ⟨Pν, fun _ _ => ⟨ne, fun y hy hν => (hν ⟨y, hy, rfl⟩).elim⟩⟩\n  exact (Ax2a (fun _ => ⊤ᵐ) w).2 ⟨all _, all _⟩\n\n/-- `¬ P ⊥`: else every positive property is empty, so every property is `⊤` or `⊥` and `E`\n(positive, `Ax3`) is `⊥`; but with everything actual (`AllActual_of_PBot_hf`) any individual\nhas `E`, each of its essences being non-empty, hence `⊤`. -/\ntheorem NotPBot_One_deriv_hf : type_of% @NotPBot_One_deriv := fun w pb =>\n  have act := AllActual_of_PBot_hf pb\n  have allbot : ∀ φ : e → σ, P φ w → φ = (fun _ : e => ⊥ᵐ) := fun φ hφ =>\n    Classical.byContradiction fun hne => (Ax2a _ w).2 ⟨pb, topEq ▸ top_of hφ hne⟩\n  let a : e := Classical.ofNonempty\n  have Ea : E a w := fun φ hess v hv =>\n    have hne : φ ≠ (fun _ => ⊥ᵐ) := (hess (fun _ => ⊤ᵐ) trivial v hv).1\n    have htop : φ = (fun _ => ⊤ᵐ) := ((Ax2a φ w).1).elim\n      (fun h => (hne (allbot φ h)).elim)\n      (fun h => funext fun z => funext fun t => propext ⟨fun _ => trivial, fun _ =>\n        Classical.byContradiction fun hn => (Eq.mp (congrFun (congrFun (allbot _ h) z) t) hn : ⊥ᵐ t)⟩)\n    ⟨a, act a v, htop ▸ trivial⟩\n  (Eq.mp (congrFun (congrFun (allbot E (Ax3 w)) a) w) Ea : ⊥ᵐ w)\n\ntheorem PTop_One_deriv_hf : type_of% @PTop_One_deriv := fun w =>\n  topEq ▸ (Ax2a (fun _ : e => ⊥ᵐ) w).1.resolve_left (NotPBot_One_deriv_hf w)\n\ntheorem E_top_of_PBot_hf : type_of% @E_top_of_PBot := fun pb =>\n  (NotPBot_One_deriv_hf _ pb).elim\n\ntheorem G_ex_One_deriv_hf : type_of% @G_ex_One_deriv := fun w =>\n  let ⟨v, _, hv⟩ := dia_G (L_One w) (NotPBot_One_deriv_hf w)\n  const _ v w hv\n\ntheorem Th4_One_deriv_hf : type_of% @Th4_One_deriv := fun w =>\n  let ⟨v, hv⟩ := Serial w\n  ⟨v, hv, G_ex_One_deriv_hf v⟩\n\n/-- `AllExist_One`: "being `y` and not actual" would be a vacuous essence of the God-like being\nat `w` (witness `z = y ∧ ¬(∃ᴱ u, u = z)`, no `Pt`). -/\ntheorem AllExist_One_hf : type_of% @AllExist_One := fun y w =>\n  Classical.byContradiction fun ny =>\n    let ⟨g, _, hG⟩ := G_ex_One_deriv_hf w\n    have Eg : E g w := hG E (Ax3 w)\n    let φ : e → σ := fun z => (z =ᵐ y) ∧ᵐ ¬ᵐ(∃ᴱ u, u =ᵐ z)\n    have ess : Ess φ g w := fun _ _ _ _ =>\n      ⟨fun h => (congrFun (congrFun h y) w ▸\n          (⟨rfl, fun ⟨_, hu, he⟩ => ny (he ▸ hu)⟩ : φ y w) : ⊥ᵐ w),\n       fun z hz ⟨_, hnz⟩ => (hnz ⟨z, hz, rfl⟩).elim⟩\n    let ⟨v, hv⟩ := Serial w\n    let ⟨z, hz, _, hnz⟩ := Eg φ ess v hv\n    hnz ⟨z, hz, rfl⟩\n\n/-- `One_gives_S`: an empty `Φ` stays empty at successors (`const` on `Φ ψ`), so the conjunction\nholds of every actual being there, and `Ax4` from `P ⊤` gives `P φ`. -/\ntheorem One_gives_S_hf : type_of% @One_gives_S := fun Φ φ w ⟨pos, cj⟩ =>\n  if hex : ∃ ψ, Φ ψ w then Ax1GenOne Φ φ w ⟨⟨hex, pos⟩, cj⟩\n  else\n    Ax4 (fun _ : e => ⊤ᵐ) φ w ⟨PTop_One_deriv_hf w, fun v hv =>\n      ⟨@neBot (fun _ : e => ⊤ᵐ) Classical.ofNonempty w trivial, fun y hy _ =>\n        (cj v hv y hy).2 fun ψ hψ => (hex ⟨ψ, const (Φ ψ) v w hψ⟩).elim⟩⟩\n\ntheorem One_gives_Box_hf : type_of% @One_gives_Box := fun Φ φ w ⟨⟨pos, _⟩, cj⟩ =>\n  One_gives_S_hf Φ φ w ⟨pos, cj⟩\n\n/-- `Box_gives_One`: `PosProps Φ` is boxed, as membership moves back by `const` and positivity\nforward by `Ax2b`. -/\ntheorem Box_gives_One_hf : type_of% @Box_gives_One := fun hBox Φ φ w ⟨⟨_, pos⟩, cj⟩ =>\n  hBox Φ φ w ⟨⟨pos, fun v hv ψ hψ => Ax2b ψ w (pos ψ (const (Φ ψ) v w hψ)) v hv⟩, cj⟩\n\nexample : type_of% @MC_unconditional_hf = type_of% @MC_unconditional := rfl\nexample : type_of% @MC_One_hf = type_of% @MC_One := rfl\nexample : type_of% @AllActual_of_PBot_hf = type_of% @AllActual_of_PBot := rfl\nexample : type_of% @NotPBot_One_deriv_hf = type_of% @NotPBot_One_deriv := rfl\nexample : type_of% @PTop_One_deriv_hf = type_of% @PTop_One_deriv := rfl\nexample : type_of% @E_top_of_PBot_hf = type_of% @E_top_of_PBot := rfl\nexample : type_of% @G_ex_One_deriv_hf = type_of% @G_ex_One_deriv := rfl\nexample : type_of% @Th4_One_deriv_hf = type_of% @Th4_One_deriv := rfl\nexample : type_of% @AllExist_One_hf = type_of% @AllExist_One := rfl\nexample : type_of% @One_gives_S_hf = type_of% @One_gives_S := rfl\nexample : type_of% @One_gives_Box_hf = type_of% @One_gives_Box := rfl\nexample : type_of% @Box_gives_One_hf = type_of% @Box_gives_One := rfl\n\nend Programme.F.OneV3\n\n#print axioms Programme.F.OneV3.MC_unconditional_hf\n#print axioms Programme.F.OneV3.MC_One_hf\n#print axioms Programme.F.OneV3.AllActual_of_PBot_hf\n#print axioms Programme.F.OneV3.NotPBot_One_deriv_hf\n#print axioms Programme.F.OneV3.PTop_One_deriv_hf\n#print axioms Programme.F.OneV3.E_top_of_PBot_hf\n#print axioms Programme.F.OneV3.G_ex_One_deriv_hf\n#print axioms Programme.F.OneV3.Th4_One_deriv_hf\n#print axioms Programme.F.OneV3.AllExist_One_hf\n#print axioms Programme.F.OneV3.One_gives_S_hf\n#print axioms Programme.F.OneV3.One_gives_Box_hf\n#print axioms Programme.F.OneV3.Box_gives_One_hf\n'
SHA = "d882ceea88d3002da1a1b2bc383c911230f0fceae1a713567e89404392d339d0"
MOD = "Programme.F.OneV3"
NAMES = ['Programme.F.OneV3.MC_unconditional_hf', 'Programme.F.OneV3.MC_One_hf', 'Programme.F.OneV3.AllActual_of_PBot_hf', 'Programme.F.OneV3.NotPBot_One_deriv_hf', 'Programme.F.OneV3.PTop_One_deriv_hf', 'Programme.F.OneV3.E_top_of_PBot_hf', 'Programme.F.OneV3.G_ex_One_deriv_hf', 'Programme.F.OneV3.Th4_One_deriv_hf', 'Programme.F.OneV3.AllExist_One_hf', 'Programme.F.OneV3.One_gives_S_hf', 'Programme.F.OneV3.One_gives_Box_hf', 'Programme.F.OneV3.Box_gives_One_hf']
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
