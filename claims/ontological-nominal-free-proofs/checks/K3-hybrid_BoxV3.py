"""Thread F check (strict, full-name matching) for Programme.F.BoxV3.

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

SRC = "import OpenQuestions.Ax1GenBoxVariant3\n/-! # Thread F: hybrid-free `MC_S4`, `Th5_S4`, `Ax1Gen_of_refl` in `Ax1GenBoxVariant3`\n\nv4 (this module's section on S4) derives these via `OneWorld`, i.e. with nominals, and notes\nthat hybrid-free derivations under `Ax1GenBox` are not known.  Here: `const` (every lifted\nproposition is constant), as in `Programme.F.TwoV3`, with the module's hybrid-free `L` and\n`PTop`.  Then collapse is `const`, `□PosProps Φ` follows from `PosProps Φ` by `const` on `Φ ψ`\nand `Ax2b`, and the God-like being of `Th4` is moved by `const`.  Reflexivity is unused. -/\n\nnamespace Programme.F.BoxV3\n\nprivate theorem topEq : (~ᵐ(fun _ : e => ⊥ᵐ)) = (fun _ : e => ⊤ᵐ) := by funext x v; simp\n\nprivate theorem neBot {φ : e → σ} {x : e} {w : i} (h : φ x w) : φ ≠ (fun _ : e => ⊥ᵐ) :=\n  fun h' => (congrFun (congrFun h' x) w ▸ h : ⊥ᵐ w)\n\n/-- A positive non-empty property makes `⊤` positive. -/\nprivate theorem _top_of {φ : e → σ} {w : i} (hφ : P φ w) (ne : φ ≠ (fun _ : e => ⊥ᵐ)) :\n    P (fun _ : e => ⊤ᵐ) w :=\n  Ax4 φ _ w ⟨hφ, fun _ _ => ⟨ne, fun _ _ _ => trivial⟩⟩\n\n/-- With `P G` and `¬ P ⊥` at `w`, a God-like being is actual at some successor of `w`. -/\nprivate theorem dia_G {w : i} (PG : P G w) (nb : ¬ P (fun _ : e => ⊥ᵐ) w) : (◇(∃ᴱ x, G x)) w :=\n  Classical.byContradiction fun hn =>\n    have Gne : G ≠ (fun _ : e => ⊥ᵐ) := fun h => nb (h ▸ PG)\n    nb (Ax4 G _ w ⟨PG, fun v hv => ⟨Gne, fun z hz hG => hn ⟨v, hv, z, hz, hG⟩⟩⟩)\n\n/-- At a world with an actual God-like `g`, every non-empty property is exemplified at some\nsuccessor (else it is a vacuous essence of `g`, against `E g u`). -/\nprivate theorem reach {g : e} {u : i} (hG : G g u) (χ : e → σ) (ne : χ ≠ (fun _ : e => ⊥ᵐ)) :\n    ∃ u1, u 𝗿 u1 ∧ ∃ y, χ y u1 :=\n  Classical.byContradiction fun hn =>\n    have Eg : E g u := hG E (Ax3 u)\n    have ess : Ess χ g u := fun _ _ v hv =>\n      ⟨ne, fun y _ hχ => (hn ⟨v, hv, y, hχ⟩).elim⟩\n    let ⟨v, hv⟩ := Serial u\n    let ⟨y, _, hχ⟩ := Eg χ ess v hv\n    hn ⟨v, hv, y, hχ⟩\n\n/-- **Every lifted proposition is constant**, hybrid-free and with no frame condition. -/\ntheorem const (q : σ) (w v : i) (hw : q w) : q v :=\n  Classical.byContradiction fun hv =>\n    let a : e := Classical.ofNonempty\n    let χ : e → σ := fun _ => q\n    let χn : e → σ := fun _ => ¬ᵐ q\n    have ne1 : χ ≠ (fun _ => ⊥ᵐ) := @neBot χ a w hw\n    have ne2 : χn ≠ (fun _ => ⊥ᵐ) := @neBot χn a v hv\n    have nb : ¬ P (fun _ : e => ⊥ᵐ) w := fun hb => (Ax2a _ w).2 ⟨hb, topEq ▸ PTop w⟩\n    let ⟨u, _, g, _, hG⟩ := dia_G (L w) nb\n    let ⟨u1, r1, _, hq1⟩ := reach hG χn ne2\n    let ⟨u2, r2, _, hq2⟩ := reach hG χ ne1\n    let ⟨_, _, hz1⟩ := Th2 g u hG u1 r1\n    let ⟨_, _, hz2⟩ := Th2 g u hG u2 r2\n    (Classical.em (q u)).elim\n      (fun hu => hq1 (hz1 χ (Ax2b χ u (PosOfGod hG hu) u1 r1)))\n      (fun hu => hz2 χn (Ax2b χn u (PosOfGod hG hu) u2 r2) hq2)\n\ntheorem MC_S4_hf : type_of% @MC_S4 := fun _ φ w hφ v _ => const φ w v hφ\n\ntheorem Ax1Gen_of_refl_hf : type_of% @Ax1Gen_of_refl := fun _ Φ φ w ⟨pos, cj⟩ =>\n  Ax1GenBox Φ φ w ⟨⟨pos, fun v hv ψ hψ => Ax2b ψ w (pos ψ (const (Φ ψ) v w hψ)) v hv⟩, cj⟩\n\ntheorem Th5_S4_hf : type_of% @Th5_S4 := fun _ w v _ =>\n  let ⟨u, _, hex⟩ := Th4 w\n  const _ u v hex\n\nexample : type_of% @MC_S4_hf = type_of% @MC_S4 := rfl\nexample : type_of% @Ax1Gen_of_refl_hf = type_of% @Ax1Gen_of_refl := rfl\nexample : type_of% @Th5_S4_hf = type_of% @Th5_S4 := rfl\n\nend Programme.F.BoxV3\n\n#print axioms Programme.F.BoxV3.MC_S4_hf\n#print axioms Programme.F.BoxV3.Ax1Gen_of_refl_hf\n#print axioms Programme.F.BoxV3.Th5_S4_hf\n"
SHA = "4aad2b0a7af4d22fa5e782d5eee80f350905d8972c2fae5fba13020c095da173"
MOD = "Programme.F.BoxV3"
NAMES = ['Programme.F.BoxV3.MC_S4_hf', 'Programme.F.BoxV3.Ax1Gen_of_refl_hf', 'Programme.F.BoxV3.Th5_S4_hf']
CONTROL = 'MC_S4'   # name of a hybrid library theorem in the imported module


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
