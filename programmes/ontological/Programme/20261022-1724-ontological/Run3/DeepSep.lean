import Programme.«20261022-1724-ontological».Run3.DeepE
/-! # DeepSep.lean (run 3, round 7)

`DeepE.lean` (claims K8-K10) verbatim, followed by section `SepR`: v4's remarks in Example
`ex:separating` (finite models do not separate; the example's model is not a model of variant 2,
whatever `Pos` is) and the example itself as a v4 `VM`+`LGen` model. -/

/-! # Run 3, thread C: the deep calculus over v4's 𝓛-general models (one self-contained file)

Concatenation, in order, of:
1. `DeepLeib.lean` (claim K4), plus `Deriv.ren`/`Deriv.wkD` (renaming of whole derivations, with the
   new `leib` case) from the round-2 development of `DeepK.lean`;
2. the derivations of `DeepK.lean` (claim K2: run 2's K1 and K14), unchanged, now in K4's calculus;
3. th's bridge `agents/th/lean/Programme/Th/Bridge.lean` (M1 `toStr`, M2 `ofStr`, `valid_iff`),
   lines 205-606 verbatim, placed in `Programme.Run3.LX` (its copied preamble is K4's own);
4. `V4`: `sound_v4` (K4's calculus is sound over v4's def:lgeneral models), `k1_valid_v4`,
   `k14_valid_v4`;
5. round 6: `K3p` (the derivations of item 2 replayed for variant 3′, `Ax1GenTwoVariant3Plain`),
   `Conv.two_of_gen` (`Ax1Gen ⇒ Ax1GenTwo`), and in `V4`: `k3p_valid_v4`, `two_equivalent_v2`,
   `two_equivalent_v3p` (the modules' `Two_equivalent` over all v4 𝓛-general models);
6. `SepV2.lean` (claim K7), plus `sep_v4`/`sep_not_valid_v4`: the eqT-quotient of K7's structure is a
   v4 𝓛-general model of variant 2 where the separating sentence fails. -/

-- [cleanup 2026-10-23] shared block (4433 lines) now imported from Programme.«20261022-1724-ontological».Run3.DeepE





/-! ## v4 Example `ex:separating`: the two remarks, and the example as a v4 𝓛-general model

* `sep_example_v4`: the eqT-quotient of K6's structure (`strR symE`: total frame, one individual,
  `Pos` empty, extensional hereditarily finitely supported carriers over the flip group) is a v4
  `VM`+`LGen` model with universal `R` and empty `Pos`, a contingent proposition `{w | w₀ = 1}`, in
  which `A ∃p.(Atom p ∧ p)` fails at every world.
* `sep_of_minimal` / `sep_finite` / `sep_singletons`: in every v4 𝓛-general model in which every
  world `v` has a least proposition containing it (in particular, every model with finitely many
  worlds, and every model whose propositional domain contains the singletons, e.g. a standard
  one), `A ∃p.(Atom p ∧ p)` holds at every world: "no model with finitely many worlds separates".
* `v2_universal_trivial` / `sep_example_not_v2`: in a v4 𝓛-general model of variant 2 (K1's `T2`)
  on a universal frame every proposition is `∅` or `W`; hence no v4 𝓛-general model with a universal
  frame whose propositional domain contains `{w | w₀ = 1}` (v4's `M`, with *any* `Pos`) is a model of
  variant 2: "M is not a model of the axioms of variant 2, whatever Pos is taken to be". -/

namespace Programme.«20261022-1724-ontological».Run3.SepR
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.SepV2 Programme.«20261022-1724-ontological».Run3.SepV2.Sep

attribute [local instance] Classical.propDecidable

section Sem
variable {W : Type} (M : VM W) (L : LGen M)

theorem ev_v0 {t : FTy} {Γ : List FTy} (x : M.C t) (ρ : VEnv M Γ) :
    L.ev (Tm.var .zero : Tm (t :: Γ) t) (x, ρ) = x := L.var _ _

theorem ev_v1 {t u : FTy} {Γ : List FTy} (y : M.C u) (x : M.C t) (ρ : VEnv M Γ) :
    L.ev (Tm.var (.succ .zero) : Tm (u :: t :: Γ) t) (y, x, ρ) = x := L.var _ _

/-- A proposition equals the bottom proposition iff it is false everywhere. -/
theorem eq_bot_iff {Γ : List FTy} (ρ : VEnv M Γ) (p : M.C .s) :
    p = L.ev (Tm.bot : Tm Γ .s) ρ ↔ ∀ u, ¬ M.pr p u := by
  constructor
  · rintro rfl u h; exact (L.bot ρ u).1 h
  · intro h
    exact M.pr_inj _ _ (funext fun u => propext ⟨fun hu => absurd hu (h u),
      fun hu => absurd hu ((L.bot ρ u).1)⟩)

/-- Semantics of `D p`: some proposition of the domain omits `u` and meets `p`. -/
theorem dTm_iff (x : M.C .s) (u : W) :
    M.pr (L.ev dTm (x, ())) u ↔ ∃ ψ : M.C .s, ¬ M.pr ψ u ∧ ∃ u', M.pr ψ u' ∧ M.pr x u' := by
  unfold dTm
  rw [L.ex]
  refine exists_congr fun ψ => ?_
  rw [L.and, L.neg, L.neg, L.eq, ev_v0, eq_bot_iff]
  simp only [L.and, L.var, Classical.not_forall, Classical.not_not]
  exact Iff.rfl

/-- Semantics of `Atom p` at `v`. -/
theorem atom_iff (x : M.C .s) (v : W) :
    M.pr (L.ev atomTm (x, ())) v ↔
      (∃ u, M.pr x u) ∧ ∀ u, ¬ (M.pr x u ∧ M.pr (L.ev dTm (x, ())) u) := by
  unfold atomTm
  rw [L.and, L.neg, L.neg, L.neg, L.eq, L.eq, ev_v0, eq_bot_iff, eq_bot_iff, Classical.not_not]
  simp only [L.and, L.var, Classical.not_forall, Classical.not_not]
  exact Iff.rfl

/-- Semantics of `A ∃p.(Atom p ∧ p)`: at any world, every world lies in an atom. -/
theorem phiSep_iff (w : W) :
    M.pr (L.ev phiSep ()) w ↔ ∀ v, ∃ x : M.C .s, M.pr (L.ev atomTm (x, ())) v ∧ M.pr x v := by
  unfold phiSep
  rw [L.eq]
  constructor
  · intro h v
    have hv : M.pr (L.ev (Tm.ex .s (.and atomTm (.var .zero))) ()) v := by
      rw [h]; exact (L.top (Γ := []) () v).2 trivial
    obtain ⟨x, hx⟩ := (L.ex _ _ _ _).1 hv
    rw [L.and, ev_v0] at hx
    exact ⟨x, hx⟩
  · intro h
    apply M.pr_inj
    funext v
    apply propext
    refine ⟨fun _ => (L.top (Γ := []) () v).2 trivial, fun _ => ?_⟩
    obtain ⟨x, hx⟩ := h v
    exact (L.ex _ _ _ _).2 ⟨x, by rw [L.and, ev_v0]; exact hx⟩

/-- **Sufficient condition for the separating sentence.** If every world `v` has a least proposition
of the domain containing it, then `A ∃p.(Atom p ∧ p)` holds at every world. -/
theorem sep_of_minimal
    (hmin : ∀ v, ∃ q : M.C .s, M.pr q v ∧ ∀ u, M.pr q u → ∀ p : M.C .s, M.pr p v → M.pr p u)
    (w : W) : M.pr (L.ev phiSep ()) w := by
  rw [phiSep_iff]
  intro v
  obtain ⟨q, hqv, hq⟩ := hmin v
  refine ⟨q, (atom_iff M L q v).2 ⟨⟨v, hqv⟩, ?_⟩, hqv⟩
  rintro u ⟨hqu, hd⟩
  obtain ⟨ψ, hψu, u', hψu', hqu'⟩ := (dTm_iff M L q u).1 hd
  by_cases hψv : M.pr ψ v
  · exact hψu (hq u hqu ψ hψv)
  · -- `¬ψ` is in the domain and contains `v`, hence `u'`
    have hn : M.pr (L.ev (Tm.neg (.var .zero) : Tm [.s] .s) (ψ, ())) v := by
      rw [L.neg, ev_v0]; exact hψv
    have hn' := hq u' hqu' _ hn
    rw [L.neg, ev_v0] at hn'
    exact hn' hψu'

/-- Conjunction in the propositional domain. -/
def conj (p q : M.C .s) : M.C .s :=
  L.ev (Tm.and (.var .zero) (.var (.succ .zero)) : Tm [.s, .s] .s) (p, q, ())

theorem pr_conj (p q : M.C .s) (u : W) : M.pr (conj M L p q) u ↔ M.pr p u ∧ M.pr q u := by
  unfold conj; rw [L.and, ev_v0, ev_v1]

/-- For a list of worlds, a proposition containing `v` and contained in every proposition of the
domain that contains `v` and omits a listed world. -/
noncomputable def cut (v : W) : List W → M.C .s
  | [] => L.ev (Tm.top : Tm [] .s) ()
  | u :: l =>
    conj M L (cut v l)
      (if h : ∃ p : M.C .s, M.pr p v ∧ ¬ M.pr p u then Classical.choose h
        else L.ev (Tm.top : Tm [] .s) ())

theorem cut_v (v : W) : ∀ l, M.pr (cut M L v l) v
  | [] => (L.top (Γ := []) () v).2 trivial
  | u :: l => by
    unfold cut
    rw [pr_conj]
    refine ⟨cut_v v l, ?_⟩
    split
    · next h => exact (Classical.choose_spec h).1
    · exact (L.top (Γ := []) () v).2 trivial

theorem cut_min (v : W) : ∀ l u, u ∈ l → M.pr (cut M L v l) u → ∀ p : M.C .s, M.pr p v → M.pr p u
  | [], _, hu, _, _, _ => nomatch hu
  | u' :: l, u, hu, hc, p, hp => by
    unfold cut at hc
    rw [pr_conj] at hc
    rcases List.mem_cons.1 hu with heq | hl
    · apply Classical.byContradiction
      intro hpu
      rw [heq] at hpu
      have h : ∃ p : M.C .s, M.pr p v ∧ ¬ M.pr p u' := ⟨p, hp, hpu⟩
      have hc2 := hc.2
      rw [dif_pos h] at hc2
      exact (Classical.choose_spec h).2 (heq ▸ hc2)
    · exact cut_min v l u hl hc.1 p hp

/-- **"No model with finitely many worlds separates"** (v4, remark in `ex:separating`). In every v4
𝓛-general model whose worlds are enumerated by a finite list, `A ∃p.(Atom p ∧ p)` holds at every
world. -/
theorem sep_finite (hfin : ∃ l : List W, ∀ w, w ∈ l) (w : W) : M.pr (L.ev phiSep ()) w := by
  obtain ⟨l, hl⟩ := hfin
  exact sep_of_minimal M L (fun v => ⟨cut M L v l, cut_v M L v l,
    fun u hu p hp => cut_min M L v l u (hl u) hu p hp⟩) w

/-- In every v4 𝓛-general model whose propositional domain contains every singleton (e.g. a
standard model), `A ∃p.(Atom p ∧ p)` holds at every world. -/
theorem sep_singletons (hs : ∀ v, ∃ q : M.C .s, ∀ u, M.pr q u ↔ u = v) (w : W) :
    M.pr (L.ev phiSep ()) w :=
  sep_of_minimal M L (fun v => by
    obtain ⟨q, hq⟩ := hs v
    exact ⟨q, (hq v).2 rfl, fun u hu p hp => by rw [(hq u).1 hu]; exact hp⟩) w

/-- **Variant 2 on a universal frame trivialises the propositional domain.** In every v4
𝓛-general model of K1's `T2` (variant 2: `Ax2a`, `Ax2b`, `Ax3`, `Ax4`, `Ax1GenTwo`, `∃x.⊤`) whose
accessibility is universal, every proposition of the domain is true everywhere or nowhere. -/
theorem v2_universal_trivial (hT : ∀ ψ, K1.T2 ψ → ∀ w, M.pr (L.ev ψ ()) w)
    (hU : ∀ w v, M.R w v) (p : M.C .s) : (∀ w, M.pr p w) ∨ (∀ w, ¬ M.pr p w) := by
  by_cases h : ∃ w, M.pr p w
  · obtain ⟨w, hw⟩ := h
    left
    intro v
    have hmc := (V4.k1_valid_v4 M L hT w).2.1
    unfold K1.MC at hmc
    rw [L.all] at hmc
    have := hmc p
    rw [L.imp, L.box, ev_v0] at this
    exact this hw v (hU w v)
  · exact Or.inr fun w hw => h ⟨w, hw⟩

/-- Hence a v4 𝓛-general model on infinite 0-1 sequences with universal accessibility whose
propositional domain contains `{w | w₀ = 1}` (as v4's `M` does, whatever `Pos` is) is not a model of
variant 2. -/
theorem not_v2_of_contingent {M : VM Cw} (L : LGen M) (hU : ∀ w v, M.R w v)
    (h0 : ∃ p : M.C .s, ∀ w, M.pr p w ↔ w 0 = true) :
    ¬ ∀ ψ, K1.T2 ψ → ∀ w, M.pr (L.ev ψ ()) w := by
  intro hT
  obtain ⟨p, hp⟩ := h0
  rcases v2_universal_trivial M L hT hU p with h | h
  · have := (hp (fun _ => false)).1 (h _); exact absurd this (by decide)
  · exact h (fun _ => true) ((hp _).2 rfl)

end Sem

/-! ### v4's model `M` of `ex:separating` as a v4 𝓛-general model -/

abbrev SE := strR symE

theorem allE_E (x : Unit) : SE.A .e x := ⟨sup_e symE x, rfl⟩

theorem resp_E : HOLX.Resp SE := by
  intro a b F hF z z' hz hz' he
  have hr : rel symE b (F z) (F z') := hF.2 z z' hz.1 hz'.1 (eqT_rel symE a z z' hz hz' he)
  have hA : ∀ y, AdmR symE a y → AdmR symE b (F y) := fun y hy =>
    closedR symE (Tm.app (.var .zero) (.var (.succ .zero)) : Tm [.arr a b, a] b) (F, y, ())
      ⟨hF, hy, trivial⟩
  exact rel_eqT symE b _ _ (hA z hz) (hA z' hz') hr

/-- The finitary proposition `{w | w₀ = 1}` is admitted. -/
theorem adm_x0 : SE.A .s (fun w => w 0 = true) :=
  (admR_s symE _).2 (sup_s_of (n := 1) fun d hd x => by
    have : d 0 = false := hd 0 (by decide)
    simp [xw, this])

/-- **Example `ex:separating` in v4's own model class.** The quotient of K6's structure is a v4
`VM` with an `LGen` (closed under every term of the full simply typed `𝓛`), one individual, universal
accessibility, `Pos` empty, and the contingent proposition `{w | w₀ = 1}`; `A ∃p.(Atom p ∧ p)`
fails at every world, and the model is not a model of variant 2. -/
theorem sep_example_v4 : ∃ (M : VM Cw) (L : LGen M), Nonempty (M.C .e) ∧ (∀ w v, M.R w v) ∧
    (∀ φ w, ¬ M.pr (M.ap M.P φ) w) ∧ (∃ p : M.C .s, ∀ w, M.pr p w ↔ w 0 = true) ∧
    (∀ w, ¬ M.pr (L.ev phiSep ()) w) ∧ ¬ (∀ ψ, K1.T2 ψ → ∀ w, M.pr (L.ev ψ ()) w) := by
  let M := ofStr SE (closedR symE) resp_E
  let L := ofStr_lgen SE (closedR symE) resp_E allE_E
  have hU : ∀ w v, M.R w v := fun _ _ => trivial
  have h0 : ∃ p : M.C .s, ∀ w, M.pr p w ↔ w 0 = true :=
    ⟨Quotient.mk (setoidT SE .s) ⟨_, adm_x0⟩, fun _ => Iff.rfl⟩
  refine ⟨M, L, ⟨Quotient.mk (setoidT SE .e) ⟨(), allE_E ()⟩⟩, hU, ?_, h0, ?_,
    not_v2_of_contingent L hU h0⟩
  · intro φ w
    refine Quotient.inductionOn (motive := fun φ => ¬ M.pr (M.ap M.P φ) w) φ ?_
    intro z h
    exact h
  · intro w h
    exact phi_false w ((ofStr_truth SE (closedR symE) resp_E allE_E phiSep w).1 h)

end Programme.«20261022-1724-ontological».Run3.SepR

#print axioms Programme.«20261022-1724-ontological».Run3.SepR.phiSep_iff
#print axioms Programme.«20261022-1724-ontological».Run3.SepR.sep_of_minimal
#print axioms Programme.«20261022-1724-ontological».Run3.SepR.sep_finite
#print axioms Programme.«20261022-1724-ontological».Run3.SepR.sep_singletons
#print axioms Programme.«20261022-1724-ontological».Run3.SepR.v2_universal_trivial
#print axioms Programme.«20261022-1724-ontological».Run3.SepR.not_v2_of_contingent
#print axioms Programme.«20261022-1724-ontological».Run3.SepR.sep_example_v4
