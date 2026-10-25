import Programme.«20261022-0733-ontological».Run2.TwoClosed

/-! # `Ax1GenTwo → Ax1Gen` without `Ax2b` and without modal collapse

`TwoClosed.ax1Gen_of_two` (K1) handles a collection with fewer than two members at `w` through
modal collapse, hence needs `Ax2b`.  Here the small case is avoided by *padding*: add `⊤` and a
positive admitted `ψ₀ ≠ ⊤` to `Φ` (admitted by `single`, `union`); the padded collection has two
members at `w`, all positive, and its conjunction is `φ ∧ ψ₀` (admitted by `conj`).  `Ax1GenTwo`
makes `φ ∧ ψ₀` positive and `Ax4` passes to `φ`.  If no such `ψ₀` exists at `w`, `Ax2a` makes
every admitted property `⊤` or `⊥`; then the admitted proposition "every member of `Φ` is `⊤`"
(`atMost`), lifted, is `⊤`, so it holds at every successor and `Ax4` from `⊤` closes.

Hypotheses: `Closed`, `Ax2a`, `⊤` positive, `Ax4`, nonempty entities.  No `Ax2b`, no frame
condition, any actuality predicate; `⊤` positive follows from `Ax3`/`Ax3v3` and `Ax4`. -/

namespace Programme.«20261022-0733-ontological».Run2.TwoNoRigidity
open Programme.«20261022-0733-ontological».Run2.TwoClosed

variable {W D : Type} {M : Model W D}

theorem ax1Gen_of_two_noRigid [Nonempty D] (C : Closed M) (h2a : Ax2a M)
    (h3 : ∀ w, M.P top w) (h4 : Ax4 M) (hT : Ax1GenTwo M) : Ax1Gen M := by
  intro Φ φ hΦ hφ w pos cj
  by_cases hψ : ∃ ψ₀, M.AT ψ₀ ∧ M.P ψ₀ w ∧ ψ₀ ≠ top
  · obtain ⟨ψ₀, hA₀, hP₀, hne⟩ := hψ
    let Φ' : (D → W → Prop) → W → Prop := fun ψ u => Φ ψ u ∨ (ψ = top ∨ ψ = ψ₀)
    have hΦ' : M.AH Φ' := C.union _ _ hΦ (C.union _ _ (C.single _ C.top) (C.single _ hA₀))
    have two : TwoMembers M Φ' w :=
      ⟨top, ψ₀, C.top, hA₀, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), fun e => hne e.symm⟩
    have pos' : PosProps M Φ' w := by
      intro ψ hA hm
      rcases hm with hm | rfl | rfl
      · exact pos ψ hA hm
      · exact h3 w
      · exact hP₀
    have cj' : ConjOf M (conj φ ψ₀) Φ' w := by
      intro v hv z hz
      constructor
      · intro ⟨hφz, h₀⟩ ψ hA hm
        rcases hm with hm | rfl | rfl
        · exact (cj v hv z hz).1 hφz ψ hA hm
        · trivial
        · exact h₀
      · intro hall
        exact ⟨(cj v hv z hz).2 fun ψ hA hm => hall ψ hA (Or.inl hm),
          hall ψ₀ hA₀ (Or.inr (Or.inr rfl))⟩
    have hP : M.P (conj φ ψ₀) w := hT Φ' _ hΦ' (C.conj _ _ hφ hA₀) w two pos' cj'
    exact h4 _ φ (C.conj _ _ hφ hA₀) hφ w hP fun _ _ _ _ h => h.1
  · have onlytop : ∀ ψ, M.AT ψ → M.P ψ w → ψ = top := fun ψ hA hP =>
      Classical.byContradiction fun hne => hψ ⟨ψ, hA, hP, hne⟩
    have x : D := Classical.ofNonempty
    have sub : ∀ ψ, M.AT ψ → Φ ψ w → ψ = top := fun ψ hA hm => onlytop ψ hA (pos ψ hA hm)
    let s : W → Prop := fun u => ∀ ψ, M.AT ψ → Φ ψ u → ψ = top
    have hs : M.AS s := C.atMost Φ top hΦ C.top
    have hl : M.AT (fun _ => s) := C.lift _ hs
    have sAll : ∀ u, s u := by
      rcases (h2a _ hl w).1 with hp | hn
      · intro u
        have := congrFun (congrFun (onlytop _ hl hp) x) u
        simpa [top] using this
      · have := congrFun (congrFun (onlytop _ (C.neg _ hl) hn) x) w
        have hnot : ¬ s w := by simpa [neg, top] using this
        exact absurd sub hnot
    exact h4 top φ C.top hφ w (h3 w) fun v hv y hy _ =>
      (cj v hv y hy).2 fun ψ hA hm => (sAll v ψ hA hm) ▸ trivial

/-- Variant 2: `Ax1GenTwo ↔ Ax1Gen` from `Ax2a`, `Ax3`, `Ax4` alone (no `Ax2b`). -/
theorem equivalence_v2_noRigid [Nonempty D] (C : Closed M) (hE : M.AT (E M)) (h2a : Ax2a M)
    (h3 : Ax3 M) (h4 : Ax4 M) : Ax1GenTwo M ↔ Ax1Gen M :=
  ⟨ax1Gen_of_two_noRigid C h2a (pTop_v2 hE C h3 h4) h4, two_of_ax1Gen⟩

/-- Variant 3′: the same. -/
theorem equivalence_v3_noRigid [Nonempty D] (C : Closed M) (hE : M.AT (E3 M)) (h2a : Ax2a M)
    (h3 : Ax3v3 M) (h4 : Ax4 M) : Ax1GenTwo M ↔ Ax1Gen M :=
  ⟨ax1Gen_of_two_noRigid C h2a (pTop_v3 hE C h3 h4) h4, two_of_ax1Gen⟩

end Programme.«20261022-0733-ontological».Run2.TwoNoRigidity

#print axioms Programme.«20261022-0733-ontological».Run2.TwoNoRigidity.ax1Gen_of_two_noRigid
#print axioms Programme.«20261022-0733-ontological».Run2.TwoNoRigidity.equivalence_v2_noRigid
#print axioms Programme.«20261022-0733-ontological».Run2.TwoNoRigidity.equivalence_v3_noRigid
