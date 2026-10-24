import OpenQuestions.GoedelVariantHOML3inS4oneFile
/-! # Thread F: hybrid-free proofs for `GoedelVariantHOML3inS4oneFile`

v4 proves `Th3`, `MC`, `EssDetermined`, `UniqueEss1`, ... through `NoNecExist` / `OneWorld`, whose
witnesses are nominals.  The module already holds hybrid-free `_K` lemmas (`G_ex`, `Serial`,
`Reach_K`, `EssMemI_K`, `MC_K`, ...); here every flagged statement is re-proved from those.
New steps: `AllExist` with the witness `¬(∃ᴱ u, u = z)` in place of a bare `existsAt`
(following th, P8), and `EssSupp` / `EssDetermined` for *arbitrary* worlds `v`, `u` (not only
successors) by `Reach_K` at the constant properties `φ y ∧ y ≠ x` and `¬ φ x`. -/

namespace Programme.F.HOML3

/-- Pointwise `AllExist`; witness `fun z => z = y ∧ ¬(∃ᴱ u, u = z)`. -/
theorem AllExist_pt (w : i) (y : e) : y @ᵐ w :=
  Classical.byContradiction fun ny =>
    let ⟨g, _, hG⟩ := G_ex w
    have Eg : E g w := hG E (Ax3 w)
    let φ : e → σ := fun z => (z =ᵐ y) ∧ᵐ ¬ᵐ(∃ᴱ u, u =ᵐ z)
    have ess : Ess φ g w := fun _ _ _ _ =>
      ⟨fun h => (congrFun (congrFun h y) w ▸
          (⟨rfl, fun ⟨_, hu, he⟩ => ny (he ▸ hu)⟩ : φ y w) : ⊥ᵐ w),
       fun z hz ⟨_, hnz⟩ => (hnz ⟨z, hz, rfl⟩).elim⟩
    let ⟨v, hv⟩ := Serial w
    let ⟨z, hz, _, hnz⟩ := Eg φ ess v hv
    hnz ⟨z, hz, rfl⟩

theorem AllExist_hf : type_of% @AllExist := AllExist_pt

theorem Th3_hf : type_of% @Th3 := Th3_K
theorem Th5_hf : type_of% @Th5 := Th5_K
theorem MC_hf : type_of% @MC := MC_K
theorem MCdual_hf : type_of% @MCdual := MCdual_K
theorem Triv_hf : type_of% @Triv := Triv_K
theorem UniqueEss3_hf : type_of% @UniqueEss3 := UniqueEss3_K

/-- v4's `EssMemI_K` run on `AllExist_pt` instead of the library's `AllExistI`, whose
`AllExist` carries an ACTUAL-flagged witness (sk, P46). -/
theorem EssMemI_pt {φ : e → σ} {x : e} {w : i} (h : Ess φ x w) : φ x w :=
  Classical.byContradiction fun hn =>
    let ⟨u, hu⟩ := Serial w
    let ⟨hne, _⟩ := h (fun z => ¬ᵐ(φ z)) hn u hu
    let ⟨v, hv, y, hy⟩ := Reach_K φ w hne
    (h (fun z => ¬ᵐ(φ z)) hn v hv).2 y (AllExist_pt v y) hy hy

theorem EssMemI_hf : type_of% @EssMemI := EssMemI_pt
theorem EssMem_hf : type_of% @EssMem := fun _ _ _ h => EssMemI_pt h
theorem Ess_iff_Ess2_hf : type_of% @Ess_iff_Ess2 := fun _ _ _ =>
  ⟨fun h => Ess2_of_Ess h (EssMemI_pt h), Ess_of_Ess2⟩

/-- `EssSupp` at an arbitrary world `v`: were `z ≠ x`, the constant property
"`φ z` and `z ≠ x`" would be non-empty, hence exemplified at a successor of `w` (`Reach_K`),
by an actual being (`AllExist_pt`), against the essence clause for `fun y => y = x`. -/
theorem EssSupp_hf : type_of% @EssSupp := by
  intro φ x w h z v _ pz
  refine Classical.byContradiction fun hzx => ?_
  let χ : e → σ := fun _ => φ z ∧ᵐ ¬ᵐ(z =ᵐ x)
  have hne : χ ≠ (fun _ : e => ⊥ᵐ) := fun hc =>
    (congrFun (congrFun hc z) v ▸ (⟨pz, hzx⟩ : χ z v) : ⊥ᵐ v)
  obtain ⟨u, hu, _, hφ, hn⟩ := Reach_K χ w hne
  exact hn ((h (fun y => y =ᵐ x) rfl u hu).2 z (AllExist_pt u z) hφ)

/-- `EssDetermined`: `⊆` by `EssSupp_hf`; `⊇` because `φ x` holds at `w` (`EssMemI_pt`) and
at every successor (`MC_K`), and a world where it fails would make the constant property
`¬ φ x` non-empty, hence true at a successor (`Reach_K`). -/
theorem EssDetermined_hf : type_of% @EssDetermined := by
  intro φ x w h
  funext z u
  refine propext ⟨fun hφ => EssSupp_hf h (AllExist_pt u z) hφ, fun hzx => ?_⟩
  subst hzx
  refine Classical.byContradiction fun hn => ?_
  let χ : e → σ := fun _ => ¬ᵐ(φ z)
  have hne : χ ≠ (fun _ : e => ⊥ᵐ) := fun hc =>
    (congrFun (congrFun hc z) u ▸ (hn : χ z u) : ⊥ᵐ u)
  obtain ⟨v, hv, _, hnv⟩ := Reach_K χ w hne
  exact hnv (MC_K (φ z) w (EssMemI_pt h) v hv)

/-- `UniqueEss1`, `UniqueEss2` from `EssDetermined_hf` (as v4 does from `EssDetermined`). -/
theorem UniqueEss1_hf : type_of% @UniqueEss1 :=
  fun _ _ _ _ ⟨hφ, hψ⟩ _ _ _ _ => by
    rw [EssDetermined_hf hφ, EssDetermined_hf hψ]; exact Iff.rfl
theorem UniqueEss2_hf : type_of% @UniqueEss2 :=
  fun _ _ _ _ ⟨hφ, hψ⟩ _ _ _ hQ => by
    rw [EssDetermined_hf hφ] at hQ; rw [EssDetermined_hf hψ]; exact hQ

example : type_of% @AllExist_hf = type_of% @AllExist := rfl
example : type_of% @Th3_hf = type_of% @Th3 := rfl
example : type_of% @Th5_hf = type_of% @Th5 := rfl
example : type_of% @MC_hf = type_of% @MC := rfl
example : type_of% @MCdual_hf = type_of% @MCdual := rfl
example : type_of% @Triv_hf = type_of% @Triv := rfl
example : type_of% @UniqueEss1_hf = type_of% @UniqueEss1 := rfl
example : type_of% @UniqueEss2_hf = type_of% @UniqueEss2 := rfl
example : type_of% @UniqueEss3_hf = type_of% @UniqueEss3 := rfl
example : type_of% @EssMemI_hf = type_of% @EssMemI := rfl
example : type_of% @EssMem_hf = type_of% @EssMem := rfl
example : type_of% @Ess_iff_Ess2_hf = type_of% @Ess_iff_Ess2 := rfl
example : type_of% @EssSupp_hf = type_of% @EssSupp := rfl
example : type_of% @EssDetermined_hf = type_of% @EssDetermined := rfl

end Programme.F.HOML3

#print axioms Programme.F.HOML3.AllExist_hf
#print axioms Programme.F.HOML3.MC_hf
#print axioms Programme.F.HOML3.UniqueEss2_hf
#print axioms Programme.F.HOML3.EssDetermined_hf
