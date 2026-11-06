import Programme.«20261024-1633-proof-complexity».KSub
/-!
# Positive errors summed over gates (counting form for the approximation method)

`pos_count` bounds the `k`-sublists of `V` containing some long set. Here it is put in the form
the gate-by-gate induction uses: any error predicate `P` on test cliques `K` that only fires when
`K` contains one of a list `Ts` of long sets is counted by `|Ts|·C(|V|-ℓ-1, k-ℓ-1)`
(`pred_count`); summing over a list of gates `(P_g, Ts_g)` gives the bound with `Σ|Ts_g|`
(`gates_count`); and the complement (`good_count`) is the number of test cliques on which no gate
errs.
-/

namespace Programme.«20261024-1633-proof-complexity».KSub

theorem pred_count (V : List Nat) (hV : V.Nodup) (k ℓ : Nat) (Ts : List (List Nat))
    (hTs : ∀ T ∈ Ts, T.Nodup ∧ (∀ i ∈ T, i ∈ V) ∧ ℓ + 1 ≤ T.length) (hk : ℓ + 1 ≤ k)
    (P : List Nat → Bool) (hP : ∀ K ∈ ksub V k, P K = true → ∃ T ∈ Ts, sub T K = true) :
    ((ksub V k).filter P).length ≤ Ts.length * ch (V.length - (ℓ + 1)) (k - (ℓ + 1)) := by
  refine Nat.le_trans (filter_mono ?_) (pos_count V hV k ℓ Ts hTs hk)
  intro K hK h
  obtain ⟨T, hT, hs⟩ := hP K hK h
  exact List.any_eq_true.2 ⟨T, hT, hs⟩

/-- Total number of long sets over a list of gates. -/
def gtot : List ((List Nat → Bool) × List (List Nat)) → Nat
  | [] => 0
  | g :: gs => g.2.length + gtot gs

theorem tot_flat : ∀ gs : List ((List Nat → Bool) × List (List Nat)),
    (gs.flatMap fun g => g.2).length = gtot gs
  | [] => rfl
  | g :: gs => by simp [List.flatMap_cons, gtot, tot_flat gs]

/-- Union bound over gates: test cliques on which some gate errs. -/
theorem gates_count (V : List Nat) (hV : V.Nodup) (k ℓ : Nat)
    (gs : List ((List Nat → Bool) × List (List Nat)))
    (hTs : ∀ g ∈ gs, ∀ T ∈ g.2, T.Nodup ∧ (∀ i ∈ T, i ∈ V) ∧ ℓ + 1 ≤ T.length) (hk : ℓ + 1 ≤ k)
    (hP : ∀ g ∈ gs, ∀ K ∈ ksub V k, g.1 K = true → ∃ T ∈ g.2, sub T K = true) :
    ((ksub V k).filter fun K => gs.any fun g => g.1 K).length
      ≤ gtot gs * ch (V.length - (ℓ + 1)) (k - (ℓ + 1)) := by
  rw [← tot_flat]
  apply pred_count V hV k ℓ _ _ hk
  · intro K hK h
    obtain ⟨g, hg, h1⟩ := List.any_eq_true.1 h
    obtain ⟨T, hT, hs⟩ := hP g hg K hK h1
    exact ⟨T, List.mem_flatMap.2 ⟨g, hg, hT⟩, hs⟩
  · intro T hT
    obtain ⟨g, hg, hT'⟩ := List.mem_flatMap.1 hT
    exact hTs g hg T hT'

theorem filter_compl (l : List (List Nat)) (P : List Nat → Bool) :
    (l.filter P).length + (l.filter fun K => !P K).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : P a <;> simp [h] <;> omega

/-- Test cliques on which no gate errs: at least `C(|V|,k) - Σ|Ts_g|·C(|V|-ℓ-1,k-ℓ-1)`. -/
theorem good_count (V : List Nat) (hV : V.Nodup) (k ℓ : Nat)
    (gs : List ((List Nat → Bool) × List (List Nat)))
    (hTs : ∀ g ∈ gs, ∀ T ∈ g.2, T.Nodup ∧ (∀ i ∈ T, i ∈ V) ∧ ℓ + 1 ≤ T.length) (hk : ℓ + 1 ≤ k)
    (hP : ∀ g ∈ gs, ∀ K ∈ ksub V k, g.1 K = true → ∃ T ∈ g.2, sub T K = true) :
    ch V.length k ≤ ((ksub V k).filter fun K => !(gs.any fun g => g.1 K)).length
      + gtot gs * ch (V.length - (ℓ + 1)) (k - (ℓ + 1)) := by
  have h1 := gates_count V hV k ℓ gs hTs hk hP
  have h2 := filter_compl (ksub V k) (fun K => gs.any fun g => g.1 K)
  rw [ksub_length] at h2
  omega

end Programme.«20261024-1633-proof-complexity».KSub

#print axioms Programme.«20261024-1633-proof-complexity».KSub.pred_count
#print axioms Programme.«20261024-1633-proof-complexity».KSub.gates_count
#print axioms Programme.«20261024-1633-proof-complexity».KSub.good_count
