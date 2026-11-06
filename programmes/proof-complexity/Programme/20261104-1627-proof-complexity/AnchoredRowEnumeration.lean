import Programme.«20261104-1627-proof-complexity».ExtensionOrder

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels

def compatible (N E : Matching) : Bool :=
  E.all fun e => freeRow N e.1 && freeCol N e.2

private theorem filter_bind {α β : Type} (L : List α) (q : α → Bool)
    (f : α → List β) :
    (L.filter q).flatMap f = L.flatMap (fun a => if q a then f a else []) := by
  induction L with
  | nil => rfl
  | cons a L ih => by_cases h : q a = true <;> simp [h, ih]

private theorem bind_congr {α β : Type} (L : List α) (f g : α → List β)
    (h : ∀ a ∈ L, f a = g a) : L.flatMap f = L.flatMap g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (by intro b hb; exact h b (by simp [hb]))]

/-- Exact enumeration by deleting the largest-row edge, with a disjoint base. -/
theorem anchored_row_enumeration (m n d : Nat) (N : Matching) :
    ((matchings m n d).filter (compatible N)).flatMap (fun E =>
      ((rows m (N ++ E)).filter (fun i => E.all fun e => e.1 < i)).flatMap
        (fun i => (cols n (N ++ E)).map (fun j => E ++ [(i,j)]))) =
    (matchings m n (d+1)).filter (compatible N) := by
  rw [matchings, List.filter_flatMap]
  rw [filter_bind]
  apply bind_congr
  intro E hE
  rw [List.filter_flatMap]
  by_cases h : compatible N E = true
  · simp only [h, ↓reduceIte]
    unfold rows cols
    simp only [List.filter_filter]
    rw [filter_bind, filter_bind]
    apply bind_congr
    intro i hi
    simp only [List.filter_map]
    unfold compatible at h ⊢
    simp only [Function.comp_def, List.all_append, List.all_cons, List.all_nil,
      Bool.and_true, h, Bool.true_and]
    have hrA : freeRow (N ++ E) i = (freeRow N i && freeRow E i) := by
      simp [freeRow, List.all_append]
    have hcA : ∀ j, freeCol (N ++ E) j = (freeCol N j && freeCol E j) := by
      intro j; simp [freeCol, List.all_append]
    have hcF : freeCol (N ++ E) = fun j => freeCol N j && freeCol E j := funext hcA
    simp only [hrA, hcF, List.filter_filter]
    by_cases hr : freeRow N i = true
    · simp only [hr, Bool.true_and]
    · simp [hr, Bool.and_comm]
  · have hf : compatible N E = false := Bool.eq_false_iff.mpr h
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    have hz : ∀ i, ((cols n E).map (fun j => E ++ [(i,j)])).filter (compatible N) = [] := by
      intro i
      simp [List.filter_map, compatible, List.all_append,
        show E.all (fun e => freeRow N e.1 && freeCol N e.2) = false from hf]
    simp [hz]

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.anchored_row_enumeration
