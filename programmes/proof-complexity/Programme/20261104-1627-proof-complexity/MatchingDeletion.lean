import Programme.«20261104-1627-proof-complexity».OrderedExtension
import Programme.«20261104-1627-proof-complexity».AnchoredRowEnumeration

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels

theorem matching_rows_strict {m n d : Nat} {M : Matching}
    (hM : M ∈ matchings m n d) : M.Pairwise (fun a b => a.1 < b.1) := by
  induction d generalizing M with
  | zero => simp only [matchings, List.mem_singleton] at hM; subst M; simp
  | succ d ih =>
    simp only [matchings, List.mem_flatMap, List.mem_map] at hM
    obtain ⟨N,hN,i,hi,j,hj,rfl⟩ := hM
    apply List.pairwise_append.mpr
    refine ⟨ih hN, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact of_decide_eq_true (List.all_eq_true.mp (List.mem_filter.mp hi).2 a ha)

/-- Removing any edge preserves the canonical row order and matching enumeration. -/
theorem matching_erase_mem {m n d : Nat} {M : Matching} {x : Nat × Nat}
    (hM : M ∈ matchings m n (d+1)) (hx : x ∈ M) :
    M.erase x ∈ matchings m n d := by
  have hp := matching_board_properties hM
  have he := matching_of_properties (M.erase x)
    (by intro a ha; exact hp.1 a (List.mem_of_mem_erase ha))
    ((matching_rows_strict hM).sublist (List.erase_sublist))
    (hp.2.2.sublist (List.erase_sublist))
  have hl := List.length_erase_of_mem hx
  have hm := matching_length hM
  have hh : (M.erase x).length = d := by omega
  simpa only [hh] using he

/-- The deleted edge is fresh for the remaining matching in both coordinates. -/
theorem matching_erase_fresh {m n d : Nat} {M : Matching} {x : Nat × Nat}
    (hM : M ∈ matchings m n (d+1)) (hx : x ∈ M) :
    x.1 ∈ rows m (M.erase x) ∧ x.2 ∈ cols n (M.erase x) := by
  have hp := matching_board_properties hM
  have perm := List.perm_cons_erase hx
  have hr := (perm.pairwise_iff (by intro a b h; exact Ne.symm h)).mp hp.2.1
  have hc := (perm.pairwise_iff (by intro a b h; exact Ne.symm h)).mp hp.2.2
  have hb := hp.1 x hx
  simp only [List.pairwise_cons] at hr hc
  constructor
  · simp only [rows, List.mem_filter, List.mem_range, freeRow, List.all_eq_true,
      bne_iff_ne]
    exact ⟨hb.1, fun a ha => (hr.1 a ha).symm⟩
  · simp only [cols, List.mem_filter, List.mem_range, freeCol, List.all_eq_true,
      bne_iff_ne]
    exact ⟨hb.2, fun a ha => (hc.1 a ha).symm⟩

theorem matching_erase_reconstruct {m n d : Nat} {M : Matching} {x : Nat × Nat}
    (hM : M ∈ matchings m n (d+1)) (hx : x ∈ M) :
    ordered (M.erase x ++ [x]) = M := by
  have hf := matching_erase_fresh hM hx
  have he := ordered_extension_mem (matching_erase_mem hM hx) hf.1 hf.2
  have hp : (ordered (M.erase x ++ [x])).Perm M :=
    (List.mergeSort_perm _ _).trans
      (List.perm_append_comm.trans (List.perm_cons_erase hx).symm)
  exact hp.eq_of_pairwise (by intro a b ha hb hab hba; have := hab; omega)
    (matching_rows_strict he) (matching_rows_strict hM)

/-- A maximal-column edge supplies a preimage in the proposed column enumeration. -/
theorem column_max_preimage {m n d : Nat} {N M : Matching} {x : Nat × Nat}
    (hM : M ∈ matchings m n (d+1)) (hx : x ∈ M)
    (hN : compatible N M = true)
    (hmax : ∀ a ∈ M, a.2 ≤ x.2) :
    M ∈ (((matchings m n d).filter (compatible N)).flatMap fun E =>
      ((cols n (N ++ E)).filter (fun j => E.all fun e => e.2 < j)).flatMap
        fun j => (rows m (N ++ E)).map fun i => ordered (E ++ [(i,j)])) := by
  have hf := matching_erase_fresh hM hx
  have hn : compatible N (M.erase x) = true := by
    apply List.all_eq_true.mpr
    intro a ha
    exact List.all_eq_true.mp hN a (List.mem_of_mem_erase ha)
  have hnx := List.all_eq_true.mp hN x hx
  simp only [Bool.and_eq_true] at hnx
  have hc : x.2 ∈ cols n (N ++ M.erase x) := by
    simp only [cols, List.mem_filter, List.mem_range, freeCol, List.all_append,
      Bool.and_eq_true] at hf ⊢
    exact ⟨hf.2.1, hnx.2, hf.2.2⟩
  have hr : x.1 ∈ rows m (N ++ M.erase x) := by
    simp only [rows, List.mem_filter, List.mem_range, freeRow, List.all_append,
      Bool.and_eq_true] at hf ⊢
    exact ⟨hf.1.1, hnx.1, hf.1.2⟩
  have hlt : (M.erase x).all (fun e => e.2 < x.2) = true := by
    apply List.all_eq_true.mpr
    intro a ha
    have hle := hmax a (List.mem_of_mem_erase ha)
    have hne := List.all_eq_true.mp (List.mem_filter.mp hf.2).2 a ha
    simp only [bne_iff_ne] at hne
    exact decide_eq_true (by omega)
  simp only [List.mem_flatMap, List.mem_filter, List.mem_map]
  exact ⟨M.erase x, ⟨matching_erase_mem hM hx, hn⟩, x.2, ⟨hc, hlt⟩,
    x.1, hr, matching_erase_reconstruct hM hx⟩

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.matching_erase_mem

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.matching_erase_fresh
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.matching_erase_reconstruct

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.column_max_preimage
