import Programme.«20261104-1627-proof-complexity».ExtensionOrder

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels

theorem matching_of_properties {m n : Nat} (M : Matching)
    (hb : ∀ e ∈ M, e.1 < m ∧ e.2 < n)
    (hr : M.Pairwise (fun a b => a.1 < b.1))
    (hc : M.Pairwise (fun a b => a.2 ≠ b.2)) :
    M ∈ matchings m n M.length := by
  have aux : ∀ L : Matching, (∀ e ∈ L.reverse, e.1 < m ∧ e.2 < n) →
      L.reverse.Pairwise (fun a b => a.1 < b.1) →
      L.reverse.Pairwise (fun a b => a.2 ≠ b.2) →
      L.reverse ∈ matchings m n L.reverse.length := by
    intro L
    induction L with
    | nil => simp [matchings]
    | cons x L ih =>
      simp only [List.reverse_cons]
      intro hb hr hc
      have hr' := List.pairwise_append.mp hr
      have hc' := List.pairwise_append.mp hc
      have hm := ih (by intro e he; exact hb e (List.mem_append_left _ he)) hr'.1 hc'.1
      simp only [List.length_append, List.length_singleton, matchings, List.mem_flatMap,
        List.mem_map]
      refine ⟨L.reverse, hm, x.1, ?_, x.2, ?_, by simp⟩
      · simp only [List.mem_filter, rows, List.mem_range, freeRow, List.all_eq_true,
          bne_iff_ne, decide_eq_true_eq]
        exact ⟨⟨(hb x (by simp)).1, fun e he => Nat.ne_of_lt (hr'.2.2 e he x (by simp))⟩,
          fun e he => hr'.2.2 e he x (by simp)⟩
      · simp only [cols, List.mem_filter, List.mem_range, freeCol, List.all_eq_true,
          bne_iff_ne]
        exact ⟨(hb x (by simp)).2, fun e he => hc'.2.2 e he x (by simp)⟩
  simpa using aux M.reverse (by simpa using hb) (by simpa using hr) (by simpa using hc)

theorem matching_board_properties {m n d : Nat} {M : Matching}
    (hM : M ∈ matchings m n d) :
    (∀ e ∈ M, e.1 < m ∧ e.2 < n) ∧
    M.Pairwise (fun a b => a.1 ≠ b.1) ∧ M.Pairwise (fun a b => a.2 ≠ b.2) := by
  induction d generalizing M with
  | zero => simp only [matchings, List.mem_singleton] at hM; subst M; simp
  | succ d ih =>
    simp only [matchings, List.mem_flatMap, List.mem_map] at hM
    obtain ⟨N,hN,i,hi,j,hj,rfl⟩ := hM
    have hp := ih hN
    simp only [List.mem_filter, rows, List.mem_range] at hi
    simp only [List.mem_filter, cols, List.mem_range] at hj
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hp.1 e he
      · simp only [List.mem_singleton] at he; subst e; exact ⟨hi.1.1,hj.1⟩
    · apply List.pairwise_append.mpr
      refine ⟨hp.2.1, by simp, ?_⟩
      intro e he f hf
      simp only [List.mem_singleton] at hf; subst f
      exact Nat.ne_of_lt (of_decide_eq_true (List.all_eq_true.mp hi.2 e he))
    · apply List.pairwise_append.mpr
      refine ⟨hp.2.2, by simp, ?_⟩
      intro e he f hf
      simp only [List.mem_singleton] at hf; subst f
      exact of_decide_eq_true (List.all_eq_true.mp hj.2 e he)

theorem ordered_extension_mem {m n e : Nat} {N : Matching}
    (hN : N ∈ matchings m n e) {i j : Nat}
    (hi : i ∈ rows m N) (hj : j ∈ cols n N) :
    ordered (N ++ [(i,j)]) ∈ matchings m n (e+1) := by
  have hp := matching_board_properties hN
  have hi' := List.mem_filter.mp hi
  have hj' := List.mem_filter.mp hj
  have hrow : ∀ a ∈ N, a.1 ≠ i := by
    simpa only [freeRow, List.all_eq_true, bne_iff_ne] using hi'.2
  have hcol : ∀ a ∈ N, a.2 ≠ j := by
    simpa only [freeCol, List.all_eq_true, bne_iff_ne] using hj'.2
  have pr : (N ++ [(i,j)]).Pairwise (fun a b => a.1 ≠ b.1) :=
    List.pairwise_append.mpr ⟨hp.2.1, by simp, by simpa using hrow⟩
  have pc : (N ++ [(i,j)]).Pairwise (fun a b => a.2 ≠ b.2) :=
    List.pairwise_append.mpr ⟨hp.2.2, by simp, by simpa using hcol⟩
  have perm := List.mergeSort_perm (N ++ [(i,j)]) (fun a b => a.1 ≤ b.1)
  have pr' : (ordered (N ++ [(i,j)])).Pairwise (fun a b => a.1 ≠ b.1) :=
    (perm.pairwise_iff (by intro a b h; exact Ne.symm h)).mpr pr
  have pc' : (ordered (N ++ [(i,j)])).Pairwise (fun a b => a.2 ≠ b.2) :=
    (perm.pairwise_iff (by intro a b h; exact Ne.symm h)).mpr pc
  have ple : (ordered (N ++ [(i,j)])).Pairwise (fun a b => a.1 ≤ b.1) := by
    simpa only [ordered, decide_eq_true_eq] using
      List.pairwise_mergeSort (le := fun a b : Nat × Nat => decide (a.1 ≤ b.1))
        (by simp only [decide_eq_true_eq]; intros; omega)
        (by simp only [Bool.or_eq_true, decide_eq_true_eq]; intros; omega) (N ++ [(i,j)])
  have h := matching_of_properties (ordered (N ++ [(i,j)])) (by
    intro a ha
    have ha' := perm.mem_iff.mp ha
    rcases List.mem_append.mp ha' with ha' | ha'
    · exact hp.1 a ha'
    · simp only [List.mem_singleton] at ha'; subst a
      exact ⟨List.mem_range.mp hi'.1, List.mem_range.mp hj'.1⟩)
    ((ple.and pr').imp (by intro a b h; omega)) pc'
  simpa only [ordered, List.length_mergeSort, List.length_append, List.length_singleton,
    matching_length hN] using h

theorem extended_row_label_mem {m n e : Nat} {N : Matching}
    (hN : N ∈ matchings m n e) {i j a : Nat}
    (hi : i ∈ rows m N) (hj : j ∈ cols n N)
    (ha : a ∈ rows m N) (hne : a ≠ i) :
    (⟨ordered (N ++ [(i,j)]), true, a⟩ : Label) ∈ labels m n (e+2) := by
  have hm := ordered_extension_mem hN hi hj
  have hf : a ∈ rows m (ordered (N ++ [(i,j)])) := by
    rw [rows_extend]
    exact List.mem_filter.mpr ⟨ha, by simpa using hne⟩
  simp only [labels, Nat.add_eq_zero_iff, Nat.reduceEqDiff, and_false, ↓reduceIte,
    List.mem_flatMap, List.mem_append, List.mem_map]
  exact ⟨_, hm, Or.inl ⟨a, hf, rfl⟩⟩

theorem extended_col_label_mem {m n e : Nat} {N : Matching}
    (hN : N ∈ matchings m n e) {i j b : Nat}
    (hi : i ∈ rows m N) (hj : j ∈ cols n N)
    (hb : b ∈ cols n N) (hne : b ≠ j) :
    (⟨ordered (N ++ [(i,j)]), false, b⟩ : Label) ∈ labels m n (e+2) := by
  have hm := ordered_extension_mem hN hi hj
  have hf : b ∈ cols n (ordered (N ++ [(i,j)])) := by
    rw [cols_extend]
    exact List.mem_filter.mpr ⟨hb, by simpa using hne⟩
  simp only [labels, Nat.add_eq_zero_iff, Nat.reduceEqDiff, and_false, ↓reduceIte,
    List.mem_flatMap, List.mem_append, List.mem_map]
  exact ⟨_, hm, Or.inr ⟨b, hf, rfl⟩⟩

theorem rr_valid {m n e : Nat} {N : Matching}
    (hN : N ∈ matchings m n e) {a b : Nat}
    (ha : a ∈ rows m N) (hb : b ∈ rows m N) (hne : a ≠ b) :
    valid m n (e+2) (rr n N a b) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
    exact extended_row_label_mem hN hb hj ha hne
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
    exact extended_row_label_mem hN ha hj hb hne.symm

theorem cc_valid {m n e : Nat} {N : Matching}
    (hN : N ∈ matchings m n e) {a b : Nat}
    (ha : a ∈ cols n N) (hb : b ∈ cols n N) (hne : a ≠ b) :
    valid m n (e+2) (cc m N a b) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
    exact extended_col_label_mem hN hi hb ha hne
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
    exact extended_col_label_mem hN hi ha hb hne.symm

theorem rc_valid_general {m n e : Nat} {N : Matching}
    (hN : N ∈ matchings m n e) {i j : Nat}
    (hi : i ∈ rows m N) (hj : j ∈ cols n N) :
    valid m n (e+2) (rc m n N i j) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
    have ha' := List.mem_filter.mp ha
    exact extended_row_label_mem hN ha'.1 hj hi
      (Ne.symm (by simpa using ha'.2))
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
    have hb' := List.mem_filter.mp hb
    exact extended_col_label_mem hN hi hb'.1 hj
      (Ne.symm (by simpa using hb'.2))

theorem rc_kernel {p m n e : Nat} {N : Matching}
    (hN : N ∈ matchings m n e) {i j : Nat}
    (hi : i ∈ rows m N) (hj : j ∈ cols n N) :
    Kernel p m n (e+2) (rc m n N i j) := by
  refine ⟨rc_valid_general hN hi hj, ?_⟩
  intro u
  rw [rc_top_zero]
  simp [Programme.«20261029-1156-proof-complexity».StdPC.coeff,
    Programme.«20261029-1156-proof-complexity».StdPC.cf]

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.ordered_extension_mem

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.extended_row_label_mem
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.extended_col_label_mem

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.rr_valid
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.cc_valid
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.rc_valid_general
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.rc_kernel
