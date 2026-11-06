import Programme.«20261104-1627-proof-complexity».ColumnCoverage
import Programme.«20261104-1627-proof-complexity».OmissionPairing
/-! Multiplicity control for maximal-column matching extensions. -/
namespace Programme.«20261104-1627-proof-complexity».MatchingLabels
private theorem extension_unique {m n d : Nat} {E F : Matching} {i j a b : Nat}
    (hE : E ∈ matchings m n d) (hF : F ∈ matchings m n d)
    (hj : E.all (fun e => e.2 < j) = true)
    (hb : F.all (fun e => e.2 < b) = true)
    (he : ordered (E ++ [(i,j)]) = ordered (F ++ [(a,b)])) :
    E = F ∧ i = a ∧ j = b := by
  have pE : (ordered (E ++ [(i,j)])).Perm (E ++ [(i,j)]) := List.mergeSort_perm _ _
  have pF : (ordered (F ++ [(a,b)])).Perm (F ++ [(a,b)]) := List.mergeSort_perm _ _
  have hp : (E ++ [(i,j)]).Perm (F ++ [(a,b)]) :=
    pE.symm.trans (by rw [he]; exact pF)
  have hx := hp.mem_iff.mp (List.mem_append_right E (by simp : (i,j) ∈ [(i,j)]))
  have hy := hp.mem_iff.mpr (List.mem_append_right F (by simp : (a,b) ∈ [(a,b)]))
  have hjb : j = b := by
    rcases List.mem_append.mp hx with hx | hx
    · have hlt := of_decide_eq_true (List.all_eq_true.mp hb (i,j) hx)
      rcases List.mem_append.mp hy with hy | hy
      · have := of_decide_eq_true (List.all_eq_true.mp hj (a,b) hy); omega
      · simp only [List.mem_singleton, Prod.mk.injEq] at hy; omega
    · exact (Prod.mk.inj (List.mem_singleton.mp hx)).2
  have hia : i = a := by
    rcases List.mem_append.mp hx with hx | hx
    · have := of_decide_eq_true (List.all_eq_true.mp hb (i,j) hx); omega
    · exact (Prod.mk.inj (List.mem_singleton.mp hx)).1
  subst a; subst b
  have hp' : E.Perm F := (List.perm_append_right_iff _).mp hp
  exact ⟨hp'.eq_of_pairwise (by intro x y _ _ hxy hyx; omega)
    (matching_rows_strict hE) (matching_rows_strict hF), rfl, rfl⟩
private theorem nodup_bind {α β : Type} (l : List α) (f : α → List β)
    (hl : l.Nodup) (hf : ∀ a ∈ l, (f a).Nodup)
    (sep : ∀ a ∈ l, ∀ b ∈ l, ∀ x ∈ f a, ∀ y ∈ f b, x = y → a = b) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨hf a (by simp), ih hl.2 (by intro b hb; exact hf b (by simp [hb]))
      (by intro b hb c hc x hx y hy he; exact sep b (by simp [hb]) c (by simp [hc]) x hx y hy he), ?_⟩
    intro x hx y hy he
    obtain ⟨b, hb, hy⟩ := List.mem_flatMap.mp hy
    have hab := sep a (by simp) b (by simp [hb]) x hx y hy he
    subst b
    exact hl.1 hb

theorem column_extensions_nodup (m n d : Nat) (N : Matching) :
    (columnExtensions m n d N).Nodup := by
  unfold columnExtensions
  apply nodup_bind _ _ ((matchings_nodup m n d).filter _)
  · intro E hE
    apply nodup_bind _ _ (((List.nodup_range).filter _).filter _)
    · intro j hj
      apply ((List.nodup_range).filter (freeRow (N ++ E))).map
      intro i a hne he
      apply hne
      exact (extension_unique (List.mem_filter.mp hE).1 (List.mem_filter.mp hE).1
          (List.mem_filter.mp hj).2 (List.mem_filter.mp hj).2 he).2.1
    · intro j hj b hb x hx y hy he
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
      exact (extension_unique (List.mem_filter.mp hE).1 (List.mem_filter.mp hE).1
        (List.mem_filter.mp hj).2 (List.mem_filter.mp hb).2 he).2.2
  · intro E hE F hF x hx y hy he
    obtain ⟨j, hj, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, hb, hy⟩ := List.mem_flatMap.mp hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
    exact (extension_unique (List.mem_filter.mp hE).1 (List.mem_filter.mp hF).1
      (List.mem_filter.mp hj).2 (List.mem_filter.mp hb).2 he).1

theorem anchored_column_enumeration (m n d : Nat) (N : Matching) :
    (columnExtensions m n d N).Perm
      ((matchings m n (d+1)).filter (compatible N)) := by
  apply (List.perm_ext_iff_of_nodup (column_extensions_nodup m n d N)
    ((matchings_nodup m n (d+1)).filter _)).mpr
  intro M
  exact column_extensions_coverage m n d N M

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.column_extensions_nodup
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.anchored_column_enumeration
