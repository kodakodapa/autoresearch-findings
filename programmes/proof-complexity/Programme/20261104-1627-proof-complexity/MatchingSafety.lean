import Programme.«20261104-1627-proof-complexity».ForbiddenClassification
import Programme.«20261104-1627-proof-complexity».SquareFreeCoefficientBridge
namespace Programme.«20261104-1627-proof-complexity».MatchingSafety
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».MatchingReduction Programme.«20261104-1627-proof-complexity».MatchingSquareFree Programme.«20261104-1627-proof-complexity».BoundedRelationCertificates

theorem matching_separated {m n d : Nat} {M : Matching}
    (hM : M ∈ matchings m n d) :
    M.Pairwise (fun a b => a.1 ≠ b.1 ∧ a.2 ≠ b.2) := by
  induction d generalizing M with
  | zero => simp only [matchings, List.mem_singleton] at hM; subst M; simp
  | succ d ih =>
    simp only [matchings, List.mem_flatMap, List.mem_map] at hM
    obtain ⟨N,hN,i,hi,j,hj,rfl⟩ := hM
    apply List.pairwise_append.mpr
    refine ⟨ih hN, by simp, ?_⟩
    intro e he f hf
    have ef : f = (i,j) := by simpa using hf
    subst f
    exact ⟨of_decide_eq_true (List.all_eq_true.mp (List.mem_filter.mp
      (List.mem_filter.mp hi).1).2 e he),
      of_decide_eq_true (List.all_eq_true.mp (List.mem_filter.mp hj).2 e he)⟩

theorem safe_codes {n k : Nat} (hn : 0 < n) (M : Matching)
    (hb : ∀ e ∈ M, e.2 < n)
    (hp : M.Pairwise (fun a b => a.1 ≠ b.1 ∧ a.2 ≠ b.2)) :
    Safe (ontoFPHP n k) (mono n M) := by
  apply Programme.«20261104-1627-proof-complexity».ForbiddenClassification.safe_of_coordinates hn
  intro u hu w hw hne
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hu
  obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hw
  have hab : a ≠ b := by intro h; subst b; exact hne rfl
  have hp' : M.Pairwise (fun a b => a = b ∨ (a.1 ≠ b.1 ∧ a.2 ≠ b.2)) :=
    hp.imp (fun h => Or.inr h)
  have all := List.Pairwise.forall_of_forall_of_flip (fun (a : Nat × Nat) (_ : a ∈ M) => Or.inl rfl) hp'
    (hp'.imp (by
      intro a b h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨h.1.symm,h.2.symm⟩))
  have sep := (all ha hb').resolve_left hab
  have div (e : Nat × Nat) (he : e ∈ M) : (e.1*n+e.2)/n = e.1 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt (hb e he)]; omega
  have mod (e : Nat × Nat) (he : e ∈ M) : (e.1*n+e.2)%n = e.2 := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt (hb e he)]
  simpa only [div a ha, div b hb', mod a ha, mod b hb'] using sep

theorem matching_safe {n k d : Nat} (hn : 0 < n) {M : Matching}
    (hM : M ∈ matchings (n+k) n d) : Safe (ontoFPHP n k) (mono n M) :=
  safe_codes hn M (fun e he => (matching_bounds hM e he).2) (matching_separated hM)

theorem extension_safe {n k d i j : Nat} (hn : 0 < n) {M : Matching}
    (hM : M ∈ matchings (n+k) n d) (hi : freeRow M i = true)
    (hj : freeCol M j = true) (hjb : j < n) :
    Safe (ontoFPHP n k) ((i*n+j) :: mono n M) := by
  change Safe (ontoFPHP n k) (mono n ((i,j)::M))
  apply safe_codes hn
  · intro e he
    rcases List.mem_cons.mp he with h | h
    · subst e; exact hjb
    · exact (matching_bounds hM e h).2
  · apply List.pairwise_cons.mpr
    refine ⟨?_, matching_separated hM⟩
    intro e he
    have hr : e.1 ≠ i := of_decide_eq_true (List.all_eq_true.mp hi e he)
    have hc : e.2 ≠ j := of_decide_eq_true (List.all_eq_true.mp hj e he)
    exact ⟨hr.symm,hc.symm⟩

theorem label_safe {n k d : Nat} (hn : 0 < n) {g : Label}
    (hg : g ∈ labels (n+k) n d) :
    ∀ t ∈ (relation (n+k) n g).terms, Safe (ontoFPHP n k) t.2 := by
  have hd : d ≠ 0 := by intro h; subst d; simpa [labels] using hg
  unfold labels at hg
  rw [if_neg hd] at hg
  obtain ⟨M,hM,hg⟩ := List.mem_flatMap.mp hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hg
    intro t ht
    simp only [relation, topLabel, Poly.sub, List.mem_append, Bool.false_eq_true,
      ite_true, ite_false, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with ht | ht
    · obtain ⟨j,hj,rfl⟩ := ht
      exact extension_safe hn hM (List.mem_filter.mp hi).2
        (List.mem_filter.mp hj).2 (List.mem_range.mp (List.mem_filter.mp hj).1)
    · obtain ⟨u,hu,rfl⟩ := ht
      have : u = (1,mono n M) := by simpa using hu
      subst u; exact matching_safe hn hM
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
    intro t ht
    simp only [relation, topLabel, Poly.sub, List.mem_append, Bool.false_eq_true,
      ite_true, ite_false, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with ht | ht
    · obtain ⟨i,hi,rfl⟩ := ht
      exact extension_safe hn hM (List.mem_filter.mp hi).2
        (List.mem_filter.mp hj).2 (List.mem_range.mp (List.mem_filter.mp hj).1)
    · obtain ⟨u,hu,rfl⟩ := ht
      have : u = (1,mono n M) := by simpa using hu
      subst u; exact matching_safe hn hM

theorem bounded_reduced {n k D : Nat} (hn : 0 < n) (v : Vector)
    (hv : ∀ z ∈ v, ∃ d, d ≤ D ∧ z.2 ∈ labels (n+k) n d) :
    Programme.«20261104-1627-proof-complexity».SquareFreeCoefficientBridge.Reduced (ontoFPHP n k) (relations (n+k) n v) := by
  intro t ht
  refine ⟨bounded_squarefree v hv t ht, ?_⟩
  obtain ⟨z,hz,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
  obtain ⟨d,_,hg⟩ := hv z hz
  exact label_safe hn hg u hu
theorem supported_raw_W {p n k D : Nat} (hn : 0 < n) (Q : Poly Nat)
    (hQ : Programme.«20261104-1627-proof-complexity».SupportedCertificates.Supported (fun x => decide (x < (n+k)*n)) Q)
    (h : Programme.«20261025-1627-proof-complexity».NoDrop.NSIn p
      (ontoFPHP n k) D Q.eval) :
    W p (n+k) n D (reduce (ontoFPHP n k) Q) := by
  obtain ⟨v,hv,he⟩ := Programme.«20261104-1627-proof-complexity».SupportedExtraction.supported_extraction hn Q hQ h
  refine ⟨v,hv,?_⟩
  apply Programme.«20261104-1627-proof-complexity».SquareFreeCoefficientBridge.peq_of_good
    (support_reduce _ _) (bounded_reduced hn v hv)
  intro a ha
  rw [eval_reduce _ _ a ha]
  obtain ⟨c,hc⟩ := he a ha
  refine ⟨-c, ?_⟩
  rw [Int.mul_neg]
  omega

end Programme.«20261104-1627-proof-complexity».MatchingSafety
#print axioms Programme.«20261104-1627-proof-complexity».MatchingSafety.supported_raw_W

#print axioms Programme.«20261104-1627-proof-complexity».MatchingSafety.bounded_reduced
