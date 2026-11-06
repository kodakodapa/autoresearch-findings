import Programme.«20261104-1627-proof-complexity».AnchoredCancellation
import Programme.«20261104-1627-proof-complexity».OrdinarySoundness

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC

theorem ordered_union_mem {m n e t : Nat} {N E : Matching}
    (hN : N ∈ matchings m n e) (hE : E ∈ matchings m n t)
    (hc : compatible N E = true) :
    ordered (N ++ E) ∈ matchings m n (e+t) := by
  have pn := matching_board_properties hN
  have pe := matching_board_properties hE
  have cross : ∀ b ∈ E, (∀ a ∈ N, a.1 ≠ b.1) ∧ (∀ a ∈ N, a.2 ≠ b.2) := by
    intro b hb
    have hh := List.all_eq_true.mp hc b hb
    simpa only [Bool.and_eq_true, freeRow, freeCol, List.all_eq_true, bne_iff_ne] using hh
  have pr : (N ++ E).Pairwise (fun a b => a.1 ≠ b.1) :=
    List.pairwise_append.mpr ⟨pn.2.1, pe.2.1, fun a ha b hb => (cross b hb).1 a ha⟩
  have pc : (N ++ E).Pairwise (fun a b => a.2 ≠ b.2) :=
    List.pairwise_append.mpr ⟨pn.2.2, pe.2.2, fun a ha b hb => (cross b hb).2 a ha⟩
  have perm := List.mergeSort_perm (N ++ E) (fun a b => a.1 ≤ b.1)
  have pr' := (perm.pairwise_iff (by intro a b (h : a.1 ≠ b.1); exact Ne.symm h)).mpr pr
  have pc' := (perm.pairwise_iff (by intro a b (h : a.2 ≠ b.2); exact Ne.symm h)).mpr pc
  have ple : (ordered (N ++ E)).Pairwise (fun a b => a.1 ≤ b.1) := by
    simpa only [ordered, decide_eq_true_eq] using
      List.pairwise_mergeSort (le := fun a b : Nat × Nat => decide (a.1 ≤ b.1))
        (by simp only [decide_eq_true_eq]; intros; omega)
        (by simp only [Bool.or_eq_true, decide_eq_true_eq]; intros; omega) (N ++ E)
  have hh := matching_of_properties (ordered (N ++ E)) (by
    intro a ha
    rcases List.mem_append.mp (perm.mem_iff.mp ha) with ha | ha
    · exact pn.1 a ha
    · exact pe.1 a ha)
    ((ple.and pr').imp (by intro a b h; omega)) pc'
  simpa only [ordered, List.length_mergeSort, List.length_append,
    matching_length hN, matching_length hE] using hh

private theorem rows_sort (m : Nat) (M : Matching) : rows m (ordered M) = rows m M := by
  unfold rows
  congr 1
  funext i
  apply Bool.eq_iff_iff.mpr
  simp [freeRow, ordered, List.all_eq_true]

private theorem cols_sort (n : Nat) (M : Matching) : cols n (ordered M) = cols n M := by
  unfold cols
  congr 1
  funext i
  apply Bool.eq_iff_iff.mpr
  simp [freeCol, ordered, List.all_eq_true]

theorem z_valid {m n e t : Nat} {N : Matching}
    (hN : N ∈ matchings m n e) :
    valid m n (e+t+1) (z m n (t+1) N) := by
  intro a ha
  simp only [z, Nat.add_sub_cancel, List.mem_flatMap, List.mem_filter] at ha
  obtain ⟨E, ⟨hE,hc⟩, ha⟩ := ha
  have hm := ordered_union_mem hN hE hc
  have hl : labels m n (e+t+1) = (matchings m n (e+t)).flatMap (fun M =>
      (rows m M).map (fun i => (⟨M,true,i⟩ : Label)) ++
      (cols n M).map (fun j => (⟨M,false,j⟩ : Label))) := by simp [labels]
  rw [hl]
  apply List.mem_flatMap.mpr
  refine ⟨_,hm,?_⟩
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨i, by rw [rows_sort]; exact (List.mem_filter.mp hi).1, rfl⟩
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨j, by rw [cols_sort]; exact (List.mem_filter.mp hj).1, rfl⟩

theorem z_kernel {p m n e t : Nat} {N : Matching}
    (hN : N ∈ matchings m n e) :
    Kernel p m n (e+t+1) (z m n (t+1) N) := by
  refine ⟨z_valid hN, ?_⟩
  intro u
  rw [z_top_zero]
  simp [coeff, cf]

theorem syzygies_sound (p m n d : Nat) :
    ∀ v ∈ syzygies m n d, Kernel p m n d v := by
  intro v hv
  unfold syzygies at hv
  rcases List.mem_append.mp hv with hv | hv
  · split at hv
    · simp at hv
    · rename_i hd
      obtain ⟨N,hN,hv⟩ := List.mem_flatMap.mp hv
      have he : d-2+2 = d := by omega
      rcases List.mem_append.mp hv with hv | hv
      · rcases List.mem_append.mp hv with hv | hv
        · obtain ⟨a,ha,hv⟩ := List.mem_flatMap.mp hv
          obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hv
          have hb' := List.mem_filter.mp hb
          have hab : a < b := by simpa using hb'.2
          simpa only [he] using rr_kernel (p := p) hN ha hb'.1 (Nat.ne_of_lt hab)
        · obtain ⟨a,ha,hv⟩ := List.mem_flatMap.mp hv
          obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hv
          have hb' := List.mem_filter.mp hb
          have hab : a < b := by simpa using hb'.2
          simpa only [he] using cc_kernel (p := p) hN ha hb'.1 (Nat.ne_of_lt hab)
      · obtain ⟨i,hi,hv⟩ := List.mem_flatMap.mp hv
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
        simpa only [he] using rc_kernel (p := p) hN hi hj
  · obtain ⟨t,ht,hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
    obtain ⟨N,hN,rfl⟩ := List.mem_map.mp hv
    have hs' := List.mem_range.mp hs
    have he : d-(s+1)+s+1 = d := by omega
    simpa only [he] using z_kernel (p := p) (t := s) hN

theorem first_block_residual_sound {p m n d : Nat} {v : Vector}
    (hv : Kernel p (m+1) n d v) (hs : Spanning p m n d) :
    ∃ C : List (Int × Vector),
      (∀ t ∈ C, t.2 ∈ syzygies (m+1) n d) ∧
      Kernel p (m+1) n d (v ++ (combine C).map (fun t => (-t.1,t.2))) ∧
      ∀ g, (p : Int) ∣ vectorCoeff (splitPigeon m 1
        (v ++ (combine C).map (fun t => (-t.1,t.2)))) g :=
  first_block_kernel_residual hv hs (syzygies_sound p (m+1) n d)

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.ordered_union_mem
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.z_valid
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.z_kernel

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.syzygies_sound

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.first_block_residual_sound
