import Programme.«20261104-1627-proof-complexity».AnchoredDegreeFour
import Programme.«20261104-1627-proof-complexity».OrdinaryRhoLowering
import Programme.«20261104-1627-proof-complexity».RhoCoordinateTransport
import Programme.«20261104-1627-proof-complexity».HomogeneousLabels
namespace Programme.«20261104-1627-proof-complexity».SyzygyLowering
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261025-0459-proof-complexity».OntoFPHP
private theorem row_mem {m : Nat} {N : Matching} {i : Nat} (h : i ∈ rows m N) :
    i < m ∧ ∀ e ∈ N, e.1 ≠ i := by
  simpa only [rows, List.mem_filter, List.mem_range, freeRow, List.all_eq_true, bne_iff_ne] using h
private theorem col_mem {n : Nat} {N : Matching} {i : Nat} (h : i ∈ cols n N) :
    i < n ∧ ∀ e ∈ N, e.2 ≠ i := by
  simpa only [cols, List.mem_filter, List.mem_range, freeCol, List.all_eq_true, bne_iff_ne] using h

theorem generator_lowering {n k d : Nat} (hk : 9 ∣ k) (hd : d ≤ 4) (hn : d ≤ n)
    {w : Vector} (hw : w ∈ syzygies (n+k) n d) :
    NSIn 3 (ontoFPHP n k) (d-1) (rho n w).eval := by
  unfold syzygies at hw
  rcases List.mem_append.mp hw with ho | hz
  · split at ho
    · simp at ho
    · rename_i h2
      have h2 : 2 ≤ d := by omega
      obtain ⟨N,hN,ho⟩ := List.mem_flatMap.mp ho
      have hlen := matching_length hN
      have hb := Programme.«20261104-1627-proof-complexity».BoundedRelationCertificates.matching_bounds hN
      have he : N.length+1 = d-1 := by omega
      rcases List.mem_append.mp ho with ho | ho
      · rcases List.mem_append.mp ho with hr | hc
        · obtain ⟨i,hi,hr⟩ := List.mem_flatMap.mp hr
          obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hr
          have hj := (List.mem_filter.mp hj).1
          obtain ⟨hi,fi⟩ := row_mem hi
          obtain ⟨hj,fj⟩ := row_mem hj
          simpa only [he] using Programme.«20261104-1627-proof-complexity».OrdinaryRhoLowering.rr_lowering (p:=3) N hi hj fi fj (fun e he => (hb e he).1)
        · obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
          obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
          have hj := (List.mem_filter.mp hj).1
          obtain ⟨hi,fi⟩ := col_mem hi
          obtain ⟨hj,fj⟩ := col_mem hj
          simpa only [he] using Programme.«20261104-1627-proof-complexity».OrdinaryRhoLowering.cc_lowering (p:=3) N hi hj fi fj (fun e he => (hb e he).2)
      · obtain ⟨i,hi,ho⟩ := List.mem_flatMap.mp ho
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ho
        obtain ⟨hi,fi⟩ := row_mem hi
        obtain ⟨hj,fj⟩ := col_mem hj
        simpa only [he] using Programme.«20261104-1627-proof-complexity».MixedRhoLowering.rc_lowering (p:=3) N hi hj fi fj (fun e he => (hb e he).1) (fun e he => (hb e he).2)
  · obtain ⟨t,ht,hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨N,hN,rfl⟩ := List.mem_map.mp hz
    exact Programme.«20261104-1627-proof-complexity».AnchoredDegreeFour.level_lowering hk hd ht hn hN

theorem kernel_lowering {n k d : Nat} (hk : 9 ∣ k) (hd : d ≤ 4) (hn : d ≤ n)
    (span : Spanning 3 (n+k) n d) {v : Vector} (hv : Kernel 3 (n+k) n d v) :
    NSIn 3 (ontoFPHP n k) (d-1) (rho n v).eval :=
  Programme.«20261104-1627-proof-complexity».RhoCoordinateTransport.kernel_lowering_of_spanning span (fun _ hw => generator_lowering hk hd hn hw) hv
#print axioms generator_lowering
#print axioms kernel_lowering
end Programme.«20261104-1627-proof-complexity».SyzygyLowering
