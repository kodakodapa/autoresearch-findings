import Programme.«20261101-0614-proof-complexity».GlobalRestriction
import Programme.«20261101-0614-proof-complexity».OnehotTruncate
namespace Programme.«20261101-0614-proof-complexity».Composition
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».RestrictionTarget
private theorem f_mem (M N L a : Nat) (ha : a < M) (c : Clause)
    (hc : c ∈ onehot N (fVar a)) : c ∈ cnf M N L := by
  simp only [cnf, List.mem_eraseDups, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (List.mem_flatMap.mpr ⟨a,List.mem_range.mpr ha,hc⟩)))
private theorem s_mem (M N L y x : Nat) (hy : y < N) (hx : x < L) (c : Clause)
    (hc : c ∈ onehot L (sVar y x)) : c ∈ cnf M N L := by
  simp only [cnf, List.mem_eraseDups, List.mem_append]
  exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨y,List.mem_range.mpr hy,
    List.mem_flatMap.mpr ⟨x,List.mem_range.mpr hx,hc⟩⟩)))
private theorem g_mem (M N L y x : Nat) (hy : y < N) (hx : x < L) (c : Clause)
    (hc : c ∈ onehot M (gVar y x)) : c ∈ cnf M N L := by
  simp only [cnf, List.mem_eraseDups, List.mem_append]
  exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨y,List.mem_range.mpr hy,
    List.mem_flatMap.mpr ⟨x,List.mem_range.mpr hx,hc⟩⟩))

theorem global_structural (M N L : Nat) (hM : 1 ≤ M) (hN : 2 ≤ N) (hL : 1 ≤ L) :
    ∀ c ∈ structural (M+1) (N+1) L, ∀ t,
      clause (globalSub M N) c = some t → t ∈ cnf M N L := by
  intro c hc t ht
  have hs := global_spec M N
  have hex := global_extra M N
  simp only [structural, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · rcases List.mem_flatMap.mp hc with ⟨a,ha,hc⟩
    have ha' := List.mem_range.mp ha
    by_cases he : a = M
    · subst a
      have hh := onehot_selected (globalSub M N) (fVar M) (N+1) N (by omega)
        (fun i _ => hex.2.1 i) c hc
      rw [hh] at ht; contradiction
    · have halt : a < M := by omega
      exact f_mem M N L a halt t
        (onehot_truncate (globalSub M N) (fVar a) N hN
          (fun i hi => hs.keptF a i halt hi) (hex.1 a halt) c hc t ht)
  · rcases List.mem_flatMap.mp hc with ⟨y,hy,hc⟩
    rcases List.mem_flatMap.mp hc with ⟨x,hx,hc⟩
    have hy' := List.mem_range.mp hy
    by_cases he : y = N
    · subst y
      have hh := onehot_selected (globalSub M N) (sVar N x) L 0 (by omega)
        (fun i _ => hex.2.2 x i) c hc
      rw [hh] at ht; contradiction
    · have hylt : y < N := by omega
      rw [onehot_fixed (globalSub M N) (sVar y x) L
        (fun i _ => hs.keptS y x i hylt) c hc] at ht
      cases ht
      exact s_mem M N L y x hylt (List.mem_range.mp hx) c hc
  · rcases List.mem_flatMap.mp hc with ⟨y,hy,hc⟩
    rcases List.mem_flatMap.mp hc with ⟨x,hx,hc⟩
    have hy' := List.mem_range.mp hy
    by_cases he : y = N
    · subst y
      have hh := onehot_selected (globalSub M N) (gVar N x) (M+1) M (by omega)
        (fun i _ => hs.removedG x i) c hc
      rw [hh] at ht; contradiction
    · have hylt : y < N := by omega
      exact g_mem M N L y x hylt (List.mem_range.mp hx) t
        (onehot_reduce (globalSub M N) (gVar y x) M hM
          (fun i hi => hs.keptG y x i hylt hi) (hs.removedInput y x hylt) c hc t ht)

theorem refutes_restrict (M N L d : Nat) (hM : 1 ≤ M) (hN : 2 ≤ N) (hL : 1 ≤ L) :
    Refutes (cnf (M+1) (N+1) L) d → Refutes (cnf M N L) d :=
  refutes_of_structural (globalSub M N) M N L d (global_spec M N) hM
    (global_structural M N L hM hN hL)
#print axioms global_structural
#print axioms refutes_restrict
end Programme.«20261101-0614-proof-complexity».Composition
