import Programme.«20261101-0614-proof-complexity».CompositionReproof
import Programme.«20261101-0614-proof-complexity».OnehotReproof
import Programme.«20261101-0614-proof-complexity».OnehotReduceReproof
import Programme.«20261101-0614-proof-complexity».PairCode

namespace Programme.«20261101-0614-proof-complexity».RestrictReproof
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».RestrictionTarget
open Programme.«20261101-0614-proof-complexity».Composition

noncomputable def dec (q : Nat) : Nat × Nat := by
  classical
  exact if h : ∃ ab : Nat × Nat, pair ab.1 ab.2 = q then Classical.choose h else (0,0)

theorem dec_pair (a b : Nat) : dec (pair a b) = (a,b) := by
  classical
  have h : ∃ ab : Nat × Nat, pair ab.1 ab.2 = pair a b := ⟨(a,b),rfl⟩
  simp only [dec, dif_pos h]
  have he := pair_injective (Classical.choose_spec h)
  exact Prod.ext he.1 he.2

-- Own substitution: row M of F selects column N; row N of S selects 0;
-- row N of G selects M; input M of G is false; singleton G rows are true.
noncomputable def sig (M N : Nat) : Substitution := fun v =>
  if v.1 = 0 then
    (if (dec v.2).1 = M then .inl ((dec v.2).2 == N)
     else if (dec v.2).2 = N then .inl false else .inr v)
  else if v.1 = 1 then
    (if (dec v.2).1 = N then .inl ((dec (dec v.2).2).2 == 0) else .inr v)
  else if v.1 = 2 then
    (if (dec v.2).1 = N then .inl ((dec (dec v.2).2).2 == M)
     else if (dec (dec v.2).2).2 = M then .inl false
     else if M = 1 then .inl true else .inr v)
  else .inr v

theorem sig_spec (M N : Nat) : RestrictionSpec (sig M N) M N where
  keptF := by
    intro a y ha hy
    simp [sig, fVar, dec_pair, show a ≠ M by omega, show y ≠ N by omega]
  keptS := by
    intro y x z hy
    simp [sig, sVar, dec_pair, show y ≠ N by omega]
  keptG := by
    intro y x a hy ha
    simp [sig, gVar, dec_pair, show y ≠ N by omega, show a ≠ M by omega]
  removedInput := by
    intro y x hy
    simp [sig, gVar, dec_pair, show y ≠ N by omega]
  removedG := by
    intro x a
    simp [sig, gVar, dec_pair]
  removedF := by
    simp [sig, fVar, dec_pair]

theorem struct_lemma (M N L : Nat) (hM : 1 ≤ M) (hN : 2 ≤ N) (hL : 1 ≤ L) :
    ∀ c ∈ structural (M+1) (N+1) L,
      ∀ t, clause (sig M N) c = some t → t ∈ cnf M N L := by
  intro c hc t ht
  have hs := sig_spec M N
  simp only [structural, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · rcases List.mem_flatMap.mp hc with ⟨a,ha,hc⟩
    have ha' := List.mem_range.mp ha
    by_cases he : a = M
    · subst a
      have hh := Programme.«20261101-0614-proof-complexity».OnehotReproof.selected (sig M N) (fVar M) (N+1) N (by omega)
        (fun i _ => by simp [sig, fVar, dec_pair]) c hc
      rw [hh] at ht; contradiction
    · have halt : a < M := by omega
      have := Programme.«20261101-0614-proof-complexity».OnehotReduceReproof.reduce (sig M N) (fVar a) N (by omega)
        (fun i hi => by rw [hs.keptF a i halt hi]; simp [show N ≠ 1 by omega])
        (by simp [sig, fVar, dec_pair, he]) c hc t ht
      simp only [Programme.«20261101-0614-proof-complexity».Composition.cnf, List.mem_eraseDups, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (List.mem_flatMap.mpr ⟨a,List.mem_range.mpr halt,this⟩)))
  · rcases List.mem_flatMap.mp hc with ⟨y,hy,hc⟩
    rcases List.mem_flatMap.mp hc with ⟨x,hx,hc⟩
    have hy' := List.mem_range.mp hy
    by_cases he : y = N
    · subst y
      have hh := Programme.«20261101-0614-proof-complexity».OnehotReproof.selected (sig M N) (sVar N x) L 0 (by omega)
        (fun i _ => by simp [sig, sVar, dec_pair]) c hc
      rw [hh] at ht; contradiction
    · have hylt : y < N := by omega
      rw [Programme.«20261101-0614-proof-complexity».OnehotReproof.fixed (sig M N) (sVar y x) L
        (fun i _ => hs.keptS y x i hylt) c hc] at ht
      cases ht
      simp only [Programme.«20261101-0614-proof-complexity».Composition.cnf, List.mem_eraseDups, List.mem_append]
      exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨y,List.mem_range.mpr hylt,
        List.mem_flatMap.mpr ⟨x,hx,hc⟩⟩)))
  · rcases List.mem_flatMap.mp hc with ⟨y,hy,hc⟩
    rcases List.mem_flatMap.mp hc with ⟨x,hx,hc⟩
    have hy' := List.mem_range.mp hy
    by_cases he : y = N
    · subst y
      have hh := Programme.«20261101-0614-proof-complexity».OnehotReproof.selected (sig M N) (gVar N x) (M+1) M (by omega)
        (fun i _ => hs.removedG x i) c hc
      rw [hh] at ht; contradiction
    · have hylt : y < N := by omega
      have := Programme.«20261101-0614-proof-complexity».OnehotReduceReproof.reduce (sig M N) (gVar y x) M hM
        (fun i hi => hs.keptG y x i hylt hi) (hs.removedInput y x hylt) c hc t ht
      simp only [Programme.«20261101-0614-proof-complexity».Composition.cnf, List.mem_eraseDups, List.mem_append]
      exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨y,List.mem_range.mpr hylt,
        List.mem_flatMap.mpr ⟨x,hx,this⟩⟩))

theorem refutes_restrict (M N L d : Nat) (hM : 1 ≤ M) (hN : 2 ≤ N) (hL : 1 ≤ L) :
    Refutes (cnf (M+1) (N+1) L) d → Refutes (cnf M N L) d :=
  Programme.«20261101-0614-proof-complexity».CompositionReproof.transport (sig M N) M N L d (sig_spec M N) hM
    (struct_lemma M N L hM hN hL)

#print axioms refutes_restrict
end Programme.«20261101-0614-proof-complexity».RestrictReproof
