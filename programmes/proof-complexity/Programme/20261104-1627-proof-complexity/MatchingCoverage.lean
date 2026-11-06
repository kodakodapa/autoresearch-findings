import Programme.«20261104-1627-proof-complexity».MatchingLabels
import Programme.«20261104-1627-proof-complexity».BoardCollisions

namespace Programme.«20261104-1627-proof-complexity».MatchingCoverage
open Programme.«20261104-1627-proof-complexity».MatchingLabels

private theorem snocInduction {α : Type} (P : List α → Prop)
    (hn : P []) (hs : ∀ L x, P L → P (L ++ [x])) (L : List α) : P L := by
  have h : ∀ K : List α, P K.reverse := by
    intro K
    induction K with
    | nil => exact hn
    | cons x K ih => simpa only [List.reverse_cons] using hs K.reverse x ih
  simpa using h L.reverse

/-- Every strictly row-ordered noncolliding board list occurs in the enumeration. -/
theorem enumeration_complete {m n : Nat} (M : Matching)
    (hb : ∀ e ∈ M, e.1 < m ∧ e.2 < n)
    (hr : M.Pairwise (fun a b => a.1 < b.1))
    (hc : M.Pairwise (fun a b => a.2 ≠ b.2)) :
    M ∈ matchings m n M.length := by
  induction M using snocInduction with
  | hn => simp [matchings]
  | hs M e ih =>
    have hbM : ∀ a ∈ M, a.1 < m ∧ a.2 < n := by
      intro a ha; exact hb a (List.mem_append_left _ ha)
    have hbe := hb e (by simp)
    have hrM := (List.pairwise_append.mp hr).1
    have hcM := (List.pairwise_append.mp hc).1
    have hrow : ∀ a ∈ M, a.1 < e.1 := by
      intro a ha
      exact (List.pairwise_append.mp hr).2.2 a ha e (by simp)
    have hcol : ∀ a ∈ M, a.2 ≠ e.2 := by
      intro a ha
      exact (List.pairwise_append.mp hc).2.2 a ha e (by simp)
    have hfreeR : freeRow M e.1 = true := by
      simp only [freeRow, List.all_eq_true, bne_iff_ne]
      intro a ha
      exact Nat.ne_of_lt (hrow a ha)
    have hfreeC : freeCol M e.2 = true := by
      simpa only [freeCol, List.all_eq_true, bne_iff_ne] using hcol
    simp only [List.length_append, List.length_singleton, matchings,
      List.mem_flatMap, List.mem_map]
    refine ⟨M, ih hbM hrM hcM, e.1, ?_, e.2, ?_, ?_⟩
    · simp only [List.mem_filter, rows, List.mem_range]
      exact ⟨⟨hbe.1, hfreeR⟩, by simpa only [List.all_eq_true, decide_eq_true_eq] using hrow⟩
    · simp only [cols, List.mem_filter, List.mem_range]
      exact ⟨hbe.2, hfreeC⟩
    · simp

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261104-1627-proof-complexity».MatchingReduction

def decode (n : Nat) (s : List Nat) : Matching := s.map fun x => (x/n,x%n)

theorem safe_decode_mem {n k : Nat} (s : List Nat)
    (hs : Safe (ontoFPHP n k) s)
    (hb : ∀ x ∈ s, x < (n+k)*n)
    (hr : s.Pairwise (fun x y => x/n < y/n)) :
    decode n s ∈ matchings (n+k) n s.length := by
  have hn : ∀ x ∈ s, 0 < n := by
    intro x hx
    have h := hb x hx
    cases n <;> simp_all
  have hboard : ∀ e ∈ decode n s, e.1 < n+k ∧ e.2 < n := by
    intro e he
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
    exact ⟨(Nat.div_lt_iff_lt_mul (hn x hx)).mpr (hb x hx), Nat.mod_lt x (hn x hx)⟩
  have hrows : (decode n s).Pairwise (fun a b => a.1 < b.1) := by
    exact List.pairwise_map.mpr hr
  have hcols : (decode n s).Pairwise (fun a b => a.2 ≠ b.2) := by
    apply List.pairwise_map.mpr
    apply hr.imp_of_mem
    intro x y hx hy hxy
    have hne : x ≠ y := by intro h; subst y; omega
    exact (Programme.«20261104-1627-proof-complexity».BoardCollisions.safe_coordinates hs hx hy (hb x hx) (hb y hy) hne).2
  simpa [decode] using enumeration_complete (decode n s) hboard hrows hcols

end Programme.«20261104-1627-proof-complexity».MatchingCoverage
#print axioms Programme.«20261104-1627-proof-complexity».MatchingCoverage.enumeration_complete

#print axioms Programme.«20261104-1627-proof-complexity».MatchingCoverage.safe_decode_mem
