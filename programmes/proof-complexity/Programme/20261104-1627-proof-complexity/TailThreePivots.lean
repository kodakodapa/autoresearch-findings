import Programme.«20261104-1627-proof-complexity».TailWeighted
import Programme.«20261104-1627-proof-complexity».MatchingDeletion

namespace Programme.«20261104-1627-proof-complexity».TailThreePivots
open Programme.«20261104-1627-proof-complexity».MatchingLabels Programme.«20261104-1627-proof-complexity».TailPivot Programme.«20261104-1627-proof-complexity».TailWeighted Programme.«20261104-1627-proof-complexity».TailCoordinates

theorem pivot_singleton (n b c : Nat) :
    pivotRows 2 n [(0,b)] c = [(1, ⟨[(0,b),(1,c)], true, 2⟩)] := by
  simp [pivotRows, rows, freeRow, List.range_succ, ordered, List.mergeSort]

theorem label_shape {n : Nat} {g : Label}
    (hg : g ∈ labels 3 n 3) (h2 : pigeonBlock 2 g = 2) :
    ∃ b c, b < n ∧ c < n ∧ b ≠ c ∧ g = ⟨[(0,b),(1,c)],true,2⟩ := by
  have ht := (block_two_iff 2 g).mp h2
  simp only [labels, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub, List.mem_flatMap, List.mem_append, List.mem_map] at hg
  obtain ⟨M,hM,hg⟩ := hg
  have he : g.base = M := by
    rcases hg with ⟨i,_,h⟩ | ⟨i,_,h⟩ <;> cases h <;> rfl
  have hl := matching_length hM
  rw [← he] at hl hM
  have hb := (matching_board_properties hM).1
  have hr := matching_rows_strict hM
  have hc := (matching_board_properties hM).2.2
  cases hbase : g.base with
  | nil => simp [hbase] at hl
  | cons a L =>
    cases L with
    | nil => simp [hbase] at hl
    | cons z L =>
      have hL : L = [] := by simpa [hbase] using hl
      subst L
      have ha := hb a (by simp [hbase])
      have hz := hb z (by simp [hbase])
      have hlt : a.1 < z.1 := by simpa [hbase] using hr
      have hne : a.2 ≠ z.2 := by simpa [hbase] using hc
      have hav : a.1 ≠ 2 ∧ z.1 ≠ 2 := by
        simpa [usesPigeon, hbase, List.any_cons, Bool.or_eq_false_iff] using ht.1
      have ha0 : a.1 = 0 := by omega
      have hz1 : z.1 = 1 := by omega
      refine ⟨a.2,z.2,ha.2,hz.2,hne,?_⟩
      cases g
      simp_all
      exact ⟨Prod.ext ha0 rfl, Prod.ext hz1 rfl⟩

theorem singleton_data {n b c : Nat} (hb : b < n) (hc : c < n) (hne : b ≠ c) :
    [(0,b)] ∈ matchings 3 n 1 ∧ 2 ∈ rows 3 [(0,b)] ∧ c ∈ cols n [(0,b)] := by
  constructor
  · have hh := matching_of_properties (m := 3) (n := n) [(0,b)] (by simpa using And.intro (by decide : 0 < 3) hb) (by simp) (by simp)
    simpa using hh
  · simp [rows, cols, freeRow, freeCol, List.mem_filter, List.mem_range, hc, hne]

/-- Every valid degree-three last-row coordinate on three pigeons has a singleton rc pivot. -/
theorem weights_exist {n : Nat} (w : Vector)
    (hw : ∀ t ∈ w, t.2 ∈ labels 3 n 3 ∧ pigeonBlock 2 t.2 = 2) :
    ∃ L : Data,
      (∀ t ∈ L, t.2.1 ∈ matchings 3 n 1 ∧
        2 ∈ rows 3 t.2.1 ∧ t.2.2 ∈ cols n t.2.1) ∧
      (∀ t ∈ L, t.2.1.any (fun e => e.1 == 2) = false) ∧
      combine (rowCorrections 2 n L) = w := by
  induction w with
  | nil => exact ⟨[], by simp, by simp, rfl⟩
  | cons t w ih =>
    obtain ⟨b,c,hb,hc,hne,hg⟩ := label_shape (hw t (by simp)).1 (hw t (by simp)).2
    obtain ⟨L,hL,ha,he⟩ := ih (fun s hs => hw s (by simp [hs]))
    refine ⟨(t.1,[(0,b)],c)::L, ?_, ?_, ?_⟩
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact singleton_data hb hc hne
      · exact hL s hs
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · rfl
      · exact ha s hs
    · simp only [rowCorrections, List.map_cons, combine, List.flatMap_cons]
      rw [pivot_singleton]
      change ([(t.1 * 1, ⟨[(0,b),(1,c)],true,2⟩)] ++ combine (rowCorrections 2 n L)) = t::w
      rw [he]
      simp only [Int.mul_one, List.singleton_append, List.cons.injEq, and_true]
      exact Prod.ext rfl hg.symm

/-- Unconditional weights for the actual block-two part of any valid vector. -/
theorem block_two_weights {n : Nat} {v : Vector} (hv : valid 3 n 3 v) :
    ∃ L : Data,
      (∀ t ∈ L, t.2.1 ∈ matchings 3 n 1 ∧
        2 ∈ rows 3 t.2.1 ∧ t.2.2 ∈ cols n t.2.1) ∧
      (∀ t ∈ L, t.2.1.any (fun e => e.1 == 2) = false) ∧
      combine (rowCorrections 2 n L) = splitPigeon 2 2 v := by
  apply weights_exist
  intro t ht
  have hh := List.mem_filter.mp ht
  exact ⟨hv t hh.1, by simpa using hh.2⟩

/-- The base-board pivot equation is solved without any additional span hypothesis. -/
theorem eliminate_block_two {p n : Nat} {v : Vector}
    (hv : Kernel p 3 n 3 v)
    (hs : ∀ t ∈ v, pigeonBlock 2 t.2 ≠ 1) :
    ∃ L : Data,
      (∀ t ∈ corrections 2 n L, t.2 ∈ syzygies 3 n 3) ∧
      Kernel p 3 n 3 (residual 2 n v L) ∧
      (∀ g, (p : Int) ∣ vectorCoeff (splitPigeon 2 2 (residual 2 n v L)) g) ∧
      Kernel p 3 n 3 (splitPigeon 2 3 (residual 2 n v L)) := by
  obtain ⟨L,hL,ha,he⟩ := block_two_weights hv.1
  have hp : ∀ g, (p : Int) ∣ vectorCoeff (splitPigeon 2 2 v) g -
      vectorCoeff (combine (rowCorrections 2 n L)) g := by
    intro g
    rw [he, Int.sub_self]
    exact ⟨0, by simp⟩
  exact ⟨L, corrections_enumerated hL, residual_kernel hv hL,
    residual_pivot_zero ha hp, incident_remainder_kernel hv hs hL ha hp⟩

end Programme.«20261104-1627-proof-complexity».TailThreePivots
#print axioms Programme.«20261104-1627-proof-complexity».TailThreePivots.block_two_weights

#print axioms Programme.«20261104-1627-proof-complexity».TailThreePivots.eliminate_block_two
