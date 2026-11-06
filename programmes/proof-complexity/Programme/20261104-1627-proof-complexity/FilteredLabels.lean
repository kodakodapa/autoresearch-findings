import Programme.«20261104-1627-proof-complexity».HomogeneousLabels

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC

def bounded (m n D : Nat) (v : Vector) : Prop :=
  ∀ t ∈ v, ∃ d, d ≤ D ∧ t.2 ∈ labels m n d

theorem relations_append (m n : Nat) (v w : Vector) (u : List Nat) :
    coeff (relations m n (v ++ w)) u =
      coeff (relations m n v) u + coeff (relations m n w) u := by
  simp [relations, coeff, List.flatMap_append, cf_append]

theorem bounded_relation_degree {m n D : Nat} {v : Vector}
    (hv : bounded m n D v) : (relations m n v).deg ≤ D := by
  rw [deg_le_iff]
  intro t ht
  rcases List.mem_flatMap.mp ht with ⟨a, ha, ht⟩
  rcases List.mem_map.mp ht with ⟨b, hb, rfl⟩
  rcases hv a ha with ⟨d, hd, hg⟩
  have hpos : 0 < d := by
    by_cases hz : d = 0
    · simp [hz, labels] at hg
    · omega
  have hl := label_length hg
  change b ∈ (topLabel m n a.2).terms ++ negT [(1, mono n a.2.base)] at hb
  rcases List.mem_append.mp hb with hb | hb
  · unfold topLabel at hb
    split at hb <;>
      rcases List.mem_map.mp hb with ⟨j, _, rfl⟩ <;>
      simp [mono, hl] <;> omega
  · simp only [negT] at hb
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst b
    simp [mono, hl]
    omega

/-- Split a filtered witness into levels below D and its level-D part.
The equality is coefficientwise, so it does not require list reordering. -/
theorem split_bounded {m n D : Nat} (hD : 0 < D) (v : Vector)
    (hv : bounded m n D v) :
    ∃ lo hi : Vector, bounded m n (D-1) lo ∧ valid m n D hi ∧
      ∀ u, coeff (relations m n v) u =
        coeff (relations m n lo) u + coeff (relations m n hi) u := by
  induction v with
  | nil => exact ⟨[], [], by simp [bounded], by simp [valid], by simp [relations, coeff, cf]⟩
  | cons a v ih =>
    have hv' : bounded m n D v := fun t ht => hv t (List.mem_cons_of_mem a ht)
    rcases ih hv' with ⟨lo, hi, hlo, hhi, he⟩
    rcases hv a (by simp) with ⟨d, hd, hg⟩
    by_cases hdD : d = D
    · refine ⟨lo, a::hi, hlo, ?_, ?_⟩
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · simpa [hdD] using hg
        · exact hhi t ht
      · intro u
        have h := relations_append m n [a] v u
        have h' := relations_append m n [a] hi u
        simp only [List.singleton_append] at h h'
        rw [h, he, h']
        omega
    · refine ⟨a::lo, hi, ?_, hhi, ?_⟩
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact ⟨d, by omega, hg⟩
        · exact hlo t ht
      · intro u
        have h := relations_append m n [a] v u
        have h' := relations_append m n [a] lo u
        simp only [List.singleton_append] at h h'
        rw [h, he, h']
        omega

/-- Filtered Lemma 1: a low-degree member has a lower-level witness plus
one homogeneous kernel contribution. This concerns raw label W only. -/
theorem filtered_kernel_split {p m n D : Nat} (hD : 0 < D)
    (P : Poly Nat) (hP : P.deg < D) (hW : W p m n D P) :
    ∃ lo hi : Vector, bounded m n (D-1) lo ∧ Kernel p m n D hi ∧
      ∀ u, (p : Int) ∣ coeff P u -
        (coeff (relations m n lo) u + coeff (relations m n hi) u) := by
  rcases hW with ⟨v, hv, heq⟩
  rcases split_bounded hD v hv with ⟨lo, hi, hlo, hhi, he⟩
  have hsum : ∀ u, (p : Int) ∣ coeff P u -
      (coeff (relations m n lo) u + coeff (relations m n hi) u) := by
    intro u
    rw [← he]
    exact heq u
  refine ⟨lo, hi, hlo, ?_, hsum⟩
  apply extract_top hD hi hhi (P.sub (relations m n lo))
  · have hl := bounded_relation_degree hlo
    have hp : P.deg ≤ D-1 := by omega
    have hh := deg_sub P (relations m n lo) (D-1) hp hl
    omega
  · intro u
    change (p : Int) ∣ cf (P.terms ++ negT (relations m n lo).terms) u - _
    rw [cf_append, cf_negT]
    have hh := hsum u
    change (p : Int) ∣ coeff P u + -coeff (relations m n lo) u -
      coeff (relations m n hi) u
    rwa [show coeff P u + -coeff (relations m n lo) u - coeff (relations m n hi) u =
      coeff P u - (coeff (relations m n lo) u + coeff (relations m n hi) u) by omega]

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.split_bounded
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.bounded_relation_degree

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.filtered_kernel_split
