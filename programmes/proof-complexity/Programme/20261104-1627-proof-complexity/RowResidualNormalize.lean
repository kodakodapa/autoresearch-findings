import Programme.«20261104-1627-proof-complexity».NormalizedResidual
import Programme.«20261104-1627-proof-complexity».RRCoordinates
import Programme.«20261104-1627-proof-complexity».OrderedExtension

namespace Programme.«20261104-1627-proof-complexity».RowResidualNormalize
open Programme.«20261104-1627-proof-complexity».MatchingLabels Programme.«20261104-1627-proof-complexity».MixedAggregate

def rowCombination (v : Vector) : List (Int × Vector) :=
  [(vectorCoeff v (edgeRowLabel 0 0 1), rr 3 [] 0 1),
   (vectorCoeff v (edgeRowLabel 0 0 2), rr 3 [] 0 2),
   (vectorCoeff v (edgeRowLabel 1 0 2), rr 3 [] 1 2)]

def rowResidual (v : Vector) : Vector := v ++ combine (rowCombination v)

theorem rowResidual_columns (v : Vector) (a b r : Nat) :
    vectorCoeff (rowResidual v) (edgeColLabel a b r) =
      vectorCoeff v (edgeColLabel a b r) := by
  simp [rowResidual, vectorCoeff_append, coeff_combine, rowCombination,
    rr_col_coefficient]

theorem rowResidual_rows (v : Vector)
    (hind : ∀ a < 3, ∀ i < 3, a ≠ i → ∀ b < 3, ∀ c < 3,
      (3 : Int) ∣ vectorCoeff v (edgeRowLabel a b i) -
        vectorCoeff v (edgeRowLabel a c i))
    (hanti : ∀ a < 3, ∀ i < 3, a ≠ i →
      (3 : Int) ∣ vectorCoeff v (edgeRowLabel a 0 i) +
        vectorCoeff v (edgeRowLabel i 0 a)) :
    ∀ a < 3, ∀ b < 3, ∀ i < 3, a ≠ i →
      (3 : Int) ∣ vectorCoeff (rowResidual v) (edgeRowLabel a b i) := by
  intro a ha b hb i hi hai
  have hd := hind a ha i hi hai b hb 0 (by omega)
  have hs := hanti a ha i hi hai
  obtain ⟨d, hd⟩ := hd
  obtain ⟨s, hs⟩ := hs
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases ha' with rfl | rfl | rfl <;>
    rcases hi' with rfl | rfl | rfl <;>
    simp_all [rowResidual, vectorCoeff_append, coeff_combine, rowCombination,
      rr_row_coefficient] <;> omega

theorem normalized_all_coordinates (v : Vector) (hv : Kernel 3 3 3 2 v) :
    (∀ a < 3, ∀ b < 3, ∀ i < 3, a ≠ i →
      (3 : Int) ∣ vectorCoeff (rowResidual (Programme.«20261104-1627-proof-complexity».NormalizedResidual.finalResidual v))
        (edgeRowLabel a b i)) ∧
    (∀ a < 3, ∀ b < 3, ∀ r < 3, b ≠ r →
      (3 : Int) ∣ vectorCoeff (rowResidual (Programme.«20261104-1627-proof-complexity».NormalizedResidual.finalResidual v))
        (edgeColLabel a b r)) := by
  obtain ⟨_, hc, hi, ha⟩ := Programme.«20261104-1627-proof-complexity».NormalizedResidual.finalResidual_properties v hv
  exact ⟨rowResidual_rows _ hi ha, by simpa only [rowResidual_columns] using hc⟩


theorem rowCombination_generators (v : Vector) :
    ∀ t ∈ rowCombination v, t.2 ∈ syzygies 3 3 2 := by
  intro t ht
  simp only [rowCombination, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  all_goals simp only [Prod.snd]
  all_goals decide +kernel

theorem label_two_shape (g : Label) (hg : g ∈ labels 3 3 2) :
    (∃ a < 3, ∃ b < 3, ∃ i < 3, a ≠ i ∧ g = edgeRowLabel a b i) ∨
    (∃ a < 3, ∃ b < 3, ∃ r < 3, b ≠ r ∧ g = edgeColLabel a b r) := by
  simp only [labels, show ¬(2 : Nat) = 0 by omega, ite_false] at hg
  obtain ⟨M, hM, hg⟩ := List.mem_flatMap.mp hg
  have hm : ∃ a < 3, ∃ b < 3, M = [(a,b)] := by
    simp only [matchings, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hM
    obtain ⟨a,ha,hM⟩ := List.mem_flatMap.mp hM
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hM
    exact ⟨a, by simpa [rows, freeRow] using ha, b,
      by simpa [cols, freeCol] using hb, rfl⟩
  obtain ⟨a,ha,b,hb,rfl⟩ := hm
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hg
    have hi' : i < 3 ∧ i ≠ a := by simpa [rows, freeRow, ne_comm] using hi
    exact Or.inl ⟨a,ha,b,hb,i,hi'.1,Ne.symm hi'.2,rfl⟩
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hg
    have hr' : r < 3 ∧ r ≠ b := by simpa [cols, freeCol, ne_comm] using hr
    exact Or.inr ⟨a,ha,b,hb,r,hr'.1,Ne.symm hr'.2,rfl⟩


theorem rowResidual_valid (v : Vector) (hv : valid 3 3 2 v) :
    valid 3 3 2 (rowResidual v) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hv t ht
  · obtain ⟨c,hc,ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    have hh : valid 3 3 2 c.2 := by
      simp only [rowCombination, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals simp only [Prod.snd]
      all_goals exact rr_valid (e := 0) (N := []) (by simp [matchings]) (by decide) (by decide) (by decide)
    exact hh u hu

theorem outside_coeff {m n d : Nat} (v : Vector) (hv : valid m n d v)
    (g : Label) (hg : g ∉ labels m n d) : vectorCoeff v g = 0 := by
  have he : v.filter (fun t => t.2 == g) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    simp only [Bool.not_eq_true, beq_iff_eq]
    exact fun h => hg (h ▸ hv t ht)
  simp [vectorCoeff, he]

theorem normalized_all_labels (v : Vector) (hv : Kernel 3 3 3 2 v) :
    ∀ g, (3 : Int) ∣ vectorCoeff
      (rowResidual (Programme.«20261104-1627-proof-complexity».NormalizedResidual.finalResidual v)) g := by
  obtain ⟨hr,hc⟩ := normalized_all_coordinates v hv
  intro g
  by_cases hg : g ∈ labels 3 3 2
  · rcases label_two_shape g hg with hr' | hc'
    · obtain ⟨a,ha,b,hb,i,hi,hai,rfl⟩ := hr'
      exact hr a ha b hb i hi hai
    · obtain ⟨a,ha,b,hb,r,hr',hbr,rfl⟩ := hc'
      exact hc a ha b hb r hr' hbr
  · rw [outside_coeff _ (rowResidual_valid _
      (Programme.«20261104-1627-proof-complexity».NormalizedResidual.finalResidual_properties v hv).1.1) g hg]
    exact ⟨0, by omega⟩

end Programme.«20261104-1627-proof-complexity».RowResidualNormalize
#print axioms Programme.«20261104-1627-proof-complexity».RowResidualNormalize.normalized_all_coordinates
