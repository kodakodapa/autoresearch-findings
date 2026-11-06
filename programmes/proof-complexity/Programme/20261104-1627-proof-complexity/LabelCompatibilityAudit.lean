import Programme.«20261104-1627-proof-complexity».MatchingLabels
namespace Programme.«20261104-1627-proof-complexity».LabelCompatibilityAudit
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261104-1627-proof-complexity».MatchingLabels

theorem not_boolean_mem : ¬ W 3 1 1 2 (boolAx 0) := by
  rintro ⟨v, hv, he⟩
  have hr : ∀ t ∈ v, (relation 1 1 t.2).terms = [(1,[0]),(-1,[])] := by
    intro t ht
    obtain ⟨d, hd, hg⟩ := hv t ht
    have hd' : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hd' with rfl | rfl | rfl
    · simp [labels] at hg
    · simp [labels, matchings, rows, cols, freeRow, freeCol] at hg
      rcases hg with hg | hg <;> rw [← hg] <;> decide
    · simp [labels, matchings, rows, cols, freeRow, freeCol] at hg
      rcases hg with ⟨a, ⟨ha, hb⟩, _⟩ | ⟨a, ⟨ha, hb⟩, _⟩ <;> omega
  have hz : ∀ L : Vector, (∀ t ∈ L, (relation 1 1 t.2).terms = [(1,[0]),(-1,[])]) →
      cf (L.flatMap fun t => (relation 1 1 t.2).terms.map fun a => (t.1*a.1,a.2)) [0,0] = 0 := by
    intro L hL
    induction L with
    | nil => rfl
    | cons t L ih =>
      rw [List.flatMap_cons, cf_append, ih (fun u hu => hL u (by simp [hu])), Int.add_zero,
        hL t (by simp)]
      simp [cf]
  have h := he [0,0]
  change (3 : Int) ∣ coeff (boolAx 0) [0,0] - cf _ [0,0] at h
  rw [hz v hr] at h
  have hc : coeff (boolAx 0) [0,0] = 1 := by decide
  rw [hc, Int.sub_zero] at h
  exact (by decide : ¬ (3 : Int) ∣ 1) h
end Programme.«20261104-1627-proof-complexity».LabelCompatibilityAudit
#print axioms Programme.«20261104-1627-proof-complexity».LabelCompatibilityAudit.not_boolean_mem
