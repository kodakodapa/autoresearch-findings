import Programme.«20261104-1627-proof-complexity».LabelCompatibilityAudit
import Programme.«20261025-1627-proof-complexity».NoDrop

namespace Programme.«20261104-1627-proof-complexity».OffboardAudit
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261104-1627-proof-complexity».MatchingLabels

def P : Poly Nat := ⟨[(-1,[2]),(1,[2,0])]⟩

theorem canonical_member : NSIn 3 (ontoFPHP 1 0) 2 P.eval := by
  have hax : sumOne (fun j => var 1 0 j) 1 ∈ ontoFPHP 1 0 := by
    simp [ontoFPHP, pigeonAx, List.range_succ]
  have hd : (sumOne (fun j => var 1 0 j) 1).deg ≤ 1 := by decide
  have h := nsIn_xmul 2 (nsIn_ax (p := 3) hax hd) (by decide : 1 ≤ 2)
  have he : ∀ a, P.eval a = xv 2 a * (sumOne (fun j => var 1 0 j) 1).eval a := by
    intro a
    simp [P, Poly.eval, sumOne, linTerms, var, monoEval, xv, Int.mul_add]
  simpa only [← he] using h

theorem not_raw_member : ¬ W 3 1 1 2 P := by
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
      cf (L.flatMap fun t => (relation 1 1 t.2).terms.map fun a => (t.1*a.1,a.2)) [2,0] = 0 := by
    intro L hL
    induction L with
    | nil => rfl
    | cons t L ih =>
      rw [List.flatMap_cons, cf_append, ih (fun u hu => hL u (by simp [hu])), Int.add_zero,
        hL t (by simp)]
      simp [cf]
  have h := he [2,0]
  change (3 : Int) ∣ coeff P [2,0] - cf _ [2,0] at h
  rw [hz v hr] at h
  have hc : coeff P [2,0] = 1 := by decide
  rw [hc, Int.sub_zero] at h
  exact (by decide : ¬ (3 : Int) ∣ 1) h
end Programme.«20261104-1627-proof-complexity».OffboardAudit
#print axioms Programme.«20261104-1627-proof-complexity».OffboardAudit.canonical_member
#print axioms Programme.«20261104-1627-proof-complexity».OffboardAudit.not_raw_member
