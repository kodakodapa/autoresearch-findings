import Programme.«20261102-1249-proof-complexity».UniformC3.Multiplicity
import Programme.«20261102-1249-proof-complexity».UniformC3.Selection

namespace Programme.«20261102-1249-proof-complexity».UniformC3
open Programme.«20261025-0459-proof-complexity».OntoLucas (bin bin_zero)
open Programme.«20261027-0607-proof-complexity».Lucas (bin_succ)
open Programme.«20261025-1627-proof-complexity».MomGen (nodup_len)

/-- Each subset is enumerated once, in decreasing order. -/
def chooseRows : Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | 0, _+1 => []
  | m+1, r+1 => chooseRows m (r+1) ++ (chooseRows m r).map (m :: ·)

theorem chooseRows_prop : ∀ m r A, A ∈ chooseRows m r →
    A.Nodup ∧ A.length = r ∧ ∀ v ∈ A, v < m := by
  intro m
  induction m with
  | zero =>
    intro r A ha
    cases r with
    | zero => simp [chooseRows] at ha; subst ha; simp
    | succ r => simp [chooseRows] at ha
  | succ m ih =>
    intro r A ha
    cases r with
    | zero => simp [chooseRows] at ha; subst ha; simp
    | succ r =>
      simp only [chooseRows, List.mem_append, List.mem_map] at ha
      rcases ha with ha | ⟨B,hb,rfl⟩
      · obtain ⟨hnd,hl,hb⟩ := ih _ _ ha
        exact ⟨hnd,hl,fun v hv => Nat.lt.step (hb v hv)⟩
      · obtain ⟨hnd,hl,hbound⟩ := ih _ _ hb
        refine ⟨List.nodup_cons.mpr ⟨?_,hnd⟩, by simp [hl], ?_⟩
        · intro hm; have := hbound m hm; omega
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · omega
          · have := hbound v hv; omega

def covers (R A : List Nat) : Prop := ∀ v ∈ R, v ∈ A
instance (R A : List Nat) : Decidable (covers R A) :=
  inferInstanceAs (Decidable (∀ v ∈ R, v ∈ A))

def coverCount (m r : Nat) (R : List Nat) : Nat :=
  ((chooseRows m r).map (fun A => if covers R A then 1 else 0)).sum

theorem coverCount_too_long {m r : Nat} {R : List Nat} (hnd : R.Nodup)
    (h : r < R.length) : coverCount m r R = 0 := by
  unfold coverCount
  apply List.sum_eq_zero_iff_forall_eq_nat.mpr
  intro a ha
  obtain ⟨A,hA,rfl⟩ := List.mem_map.mp ha
  apply if_neg
  intro hc
  have hlen := nodup_len R A hnd hc
  have := (chooseRows_prop m r A hA).2.1
  omega

theorem covers_cons {R A : List Nat} {m : Nat} (hnd : R.Nodup)
    (hA : ∀ x ∈ A, x < m) : covers R (m::A) ↔ covers (R.erase m) A := by
  constructor
  · intro h x hx
    have hx' := hnd.mem_erase_iff.mp hx
    have hc := List.mem_cons.mp (h x hx'.2)
    exact hc.resolve_left hx'.1
  · intro h x hx
    by_cases hm : x = m
    · exact List.mem_cons.mpr (Or.inl hm)
    · exact List.mem_cons_of_mem _ (h x (hnd.mem_erase_iff.mpr ⟨hm,hx⟩))

theorem coverCount_step_mem {m r : Nat} {R : List Nat} (hnd : R.Nodup)
    (hm : m ∈ R) : coverCount (m+1) (r+1) R = coverCount m r (R.erase m) := by
  unfold coverCount
  simp only [chooseRows, List.map_append, List.sum_append, List.map_map]
  have hz : ((chooseRows m (r+1)).map (fun A => if covers R A then 1 else 0)).sum = (0 : Nat) := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro a ha
    obtain ⟨A,hA,rfl⟩ := List.mem_map.mp ha
    apply if_neg
    intro hc
    have := (chooseRows_prop m (r+1) A hA).2.2 m (hc m hm)
    omega
  rw [hz, Nat.zero_add]
  congr 1
  apply List.map_congr_left
  intro A hA
  simp only [Function.comp_def]
  simp only [covers_cons hnd (chooseRows_prop m r A hA).2.2]

theorem coverCount_step_notmem {m r : Nat} {R : List Nat} (hm : m ∉ R) :
    coverCount (m+1) (r+1) R = coverCount m (r+1) R + coverCount m r R := by
  unfold coverCount
  simp only [chooseRows, List.map_append, List.sum_append, List.map_map]
  congr 2
  apply List.map_congr_left
  intro A _
  simp only [Function.comp_def]
  have hiff : covers R (m::A) ↔ covers R A := by
    constructor
    · intro h x hx
      exact (List.mem_cons.mp (h x hx)).resolve_left (fun he => hm (he ▸ hx))
    · intro h x hx; exact List.mem_cons_of_mem _ (h x hx)
  simp only [hiff]

theorem coverCount_zero (m : Nat) (R : List Nat) :
    coverCount m 0 R = if R = [] then 1 else 0 := by
  unfold coverCount
  simp only [chooseRows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  have hiff : covers R [] ↔ R = [] := by
    constructor
    · intro h; exact List.eq_nil_iff_forall_not_mem.mpr (fun x hx => List.not_mem_nil (h x hx))
    · rintro rfl; intro x hx; simp at hx
  simp only [hiff]

/-- Exact number of row subsets containing a specified set of distinct rows. -/
theorem coverCount_eq : ∀ m r R, R.Nodup → (∀ x ∈ R, x < m) →
    coverCount m r R = if R.length ≤ r then bin (m-R.length) (r-R.length) else 0 := by
  intro m
  induction m with
  | zero =>
    intro r R _ hb
    have hr : R = [] := List.eq_nil_iff_forall_not_mem.mpr (fun x hx => by have := hb x hx; omega)
    subst hr
    cases r <;> simp [coverCount, chooseRows, bin, covers]
  | succ m ih =>
    intro r R hnd hb
    cases r with
    | zero =>
      rw [coverCount_zero]
      by_cases hr : R = []
      · simp [hr, bin_zero]
      · have hl : 0 < R.length := List.length_pos_iff.mpr hr
        simp [hr, show ¬R.length ≤ 0 by omega]
    | succ r =>
      by_cases hm : m ∈ R
      · rw [coverCount_step_mem hnd hm]
        have he : (R.erase m).length = R.length-1 := List.length_erase_of_mem hm
        have hl : 0 < R.length := List.length_pos_iff.mpr (by intro hh; simp [hh] at hm)
        have hb' : ∀ x ∈ R.erase m, x < m := by
          intro x hx
          have hx' := hnd.mem_erase_iff.mp hx
          have := hb x hx'.2
          omega
        rw [ih r (R.erase m) (List.Nodup.erase m hnd) hb', he]
        have e1 : (R.length-1 ≤ r) ↔ R.length ≤ r+1 := by omega
        have e2 : m-(R.length-1) = m+1-R.length := by omega
        have e3 : r-(R.length-1) = r+1-R.length := by omega
        simp only [e1,e2,e3]
      · rw [coverCount_step_notmem hm]
        have hb' : ∀ x ∈ R, x < m := by
          intro x hx
          have hlt := hb x hx
          have hne : x ≠ m := fun he => hm (he ▸ hx)
          omega
        have hlen : R.length ≤ m := by
          have h := nodup_len R (List.range m) hnd (fun x hx => List.mem_range.mpr (hb' x hx))
          simpa using h
        rw [ih (r+1) R hnd hb', ih r R hnd hb']
        by_cases hr : R.length ≤ r
        · rw [if_pos hr, if_pos (by omega), if_pos (by omega)]
          have e1 : m+1-R.length = (m-R.length)+1 := by omega
          have e2 : r+1-R.length = (r-R.length)+1 := by omega
          rw [e1,e2,bin_succ]
          omega
        · by_cases hr' : R.length ≤ r+1
          · have he : R.length = r+1 := by omega
            rw [if_neg hr, if_pos hr', if_pos hr', he]
            simp only [Nat.sub_self, bin_zero, Nat.add_zero]
          · rw [if_neg hr, if_neg hr', if_neg hr']

#print axioms coverCount_eq
end Programme.«20261102-1249-proof-complexity».UniformC3
