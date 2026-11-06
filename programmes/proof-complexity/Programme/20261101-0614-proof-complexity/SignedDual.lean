import Programme.«20261101-0614-proof-complexity».ConeDual

namespace Programme.«20261101-0614-proof-complexity».SignedDual
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».ConeDual

abbrev Sample := Rat × Assignment

def evaluate (samples : List Sample) (f : Assignment → Rat) : Rat :=
  (samples.map fun s => s.1 * f s.2).sum

theorem evaluate_add (samples : List Sample) (f g : Assignment → Rat) :
    evaluate samples (fun a => f a + g a) = evaluate samples f + evaluate samples g := by
  induction samples with
  | nil => simp [evaluate, Rat.zero_add]
  | cons s ss ih =>
    simp only [evaluate, List.map_cons, List.sum_cons] at *
    rw [Rat.mul_add, ih]
    simp only [Rat.add_assoc, Rat.add_left_comm]

theorem evaluate_scale (samples : List Sample) (r : Rat) (f : Assignment → Rat) :
    evaluate samples (fun a => r * f a) = r * evaluate samples f := by
  induction samples with
  | nil => simp [evaluate]
  | cons s ss ih =>
    simp only [evaluate, List.map_cons, List.sum_cons] at *
    rw [ih, Rat.mul_add]
    congr 1
    rw [← Rat.mul_assoc, ← Rat.mul_assoc, Rat.mul_comm s.1 r]

theorem evaluate_zero (samples : List Sample) : evaluate samples (fun _ => 0) = 0 := by
  induction samples with
  | nil => rfl
  | cons s ss ih => simpa only [evaluate, List.map_cons, List.sum_cons, Rat.mul_zero, Rat.zero_add] using ih

def functional (samples : List Sample)
    (hn : evaluate samples (fun _ => 1) = 1) : Functional where
  eval := evaluate samples
  zero := evaluate_zero samples
  add := evaluate_add samples
  scale := evaluate_scale samples
  unit := hn

/-- All samples set unsupported variables false. -/
def Supported (vars : List Var) (samples : List Sample) : Prop :=
  ∀ s ∈ samples, ∀ v, v ∉ vars → s.2 v = false

/-- Keep only literals on the finite variable support. -/
def project (vars : List Var) (m : List Lit) : List Lit :=
  m.filter fun l => l.1 ∈ vars

/-- A positive literal outside the support makes the whole event empty. -/
def killed (vars : List Var) (m : List Lit) : Bool :=
  m.any fun l => !(decide (l.1 ∈ vars)) && l.2

theorem conjunction_project (vars : List Var) (a : Assignment)
    (ha : ∀ v, v ∉ vars → a v = false) (m : List Lit) :
    conjunction m a = if killed vars m then 0 else conjunction (project vars m) a := by
  have aux : m.all (holds a) =
      (!killed vars m && (project vars m).all (holds a)) := by
    induction m with
    | nil => simp [killed, project]
    | cons l ls ih =>
      rcases l with ⟨v,b⟩
      by_cases hv : v ∈ vars
      · simp only [killed, project, List.any_cons, List.filter_cons, hv,
          decide_true, Bool.not_true, Bool.false_and, Bool.false_or,
          ↓reduceIte, List.all_cons] at *
        rw [ih]
        exact Bool.and_left_comm _ _ _
      · have ha' := ha v hv
        cases b <;> simp_all [killed, project, holds, List.all_cons, List.any_cons]
  unfold conjunction
  rw [aux]
  cases killed vars m <;> simp only [Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem evaluate_project (vars : List Var) (samples : List Sample)
    (hs : Supported vars samples) (m : List Lit) :
    evaluate samples (conjunction m) =
      if killed vars m then 0 else evaluate samples (conjunction (project vars m)) := by
  by_cases hk : killed vars m = true
  · simp only [hk, ↓reduceIte]
    unfold evaluate
    have he : samples.map (fun s => s.1 * conjunction m s.2) = samples.map (fun _ => (0 : Rat)) := by
      apply List.map_congr_left
      intro s hmem
      rw [conjunction_project vars s.2 (hs s hmem) m, hk]
      simp
    rw [he]
    have hz (xs : List Sample) : (xs.map (fun _ => (0 : Rat))).sum = 0 := by
      induction xs with
      | nil => rfl
      | cons x xs ih => simpa only [List.map_cons, List.sum_cons, Rat.zero_add] using ih
    exact hz samples
  · have hk' : killed vars m = false := Bool.eq_false_iff.mpr hk
    simp only [hk', Bool.false_eq_true, ↓reduceIte]
    unfold evaluate
    congr 1
    apply List.map_congr_left
    intro s hmem
    rw [conjunction_project vars s.2 (hs s hmem) m, hk']
    rfl

/-- Finite-support obligations suffice, even though the canonical cone permits
multipliers on arbitrary variables. Repeated variables are allowed in the test
obligations, so a simple bounded-word enumerator can discharge them. -/
def certificate (vars : List Var) (samples : List Sample)
    (hs : Supported vars samples)
    (hn : evaluate samples (fun _ => 1) = 1)
    (hF : ∀ c ∈ F, ∀ l ∈ c, l.1 ∈ vars)
    (hp : ∀ m : List Lit, (∀ l ∈ m, l.1 ∈ vars) → m.length ≤ d →
      0 ≤ evaluate samples (conjunction m))
    (he : ∀ c ∈ F, ∀ m : List Lit, (∀ l ∈ m, l.1 ∈ vars) →
      m.length + c.length ≤ d →
      evaluate samples (conjunction (m ++ falsity c)) = 0) : Certificate F d where
  functional := functional samples hn
  positive := by
    intro m _ hd
    change 0 ≤ evaluate samples (conjunction m)
    rw [evaluate_project vars samples hs m]
    split
    · exact Rat.le_refl
    · apply hp
      · intro l hl
        exact of_decide_eq_true (List.mem_filter.mp hl).2
      · exact Nat.le_trans (List.length_filter_le _ _) hd
  equation := by
    intro c hc m hd
    change evaluate samples (conjunction (m ++ falsity c)) = 0
    rw [evaluate_project vars samples hs (m ++ falsity c)]
    split
    · rfl
    · have hproj : project vars (falsity c) = falsity c := by
        apply List.filter_eq_self.mpr
        intro l hl
        obtain ⟨l',hl',rfl⟩ := List.mem_map.mp hl
        exact decide_eq_true (hF c hc l' hl')
      rw [show project vars (m ++ falsity c) = project vars m ++ falsity c by
        simp only [project, List.filter_append] at *
        rw [hproj]]
      apply he c hc
      · intro l hl
        exact of_decide_eq_true (List.mem_filter.mp hl).2
      · have hh := List.length_filter_le (fun l : Lit => decide (l.1 ∈ vars)) m
        change (project vars m).length ≤ m.length at hh
        have := hd.2
        omega

#print axioms certificate
#print axioms functional
#print axioms evaluate_project
end Programme.«20261101-0614-proof-complexity».SignedDual
