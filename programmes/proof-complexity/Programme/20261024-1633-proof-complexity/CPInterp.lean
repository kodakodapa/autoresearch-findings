import Programme.«20261024-1633-proof-complexity».CP

/-!
# Feasible interpolation for tree-like cutting planes (Pudlák 1997)

Split the variables of `A ++ B` into `Q` (only in `A`), `R` (only in `B`) and the shared rest `P`,
and suppose the shared variables occur only negatively in `A`. From a tree-like cutting-planes
refutation of `A ++ B` with `s` nodes over the variable list `X` we build a *monotone real formula*
`f` with at most `s (2|X| + 1)` gates, reading only shared variables, such that for every assignment
`β`: if `f β ≥ 1` then `β` falsifies a clause of `A`, and if `f β ≤ 0` then `β` falsifies a clause
of `B`. Every gate is an arbitrary monotone function `ℤ → ℤ` or `ℤ × ℤ → ℤ`, so `f` is
non-decreasing in `β` and depends only on the shared variables (`RC.mono`, `RC.local`).

Pudlák's proof: each line `∑ a_v x_v ≥ b` is split into a `Q`-part and an `R ∪ P`-part. The formula
computes a threshold `f β` with `Q`-part `≥ f β` whenever `β` satisfies `A`, and
`R`-part `+ P`-part `≥ b - f β` whenever `β` satisfies `B`. Division rounds `f` up, `⌈f / c⌉`.
-/

namespace Programme.«20261024-1633-proof-complexity».CPInterp

open Programme.«20261024-1110-proof-complexity».Haken (Lit Clause CNF Lit.eval Clause.eval)
open Programme.«20261024-1633-proof-complexity».CP

/-- Monotone real formulas over the variables satisfying `P`, with their number of gates. -/
inductive RC {V} (P : V → Bool) : ((V → Bool) → Int) → Nat → Prop
  | const (k : Int) : RC P (fun _ => k) 1
  | inp (u : V) : P u = true → RC P (fun β => val β u) 1
  | gate1 {f : (V → Bool) → Int} {s : Nat} (g : Int → Int) : (∀ x y, x ≤ y → g x ≤ g y) →
      RC P f s → RC P (fun β => g (f β)) (s + 1)
  | gate2 {f h : (V → Bool) → Int} {s t : Nat} (g : Int → Int → Int) :
      (∀ x x' y y', x ≤ x' → y ≤ y' → g x y ≤ g x' y') →
      RC P f s → RC P h t → RC P (fun β => g (f β) (h β)) (s + t + 1)

theorem val_mono {V} {α β : V → Bool} (h : ∀ v, α v = true → β v = true) (u : V) :
    val α u ≤ val β u := by
  unfold val; cases e : α u
  · cases β u <;> simp
  · simp [h u e]

/-- A monotone real formula computes a non-decreasing function. -/
theorem RC.mono {V} {P : V → Bool} {f : (V → Bool) → Int} {s : Nat} (c : RC P f s)
    {α β : V → Bool} (h : ∀ v, α v = true → β v = true) : f α ≤ f β := by
  induction c with
  | const k => exact Int.le_refl _
  | inp u _ => exact val_mono h u
  | gate1 g hg _ ih => exact hg _ _ ih
  | gate2 g hg _ _ ih1 ih2 => exact hg _ _ _ _ ih1 ih2

/-- A monotone real formula reads only the variables in `P`. -/
theorem RC.local {V} {P : V → Bool} {f : (V → Bool) → Int} {s : Nat} (c : RC P f s)
    {α β : V → Bool} (h : ∀ v, P v = true → α v = β v) : f α = f β := by
  induction c with
  | const k => rfl
  | inp u hu => simp [val, h u hu]
  | gate1 g _ _ ih => simp only [ih]
  | gate2 g _ _ _ ih1 ih2 => simp only [ih1, ih2]

theorem RC.congr {V} {P : V → Bool} {f g : (V → Bool) → Int} {s : Nat} (c : RC P f s)
    (h : ∀ β, f β = g β) : RC P g s := by
  have : f = g := funext h
  subst this; exact c

/-- `b + ∑_{v ∈ X, P v} c_v x_v` with `c_v ≥ 0` is a monotone formula with `≤ 2|X| + 1` gates. -/
theorem build {V} (P : V → Bool) (c : V → Int) (hc : ∀ v, P v = true → 0 ≤ c v) (b : Int) :
    ∀ X : List V, ∃ s, s ≤ 2 * X.length + 1 ∧
      RC P (fun β => b + (X.map fun v => if P v then c v * val β v else 0).sum) s
  | [] => ⟨1, by simp, (RC.const (P := P) b).congr (by intro β; simp)⟩
  | x :: X => by
    obtain ⟨s, hs, r⟩ := build P c hc b X
    cases hx : P x
    · refine ⟨s, by simp; omega, r.congr ?_⟩
      intro β; simp [hx]
    · refine ⟨s + 1 + 1, by simp; omega, ?_⟩
      have := RC.gate2 (fun y z => y + c x * z) ?_ r (RC.inp x hx)
      · refine this.congr ?_
        intro β; simp only [hx, List.map_cons, List.sum_cons, ite_true]; omega
      · intro y y' z z' hy hz
        have := Int.mul_le_mul_of_nonneg_left hz (hc x hx)
        omega

/-! ## Parts of a line -/

def part {V} (S : V → Bool) (X : List V) (L : Line V) (β : V → Bool) : Int :=
  (X.map fun v => if S v then L.a v * val β v else 0).sum

/-- The shared variables. -/
def shared {V} (Q R : V → Bool) (v : V) : Bool := !Q v && !R v

theorem lhs_parts {V} (Q R : V → Bool) (hQR : ∀ v, Q v = true → R v = false) (X : List V)
    (L : Line V) (β : V → Bool) :
    L.lhs X β = part Q X L β + part R X L β + part (shared Q R) X L β := by
  unfold Line.lhs part
  induction X with
  | nil => simp
  | cons x X ih =>
    have key : L.a x * val β x = (if Q x then L.a x * val β x else 0) +
        (if R x then L.a x * val β x else 0) + (if shared Q R x then L.a x * val β x else 0) := by
      unfold shared
      cases hq : Q x
      · cases R x <;> simp
      · simp [hQR x hq]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem part_add {V} (S : V → Bool) (X : List V) (L M : Line V) (β : V → Bool) :
    part S X (L.add M) β = part S X L β + part S X M β := by
  unfold part Line.add
  rw [← sum_add]; congr 1; apply List.map_congr_left; intro v _
  split
  · simp only; rw [Int.add_mul]
  · simp

theorem part_smul {V} (S : V → Bool) (X : List V) (c : Nat) (L : Line V) (β : V → Bool) :
    part S X (L.smul c) β = c * part S X L β := by
  unfold part Line.smul
  rw [← sum_mul]; congr 1; apply List.map_congr_left; intro v _
  split
  · simp only; rw [Int.mul_assoc]
  · simp

theorem part_div {V} (S : V → Bool) (X : List V) (c : Nat) (L : Line V) (a' : V → Int) (b' : Int)
    (ha : ∀ v, L.a v = (c : Int) * a' v) (β : V → Bool) :
    part S X L β = c * part S X ⟨a', b'⟩ β := by
  unfold part
  rw [← sum_mul]; congr 1; apply List.map_congr_left; intro v _
  split
  · simp only; rw [ha v, Int.mul_assoc]
  · simp

theorem part_vanish {V} (S : V → Bool) (X : List V) (L : Line V) (β : V → Bool)
    (h : ∀ v, S v = true → L.a v = 0) : part S X L β = 0 := by
  unfold part
  induction X with
  | nil => rfl
  | cons x X ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    cases e : S x
    · simp
    · simp [h x e]

theorem part_single {V} [DecidableEq V] (S : V → Bool) (X : List V) (hX : X.Nodup) (u : V)
    (r b : Int) (β : V → Bool) :
    part S X ⟨fun v => if u = v then r else 0, b⟩ β =
      if u ∈ X then (if S u then r * val β u else 0) else 0 := by
  unfold part
  rw [← sum_single X hX u]
  congr 1; apply List.map_congr_left; intro v _
  by_cases e : u = v
  · subst e; simp
  · simp [e]

theorem val_01 {V} (β : V → Bool) (u : V) : val β u = 0 ∨ val β u = 1 := by
  unfold val; split <;> simp

/-! ## Clause lines -/

theorem clause_coef_zero {V} [DecidableEq V] (C : Clause V) (v : V) (h : ∀ l ∈ C, l.var ≠ v) :
    (clauseLine C).a v = 0 := by
  simp only [clauseLine]
  induction C with
  | nil => rfl
  | cons l C ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))]
    simp [litCoef, h l (List.mem_cons_self ..)]

theorem clause_coef_nonpos {V} [DecidableEq V] (C : Clause V) (v : V)
    (h : ∀ l ∈ C, l.var = v → l.pos = false) : (clauseLine C).a v ≤ 0 := by
  simp only [clauseLine]
  induction C with
  | nil => simp
  | cons l C ih =>
    simp only [List.map_cons, List.sum_cons]
    have ih := ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    have : litCoef l v ≤ 0 := by
      unfold litCoef
      by_cases e : l.var = v
      · simp [e, h l (List.mem_cons_self ..) e]
      · simp [e]
    omega

theorem clause_sound {V} [DecidableEq V] (X : List V) (hX : X.Nodup) (C : Clause V)
    (hC : ∀ l ∈ C, l.var ∈ X) (β : V → Bool) (h : C.eval β = true) :
    (clauseLine C).holds X β :=
  D_sound (F := [C]) X hX (fun C' hC' => by simp at hC'; subst hC'; exact hC) β
    (fun C' hC' => by simp at hC'; subst hC'; exact h) (D.ax C (List.mem_singleton_self C))

/-! ## The interpolation invariant -/

/-- Ceiling division by a positive integer, `⌈x / c⌉`. -/
def cdiv (c : Nat) (x : Int) : Int := (x + c - 1) / (c : Int)

theorem cdiv_spec (c : Nat) (hc : 0 < c) (x : Int) :
    x ≤ c * cdiv c x ∧ c * cdiv c x < x + c := by
  unfold cdiv
  have hc' : (0 : Int) < c := by omega
  have e := Int.mul_ediv_add_emod (x + c - 1) (c : Int)
  have h1 := Int.emod_nonneg (x + c - 1) (Int.ne_of_gt hc')
  have h2 := Int.emod_lt_of_pos (x + c - 1) hc'
  omega

theorem lt_of_cmul {c : Nat} {x y : Int} (h : (c : Int) * x < c * y) : x < y :=
  Int.lt_of_mul_lt_mul_left h (Int.natCast_nonneg c)

section
variable {V : Type} [DecidableEq V] (A B : CNF V) (Q R : V → Bool) (X : List V)

def satF (F : CNF V) (β : V → Bool) : Prop := ∀ C ∈ F, C.eval β = true

/-- The invariant: `Q`-part `≥ f` under `A`, and `R`-part `+ P`-part `≥ b - f` under `B`. -/
def Inv (L : Line V) (f : (V → Bool) → Int) : Prop :=
  (∀ β, satF A β → f β ≤ part Q X L β) ∧
  (∀ β, satF B β → L.b - f β ≤ part R X L β + part (shared Q R) X L β)

theorem sum_filter {α} (X : List α) (p : α → Bool) (g : α → Int) (h : ∀ v, p v = false → g v = 0) :
    ((X.filter p).map g).sum = (X.map g).sum := by
  induction X with
  | nil => rfl
  | cons x X ih =>
    cases hx : p x
    · simp [hx, ih, h x hx]
    · simp [hx, ih]

theorem interp_node (w : Nat)
    (hw : ∀ C ∈ A, (X.filter fun v => decide (v ∈ C.map Lit.var)).length ≤ w) (hX : X.Nodup) (cover : ∀ C ∈ A ++ B, ∀ l ∈ C, l.var ∈ X)
    (hQR : ∀ v, Q v = true → R v = false)
    (hA : ∀ C ∈ A, ∀ l ∈ C, R l.var = false) (hB : ∀ C ∈ B, ∀ l ∈ C, Q l.var = false)
    (hneg : ∀ C ∈ A, ∀ l ∈ C, Q l.var = false → l.pos = false)
    {L : Line V} {s : Nat} (d : D (A ++ B) L s) :
    ∃ f t, RC (shared Q R) f t ∧ t ≤ s * (2 * w + 1) ∧ Inv A B Q R X L f := by
  induction d with
  | ax C hC =>
    have cov := cover C hC
    by_cases hCA : C ∈ A
    · -- `f β = b - P`-part, a monotone formula since `P`-coefficients are `≤ 0`.
      have hR0 : ∀ v, R v = true → (clauseLine C).a v = 0 := by
        intro v hv; apply clause_coef_zero; intro l hl e; subst e; simp [hA C hCA l hl] at hv
      obtain ⟨t, ht, r⟩ := build (shared Q R) (fun v => -(clauseLine C).a v) (by
          intro v hv
          have : (clauseLine C).a v ≤ 0 := by
            apply clause_coef_nonpos; intro l hl e; subst e
            apply hneg C hCA l hl; simp [shared] at hv; exact hv.1
          omega) (clauseLine C).b (X.filter fun v => decide (v ∈ C.map Lit.var))
      have hwC := hw C hCA
      have r := r.congr (g := fun β => (clauseLine C).b +
          (X.map fun v => if shared Q R v then -(clauseLine C).a v * val β v else 0).sum) (by
        intro β; congr 1; apply sum_filter; intro v hv
        have : (clauseLine C).a v = 0 := by
          apply clause_coef_zero; intro l hl e; subst e
          simp only [decide_eq_false_iff_not, List.mem_map, not_exists, not_and] at hv
          exact hv l hl rfl
        simp [this])
      refine ⟨_, t, r, by omega, ?_, ?_⟩
      · intro β hβ
        have hs := clause_sound X hX C cov β (hβ C hCA)
        unfold Line.holds at hs
        rw [lhs_parts Q R hQR, part_vanish R X _ β hR0] at hs
        have : (X.map fun v => if shared Q R v then -(clauseLine C).a v * val β v else 0).sum =
            -part (shared Q R) X (clauseLine C) β := by
          unfold part; rw [← Int.neg_one_mul, ← sum_mul]; congr 1
          apply List.map_congr_left; intro v _; split <;> simp [Int.neg_mul]
        simp only [this]; omega
      · intro β _
        have : (X.map fun v => if shared Q R v then -(clauseLine C).a v * val β v else 0).sum =
            -part (shared Q R) X (clauseLine C) β := by
          unfold part; rw [← Int.neg_one_mul, ← sum_mul]; congr 1
          apply List.map_congr_left; intro v _; split <;> simp [Int.neg_mul]
        simp only [this, part_vanish R X _ β hR0]; omega
    · have hCB : C ∈ B := by
        rcases List.mem_append.mp hC with h | h
        · exact absurd h hCA
        · exact h
      have hQ0 : ∀ v, Q v = true → (clauseLine C).a v = 0 := by
        intro v hv; apply clause_coef_zero; intro l hl e; subst e; simp [hB C hCB l hl] at hv
      refine ⟨fun _ => 0, 1, RC.const 0, by omega, ?_, ?_⟩
      · intro β _; simp [part_vanish Q X _ β hQ0]
      · intro β hβ
        have hs := clause_sound X hX C cov β (hβ C hCB)
        unfold Line.holds at hs
        rw [lhs_parts Q R hQR, part_vanish Q X _ β hQ0] at hs
        show _ - (0 : Int) ≤ _
        omega
  | lo u =>
    refine ⟨fun _ => 0, 1, RC.const 0, by omega, ?_, ?_⟩
    · intro β _
      simp only [part_single _ X hX]
      have := val_01 β u
      split <;> (try split) <;> omega
    · intro β _
      simp only [part_single _ X hX, shared]
      have := val_01 β u
      split <;> (try split) <;> (try split) <;> omega
  | hi u =>
    refine ⟨fun _ => if Q u then -1 else 0, 1, RC.const _, by omega, ?_, ?_⟩
    · intro β _
      simp only [part_single _ X hX]
      have := val_01 β u
      split <;> (try split) <;> omega
    · intro β _
      simp only [part_single _ X hX, shared]
      have := val_01 β u
      by_cases hq : Q u = true
      · simp only [hq, hQR u hq]; simp
      · have hq' : Q u = false := by simpa using hq
        simp only [hq']
        cases hr : R u <;> simp <;> split <;> omega
  | add _ _ ih1 ih2 =>
    obtain ⟨f1, t1, r1, ht1, i1, j1⟩ := ih1
    obtain ⟨f2, t2, r2, ht2, i2, j2⟩ := ih2
    refine ⟨fun β => f1 β + f2 β, t1 + t2 + 1,
      RC.gate2 (fun x y => x + y) (by intro x x' y y' _ _; omega) r1 r2, ?_, ?_, ?_⟩
    · rw [Nat.add_mul, Nat.add_mul]; omega
    · intro β hβ; have := i1 β hβ; have := i2 β hβ
      simp only [part_add]; omega
    · intro β hβ; have := j1 β hβ; have := j2 β hβ
      rw [part_add, part_add]; simp only [Line.add]; omega
  | smul c _ ih =>
    obtain ⟨f1, t1, r1, ht1, i1, j1⟩ := ih
    refine ⟨fun β => c * f1 β, t1 + 1,
      RC.gate1 (fun x => c * x) (fun x y h => Int.mul_le_mul_of_nonneg_left h (Int.natCast_nonneg c)) r1,
      ?_, ?_, ?_⟩
    · rw [Nat.add_mul]; omega
    · intro β hβ
      simp only [part_smul]
      exact Int.mul_le_mul_of_nonneg_left (i1 β hβ) (Int.natCast_nonneg c)
    · intro β hβ
      rw [part_smul, part_smul]; simp only [Line.smul]
      have := Int.mul_le_mul_of_nonneg_left (j1 β hβ) (Int.natCast_nonneg c)
      rw [Int.mul_sub, Int.mul_add] at this; exact this
  | @div L s c a' b' _ hc ha hb ih =>
    obtain ⟨f1, t1, r1, ht1, i1, j1⟩ := ih
    refine ⟨fun β => cdiv c (f1 β), t1 + 1,
      RC.gate1 (cdiv c) (fun x y h => Int.ediv_le_ediv (by omega) (by omega)) r1, ?_, ?_, ?_⟩
    · rw [Nat.add_mul]; omega
    · intro β hβ
      have h1 := i1 β hβ
      rw [part_div Q X c L a' b' ha] at h1
      have ⟨_, h3⟩ := cdiv_spec c hc (f1 β)
      have : (c : Int) * cdiv c (f1 β) < c * (part Q X ⟨a', b'⟩ β + 1) := by
        rw [Int.mul_add]; omega
      have := lt_of_cmul this
      show cdiv c (f1 β) ≤ _; omega
    · intro β hβ
      have h1 := j1 β hβ
      rw [part_div R X c L a' b' ha, part_div (shared Q R) X c L a' b' ha] at h1
      have ⟨h2, _⟩ := cdiv_spec c hc (f1 β)
      have : (c : Int) * (b' - 1) < c * (part R X ⟨a', b'⟩ β + part (shared Q R) X ⟨a', b'⟩ β +
          cdiv c (f1 β)) := by
        rw [Int.mul_add, Int.mul_add]; omega
      have := lt_of_cmul this
      show b' - cdiv c (f1 β) ≤ _; omega

end

/-- **Feasible interpolation for tree-like cutting planes into monotone real formulas.**
If the shared variables occur only negatively in `A`, every tree-like CP refutation of `A ++ B` with
`s` nodes yields a monotone real formula `f` on the shared variables with at most `s (2|X| + 1)`
gates such that `f β ≥ 1` forces `β` to falsify `A` and `f β ≤ 0` forces `β` to falsify `B`. -/
theorem interp {V} [DecidableEq V] (A B : CNF V) (Q R : V → Bool)
    (hQR : ∀ v, Q v = true → R v = false)
    (hA : ∀ C ∈ A, ∀ l ∈ C, R l.var = false) (hB : ∀ C ∈ B, ∀ l ∈ C, Q l.var = false)
    (hneg : ∀ C ∈ A, ∀ l ∈ C, Q l.var = false → l.pos = false)
    (Rf : Refutation (A ++ B)) :
    ∃ f t, RC (shared Q R) f t ∧ t ≤ Rf.size * (2 * Rf.X.length + 1) ∧
      (∀ α β : V → Bool, (∀ v, α v = true → β v = true) → f α ≤ f β) ∧
      (∀ α β : V → Bool, (∀ v, shared Q R v = true → α v = β v) → f α = f β) ∧
      ∀ β, (1 ≤ f β → ¬ ∀ C ∈ A, C.eval β = true) ∧ (f β ≤ 0 → ¬ ∀ C ∈ B, C.eval β = true) := by
  obtain ⟨f, t, r, ht, iA, iB⟩ :=
    interp_node A B Q R Rf.X Rf.X.length (fun _ _ => List.length_filter_le _ _) Rf.nodup Rf.cover
      hQR hA hB hneg Rf.deriv
  refine ⟨f, t, r, ht, fun α β h => r.mono h, fun α β h => r.local h, fun β => ⟨?_, ?_⟩⟩
  · intro h1 hβ
    have := iA β hβ
    rw [part_vanish Q _ _ β (fun _ _ => rfl)] at this; omega
  · intro h1 hβ
    have := iB β hβ
    rw [part_vanish R _ _ β (fun _ _ => rfl), part_vanish _ _ _ β (fun _ _ => rfl)] at this
    simp only at this; omega

/-- `interp` with the gate bound `s (2w + 1)`, where every clause of `A` has at most `w` literals
(independent of the variable list `X`). -/
theorem interp_width {V} [DecidableEq V] (A B : CNF V) (Q R : V → Bool) (w : Nat)
    (hwA : ∀ C ∈ A, C.length ≤ w)
    (hQR : ∀ v, Q v = true → R v = false)
    (hA : ∀ C ∈ A, ∀ l ∈ C, R l.var = false) (hB : ∀ C ∈ B, ∀ l ∈ C, Q l.var = false)
    (hneg : ∀ C ∈ A, ∀ l ∈ C, Q l.var = false → l.pos = false)
    (Rf : Refutation (A ++ B)) :
    ∃ f t, RC (shared Q R) f t ∧ t ≤ Rf.size * (2 * w + 1) ∧
      (∀ α β : V → Bool, (∀ v, α v = true → β v = true) → f α ≤ f β) ∧
      (∀ α β : V → Bool, (∀ v, shared Q R v = true → α v = β v) → f α = f β) ∧
      ∀ β, (1 ≤ f β → ¬ ∀ C ∈ A, C.eval β = true) ∧ (f β ≤ 0 → ¬ ∀ C ∈ B, C.eval β = true) := by
  have hw : ∀ C ∈ A, (Rf.X.filter fun v => decide (v ∈ C.map Lit.var)).length ≤ w := by
    intro C hC
    have h1 := List.Nodup.length_le_of_subset (Rf.nodup.filter (fun v => decide (v ∈ C.map Lit.var)))
      (l₂ := C.map Lit.var) (by intro v hv; have := (List.mem_filter.1 hv).2; simpa using this)
    have := hwA C hC; rw [List.length_map] at h1; omega
  obtain ⟨f, t, r, ht, iA, iB⟩ := interp_node A B Q R Rf.X w hw Rf.nodup Rf.cover hQR hA hB hneg Rf.deriv
  refine ⟨f, t, r, ht, fun α β h => r.mono h, fun α β h => r.local h, fun β => ⟨?_, ?_⟩⟩
  · intro h1 hβ
    have := iA β hβ
    rw [part_vanish Q _ _ β (fun _ _ => rfl)] at this; omega
  · intro h1 hβ
    have := iB β hβ
    rw [part_vanish R _ _ β (fun _ _ => rfl), part_vanish _ _ _ β (fun _ _ => rfl)] at this
    simp only at this; omega

end Programme.«20261024-1633-proof-complexity».CPInterp
