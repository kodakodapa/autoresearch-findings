import Programme.«20261024-1633-proof-complexity».CPInterp

/-!
# Range-bounded interpolants for tree-like cutting planes with bounded coefficients

The approximation method for monotone *real* formulas needs, for every subformula `h`, a bound
`h α - h β ≤ R` on its range. `interp` (K12) gives no such bound: its gates are arbitrary monotone
maps. Here the derivation carries a weight bound: every line `∑ a_v x_v ≥ b` of the tree-like
cutting-planes derivation has `wt = ∑_{v ∈ X} |a_v| + |b| ≤ W` (`DW`, `BRefutation`). We rebuild
Pudlák's interpolant with one extra *clamp* gate per node, clamping the threshold of a line into
`[N_Q, b - N_R - N_P]`, where `N_S` is the sum of the negative coefficients on `S`. Clamping keeps
the interpolation invariant (the `Q`-part is always `≥ N_Q`, the `R ∪ P`-part always `≥ N_R + N_P`)
and leaves a range of at most `wt ≤ W`. Every subformula then has range `≤ 2W` (`RCR`).

Main result: `interp_range`.
-/

set_option linter.unusedSectionVars false

namespace Programme.«20261024-1633-proof-complexity».CPRange

open Programme.«20261024-1110-proof-complexity».Haken (Lit Clause CNF Lit.eval Clause.eval)
open Programme.«20261024-1633-proof-complexity».CP Programme.«20261024-1633-proof-complexity».CPInterp

/-- `f` has range at most `R`. -/
def Rng {V} (R : Int) (f : (V → Bool) → Int) : Prop := ∀ α β, f α - f β ≤ R

/-- Monotone real formulas on the variables satisfying `P` in which **every subformula** has
range at most `R`. -/
inductive RCR {V} (P : V → Bool) (R : Int) : ((V → Bool) → Int) → Nat → Prop
  | const (k : Int) : 0 ≤ R → RCR P R (fun _ => k) 1
  | inp (u : V) : P u = true → 1 ≤ R → RCR P R (fun β => val β u) 1
  | gate1 {f : (V → Bool) → Int} {s : Nat} (g : Int → Int) : (∀ x y, x ≤ y → g x ≤ g y) →
      RCR P R f s → Rng R (fun β => g (f β)) → RCR P R (fun β => g (f β)) (s + 1)
  | gate2 {f h : (V → Bool) → Int} {s t : Nat} (g : Int → Int → Int) :
      (∀ x x' y y', x ≤ x' → y ≤ y' → g x y ≤ g x' y') →
      RCR P R f s → RCR P R h t → Rng R (fun β => g (f β) (h β)) →
      RCR P R (fun β => g (f β) (h β)) (s + t + 1)

theorem RCR.rng {V} {P : V → Bool} {R : Int} {f : (V → Bool) → Int} {s : Nat} (c : RCR P R f s) :
    Rng R f := by
  cases c with
  | const k h => intro α β; simp only; omega
  | inp u _ h => intro α β; have := val_01 α u; have := val_01 β u; simp only; omega
  | gate1 _ _ _ h => exact h
  | gate2 _ _ _ _ h => exact h

/-- Forgetting the range bounds gives a formula of K12's type `RC`. -/
theorem RCR.toRC {V} {P : V → Bool} {R : Int} {f : (V → Bool) → Int} {s : Nat} (c : RCR P R f s) :
    RC P f s := by
  induction c with
  | const k _ => exact RC.const k
  | inp u hu _ => exact RC.inp u hu
  | gate1 g hg _ _ ih => exact RC.gate1 g hg ih
  | gate2 g hg _ _ _ ih1 ih2 => exact RC.gate2 g hg ih1 ih2

theorem RCR.congr {V} {P : V → Bool} {R : Int} {f g : (V → Bool) → Int} {s : Nat}
    (c : RCR P R f s) (h : ∀ β, f β = g β) : RCR P R g s := by
  have : f = g := funext h
  subst this; exact c

/-! ## Weights and weight-bounded derivations -/

/-- `∑_{v ∈ X} |a_v| + |b|`. -/
def wt {V} (X : List V) (L : Line V) : Int := (X.map fun v => ((L.a v).natAbs : Int)).sum + (L.b.natAbs : Int)

/-- Tree-like cutting-planes derivations in which every line has weight `≤ W` over `X`. -/
inductive DW {V} [DecidableEq V] (F : CNF V) (X : List V) (W : Int) : Line V → Nat → Prop
  | ax (C : Clause V) : C ∈ F → wt X (clauseLine C) ≤ W → DW F X W (clauseLine C) 1
  | lo (u : V) : wt X ⟨fun v => if u = v then 1 else 0, 0⟩ ≤ W →
      DW F X W ⟨fun v => if u = v then 1 else 0, 0⟩ 1
  | hi (u : V) : wt X ⟨fun v => if u = v then -1 else 0, -1⟩ ≤ W →
      DW F X W ⟨fun v => if u = v then -1 else 0, -1⟩ 1
  | add {L M : Line V} {s t : Nat} : DW F X W L s → DW F X W M t → wt X (L.add M) ≤ W →
      DW F X W (L.add M) (s + t + 1)
  | smul {L : Line V} {s : Nat} (c : Nat) : DW F X W L s → wt X (L.smul c) ≤ W →
      DW F X W (L.smul c) (s + 1)
  | div {L : Line V} {s : Nat} (c : Nat) (a' : V → Int) (b' : Int) : DW F X W L s → 0 < c →
      (∀ v, L.a v = (c : Int) * a' v) → (c : Int) * (b' - 1) < L.b → wt X ⟨a', b'⟩ ≤ W →
      DW F X W ⟨a', b'⟩ (s + 1)

theorem DW.toD {V} [DecidableEq V] {F : CNF V} {X : List V} {W : Int} {L : Line V} {s : Nat}
    (d : DW F X W L s) : D F L s := by
  induction d with
  | ax C hC _ => exact D.ax C hC
  | lo u _ => exact D.lo u
  | hi u _ => exact D.hi u
  | add _ _ _ ih1 ih2 => exact D.add ih1 ih2
  | smul c _ _ ih => exact D.smul c ih
  | div c a' b' _ hc ha hb _ ih => exact D.div c a' b' ih hc ha hb

theorem DW.wt_le {V} [DecidableEq V] {F : CNF V} {X : List V} {W : Int} {L : Line V} {s : Nat}
    (d : DW F X W L s) : wt X L ≤ W := by
  cases d with
  | ax _ _ h => exact h
  | lo _ h => exact h
  | hi _ h => exact h
  | add _ _ h => exact h
  | smul _ _ h => exact h
  | div _ _ _ _ _ _ _ h => exact h

/-- A tree-like cutting-planes refutation in which every line has weight at most `W`
(cutting planes with bounded coefficients, CP*, when `W` is polynomial). -/
structure BRefutation {V} [DecidableEq V] (F : CNF V) where
  X : List V
  nodup : X.Nodup
  cover : ∀ C ∈ F, ∀ l ∈ C, l.var ∈ X
  size : Nat
  W : Int
  deriv : DW F X W ⟨fun _ => 0, 1⟩ size

/-- Every bounded refutation is a refutation of the unrestricted system (K9's `Refutation`). -/
def BRefutation.toRef {V} [DecidableEq V] {F : CNF V} (R : BRefutation F) : Refutation F :=
  ⟨R.X, R.nodup, R.cover, R.size, R.deriv.toD⟩

theorem sum_abs_nonneg {V} (X : List V) (a : V → Int) : 0 ≤ (X.map fun v => ((a v).natAbs : Int)).sum := by
  induction X with
  | nil => simp
  | cons x X ih => simp only [List.map_cons, List.sum_cons]; omega

theorem wt_nonneg {V} (X : List V) (L : Line V) : 0 ≤ wt X L := by
  unfold wt; have := sum_abs_nonneg X L.a; omega

theorem one_le_W {V} [DecidableEq V] {F : CNF V} (R : BRefutation F) : 1 ≤ R.W := by
  have h := R.deriv.wt_le
  have := sum_abs_nonneg R.X (fun _ => (0 : Int))
  unfold wt at h; simp only at h this; omega

theorem sum_natAbs_smul {V} (X : List V) (c : Nat) (a : V → Int) :
    (X.map fun v => (((c : Int) * a v).natAbs : Int)).sum = c * (X.map fun v => ((a v).natAbs : Int)).sum := by
  rw [← sum_mul]; congr 1; apply List.map_congr_left; intro v _
  rw [Int.natAbs_mul]; simp

theorem wt_smul {V} (X : List V) (c : Nat) (L : Line V) : wt X (L.smul c) = c * wt X L := by
  unfold wt Line.smul; simp only
  rw [sum_natAbs_smul, Int.natAbs_mul, Int.mul_add]; simp

/-! ## Negative parts and the clamp -/

/-- Sum of the negative coefficients of `L` on the variables of `X` satisfying `S`. -/
def negSum {V} (S : V → Bool) (X : List V) (L : Line V) : Int :=
  (X.map fun v => if S v then min (L.a v) 0 else 0).sum

theorem negSum_le {V} (S : V → Bool) (X : List V) (L : Line V) (β : V → Bool) :
    negSum S X L ≤ part S X L β := by
  unfold negSum part
  induction X with
  | nil => simp
  | cons x X ih =>
    simp only [List.map_cons, List.sum_cons]
    have : (if S x then min (L.a x) 0 else 0) ≤ (if S x then L.a x * val β x else 0) := by
      split
      · rcases val_01 β x with h | h <;> rw [h] <;> omega
      · exact Int.le_refl 0
    omega

theorem negSum_total {V} (Q R : V → Bool) (hQR : ∀ v, Q v = true → R v = false) (X : List V)
    (L : Line V) :
    -(X.map fun v => ((L.a v).natAbs : Int)).sum ≤ negSum Q X L + negSum R X L + negSum (shared Q R) X L := by
  unfold negSum
  induction X with
  | nil => simp
  | cons x X ih =>
    simp only [List.map_cons, List.sum_cons]
    have : -((L.a x).natAbs : Int) ≤ (if Q x then min (L.a x) 0 else 0) +
        (if R x then min (L.a x) 0 else 0) + (if shared Q R x then min (L.a x) 0 else 0) := by
      unfold shared
      cases hq : Q x
      · cases R x <;> simp <;> omega
      · simp [hQR x hq]; omega
    omega

section
variable {V : Type} [DecidableEq V] (A B : CNF V) (Q R : V → Bool) (X : List V)

/-- Clamp the threshold of line `L` into `[N_Q, b - N_R - N_P]`. -/
def clamp (L : Line V) (x : Int) : Int :=
  min (max x (negSum Q X L)) (L.b - (negSum R X L + negSum (shared Q R) X L))

theorem clamp_mono (L : Line V) : ∀ x y, x ≤ y → clamp Q R X L x ≤ clamp Q R X L y := by
  intro x y h; unfold clamp; omega

theorem clamp_inv (L : Line V) (f : (V → Bool) → Int) (h : Inv A B Q R X L f) :
    Inv A B Q R X L (fun β => clamp Q R X L (f β)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun β hβ => ?_, fun β hβ => ?_⟩
  · have := h1 β hβ; have := negSum_le Q X L β
    unfold clamp; dsimp only; omega
  · have := h2 β hβ; have := negSum_le R X L β; have := negSum_le (shared Q R) X L β
    unfold clamp; dsimp only; omega

theorem clamp_bounds (x c1 c2 : Int) : min (max x c1) c2 ≤ c2 ∧ min c1 c2 ≤ min (max x c1) c2 := by
  omega

theorem clamp_rng (hQR : ∀ v, Q v = true → R v = false) (L : Line V) (f : (V → Bool) → Int) :
    Rng (wt X L) (fun β => clamp Q R X L (f β)) := by
  intro α β
  have := negSum_total Q R hQR X L
  have := sum_abs_nonneg X L.a
  have := clamp_bounds (f α) (negSum Q X L) (L.b - (negSum R X L + negSum (shared Q R) X L))
  have := clamp_bounds (f β) (negSum Q X L) (L.b - (negSum R X L + negSum (shared Q R) X L))
  show min (max (f α) (negSum Q X L)) (L.b - (negSum R X L + negSum (shared Q R) X L)) -
    min (max (f β) (negSum Q X L)) (L.b - (negSum R X L + negSum (shared Q R) X L)) ≤
    (X.map fun v => ((L.a v).natAbs : Int)).sum + (L.b.natAbs : Int)
  omega

/-- The clamp gate closes every node. -/
theorem finish (hQR : ∀ v, Q v = true → R v = false) (W : Int) (L : Line V) (hL : wt X L ≤ W)
    {g : (V → Bool) → Int} {t : Nat} (r : RCR (shared Q R) (2 * W) g t) (i : Inv A B Q R X L g) :
    RCR (shared Q R) (2 * W) (fun β => clamp Q R X L (g β)) (t + 1) ∧
      Inv A B Q R X L (fun β => clamp Q R X L (g β)) ∧ Rng (wt X L) (fun β => clamp Q R X L (g β)) := by
  have h0 := wt_nonneg X L
  refine ⟨RCR.gate1 _ (clamp_mono Q R X L) r ?_, clamp_inv A B Q R X L g i, clamp_rng Q R X hQR L g⟩
  intro α β; have := clamp_rng Q R X hQR L g α β; simp only at this ⊢; omega

end

/-- `b + ∑_{v ∈ X, P v} c_v x_v` with `c_v ≥ 0` and `∑ c_v ≤ R`, every partial sum a subformula. -/
theorem buildR {V} (P : V → Bool) (c : V → Int) (hc : ∀ v, P v = true → 0 ≤ c v) (b R : Int)
    (hR1 : 1 ≤ R) :
    ∀ X : List V, (X.map fun v => if P v then c v else 0).sum ≤ R → ∃ s, s ≤ 2 * X.length + 1 ∧
      RCR P R (fun β => b + (X.map fun v => if P v then c v * val β v else 0).sum) s
  | [], _ => ⟨1, by simp, (RCR.const (P := P) b (by omega)).congr (by intro β; simp)⟩
  | x :: X, hX => by
    have hcx : 0 ≤ (if P x then c x else 0) := by split <;> simp_all
    simp only [List.map_cons, List.sum_cons] at hX
    obtain ⟨s, hs, r⟩ := buildR P c hc b R hR1 X (by omega)
    -- the range of a partial sum is at most the sum of its coefficients
    have rngX : ∀ (Y : List V) α β, (Y.map fun v => if P v then c v * val α v else 0).sum -
        (Y.map fun v => if P v then c v * val β v else 0).sum ≤ (Y.map fun v => if P v then c v else 0).sum := by
      intro Y α β
      induction Y with
      | nil => simp
      | cons y Y ih =>
        simp only [List.map_cons, List.sum_cons]
        have : (if P y then c y * val α y else 0) - (if P y then c y * val β y else 0) ≤
            (if P y then c y else 0) := by
          split
          · have := hc y (by assumption)
            rcases val_01 α y with h | h <;> rcases val_01 β y with h' | h' <;> rw [h, h'] <;> omega
          · simp
        omega
    cases hx : P x
    · refine ⟨s, by simp; omega, r.congr ?_⟩
      intro β; simp [hx]
    · refine ⟨s + 1 + 1, by simp; omega, ?_⟩
      have := RCR.gate2 (fun y z => y + c x * z) ?_ r (RCR.inp x hx hR1) ?_
      · refine this.congr ?_
        intro β; simp only [hx, List.map_cons, List.sum_cons, ite_true]; omega
      · intro y y' z z' hy hz
        have := Int.mul_le_mul_of_nonneg_left hz (hc x hx)
        omega
      · intro α β
        have h1 := rngX X α β
        have h2 := hc x hx
        simp only [hx, ite_true] at hcx hX
        simp only
        rcases val_01 α x with h | h <;> rcases val_01 β x with h' | h' <;> rw [h, h'] <;>
          simp only [Int.mul_one, Int.mul_zero] <;> omega

theorem sum_filter_le {α} (Y : List α) (p : α → Bool) (g : α → Int) (h : ∀ v, 0 ≤ g v) :
    ((Y.filter p).map g).sum ≤ (Y.map g).sum := by
  induction Y with
  | nil => simp
  | cons y Y ih =>
    have := h y
    cases hy : p y <;> simp [hy] <;> omega

theorem cdiv_rng (c : Nat) (hc : 0 < c) (x y : Int) : cdiv c x - cdiv c y ≤ max 0 (x - y) := by
  have ⟨_, h1⟩ := cdiv_spec c hc x
  have ⟨h2, _⟩ := cdiv_spec c hc y
  have e : (c : Int) * (cdiv c x - cdiv c y) < x - y + c := by rw [Int.mul_sub]; omega
  apply Int.not_lt.mp; intro hlt
  have hc1 : (1 : Int) ≤ c := by omega
  by_cases hxy : 0 ≤ x - y
  · have : (c : Int) * (x - y + 1) ≤ c * (cdiv c x - cdiv c y) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have : (x - y) ≤ (c : Int) * (x - y) := by
      have := Int.mul_le_mul_of_nonneg_right hc1 hxy; omega
    rw [Int.mul_add] at *; omega
  · have : (c : Int) * 1 ≤ c * (cdiv c x - cdiv c y) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega

section
variable {V : Type} [DecidableEq V] (A B : CNF V) (Q R : V → Bool) (X : List V)

theorem interp_range_node (w : Nat) (W : Int) (hW : 1 ≤ W)
    (hw : ∀ C ∈ A, (X.filter fun v => decide (v ∈ C.map Lit.var)).length ≤ w) (hX : X.Nodup)
    (cover : ∀ C ∈ A ++ B, ∀ l ∈ C, l.var ∈ X)
    (hQR : ∀ v, Q v = true → R v = false)
    (hA : ∀ C ∈ A, ∀ l ∈ C, R l.var = false) (hB : ∀ C ∈ B, ∀ l ∈ C, Q l.var = false)
    (hneg : ∀ C ∈ A, ∀ l ∈ C, Q l.var = false → l.pos = false)
    {L : Line V} {s : Nat} (d : DW (A ++ B) X W L s) :
    ∃ f t, RCR (shared Q R) (2 * W) f t ∧ t ≤ s * (2 * w + 2) ∧ Inv A B Q R X L f ∧
      Rng (wt X L) f := by
  induction d with
  | ax C hC hwt =>
    have cov := cover C hC
    by_cases hCA : C ∈ A
    · have hR0 : ∀ v, R v = true → (clauseLine C).a v = 0 := by
        intro v hv; apply clause_coef_zero; intro l hl e; subst e; simp [hA C hCA l hl] at hv
      have hcn : ∀ v, shared Q R v = true → 0 ≤ -(clauseLine C).a v := by
          intro v hv
          have : (clauseLine C).a v ≤ 0 := by
            apply clause_coef_nonpos; intro l hl e; subst e
            apply hneg C hCA l hl; simp [shared] at hv; exact hv.1
          omega
      -- the coefficient sum of the filtered list is at most the weight
      have hsum : ((X.filter fun v => decide (v ∈ C.map Lit.var)).map fun v =>
          if shared Q R v then -(clauseLine C).a v else 0).sum ≤ 2 * W := by
        have h1 : ∀ Y : List V, (Y.map fun v => if shared Q R v then -(clauseLine C).a v else 0).sum ≤
            (Y.map fun v => (((clauseLine C).a v).natAbs : Int)).sum := by
          intro Y; induction Y with
          | nil => simp
          | cons y Y ih =>
            simp only [List.map_cons, List.sum_cons]
            have : (if shared Q R y then -(clauseLine C).a y else 0) ≤ (((clauseLine C).a y).natAbs : Int) := by
              split <;> omega
            omega
        have h2 : ((X.filter fun v => decide (v ∈ C.map Lit.var)).map fun v =>
            (((clauseLine C).a v).natAbs : Int)).sum ≤ (X.map fun v => (((clauseLine C).a v).natAbs : Int)).sum := by
          exact sum_filter_le _ _ _ (fun v => by omega)
        have := h1 (X.filter fun v => decide (v ∈ C.map Lit.var))
        unfold wt at hwt; have := sum_abs_nonneg X (clauseLine C).a; omega
      obtain ⟨t, ht, r⟩ := buildR (shared Q R) (fun v => -(clauseLine C).a v) hcn (clauseLine C).b
        (2 * W) (by omega) (X.filter fun v => decide (v ∈ C.map Lit.var)) hsum
      have hwC := hw C hCA
      have r := r.congr (g := fun β => (clauseLine C).b +
          (X.map fun v => if shared Q R v then -(clauseLine C).a v * val β v else 0).sum) (by
        intro β; congr 1; apply sum_filter; intro v hv
        have : (clauseLine C).a v = 0 := by
          apply clause_coef_zero; intro l hl e; subst e
          simp only [decide_eq_false_iff_not, List.mem_map, not_exists, not_and] at hv
          exact hv l hl rfl
        simp [this])
      have neg : ∀ β, (X.map fun v => if shared Q R v then -(clauseLine C).a v * val β v else 0).sum =
          -part (shared Q R) X (clauseLine C) β := by
        intro β
        unfold part; rw [← Int.neg_one_mul, ← sum_mul]; congr 1
        apply List.map_congr_left; intro v _; split <;> simp [Int.neg_mul]
      have i : Inv A B Q R X (clauseLine C) (fun β => (clauseLine C).b +
          (X.map fun v => if shared Q R v then -(clauseLine C).a v * val β v else 0).sum) := by
        refine ⟨?_, ?_⟩
        · intro β hβ
          have hs := clause_sound X hX C cov β (hβ C hCA)
          unfold Line.holds at hs
          rw [lhs_parts Q R hQR, part_vanish R X _ β hR0] at hs
          simp only [neg β]; omega
        · intro β _
          simp only [neg β, part_vanish R X _ β hR0]; omega
      obtain ⟨r', i', g'⟩ := finish A B Q R X hQR W _ hwt r i
      exact ⟨_, t + 1, r', by omega, i', g'⟩
    · have hCB : C ∈ B := by
        rcases List.mem_append.mp hC with h | h
        · exact absurd h hCA
        · exact h
      have hQ0 : ∀ v, Q v = true → (clauseLine C).a v = 0 := by
        intro v hv; apply clause_coef_zero; intro l hl e; subst e; simp [hB C hCB l hl] at hv
      have i : Inv A B Q R X (clauseLine C) (fun _ => 0) := by
        refine ⟨?_, ?_⟩
        · intro β _; simp [part_vanish Q X _ β hQ0]
        · intro β hβ
          have hs := clause_sound X hX C cov β (hβ C hCB)
          unfold Line.holds at hs
          rw [lhs_parts Q R hQR, part_vanish Q X _ β hQ0] at hs
          show _ - (0 : Int) ≤ _
          omega
      obtain ⟨r', i', g'⟩ := finish A B Q R X hQR W _ hwt (RCR.const 0 (by omega)) i
      exact ⟨_, 2, r', by omega, i', g'⟩
  | lo u hwt =>
    have i : Inv A B Q R X ⟨fun v => if u = v then 1 else 0, 0⟩ (fun _ => 0) := by
      refine ⟨?_, ?_⟩
      · intro β _
        simp only [part_single _ X hX]
        have := val_01 β u
        split <;> (try split) <;> omega
      · intro β _
        simp only [part_single _ X hX, shared]
        have := val_01 β u
        split <;> (try split) <;> (try split) <;> omega
    obtain ⟨r', i', g'⟩ := finish A B Q R X hQR W _ hwt (RCR.const 0 (by omega)) i
    exact ⟨_, 2, r', by omega, i', g'⟩
  | hi u hwt =>
    have i : Inv A B Q R X ⟨fun v => if u = v then -1 else 0, -1⟩ (fun _ => if Q u then -1 else 0) := by
      refine ⟨?_, ?_⟩
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
    obtain ⟨r', i', g'⟩ := finish A B Q R X hQR W _ hwt (RCR.const _ (by omega)) i
    exact ⟨_, 2, r', by omega, i', g'⟩
  | @add L1 M1 s1 t1' d1 d2 hwt ih1 ih2 =>
    obtain ⟨f1, t1, r1, ht1, ⟨i1, j1⟩, g1⟩ := ih1
    obtain ⟨f2, t2, r2, ht2, ⟨i2, j2⟩, g2⟩ := ih2
    have w1 := d1.wt_le; have w2 := d2.wt_le
    have r := RCR.gate2 (fun x y => x + y) (by intro x x' y y' _ _; omega) r1 r2
      (by intro α β; have := g1 α β; have := g2 α β; simp only; omega)
    have i : Inv A B Q R X (L1.add M1) (fun β => f1 β + f2 β) := by
      refine ⟨?_, ?_⟩
      · intro β hβ; have := i1 β hβ; have := i2 β hβ
        simp only [part_add]; omega
      · intro β hβ; have := j1 β hβ; have := j2 β hβ
        rw [part_add, part_add]; simp only [Line.add]; omega
    obtain ⟨r', i', g'⟩ := finish A B Q R X hQR W _ hwt r i
    refine ⟨_, _, r', ?_, i', g'⟩
    rw [Nat.add_mul, Nat.add_mul]; omega
  | @smul L1 s1 c d1 hwt ih =>
    obtain ⟨f1, t1, r1, ht1, ⟨i1, j1⟩, g1⟩ := ih
    have r := RCR.gate1 (fun x => c * x)
      (fun x y h => Int.mul_le_mul_of_nonneg_left h (Int.natCast_nonneg c)) r1 (by
        intro α β
        have := Int.mul_le_mul_of_nonneg_left (g1 α β) (Int.natCast_nonneg c)
        rw [← wt_smul, Int.mul_sub] at this
        simp only; omega)
    have i : Inv A B Q R X (L1.smul c) (fun β => c * f1 β) := by
      refine ⟨?_, ?_⟩
      · intro β hβ
        simp only [part_smul]
        exact Int.mul_le_mul_of_nonneg_left (i1 β hβ) (Int.natCast_nonneg c)
      · intro β hβ
        rw [part_smul, part_smul]; simp only [Line.smul]
        have := Int.mul_le_mul_of_nonneg_left (j1 β hβ) (Int.natCast_nonneg c)
        rw [Int.mul_sub, Int.mul_add] at this; exact this
    obtain ⟨r', i', g'⟩ := finish A B Q R X hQR W _ hwt r i
    refine ⟨_, _, r', ?_, i', g'⟩
    rw [Nat.add_mul]; omega
  | @div L s c a' b' d1 hc ha hb hwt ih =>
    obtain ⟨f1, t1, r1, ht1, ⟨i1, j1⟩, g1⟩ := ih
    have w1 := d1.wt_le
    have r := RCR.gate1 (cdiv c) (fun x y h => Int.ediv_le_ediv (by omega) (by omega)) r1 (by
        intro α β
        have := cdiv_rng c hc (f1 α) (f1 β); have := g1 α β
        simp only; omega)
    have i : Inv A B Q R X ⟨a', b'⟩ (fun β => cdiv c (f1 β)) := by
      refine ⟨?_, ?_⟩
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
    obtain ⟨r', i', g'⟩ := finish A B Q R X hQR W _ hwt r i
    refine ⟨_, _, r', ?_, i', g'⟩
    rw [Nat.add_mul]; omega

end

/-- **Range-bounded feasible interpolation for tree-like CP with bounded weights.**
If the shared variables occur only negatively in `A` and every clause of `A` has at most `w`
literals, every tree-like CP refutation of `A ++ B` with `s` nodes and every line of weight
`≤ W` yields a monotone real formula `f` on the shared variables with at most `s (2w + 2)` gates,
**every subformula of range at most `2W`**, such that `f β ≥ 1` forces `β` to falsify `A` and
`f β ≤ 0` forces `β` to falsify `B`. -/
theorem interp_range {V} [DecidableEq V] (A B : CNF V) (Q R : V → Bool) (w : Nat)
    (hwA : ∀ C ∈ A, C.length ≤ w)
    (hQR : ∀ v, Q v = true → R v = false)
    (hA : ∀ C ∈ A, ∀ l ∈ C, R l.var = false) (hB : ∀ C ∈ B, ∀ l ∈ C, Q l.var = false)
    (hneg : ∀ C ∈ A, ∀ l ∈ C, Q l.var = false → l.pos = false)
    (Rf : BRefutation (A ++ B)) :
    ∃ f t, RCR (shared Q R) (2 * Rf.W) f t ∧ t ≤ Rf.size * (2 * w + 2) ∧
      (∀ α β : V → Bool, (∀ v, α v = true → β v = true) → f α ≤ f β) ∧
      (∀ α β : V → Bool, (∀ v, shared Q R v = true → α v = β v) → f α = f β) ∧
      ∀ β, (1 ≤ f β → ¬ ∀ C ∈ A, C.eval β = true) ∧ (f β ≤ 0 → ¬ ∀ C ∈ B, C.eval β = true) := by
  have hw : ∀ C ∈ A, (Rf.X.filter fun v => decide (v ∈ C.map Lit.var)).length ≤ w := by
    intro C hC
    have h1 := List.Nodup.length_le_of_subset (Rf.nodup.filter (fun v => decide (v ∈ C.map Lit.var)))
      (l₂ := C.map Lit.var) (by intro v hv; have := (List.mem_filter.1 hv).2; simpa using this)
    have := hwA C hC; rw [List.length_map] at h1; omega
  obtain ⟨f, t, r, ht, ⟨iA, iB⟩, _⟩ := interp_range_node A B Q R Rf.X w Rf.W (one_le_W Rf) hw
    Rf.nodup Rf.cover hQR hA hB hneg Rf.deriv
  refine ⟨f, t, r, ht, fun α β h => r.toRC.mono h, fun α β h => r.toRC.local h, fun β => ⟨?_, ?_⟩⟩
  · intro h1 hβ
    have := iA β hβ
    rw [part_vanish Q _ _ β (fun _ _ => rfl)] at this; omega
  · intro h1 hβ
    have := iB β hβ
    rw [part_vanish R _ _ β (fun _ _ => rfl), part_vanish _ _ _ β (fun _ _ => rfl)] at this
    simp only at this; omega

end Programme.«20261024-1633-proof-complexity».CPRange
