import Programme.«20261024-1633-proof-complexity».NSLower

/-!
# Grigoriev's Nullstellensatz degree lower bound for Tseitin formulas over odd characteristic

Hypotheses exactly as in the library width bound `Tseitin.tseitin_width` (K20): `n ≥ 3`, edges
between distinct vertices `< n`, connectivity (`hconn`), and every vertex set `T` with
`n/3 < |T| ≤ 2(n/3)` has `≥ e` boundary edges (`hexp`). Then for every odd `p > 1` and every
charge, `Tseitin n E χ` has no `NSRefutation p` of degree `< e` (`tseitin_ns_lower`). Since
`NSRefutation` only asks the identity to hold on the Boolean cube mod `p`, this also rules out
the usual syntactic Nullstellensatz refutations (with Boolean axioms) of degree `< e` over `F_p`.

Proof (Grigoriev 1998, in the `±1` basis): `coef S = (-1)^{χ(T)}` if `S = ∂T` with `|T| ≤ n/3`,
else `0` (well defined by connectivity, `bd_unique`). For `|S|, |S ⊕ E(v)| < e`,
`coef (S ⊕ E(v)) = (-1)^{χ v} coef S` (`coef_step`: `T ↦ T ⊕ {v}` cannot become medium-sized
without `e` boundary edges). Each term `κ · m · f_C` of a refutation, `C` a clause of vertex `v`,
lives on `≤ deg m + |C| < e` coordinates and satisfies `h · χ_{E(v)} = -(-1)^{χ v} h`, so the
involution lemma kills it; but the design of `1 + p·k` is `±2^N + p·(…)`, and an odd `p > 1` does
not divide `2^N`.
-/

namespace Programme.«20261024-1633-proof-complexity».NSTseitin

open Classical Programme.«20261024-1110-proof-complexity».Haken
open Programme.«20261024-1110-proof-complexity».Tseitin
open Programme.«20261024-1633-proof-complexity».NS Programme.«20261024-1633-proof-complexity».NSLower

/-! ## Parity signs and small lemmas -/

def psg (k : Nat) : Int := if k % 2 = 0 then 1 else -1

theorem psg_sq (k : Nat) : psg k * psg k = 1 := by unfold psg; split <;> rfl

theorem psg_add (j k : Nat) : psg (j + k) = psg j * psg k := by
  unfold psg
  by_cases hj : j % 2 = 0 <;> by_cases hk : k % 2 = 0 <;> simp [hj, hk] <;> omega

theorem psg_mod (j k : Nat) (h : j % 2 = k % 2) : psg j = psg k := by unfold psg; rw [h]

theorem chi_count (N : Nat) (S a : Nat → Bool) :
    chi N S a = psg ((List.range N).countP fun i => S i && a i) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [chi, ih, List.range_succ, List.countP_append, psg_add]
    rw [Int.mul_comm]; congr 1
    simp only [List.countP_cons, List.countP_nil]
    cases S N <;> cases a N <;> rfl

theorem countP_eq (n v : Nat) :
    (List.range n).countP (fun w => w == v) = if v < n then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih]
    by_cases h1 : v < n
    · have : v < n + 1 := by omega
      have h2 : (n == v) = false := by simp; omega
      simp [h1, this, h2]
    · by_cases h3 : v = n
      · subst h3; simp
      · have : ¬ v < n + 1 := by omega
        have h2 : (n == v) = false := by simp; omega
        simp [h1, this, h2]

theorem sum_single (n v : Nat) (x : Nat) :
    ((List.range n).map fun w => if w = v then x else 0).sum = if v < n then x else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    by_cases h1 : v < n
    · have : v < n + 1 := by omega
      have h2 : ¬ n = v := by omega
      simp [h1, this, h2]
    · by_cases h3 : v = n
      · subst h3; simp
      · have : ¬ v < n + 1 := by omega
        have h2 : ¬ n = v := by omega
        simp [h1, this, h2]

theorem countP_mem_le (N : Nat) (m : List Nat) :
    (List.range N).countP (fun i => decide (i ∈ m)) ≤ m.length := by
  induction m with
  | nil => simp
  | cons x m ih =>
    have h1 : (List.range N).countP (fun i => decide (i ∈ x :: m))
        ≤ (List.range N).countP (fun i => (i == x) || decide (i ∈ m)) := by
      apply List.countP_mono_left; intro i _ h; simpa using h
    have h2 := size_union (n := N) (fun i => i == x) (fun i => decide (i ∈ m))
    unfold size at h2
    have h3 := countP_eq N x
    simp only [List.length_cons]
    split at h3 <;> omega

theorem sum_parity3 {α} (l : List α) (f g h : α → Nat) (H : ∀ x ∈ l, (f x + g x + h x) % 2 = 0) :
    ((l.map f).sum + (l.map g).sum + (l.map h).sum) % 2 = 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := H x List.mem_cons_self
    have := ih (fun y hy => H y (List.mem_cons_of_mem _ hy))
    omega

theorem bne_xor (a b : Bool) : (a != b) = (a ^^ b) := by cases a <;> cases b <;> rfl

/-! ## The Grigoriev design for Tseitin -/

section
variable (n : Nat) (E : List (Nat × Nat)) (χ : Nat → Nat)

/-- Total charge of the vertices of `T`. -/
def chT (T : Nat → Bool) : Nat := ((List.range n).map fun v => if T v then χ v else 0).sum

/-- `S` is the edge boundary of `T` (on the edge indices `< |E|`). -/
def BdOf (T S : Nat → Bool) : Prop :=
  ∀ i, i < E.length → S i = (T (edge E i).1 != T (edge E i).2)

/-- `S` is the boundary of a vertex set of size `≤ n/3`. -/
def SmallBd (S : Nat → Bool) : Prop := ∃ T, size n T ≤ n / 3 ∧ BdOf E T S

/-- The design coefficient: `(-1)^{χ(T)}` if `S = ∂T` with `|T| ≤ n/3`, else `0`. -/
noncomputable def coef (S : Nat → Bool) : Int :=
  if h : SmallBd n E S then psg (chT n χ (Classical.choose h)) else 0

/-- The edges at `v`, as an indicator on `[0, |E|)`. -/
def Rv (v : Nat) : Nat → Bool :=
  fun i => decide (i < E.length) && ((edge E i).1 == v || (edge E i).2 == v)

end

section main
variable {n : Nat} {E : List (Nat × Nat)} {χ : Nat → Nat}

/-- Two vertex sets of size `≤ n/3` with the same boundary have the same charge (connectivity). -/
theorem bd_unique (hn : 1 ≤ n)
    (hconn : ∀ S : Nat → Bool, 0 < size n S → size n S < n → bd E S ≠ [])
    {T1 T2 S : Nat → Bool} (h1 : size n T1 ≤ n / 3) (h2 : size n T2 ≤ n / 3)
    (b1 : BdOf E T1 S) (b2 : BdOf E T2 S) : chT n χ T1 = chT n χ T2 := by
  let D : Nat → Bool := fun w => T1 w != T2 w
  have hsz : size n D ≤ size n T1 + size n T2 := by
    have := size_union (n := n) T1 T2
    have : size n D ≤ size n (fun w => T1 w || T2 w) := by
      unfold size; apply List.countP_mono_left; intro w _ h
      simp only [D] at h; cases hT1 : T1 w <;> cases hT2 : T2 w <;> simp_all
    omega
  have hbd : bd E D = [] := by
    unfold bd; rw [List.filter_eq_nil_iff]
    intro i hi
    have hi' := List.mem_range.mp hi
    have e1 := b1 i hi'; have e2 := b2 i hi'
    rw [e1] at e2
    simp only [D]
    generalize T1 (edge E i).1 = a1 at e2 ⊢; generalize T1 (edge E i).2 = a2 at e2 ⊢
    generalize T2 (edge E i).1 = c1 at e2 ⊢; generalize T2 (edge E i).2 = c2 at e2 ⊢
    cases a1 <;> cases a2 <;> cases c1 <;> cases c2 <;> simp_all
  have h0 : size n D = 0 := by
    apply Classical.byContradiction; intro h
    exact hconn D (by omega) (by omega) hbd
  have hz : ∀ w, w < n → T1 w = T2 w := by
    intro w hw
    have := List.countP_eq_zero.mp h0 w (List.mem_range.mpr hw)
    simp only [D] at this
    cases hT1 : T1 w <;> cases hT2 : T2 w <;> simp_all
  unfold chT
  congr 1
  apply List.map_congr_left
  intro w hw; rw [hz w (List.mem_range.mp hw)]

theorem bd_len_eq {T S : Nat → Bool} (b : BdOf E T S) :
    (bd E T).length = (List.range E.length).countP S := by
  unfold bd; rw [← List.countP_eq_length_filter]
  apply List.countP_congr; intro i hi; rw [b i (List.mem_range.mp hi)]

/-- Adding/removing `v` to `T` changes the boundary by the edges at `v` and the charge by `χ v`. -/
theorem step_set (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2) {v : Nat} (hv : v < n)
    {T X : Nat → Bool} (hb : BdOf E T X) :
    BdOf E (fun w => T w != (w == v)) (bxor X (Rv E v)) ∧
    size n (fun w => T w != (w == v)) ≤ size n T + 1 ∧
    psg (chT n χ (fun w => T w != (w == v))) = psg (χ v) * psg (chT n χ T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hne := (hE _ (edge_mem hi)).2.2
    simp only [bxor, Rv, hb i hi, decide_eq_true hi, Bool.true_and]
    generalize (edge E i).1 = x at hne ⊢; generalize (edge E i).2 = y at hne ⊢
    by_cases hx : x = v <;> by_cases hy : y = v
    · omega
    · simp only [hx, beq_self_eq_true]
      have : (y == v) = false := by simp [hy]
      rw [this]; cases T v <;> cases T y <;> rfl
    · simp only [hy, beq_self_eq_true]
      have : (x == v) = false := by simp [hx]
      rw [this]; cases T v <;> cases T x <;> rfl
    · have h1 : (x == v) = false := by simp [hx]
      have h2 : (y == v) = false := by simp [hy]
      rw [h1, h2]; cases T x <;> cases T y <;> rfl
  · have h1 := size_union (n := n) T (fun w => w == v)
    have h2 : size n (fun w => T w != (w == v)) ≤ size n (fun w => T w || (w == v)) := by
      unfold size; apply List.countP_mono_left; intro w _ h
      cases hT : T w <;> cases hw : (w == v) <;> simp_all
    have h3 := countP_eq n v
    unfold size at h1 h2 ⊢
    rw [ite_eq_left hv] at h3
    omega
  · have hp := sum_parity3 (List.range n)
      (fun w => if (T w != (w == v)) then χ w else 0) (fun w => if T w then χ w else 0)
      (fun w => if w = v then χ v else 0) (by
        intro w _
        by_cases hw : w = v
        · subst hw; cases T w <;> simp <;> omega
        · have : (w == v) = false := by simp [hw]
          simp only [this, hw]; cases T w <;> simp <;> omega)
    rw [sum_single, ite_eq_left hv] at hp
    unfold chT
    rw [← psg_add, Nat.add_comm (χ v)]
    apply psg_mod; dsimp only; omega

variable (hn : 3 ≤ n) (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2)
  (hconn : ∀ S : Nat → Bool, 0 < size n S → size n S < n → bd E S ≠ [])
  {e : Nat}
  (hexp : ∀ S : Nat → Bool, n / 3 < size n S → size n S ≤ 2 * (n / 3) → e ≤ (bd E S).length)
include hn hE hconn hexp

theorem coef_step_small {v : Nat} (hv : v < n) {X : Nat → Bool} (hX : SmallBd n E X)
    (hc : (List.range E.length).countP (bxor X (Rv E v)) < e) :
    SmallBd n E (bxor X (Rv E v)) ∧ coef n E χ (bxor X (Rv E v)) = psg (χ v) * coef n E χ X := by
  obtain ⟨hT, hb⟩ := Classical.choose_spec hX
  obtain ⟨b', s', c'⟩ := step_set (χ := χ) hE hv hb
  have hs : size n (fun w => Classical.choose hX w != (w == v)) ≤ n / 3 := by
    apply Classical.byContradiction; intro h
    have := hexp (fun w => Classical.choose hX w != (w == v)) (by omega) (by omega)
    rw [bd_len_eq b'] at this; omega
  have hX' : SmallBd n E (bxor X (Rv E v)) := ⟨_, hs, b'⟩
  refine ⟨hX', ?_⟩
  unfold coef
  rw [dite_eq_left hX', dite_eq_left hX]
  obtain ⟨hT2, hb2⟩ := Classical.choose_spec hX'
  rw [bd_unique (by omega) hconn hT2 hs hb2 b', c']

omit hn hE hconn hexp in
theorem bxor_bxor (X R : Nat → Bool) : bxor (bxor X R) R = X := by
  funext i; simp [bxor]

theorem coef_step {v : Nat} (hv : v < n) (X : Nat → Bool)
    (hc1 : (List.range E.length).countP X < e)
    (hc2 : (List.range E.length).countP (bxor X (Rv E v)) < e) :
    coef n E χ (bxor X (Rv E v)) = psg (χ v) * coef n E χ X := by
  by_cases hX : SmallBd n E X
  · exact (coef_step_small hn hE hconn hexp hv hX hc2).2
  · by_cases hX' : SmallBd n E (bxor X (Rv E v))
    · have hc1' : (List.range E.length).countP (bxor (bxor X (Rv E v)) (Rv E v)) < e := by
        rw [bxor_bxor]; exact hc1
      have := (coef_step_small (χ := χ) hn hE hconn hexp hv hX' hc1').2
      rw [bxor_bxor] at this
      rw [this, ← Int.mul_assoc, psg_sq, Int.one_mul]
    · unfold coef; rw [dite_eq_right hX, dite_eq_right hX']; simp

end main

/-! ## Each term `κ · m · f_C` is annihilated by the design -/

theorem psg_ne (j k : Nat) (h : j % 2 ≠ k % 2) : psg j = -psg k := by
  unfold psg; by_cases hj : j % 2 = 0 <;> by_cases hk : k % 2 = 0 <;> simp [hj, hk] <;> omega

theorem monoEval_congr (a b : Nat → Bool) (m : List Nat) (h : ∀ x ∈ m, a x = b x) :
    monoEval a m = monoEval b m := by
  unfold monoEval; congr 1; apply List.map_congr_left; intro x hx; rw [h x hx]

theorem clause_eval_congr (a b : Nat → Bool) (C : Clause Nat) (h : ∀ l ∈ C, a l.var = b l.var) :
    Clause.eval a C = Clause.eval b C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
    simp only [Clause.eval, List.any_cons] at ih ⊢
    rw [ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))]
    cases l with | mk x q => simp only [Lit.eval]; rw [h _ List.mem_cons_self]

theorem inc_count (E : List (Nat × Nat)) (v : Nat) (a : Nat → Bool) :
    (List.range E.length).countP (fun i => Rv E v i && a i) = (inc E v).countP a := by
  unfold inc; rw [List.countP_filter]
  apply List.countP_congr; intro i hi
  have := List.mem_range.mp hi
  simp [Rv, this, Bool.and_comm]

theorem inc_len (E : List (Nat × Nat)) (v : Nat) :
    (List.range E.length).countP (Rv E v) = (inc E v).length := by
  have := inc_count E v (fun _ => true)
  simp only [Bool.and_true] at this; rw [this, List.countP_true]

theorem mem_inc {E : List (Nat × Nat)} {v i : Nat} (h : i ∈ inc E v) : Rv E v i = true := by
  unfold inc at h; rw [List.mem_filter] at h
  simp [Rv, List.mem_range.mp h.1, h.2]

theorem sum_mul_right (l : List (Int × List Nat)) (f : Int × List Nat → Int) (x : Int) :
    (l.map f).sum * x = (l.map fun t => f t * x).sum := by
  induction l with
  | nil => simp
  | cons t l ih => simp only [List.map_cons, List.sum_cons, Int.add_mul, ih]

theorem sum_zero {α} (l : List α) (f : α → Int) (h : ∀ x ∈ l, f x = 0) : (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]; rfl

section main2
variable {n : Nat} {E : List (Nat × Nat)} {χ : Nat → Nat}
  (hn : 3 ≤ n) (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2)
  (hconn : ∀ S : Nat → Bool, 0 < size n S → size n S < n → bd E S ≠ [])
  {e : Nat}
  (hexp : ∀ S : Nat → Bool, n / 3 < size n S → size n S ≤ 2 * (n / 3) → e ≤ (bd E S).length)
include hn hE hconn hexp

theorem term_zero {v : Nat} (hv : v < n) {C : Clause Nat} (hC : C ∈ vclauses E χ v)
    (κ : Int) (m : List Nat) (hD : m.length + C.length < e) :
    design E.length (coef n E χ)
      (fun a => κ * monoEval a m * (clausePoly C).eval a) = 0 := by
  have hCs := (List.mem_filter.mp hC).1
  have hCvar := mem_signs hCs
  have hClen : C.length = (inc E v).length := by rw [← hCvar, List.length_map]
  let U : Nat → Bool := fun i => decide (i ∈ m) || Rv E v i
  have hU : (List.range E.length).countP U < e := by
    have h1 := size_union (n := E.length) (fun i => decide (i ∈ m)) (Rv E v)
    have h2 := countP_mem_le E.length m
    have h3 := inc_len E v
    unfold size at h1; simp only [U]; omega
  apply design_zero E.length (Rv E v) U (psg (χ v))
  · intro i hi; simp [Rv]; omega
  · intro i h; simp [U, h]
  · exact psg_sq _
  · intro a _
    rw [chi_count, inc_count, clausePoly_eval]
    cases hCa : Clause.eval a C
    · have hpar := signs_cpar hCs hCa
      have hne := (List.mem_filter.mp hC).2
      have : (inc E v).countP a % 2 ≠ χ v % 2 := by
        rw [← hpar]; intro h; rw [h] at hne; simp at hne
      rw [psg_ne _ _ this]; simp [Int.mul_comm]
    · simp
  · intro a _ x hx hUx
    have hm : x ∉ m := by intro h; simp [U, h] at hUx
    have hR : Rv E v x = false := by
      cases h : Rv E v x
      · rfl
      · simp [U, h] at hUx
    have hflip : ∀ y, y ≠ x → bxor a (fun i => i == x) y = a y := by
      intro y hy
      have : (y == x) = false := by simp [hy]
      simp [bxor, this]
    have hcl : Clause.eval (bxor a (fun i => i == x)) C = Clause.eval a C := by
      apply clause_eval_congr
      intro l hl
      apply hflip
      intro h
      have : l.var ∈ inc E v := by rw [← hCvar]; exact List.mem_map_of_mem hl
      rw [← h, mem_inc this] at hR; exact Bool.noConfusion hR
    have hmo : monoEval (bxor a (fun i => i == x)) m = monoEval a m :=
      monoEval_congr _ a m (fun y hy => hflip y (fun h => hm (h ▸ hy)))
    simp only [clausePoly_eval, hcl, hmo]
  · intro S _ hsub
    apply coef_step hn hE hconn hexp hv
    · apply Nat.lt_of_le_of_lt _ hU
      apply List.countP_mono_left; intro i hi h; exact hsub i (List.mem_range.mp hi) h
    · apply Nat.lt_of_le_of_lt _ hU
      apply List.countP_mono_left; intro i hi h
      simp only [bxor] at h
      cases hS : S i
      · rw [hS] at h; simp at h; simp [U, h]
      · exact hsub i (List.mem_range.mp hi) hS

theorem clause_zero {v : Nat} (hv : v < n) {C : Clause Nat} (hC : C ∈ vclauses E χ v)
    (g : Poly Nat) {D : Nat} (hgD : g.deg + C.length ≤ D) (hD : D < e) :
    design E.length (coef n E χ) (fun a => g.eval a * (clausePoly C).eval a) = 0 := by
  have e1 : (fun a => g.eval a * (clausePoly C).eval a)
      = fun a => (g.terms.map fun t => t.1 * monoEval a t.2 * (clausePoly C).eval a).sum := by
    funext a; unfold Poly.eval; rw [sum_mul_right]
  rw [e1, design_list]
  apply sum_zero
  intro t ht
  have := (deg_le_iff g g.deg).mp (Nat.le_refl _) t ht
  exact term_zero hn hE hconn hexp hv hC t.1 t.2 (by omega)

omit hn hE hconn hexp in
theorem odd_dvd_pow (p : Nat) (hp : p % 2 = 1) : ∀ N, p ∣ 2 ^ N → p = 1
  | 0, h => Nat.dvd_one.mp h
  | N + 1, h => by
    have hc : Nat.Coprime p 2 := by
      unfold Nat.Coprime; rw [Nat.gcd_comm, Nat.gcd_rec, hp]; rfl
    rw [Nat.pow_succ, Nat.mul_comm] at h
    exact odd_dvd_pow p hp N (Nat.Coprime.dvd_of_dvd_mul_left hc h)

/-- **Grigoriev's Nullstellensatz degree lower bound for Tseitin.** For a connected loopless graph
on `n ≥ 3` vertices whose middle-third vertex sets have `≥ e` boundary edges, and any odd `p > 1`,
the Tseitin formula (any charge) has no Nullstellensatz refutation over `Z/p` of degree `< e`. -/
theorem tseitin_ns_lower (p : Nat) (hp : p % 2 = 1) (hp1 : 1 < p) {D : Nat} (hD : D < e)
    (π : NSRefutation p (Tseitin n E χ) D) : False := by
  let F := Tseitin n E χ
  let N := E.length
  let c := coef n E χ
  let Fs : (Nat → Bool) → Int := fun a =>
    ((List.range F.length).map fun i => (π.g i).eval a * (clausePoly (F.getD i [])).eval a).sum
  -- the design kills the left-hand side
  have hz : design N c Fs = 0 := by
    simp only [Fs]
    rw [design_list]
    apply sum_zero
    intro i hi
    have hi' := List.mem_range.mp hi
    have hget : F.getD i [] = F[i] := by simp [List.getD, List.getElem?_eq_getElem hi']
    rw [hget]
    obtain ⟨v, hv, hCv⟩ := tseitin_mem (List.getElem_mem hi')
    exact clause_zero hn hE hconn hexp hv hCv (π.g i) (π.deg_le i hi') hD
  -- the left-hand side is `1 + p k`
  let k : (Nat → Bool) → Int := fun a => (Fs a - 1) / p
  have hk : ∀ a, Valid N a → Fs a = 1 + p * k a := by
    intro a _
    have h1 := π.identity a
    have h2 : (Fs a - 1) % (p : Int) = 0 := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h1
    have h3 := Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero h2)
    simp only [k]; omega
  rw [design_congr N c Fs (fun a => 1 + p * k a) hk, design_add, design_mul, design_one] at hz
  -- `c ∅ = ±1`
  have h0 : SmallBd n E (fun _ => false) :=
    ⟨fun _ => false, by simp [size], fun i _ => rfl⟩
  have hc0 : c (fun _ => false) * c (fun _ => false) = 1 := by
    simp only [c]; unfold coef; rw [dite_eq_left h0]; exact psg_sq _
  have hdvd : (p : Int) ∣ ((2 ^ N : Nat) : Int) := by
    refine ⟨-(c (fun _ => false) * design N c k), ?_⟩
    rw [Int.natCast_pow, show ((2 : Nat) : Int) = 2 from rfl]
    have : (2 : Int) ^ N = c (fun _ => false) * (c (fun _ => false) * 2 ^ N) := by
      rw [← Int.mul_assoc, hc0, Int.one_mul]
    rw [this]
    have h4 : c (fun _ => false) * 2 ^ N = -(p * design N c k) := by omega
    rw [h4, Int.mul_neg, Int.mul_neg, Int.mul_left_comm]
  have := odd_dvd_pow p hp N (Int.ofNat_dvd.mp hdvd)
  omega

end main2

end Programme.«20261024-1633-proof-complexity».NSTseitin

#print axioms Programme.«20261024-1633-proof-complexity».NSTseitin.tseitin_ns_lower
