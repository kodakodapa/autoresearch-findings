import Programme.«20261024-1633-proof-complexity».Z3Design
import Programme.«20261024-1633-proof-complexity».NSTseitin

/-!
# Mod-3 Tseitin formulas: no low-degree Nullstellensatz refutation over `Z/p`, `3 ∤ p`

`Ts3 n E c`: every edge `i` (an ordered pair `(x, y)` of distinct vertices `< n`) carries a value
`a_i ∈ ℤ₃`, encoded by the indicators `x_{3i}, x_{3i+1}, x_{3i+2}` with exactly-one clauses
(`eclauses`); every vertex `v` requires `∑_{i ∋ v} ±a_i ≡ c_v (mod 3)` (`+` when `v` is the tail
`x`, `-` when it is the head `y`), with one clause per forbidden local tuple (`vclauses3`).

Theorem `ts3_ns_lower` (Buss–Grigoriev–Impagliazzo–Pitassi 2001, the `q = 3` case of their
Tseitin_q bound; NS version): for a connected graph whose middle-third vertex sets have `≥ e`
boundary edges (K3's hypotheses), every `p > 1` with `3 ∤ p` (in particular `p = 2`), any charge,
`Ts3 n E c` has no `NSRefutation p` of degree `D < e`.

Proof: the design `E(h) = ∑_S co(S) ∑_{a ∈ ℤ₃^E} h(a) ω^{⟨S,a⟩}` in `ℤ[ω]` (`Work.Z3Design`),
with `co(∂T) = ω^{-⟨c,T⟩}` for vertex labellings `T : V → ℤ₃` of support `≤ n/3` and `co = 0`
otherwise. It sums only over exactly-one points, so edge clauses vanish; vertex clause terms vanish
by the rotation lemma (`r + s = -c_v + L_v(τ) ≢ 0`); and `E(1) = 3^{|E|}`, not divisible by `p`.
-/

namespace Programme.«20261024-1633-proof-complexity».Ts3

open Classical Programme.«20261024-1110-proof-complexity».Haken
open Programme.«20261024-1110-proof-complexity».Tseitin
open Programme.«20261024-1633-proof-complexity».NS Programme.«20261024-1633-proof-complexity».Z3Design Programme.«20261024-1633-proof-complexity».Z3Design.ZW
open Programme.«20261024-1633-proof-complexity».NSTseitin (monoEval_congr clause_eval_congr sum_mul_right countP_mem_le countP_eq)

/-! ## The formula -/

def vx (i j : Nat) : Nat := 3 * i + j

/-- Exactly one of `x_{3i}, x_{3i+1}, x_{3i+2}`. -/
def eclauses (i : Nat) : List (Clause Nat) :=
  [[⟨vx i 0, true⟩, ⟨vx i 1, true⟩, ⟨vx i 2, true⟩],
   [⟨vx i 0, false⟩, ⟨vx i 1, false⟩], [⟨vx i 0, false⟩, ⟨vx i 2, false⟩],
   [⟨vx i 1, false⟩, ⟨vx i 2, false⟩]]

/-- Coefficient of edge `i` in the constraint of `v`: `1` at the tail, `2 ≡ -1` at the head. -/
def sgn (E : List (Nat × Nat)) (v i : Nat) : Nat := if (edge E i).1 = v then 1 else 2

/-- All assignments `(i, a_i)` of values in `{0,1,2}` to the list `L`. -/
def tuples : List Nat → List (List (Nat × Nat))
  | [] => [[]]
  | i :: l => (tuples l).flatMap fun t => [(i, 0) :: t, (i, 1) :: t, (i, 2) :: t]

def lval (E : List (Nat × Nat)) (v : Nat) (t : List (Nat × Nat)) : Nat :=
  (t.map fun q => sgn E v q.1 * q.2).sum

/-- The clause falsified exactly by the local assignment `t`. -/
def tclause (t : List (Nat × Nat)) : Clause Nat := t.map fun q => ⟨vx q.1 q.2, false⟩

/-- The clauses of vertex `v`: one per local assignment violating `∑ ±a_i ≡ c_v`. -/
def vclauses3 (E : List (Nat × Nat)) (c : Nat → Nat) (v : Nat) : List (Clause Nat) :=
  ((tuples (inc E v)).filter fun t => lval E v t % 3 != c v % 3).map tclause

/-- The mod-3 Tseitin formula of `(0..n-1, E)` with charge `c`. -/
def Ts3 (n : Nat) (E : List (Nat × Nat)) (c : Nat → Nat) : CNF Nat :=
  (List.range E.length).flatMap eclauses ++ (List.range n).flatMap (vclauses3 E c)

/-- The Boolean point of a `ℤ₃` edge assignment. -/
def emb (a : Nat → Nat) : Nat → Bool := fun x => decide (a (x / 3) = x % 3)

theorem vx_div (i j : Nat) (hj : j < 3) : vx i j / 3 = i := by unfold vx; omega
theorem vx_mod (i j : Nat) (hj : j < 3) : vx i j % 3 = j := by unfold vx; omega

theorem emb_vx (a : Nat → Nat) (i j : Nat) (hj : j < 3) : emb a (vx i j) = decide (a i = j) := by
  simp only [emb, vx_div i j hj, vx_mod i j hj]

theorem mem_tuples {L : List Nat} {t : List (Nat × Nat)} (h : t ∈ tuples L) :
    t.map Prod.fst = L ∧ ∀ q ∈ t, q.2 < 3 := by
  induction L generalizing t with
  | nil => simp only [tuples, List.mem_singleton] at h; subst h; simp
  | cons x L ih =>
    simp only [tuples, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
    obtain ⟨t', ht', h⟩ := h
    obtain ⟨h1, h2⟩ := ih ht'
    have key : ∀ j, j < 3 → ((x, j) :: t').map Prod.fst = x :: L ∧
        ∀ q ∈ (x, j) :: t', q.2 < 3 := by
      intro j hj
      refine ⟨by simp [h1], ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with h' | h'
      · rw [h']; exact hj
      · exact h2 q h'
    rcases h with rfl | rfl | rfl
    · exact key 0 (by omega)
    · exact key 1 (by omega)
    · exact key 2 (by omega)

theorem ts3_mem {n : Nat} {E : List (Nat × Nat)} {c : Nat → Nat} {C : Clause Nat}
    (h : C ∈ Ts3 n E c) :
    (∃ i, i < E.length ∧ C ∈ eclauses i) ∨
    (∃ v, v < n ∧ ∃ t ∈ tuples (inc E v), lval E v t % 3 ≠ c v % 3 ∧ C = tclause t) := by
  simp only [Ts3, List.mem_append, List.mem_flatMap, List.mem_range] at h
  rcases h with ⟨i, hi, hC⟩ | ⟨v, hv, hC⟩
  · exact Or.inl ⟨i, hi, hC⟩
  · right
    simp only [vclauses3, List.mem_map, List.mem_filter] at hC
    obtain ⟨t, ⟨ht, hl⟩, rfl⟩ := hC
    exact ⟨v, hv, t, ht, by simpa using hl, rfl⟩

def Valid3' := Valid3

theorem eclause_zero {N : Nat} {a : Nat → Nat} (ha : Valid3 N a) {i : Nat} (hi : i < N)
    {C : Clause Nat} (hC : C ∈ eclauses i) : (clausePoly C).eval (emb a) = 0 := by
  rw [clausePoly_eval]
  have h3 := ha.1 i hi
  simp only [eclauses, List.mem_cons, List.not_mem_nil, or_false] at hC
  have : a i = 0 ∨ a i = 1 ∨ a i = 2 := by omega
  rcases hC with rfl | rfl | rfl | rfl <;>
    simp only [Clause.eval, List.any_cons, List.any_nil, Lit.eval, emb_vx a i _ (by decide : 0 < 3),
      emb_vx a i _ (by decide : 1 < 3), emb_vx a i _ (by decide : 2 < 3)] <;>
    rcases this with h | h | h <;> simp [h]

theorem tclause_eval (a : Nat → Nat) (t : List (Nat × Nat)) (ht : ∀ q ∈ t, q.2 < 3) :
    (clausePoly (tclause t)).eval (emb a) = if (∀ q ∈ t, a q.1 = q.2) then 1 else 0 := by
  rw [clausePoly_eval]
  have : Clause.eval (emb a) (tclause t) = !decide (∀ q ∈ t, a q.1 = q.2) := by
    induction t with
    | nil => simp [tclause, Clause.eval]
    | cons q t ih =>
      have hq := ht q List.mem_cons_self
      have ih' := ih (fun q' hq' => ht q' (List.mem_cons_of_mem _ hq'))
      simp only [tclause, List.map_cons, Clause.eval, List.any_cons] at ih' ⊢
      rw [ih']
      simp only [Lit.eval, emb_vx a q.1 q.2 hq, List.mem_cons, forall_eq_or_imp]
      by_cases h1 : a q.1 = q.2 <;> simp [h1]
  rw [this]
  by_cases h : ∀ q ∈ t, a q.1 = q.2
  · rw [ite_eq_left h, decide_eq_true h]; rfl
  · rw [ite_eq_right h, decide_eq_false h]; rfl

/-! ## The design coefficient -/

def supp (T : Nat → Nat) : Nat → Bool := fun w => T w != 0

def BdOf3 (E : List (Nat × Nat)) (T S : Nat → Nat) : Prop :=
  ∀ i, i < E.length → S i = (T (edge E i).1 + 2 * T (edge E i).2) % 3

def SmallBd3 (n : Nat) (E : List (Nat × Nat)) (S : Nat → Nat) : Prop :=
  ∃ T : Nat → Nat, (∀ w, T w < 3) ∧ size n (supp T) ≤ n / 3 ∧ BdOf3 E T S

def chT3 (n : Nat) (c T : Nat → Nat) : Nat := ((List.range n).map fun w => c w * T w).sum

/-- `ω^{-⟨c,T⟩} = ω^{2⟨c,T⟩}` if `S = ∂T` with `|supp T| ≤ n/3`, else `0`. -/
noncomputable def co3 (n : Nat) (E : List (Nat × Nat)) (c : Nat → Nat) (S : Nat → Nat) :
    Option Nat :=
  if h : SmallBd3 n E S then some (2 * chT3 n c (Classical.choose h)) else none

/-- The constraint vector of `v`. -/
def Rd (E : List (Nat × Nat)) (v : Nat) : Nat → Nat := fun i => if i ∈ inc E v then sgn E v i else 0

theorem Rd_lt (E : List (Nat × Nat)) (v i : Nat) : Rd E v i < 3 := by
  unfold Rd sgn; split
  · split <;> omega
  · omega

theorem mem_inc_iff {E : List (Nat × Nat)} {v i : Nat} :
    i ∈ inc E v ↔ i < E.length ∧ ((edge E i).1 = v ∨ (edge E i).2 = v) := by
  unfold inc; simp [List.mem_filter, List.mem_range]

theorem Rd_valid (E : List (Nat × Nat)) (v : Nat) : Valid3 E.length (Rd E v) := by
  constructor
  · intro i _; exact Rd_lt E v i
  · intro i hi; unfold Rd; rw [ite_eq_right]; intro h; have := (mem_inc_iff.mp h).1; omega

theorem chT3_congr (n : Nat) (c T1 T2 : Nat → Nat) (h : ∀ w, w < n → T1 w = T2 w) :
    chT3 n c T1 = chT3 n c T2 := by
  unfold chT3; congr 1; apply List.map_congr_left; intro w hw; rw [h w (List.mem_range.mp hw)]

theorem chT3_zero (n : Nat) (c : Nat → Nat) : chT3 n c (fun _ => 0) = 0 := by
  unfold chT3
  induction n with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp

section comb
variable {n : Nat} {E : List (Nat × Nat)} {c : Nat → Nat}

/-- Two small labellings with the same boundary agree (connectivity). -/
theorem bd3_unique (hn : 1 ≤ n)
    (hconn : ∀ S : Nat → Bool, 0 < size n S → size n S < n → bd E S ≠ [])
    {T1 T2 S : Nat → Nat} (v1 : ∀ w, T1 w < 3) (v2 : ∀ w, T2 w < 3)
    (h1 : size n (supp T1) ≤ n / 3) (h2 : size n (supp T2) ≤ n / 3)
    (b1 : BdOf3 E T1 S) (b2 : BdOf3 E T2 S) : ∀ w, w < n → T1 w = T2 w := by
  let X : Nat → Bool := fun w => (T1 w + 2 * T2 w) % 3 != 0
  have hsz : size n X ≤ size n (supp T1) + size n (supp T2) := by
    have := size_union (n := n) (supp T1) (supp T2)
    have : size n X ≤ size n (fun w => supp T1 w || supp T2 w) := by
      unfold size; apply List.countP_mono_left; intro w _ h
      simp only [X, supp, bne_iff_ne, ne_eq, Bool.or_eq_true] at h ⊢
      omega
    omega
  have hbd : bd E X = [] := by
    unfold bd; rw [List.filter_eq_nil_iff]
    intro i hi
    have hi' := List.mem_range.mp hi
    have e1 := b1 i hi'; have e2 := b2 i hi'
    rw [e1] at e2
    have w1 := v1 (edge E i).1; have w2 := v1 (edge E i).2
    have w3 := v2 (edge E i).1; have w4 := v2 (edge E i).2
    have key : (T1 (edge E i).1 + 2 * T2 (edge E i).1) % 3
        = (T1 (edge E i).2 + 2 * T2 (edge E i).2) % 3 := by omega
    simp only [X, key, bne_self_eq_false, Bool.false_eq_true, not_false_eq_true]
  have h0 : size n X = 0 := by
    apply Classical.byContradiction; intro h
    exact hconn X (by omega) (by omega) hbd
  intro w hw
  have := List.countP_eq_zero.mp h0 w (List.mem_range.mpr hw)
  simp only [X, bne_iff_ne, ne_eq, Classical.not_not] at this
  have := v1 w; have := v2 w
  omega

/-- The boundary of a labelling has at least as many nonzero entries as its support has
boundary edges. -/
theorem bd_le {T S : Nat → Nat} (vT : ∀ w, T w < 3) (b : BdOf3 E T S) :
    (bd E (supp T)).length ≤ (List.range E.length).countP (fun i => S i != 0) := by
  unfold bd; rw [← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro i hi h
  rw [b i (List.mem_range.mp hi)]
  have h1 := vT (edge E i).1; have h2 := vT (edge E i).2
  simp only [supp] at h ⊢
  revert h h1 h2
  generalize T (edge E i).1 = x; generalize T (edge E i).2 = y
  intro h h1 h2
  have hx : x = 0 ∨ x = 1 ∨ x = 2 := by omega
  have hy : y = 0 ∨ y = 1 ∨ y = 2 := by omega
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp at h ⊢

theorem sum_mod3 (l : List Nat) (c T d : Nat → Nat) :
    (l.map fun w => c w * ((T w + d w) % 3)).sum % 3
      = ((l.map fun w => c w * T w).sum + (l.map fun w => c w * d w).sum) % 3 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := mul_mod3 (c x) (T x + d x)
    rw [Nat.mul_add] at h1
    omega

theorem sum_single3 (n v k : Nat) (c : Nat → Nat) (hv : v < n) :
    ((List.range n).map fun w => c w * if w = v then k else 0).sum = c v * k := by
  have : ∀ m, ((List.range m).map fun w => c w * if w = v then k else 0).sum
      = if v < m then c v * k else 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      by_cases h : m = v
      · subst h; simp
      · rw [ite_eq_right h, Nat.mul_zero, Nat.add_zero]
        by_cases h2 : v < m
        · rw [ite_eq_left h2, ite_eq_left (by omega)]
        · rw [ite_eq_right h2, ite_eq_right (by omega)]
  rw [this, ite_eq_left hv]

/-- Adding `k · 1_v` to a labelling adds `k · R_v` to its boundary and `k c_v` to its charge. -/
theorem step3 (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2) {v : Nat} (hv : v < n) (k : Nat)
    (_hk : k < 3) {T X : Nat → Nat} (vT : ∀ w, T w < 3) (hb : BdOf3 E T X) :
    (∀ w, (T w + (if w = v then k else 0)) % 3 < 3) ∧
    BdOf3 E (fun w => (T w + (if w = v then k else 0)) % 3)
      (ashift X (fun i => k * Rd E v i % 3)) ∧
    size n (supp (fun w => (T w + (if w = v then k else 0)) % 3)) ≤ size n (supp T) + 1 ∧
    chT3 n c (fun w => (T w + (if w = v then k else 0)) % 3) % 3
      = (chT3 n c T + c v * k) % 3 := by
  refine ⟨fun w => Nat.mod_lt _ (by omega), ?_, ?_, ?_⟩
  · intro i hi
    have hne := (hE _ (edge_mem hi)).2.2
    simp only [ashift, hb i hi, Rd, sgn, mem_inc_iff]
    have := vT (edge E i).1; have := vT (edge E i).2
    generalize (edge E i).1 = x at hne ⊢; generalize (edge E i).2 = y at hne ⊢
    by_cases hx : x = v <;> by_cases hy : y = v
    · omega
    · subst hx; simp only [hy, ite_true, ite_false, true_or, and_true, hi, Nat.add_zero,
        Nat.mul_one]; omega
    · subst hy; simp only [hx, ite_true, ite_false, or_true, and_true, hi, Nat.add_zero]; omega
    · simp only [hx, hy, ite_false, or_self, and_false, Nat.add_zero, Nat.mul_zero]; omega
  · have h1 := size_union (n := n) (supp T) (fun w => w == v)
    have h2 : size n (supp (fun w => (T w + (if w = v then k else 0)) % 3))
        ≤ size n (fun w => supp T w || (w == v)) := by
      unfold size; apply List.countP_mono_left; intro w _ h
      simp only [supp, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq] at h ⊢
      by_cases hw : w = v
      · exact Or.inr hw
      · rw [ite_eq_right hw] at h; left; omega
    have h3 := countP_eq n v
    unfold size at h1 h2 ⊢
    rw [ite_eq_left hv] at h3
    omega
  · unfold chT3
    rw [sum_mod3, sum_single3 n v k c hv]

end comb

section coef
variable {n : Nat} {E : List (Nat × Nat)} {c : Nat → Nat}
  (hn : 3 ≤ n) (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2)
  (hconn : ∀ S : Nat → Bool, 0 < size n S → size n S < n → bd E S ≠ [])
  {e : Nat}
  (hexp : ∀ S : Nat → Bool, n / 3 < size n S → size n S ≤ 2 * (n / 3) → e ≤ (bd E S).length)
include hn hE hconn hexp

omit hconn in
/-- A step from a small boundary stays small while the boundary has `< e` nonzero entries. -/
theorem small_step {v : Nat} (hv : v < n) (k : Nat) (hk : k < 3) {X : Nat → Nat}
    (hX : SmallBd3 n E X)
    (hc : (List.range E.length).countP (fun i => ashift X (fun i => k * Rd E v i % 3) i != 0) < e) :
    ∃ T : Nat → Nat, (∀ w, T w < 3) ∧ size n (supp T) ≤ n / 3 ∧
      BdOf3 E T (ashift X (fun i => k * Rd E v i % 3)) ∧
      chT3 n c T % 3 = (chT3 n c (Classical.choose hX) + c v * k) % 3 := by
  obtain ⟨vT, hT, hb⟩ := Classical.choose_spec hX
  obtain ⟨v', b', s', c'⟩ := step3 (c := c) hE hv k hk vT hb
  have hsz : size n (supp (fun w => (Classical.choose hX w + if w = v then k else 0) % 3))
      ≤ n / 3 := by
    apply Classical.byContradiction; intro h
    have := hexp (supp (fun w => (Classical.choose hX w + if w = v then k else 0) % 3))
      (by omega) (by omega)
    have := bd_le v' b'
    omega
  exact ⟨_, v', hsz, b', c'⟩

theorem coef_step3 {v : Nat} (hv : v < n) (X : Nat → Nat) (hX : Valid3 E.length X)
    (hc1 : (List.range E.length).countP (fun i => X i != 0) < e)
    (hc2 : (List.range E.length).countP (fun i => ashift X (Rd E v) i != 0) < e) (z : ZW) :
    cm (co3 n E c (ashift X (Rd E v))) z = rotN (2 * c v) (cm (co3 n E c X) z) := by
  have r1 : (fun i => 1 * Rd E v i % 3) = Rd E v := by
    funext i; have := Rd_lt E v i; omega
  by_cases hs : SmallBd3 n E X
  · have hc2' := hc2; rw [← r1] at hc2'
    obtain ⟨T, vT, hT, hb, hch⟩ := small_step (c := c) hn hE hexp hv 1 (by omega) hs hc2'
    rw [r1] at hb
    have hs' : SmallBd3 n E (ashift X (Rd E v)) := ⟨T, vT, hT, hb⟩
    unfold co3
    rw [dite_eq_left hs', dite_eq_left hs]
    simp only [cm, rotN_rotN]
    obtain ⟨vT2, hT2, hb2⟩ := Classical.choose_spec hs'
    have heq := chT3_congr n c _ _ (bd3_unique (by omega) hconn vT2 vT hT2 hT hb2 hb)
    rw [rotN_mod, rotN_mod (2 * c v + _)]
    congr 1
    rw [heq]; omega
  · by_cases hs' : SmallBd3 n E (ashift X (Rd E v))
    · exfalso
      have back : ashift (ashift X (Rd E v)) (fun i => 2 * Rd E v i % 3) = X := by
        funext i
        simp only [ashift]
        have := Rd_lt E v i
        by_cases hi : i < E.length
        · have := hX.1 i hi; omega
        · rw [hX.2 i (by omega), (Rd_valid E v).2 i (by omega)]
      have hc1' : (List.range E.length).countP
          (fun i => ashift (ashift X (Rd E v)) (fun i => 2 * Rd E v i % 3) i != 0) < e := by
        rw [back]; exact hc1
      obtain ⟨T, vT, hT, hb, _⟩ := small_step (c := c) hn hE hexp hv 2 (by omega) hs' hc1'
      rw [back] at hb
      exact hs ⟨T, vT, hT, hb⟩
    · unfold co3; rw [dite_eq_right hs, dite_eq_right hs']; simp only [cm, rotN_zero]

end coef

/-! ## Each vertex-clause term is annihilated -/

theorem ex_eq_sum (N : Nat) (R a : Nat → Nat) :
    ex N R a = ((List.range N).map fun i => R i * a i).sum := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ex, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega

theorem sum_filter_ite (l : List Nat) (P : Nat → Bool) (f a : Nat → Nat) :
    (l.map fun i => (if P i then f i else 0) * a i).sum = ((l.filter P).map fun i => f i * a i).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    by_cases h : P x
    · simp [h, ih]
    · simp [h, ih]

theorem ex_Rd (E : List (Nat × Nat)) (v : Nat) (a : Nat → Nat) :
    ex E.length (Rd E v) a = ((inc E v).map fun i => sgn E v i * a i).sum := by
  rw [ex_eq_sum]
  have : ((List.range E.length).map fun i => Rd E v i * a i)
      = ((List.range E.length).map fun i =>
          (if ((edge E i).1 == v || (edge E i).2 == v) then sgn E v i else 0) * a i) := by
    apply List.map_congr_left; intro i hi
    have hi' := List.mem_range.mp hi
    simp only [Rd, mem_inc_iff, hi', true_and]
    by_cases h : (edge E i).1 = v ∨ (edge E i).2 = v
    · rw [ite_eq_left h, ite_eq_left (by simpa using h)]
    · rw [ite_eq_right h, ite_eq_right (by simpa using h)]
  rw [this, sum_filter_ite]; rfl

theorem countP_union_le (N : Nat) (L m : List Nat) :
    (List.range N).countP (fun i => decide (i ∈ L ∨ i ∈ m)) ≤ L.length + m.length := by
  have h1 := size_union (n := N) (fun i => decide (i ∈ L)) (fun i => decide (i ∈ m))
  have h2 := countP_mem_le N L
  have h3 := countP_mem_le N m
  unfold size at h1
  have : (List.range N).countP (fun i => decide (i ∈ L ∨ i ∈ m))
      = (List.range N).countP (fun i => decide (i ∈ L) || decide (i ∈ m)) := by
    apply List.countP_congr; intro i _; simp
  omega

section main
variable {n : Nat} {E : List (Nat × Nat)} {c : Nat → Nat}
  (hn : 3 ≤ n) (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2)
  (hconn : ∀ S : Nat → Bool, 0 < size n S → size n S < n → bd E S ≠ [])
  {e : Nat}
  (hexp : ∀ S : Nat → Bool, n / 3 < size n S → size n S ≤ 2 * (n / 3) → e ≤ (bd E S).length)
include hn hE hconn hexp

theorem term_zero3 {v : Nat} (hv : v < n) {t : List (Nat × Nat)} (ht : t ∈ tuples (inc E v))
    (hl : lval E v t % 3 ≠ c v % 3) (κ : Int) (m : List Nat)
    (hD : m.length + (inc E v).length < e) :
    design3 E.length (co3 n E c)
      (fun a => κ * monoEval (emb a) m * (clausePoly (tclause t)).eval (emb a)) = zero := by
  obtain ⟨hfst, h3⟩ := mem_tuples ht
  let U : Nat → Bool := fun i => decide (i ∈ inc E v ∨ i ∈ m.map (· / 3))
  have hUc : (List.range E.length).countP U < e := by
    have := countP_union_le E.length (inc E v) (m.map (· / 3))
    simp only [List.length_map] at this
    exact Nat.lt_of_le_of_lt this (by omega)
  apply design3_zero E.length (Rd E v) U (2 * c v) (lval E v t) (co3 n E c) _ (Rd_valid E v)
  · intro i hi hR
    simp only [U, decide_eq_true_eq]; left
    apply Classical.byContradiction; intro h
    exact hR (by simp [Rd, h])
  · omega
  · intro a ha
    rw [tclause_eval a t h3]
    by_cases hall : ∀ q ∈ t, a q.1 = q.2
    · right
      rw [ex_Rd, ← hfst, List.map_map]
      unfold lval
      congr 2
      apply List.map_congr_left; intro q hq
      simp only [Function.comp, hall q hq]
    · left; rw [ite_eq_right hall, Int.mul_zero]
  · intro a ha e' he' hUe
    simp only [U, decide_eq_false_iff_not, not_or] at hUe
    have hemb : ∀ x, x / 3 ≠ e' → emb (ashift a (fun i => if i = e' then 1 else 0)) x = emb a x := by
      intro x hx
      simp only [emb, ashift, ite_eq_right hx, Nat.add_zero]
      have := ha.1 (x / 3)
      by_cases hN : x / 3 < E.length
      · rw [Nat.mod_eq_of_lt (this hN)]
      · rw [ha.2 _ (by omega)]
    have hm : monoEval (emb (ashift a (fun i => if i = e' then 1 else 0))) m = monoEval (emb a) m :=
      monoEval_congr _ _ m (fun x hx => hemb x (fun h => hUe.2 (List.mem_map.mpr ⟨x, hx, h⟩)))
    have hC : (clausePoly (tclause t)).eval (emb (ashift a (fun i => if i = e' then 1 else 0)))
        = (clausePoly (tclause t)).eval (emb a) := by
      rw [clausePoly_eval, clausePoly_eval, clause_eval_congr]
      intro l hl
      simp only [tclause, List.mem_map] at hl
      obtain ⟨q, hq, rfl⟩ := hl
      apply hemb
      rw [vx_div _ _ (h3 q hq)]
      intro h; apply hUe.1; rw [← h, ← hfst]; exact List.mem_map_of_mem hq
    simp only [hm, hC]
  · intro S hS hSU z
    apply coef_step3 hn hE hconn hexp hv S hS
    · apply Nat.lt_of_le_of_lt _ hUc
      apply List.countP_mono_left; intro i hi h
      exact hSU i (List.mem_range.mp hi) (by simpa using h)
    · apply Nat.lt_of_le_of_lt _ hUc
      apply List.countP_mono_left; intro i hi h
      have hi' := List.mem_range.mp hi
      by_cases hS0 : S i = 0
      · simp only [U, decide_eq_true_eq]; left
        apply Classical.byContradiction; intro hn'
        simp [ashift, hS0, Rd, hn'] at h
      · exact hSU i hi' hS0

omit hn hE hconn hexp in
theorem coprime3_dvd_pow (p : Nat) (hp : p % 3 ≠ 0) : ∀ N, p ∣ 3 ^ N → p = 1
  | 0, h => Nat.dvd_one.mp h
  | N + 1, h => by
    have hc : Nat.Coprime p 3 := by
      unfold Nat.Coprime; rw [Nat.gcd_comm, Nat.gcd_rec]
      have : p % 3 = 1 ∨ p % 3 = 2 := by omega
      rcases this with h1 | h1 <;> rw [h1] <;> rfl
    rw [Nat.pow_succ, Nat.mul_comm] at h
    exact coprime3_dvd_pow p hp N (Nat.Coprime.dvd_of_dvd_mul_left hc h)

/-- **Mod-3 Tseitin is hard for Nullstellensatz over `Z/p`, `3 ∤ p`.** For a connected loopless
graph on `n ≥ 3` vertices whose middle-third vertex sets have `≥ e` boundary edges, every `p > 1`
not divisible by `3`, and any charge, `Ts3 n E c` has no Nullstellensatz refutation over `Z/p` of
degree `< e`. -/
theorem ts3_ns_lower (p : Nat) (hp : p % 3 ≠ 0) (hp1 : 1 < p) {D : Nat} (hD : D < e)
    (π : NSRefutation p (Ts3 n E c) D) : False := by
  let F := Ts3 n E c
  let N := E.length
  let co := co3 n E c
  let Fs : (Nat → Bool) → Int := fun b =>
    ((List.range F.length).map fun i => (π.g i).eval b * (clausePoly (F.getD i [])).eval b).sum
  have hz : design3 N co (fun a => Fs (emb a)) = zero := by
    simp only [Fs]
    apply design3_list
    intro i hi
    have hi' := List.mem_range.mp hi
    have hget : F.getD i [] = F[i] := by simp [List.getD, List.getElem?_eq_getElem hi']
    rw [hget]
    have hdeg := π.deg_le i hi'
    rcases ts3_mem (List.getElem_mem hi') with ⟨j, hj, hCj⟩ | ⟨v, hv, t, ht, hl, hCt⟩
    · rw [design3_congr N co _ (fun a => 0 * 0) (fun a ha => by
        rw [eclause_zero ha hj hCj, Int.mul_zero, Int.mul_zero])]
      rw [design3_smul]; exact eq_of (by simp [smul, zero]) (by simp [smul, zero])
    · rw [hCt] at hdeg ⊢
      have hlen : (tclause t).length = (inc E v).length := by
        rw [← (mem_tuples ht).1]; simp [tclause]
      have e1 : (fun a => (π.g i).eval (emb a) * (clausePoly (tclause t)).eval (emb a))
          = fun a => ((π.g i).terms.map fun s =>
              s.1 * monoEval (emb a) s.2 * (clausePoly (tclause t)).eval (emb a)).sum := by
        funext a; unfold Poly.eval; rw [sum_mul_right]
      rw [e1]
      apply design3_list
      intro s hs
      have := (deg_le_iff (π.g i) (π.g i).deg).mp (Nat.le_refl _) s hs
      exact term_zero3 hn hE hconn hexp hv ht hl s.1 s.2 (by omega)
  -- the left-hand side is `1 + p k`
  let k : (Nat → Nat) → Int := fun a => (Fs (emb a) - 1) / p
  have hk : ∀ a, Valid3 N a → Fs (emb a) = 1 + p * k a := by
    intro a _
    have h1 := π.identity (emb a)
    have h2 : (Fs (emb a) - 1) % (p : Int) = 0 := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h1
    have h3 := Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero h2)
    simp only [k]; omega
  rw [design3_congr N co _ (fun a => 1 + p * k a) hk, design3_add, design3_smul, design3_one] at hz
  -- `co(0) = ω^0`
  have hs0 : size n (supp (fun _ => 0)) = 0 :=
    List.countP_eq_zero.mpr (fun w _ => by simp [supp])
  have h0 : SmallBd3 n E (fun _ => 0) :=
    ⟨fun _ => 0, fun _ => (by decide : 0 < 3), by omega, fun i _ => rfl⟩
  have hc0 : ∀ z, cm (co (fun _ => 0)) z = z := by
    intro z
    simp only [co, co3]; rw [dite_eq_left h0]
    obtain ⟨vT, hT, hb⟩ := Classical.choose_spec h0
    have := chT3_congr n c _ (fun _ => 0)
      (bd3_unique (by omega) hconn vT (fun _ => (by decide : 0 < 3)) hT (by omega) hb
        (fun i _ => rfl))
    simp only [cm]; rw [this]
    have : chT3 n c (fun _ => 0) = 0 := chT3_zero n c
    rw [this]; rfl
  rw [hc0] at hz
  have hx := congrArg ZW.x hz
  simp only [ZW.add, smul, zero] at hx
  have hdvd : (p : Int) ∣ ((3 ^ N : Nat) : Int) := by
    refine ⟨-(design3 N co k).x, ?_⟩
    rw [Int.natCast_pow, show ((3 : Nat) : Int) = 3 from rfl, Int.mul_neg]; omega
  have := coprime3_dvd_pow p hp N (Int.ofNat_dvd.mp hdvd)
  omega

end main

end Programme.«20261024-1633-proof-complexity».Ts3

#print axioms Programme.«20261024-1633-proof-complexity».Ts3.ts3_ns_lower
