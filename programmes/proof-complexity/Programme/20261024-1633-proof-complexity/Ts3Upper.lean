import Programme.«20261024-1633-proof-complexity».NSCover
import Programme.«20261024-1633-proof-complexity».Ts3

/-!
# Mod-3 Tseitin is easy for Nullstellensatz over `F_3`

`ts3_ns_upper`: if the total charge is not divisible by `3` and every vertex has degree `≤ Δ`,
`Δ ≥ 3`, then `Ts3 n E c` has a Nullstellensatz refutation over `F_3` of degree `4Δ`.

Certificate (via `Work.NSCover.cover_ns`): with `y_i = x_{3i+1} + 2 x_{3i+2}` and
`L_v = ∑_{i ∋ v} ±y_i`, put `ψ_v = κ (c_v - L_v)` with `κ = (∑ c) mod 3`. Every edge is counted
once with `+1` and once with `+2`, so `∑_v L_v = 3 ∑_i y_i` and `∑_v ψ_v ≡ κ ∑ c ≡ 1 (mod 3)`;
and if the clauses on the `3 deg v` variables of `v` hold, every incident edge has one value and the
vertex constraint holds, so `3 ∣ ψ_v`.
-/

namespace Programme.«20261024-1633-proof-complexity».Ts3Upper

open Classical Programme.«20261024-1110-proof-complexity».Haken
open Programme.«20261024-1110-proof-complexity».Tseitin
open Programme.«20261024-1633-proof-complexity».NS Programme.«20261024-1633-proof-complexity».NSCover Programme.«20261024-1633-proof-complexity».Ts3 Programme.«20261024-1633-proof-complexity».Z3Design

def bv (b : Bool) : Nat := if b then 1 else 0

/-- The `ℤ₃` value read off the indicators of edge `i` (correct on exactly-one points). -/
def yN (a : Nat → Bool) (i : Nat) : Nat := bv (a (vx i 1)) + 2 * bv (a (vx i 2))

def Wv (E : List (Nat × Nat)) (v : Nat) : List Nat := (inc E v).flatMap fun i => [vx i 0, vx i 1, vx i 2]

def psi (E : List (Nat × Nat)) (c : Nat → Nat) (κ : Int) (v : Nat) (a : Nat → Bool) : Int :=
  κ * ((c v : Int) - (ex E.length (Rd E v) (yN a) : Nat))

theorem mem_Wv {E : List (Nat × Nat)} {v i : Nat} (hi : i ∈ inc E v) (j : Nat) (hj : j < 3) :
    vx i j ∈ Wv E v := by
  unfold Wv; rw [List.mem_flatMap]
  refine ⟨i, hi, ?_⟩
  have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases this with rfl | rfl | rfl <;> simp

theorem len_Wv (E : List (Nat × Nat)) (v : Nat) : (Wv E v).length = 3 * (inc E v).length := by
  unfold Wv
  induction (inc E v) with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons, ih]; simp; omega

theorem ex_congr (N : Nat) (R a b : Nat → Nat) (h : ∀ i, i < N → R i ≠ 0 → a i = b i) :
    ex N R a = ex N R b := by
  rw [ex_eq_sum, ex_eq_sum]; congr 1; apply List.map_congr_left; intro i hi
  by_cases hR : R i = 0
  · simp [hR]
  · rw [h i (List.mem_range.mp hi) hR]

theorem sum_zeroN (l : List Nat) : (l.map fun _ => 0).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]

theorem sum_ind (n t : Nat) (ht : t < n) (k : Nat) :
    ((List.range n).map fun v => if t = v then k else 0).sum = k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases h : t = n
    · subst h
      have : ((List.range t).map fun v => if t = v then k else 0).sum = 0 := by
        rw [List.map_congr_left (g := fun _ => 0) (fun v hv =>
          by rw [ite_eq_right (Nat.ne_of_gt (List.mem_range.mp hv))])]
        exact sum_zeroN _
      simp [this]
    · rw [ih (by omega)]; simp [h]

theorem sum_swapN (l1 l2 : List Nat) (g : Nat → Nat → Nat) :
    (l1.map fun i => (l2.map fun v => g v i).sum).sum =
      (l2.map fun v => (l1.map fun i => g v i).sum).sum := by
  induction l1 with
  | nil => simp only [List.map_nil, List.sum_nil]; exact (sum_zeroN l2).symm
  | cons x l1 ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    clear ih
    induction l2 with
    | nil => simp
    | cons y l2 ih2 => simp only [List.map_cons, List.sum_cons]; omega

theorem sum_mulN (l : List Nat) (f : Nat → Nat) (k : Nat) :
    (l.map fun i => k * f i).sum = k * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem sum_psi (l : List Nat) (κ : Int) (f g : Nat → Nat) :
    (l.map fun v => κ * ((f v : Int) - (g v : Int))).sum =
      κ * (((l.map f).sum : Nat) - ((l.map g).sum : Nat) : Int) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih, Int.natCast_add]
    rw [← Int.mul_add]; congr 1; omega

section
variable {n : Nat} {E : List (Nat × Nat)} {c : Nat → Nat}
  (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2)

include hE in
theorem Rd_sum {i : Nat} (hi : i < E.length) : ((List.range n).map fun v => Rd E v i).sum = 3 := by
  have he : edge E i ∈ E := by simp [edge, List.getElem?_eq_getElem hi]
  obtain ⟨h1, h2, h3⟩ := hE _ he
  have : ((List.range n).map fun v => Rd E v i) = (List.range n).map fun v =>
      (if (edge E i).1 = v then 1 else 0) + (if (edge E i).2 = v then 2 else 0) := by
    apply List.map_congr_left; intro v _
    simp only [Rd, sgn, mem_inc_iff, hi, true_and]
    by_cases a1 : (edge E i).1 = v
    · have : (edge E i).2 ≠ v := fun h => h3 (a1.trans h.symm)
      simp [a1]; omega
    · by_cases a2 : (edge E i).2 = v
      · simp [a1, a2]
      · simp [a1, a2]
  rw [this]
  have hadd : ∀ (l : List Nat) (f g : Nat → Nat),
      (l.map fun v => f v + g v).sum = (l.map f).sum + (l.map g).sum := by
    intro l f g; induction l with
    | nil => simp
    | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; omega
  rw [hadd, sum_ind n _ h1, sum_ind n _ h2]

include hE in
theorem sumL (a : Nat → Bool) :
    ((List.range n).map fun v => ex E.length (Rd E v) (yN a)).sum =
      3 * ((List.range E.length).map (yN a)).sum := by
  simp only [ex_eq_sum]
  rw [← sum_swapN]
  have : ((List.range E.length).map fun i => ((List.range n).map fun v => Rd E v i * yN a i).sum)
      = (List.range E.length).map fun i => 3 * yN a i := by
    apply List.map_congr_left; intro i hi
    have := Rd_sum (n := n) hE (List.mem_range.mp hi)
    have e : ((List.range n).map fun v => Rd E v i * yN a i)
        = (List.range n).map fun v => yN a i * Rd E v i := by
      apply List.map_congr_left; intro v _; exact Nat.mul_comm _ _
    rw [e, sum_mulN, this, Nat.mul_comm]
  rw [this, sum_mulN]

theorem mem_tuples_map (L : List Nat) (f : Nat → Nat) (hf : ∀ i, f i < 3) :
    (L.map fun i => (i, f i)) ∈ tuples L := by
  induction L with
  | nil => simp [tuples]
  | cons x L ih =>
    simp only [tuples, List.map_cons, List.mem_flatMap]
    refine ⟨_, ih, ?_⟩
    have : f x = 0 ∨ f x = 1 ∨ f x = 2 := by have := hf x; omega
    rcases this with h | h | h <;> simp [h]

theorem hzero_ts3 (κ : Int) {v : Nat} (hv : v < n) (a : Nat → Bool)
    (hsat : ∀ C ∈ Ts3 n E c, (∀ l ∈ C, l.var ∈ Wv E v) → Clause.eval a C = true) :
    (3 : Int) ∣ psi E c κ v a := by
  -- every incident edge has exactly one value
  have hec : ∀ i ∈ inc E v, ∀ C ∈ eclauses i, Clause.eval a C = true := by
    intro i hi C hC
    apply hsat
    · simp only [Ts3, List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inl ⟨i, (mem_inc_iff.mp hi).1, hC⟩
    · intro l hl
      simp only [eclauses, List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
        rcases hl with rfl | rfl | rfl <;> exact mem_Wv hi _ (by omega)
  let val : Nat → Nat := fun i => if a (vx i 1) then 1 else if a (vx i 2) then 2 else 0
  have hval : ∀ i ∈ inc E v, yN a i = val i ∧ a (vx i (val i)) = true := by
    intro i hi
    have h := hec i hi
    have c0 := h [⟨vx i 0, true⟩, ⟨vx i 1, true⟩, ⟨vx i 2, true⟩] (by simp [eclauses])
    have c12 := h [⟨vx i 1, false⟩, ⟨vx i 2, false⟩] (by simp [eclauses])
    simp only [Clause.eval, List.any_cons, List.any_nil, Lit.eval] at c0 c12
    simp only [yN, bv, val]
    cases h0 : a (vx i 0) <;> cases h1 : a (vx i 1) <;> cases h2 : a (vx i 2) <;>
      simp_all
  let t := (inc E v).map fun i => (i, val i)
  have ht : t ∈ tuples (inc E v) := mem_tuples_map _ _ (fun i => by simp only [val]; split <;> (try split) <;> omega)
  have hlv : lval E v t % 3 = c v % 3 := by
    apply Classical.byContradiction
    intro hne
    have hC : tclause t ∈ Ts3 n E c := by
      simp only [Ts3, List.mem_append, List.mem_flatMap, List.mem_range, vclauses3, List.mem_map,
        List.mem_filter]
      exact Or.inr ⟨v, hv, t, ⟨ht, by simpa using hne⟩, rfl⟩
    have := hsat _ hC (by
      intro l hl
      simp only [tclause, t, List.map_map, List.mem_map, Function.comp_def] at hl
      obtain ⟨i, hi, rfl⟩ := hl
      exact mem_Wv hi _ (by simp only [val]; split <;> (try split) <;> omega))
    have hf : Clause.eval a (tclause t) = false := by
      unfold Clause.eval
      apply List.any_eq_false.mpr
      intro l hl
      simp only [tclause, t, List.map_map, List.mem_map, Function.comp_def] at hl
      obtain ⟨i, hi, rfl⟩ := hl
      simp [Lit.eval, (hval i hi).2]
    rw [hf] at this; cases this
  have hL : ex E.length (Rd E v) (yN a) = lval E v t := by
    rw [ex_Rd]
    simp only [lval, t, List.map_map, Function.comp_def]
    congr 1; apply List.map_congr_left; intro i hi; rw [(hval i hi).1]
  have h3 : (3 : Int) ∣ ((c v : Int) - (ex E.length (Rd E v) (yN a) : Nat)) := by
    rw [hL]; omega
  obtain ⟨k, hk⟩ := h3
  exact ⟨κ * k, by simp only [psi]; rw [hk, Int.mul_left_comm]⟩

include hE in
/-- **Mod-3 Tseitin has degree-`4Δ` Nullstellensatz refutations over `F_3`** when the total charge
is not divisible by `3` (graph loopless, degrees `≤ Δ`, `Δ ≥ 3`). -/
theorem ts3_ns_upper (Δ : Nat) (hc : ((List.range n).map c).sum % 3 ≠ 0)
    (hΔ : ∀ v, v < n → (inc E v).length ≤ Δ) (h3 : 3 ≤ Δ) :
    Nonempty (NSRefutation 3 (Ts3 n E c) (4 * Δ)) := by
  let κ : Int := (((List.range n).map c).sum % 3 : Nat)
  have hlen : ∀ C ∈ Ts3 n E c, C.length ≤ Δ := by
    intro C hC
    rcases ts3_mem hC with ⟨i, _, hC⟩ | ⟨u, hu, t, ht, _, rfl⟩
    · simp only [eclauses, List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl | rfl | rfl <;> simp <;> omega
    · have : (tclause t).length = (inc E u).length := by
        rw [← (mem_tuples ht).1]; simp [tclause]
      rw [this]; exact hΔ u hu
  apply cover_ns 3 n (4 * Δ) (Ts3 n E c) (Wv E) (psi E c κ)
  · intro v _ a b h
    simp only [psi]
    rw [ex_congr E.length (Rd E v) (yN a) (yN b) (fun i _ hR => by
      have hi : i ∈ inc E v := by
        apply Classical.byContradiction; intro hn; exact hR (by simp [Rd, hn])
      simp only [yN, h _ (mem_Wv hi 1 (by omega)), h _ (mem_Wv hi 2 (by omega))])]
  · intro v hv a hsat; exact hzero_ts3 κ hv a hsat
  · intro a
    simp only [psi]
    rw [sum_psi, sumL hE a]
    simp only [κ]
    have hr : ((List.range n).map c).sum % 3 = 1 ∨ ((List.range n).map c).sum % 3 = 2 := by omega
    generalize ((List.range n).map c).sum = s at hr ⊢
    generalize ((List.range E.length).map (yN a)).sum = Y
    rcases hr with h | h <;> rw [h] <;> simp only [Int.natCast_mul] <;> omega
  · intro v hv C hC _
    have := hlen C hC
    rw [len_Wv]; have := hΔ v hv; omega
  · intro C hC; have := hlen C hC; omega

end

end Programme.«20261024-1633-proof-complexity».Ts3Upper

#print axioms Programme.«20261024-1633-proof-complexity».Ts3Upper.ts3_ns_upper
