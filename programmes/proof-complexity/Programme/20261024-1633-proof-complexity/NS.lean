import Programme.«20261024-1110-proof-complexity».Tseitin

/-!
# Nullstellensatz refutations over `Z/p` and the degree-Δ refutation of Tseitin over `F_2`

Polynomials are lists of integer-coefficient monomials over variables `V`; a clause `C` is encoded
as the polynomial `f_C = ∏_{x ∈ C} (1 - x) · ∏_{¬x ∈ C} x`, which is `1` exactly on the Boolean
assignments falsifying `C` (`clausePoly_eval`).

`NSRefutation p F D`: polynomials `g_i`, one per clause `F[i]`, with `deg g_i + |F[i]| ≤ D` and
`∑_i g_i(a) f_{F[i]}(a) ≡ 1 (mod p)` for every Boolean assignment `a`. Since a multilinear
polynomial vanishing on `{0,1}^V` mod `p` is zero over `F_p`, this is the usual Nullstellensatz
identity `∑ g_i f_i + ∑ h_j (x_j^2 - x_j) = 1` over `F_p` with `deg (g_i f_i) ≤ D` (the `h_j`
come from multilinearising, of degree `≤ D`); `|F[i]|` bounds `deg f_{F[i]}`.

Theorem `tseitin_ns2`: for a graph on `0..n-1` without loops (edge list `E`, endpoints `< n`) and a
charge `χ` with `∑_{v<n} χ v` odd, the library Tseitin formula `Tseitin n E χ` has a Nullstellensatz
refutation over `F_2` of degree `Δ` whenever every vertex has at most `Δ` incident edges; every
`g_i` is the constant `1`. Reason: `∑_C f_C(a)` counts the vertices whose parity constraint `a`
violates, and that count is `≡ ∑_v (deg_a v + χ v) ≡ 2·#{true edges} + ∑ χ ≡ 1 (mod 2)`.
-/

namespace Programme.«20261024-1633-proof-complexity».NS

open Classical Programme.«20261024-1110-proof-complexity».Haken
open Programme.«20261024-1110-proof-complexity».Tseitin

/-! ## Polynomials -/

structure Poly (V : Type) where
  terms : List (Int × List V)

variable {V : Type}

def monoEval (a : V → Bool) (m : List V) : Int := (m.map fun v => if a v then (1 : Int) else 0).prod

def Poly.eval (a : V → Bool) (P : Poly V) : Int := (P.terms.map fun t => t.1 * monoEval a t.2).sum

def Poly.deg (P : Poly V) : Nat := (P.terms.map fun t => t.2.length).foldr max 0

def Poly.one : Poly V := ⟨[(1, [])]⟩

def Poly.mulVar (x : V) (P : Poly V) : Poly V := ⟨P.terms.map fun t => (t.1, x :: t.2)⟩

def Poly.sub (P Q : Poly V) : Poly V := ⟨P.terms ++ Q.terms.map fun t => (-t.1, t.2)⟩

/-- `f_C`: the product of `1 - x` over positive literals `x` and `x` over negative literals. -/
def clausePoly : Clause V → Poly V
  | [] => Poly.one
  | l :: C => if l.pos then (clausePoly C).sub ((clausePoly C).mulVar l.var)
              else (clausePoly C).mulVar l.var

/-- A Nullstellensatz refutation of `F` over `Z/p` of degree at most `D`. -/
structure NSRefutation (p : Nat) (F : CNF V) (D : Nat) where
  g : Nat → Poly V
  deg_le : ∀ i (h : i < F.length), (g i).deg + F[i].length ≤ D
  identity : ∀ a : V → Bool,
    ((List.range F.length).map fun i => (g i).eval a * (clausePoly (F.getD i [])).eval a).sum
      % (p : Int) = 1 % (p : Int)

/-! ## Evaluation and degree lemmas -/

theorem eval_one (a : V → Bool) : (Poly.one : Poly V).eval a = 1 := by
  simp [Poly.one, Poly.eval, monoEval]

theorem deg_one : (Poly.one : Poly V).deg = 0 := by simp [Poly.one, Poly.deg]

theorem eval_mulVar (a : V → Bool) (x : V) (P : Poly V) :
    (P.mulVar x).eval a = (if a x then 1 else 0) * P.eval a := by
  unfold Poly.mulVar Poly.eval
  simp only [List.map_map]
  induction P.terms with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, Function.comp, monoEval, List.prod_cons]
    rw [Int.mul_add]; congr 1
    rw [← Int.mul_assoc, Int.mul_comm t.1, Int.mul_assoc]

theorem eval_sub (a : V → Bool) (P Q : Poly V) : (P.sub Q).eval a = P.eval a - Q.eval a := by
  unfold Poly.sub Poly.eval
  simp only [List.map_append, List.sum_append, List.map_map]
  suffices h : ∀ l : List (Int × List V),
      (l.map ((fun t => t.1 * monoEval a t.2) ∘ fun t => (-t.1, t.2))).sum
        = -(l.map fun t => t.1 * monoEval a t.2).sum by
    rw [h]; omega
  intro l
  induction l with
  | nil => simp
  | cons t ts ih => simp only [List.map_cons, List.sum_cons, ih, Function.comp, Int.neg_mul]; omega

theorem foldr_max_le (l : List Nat) (d : Nat) : l.foldr max 0 ≤ d ↔ ∀ x ∈ l, x ≤ d := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.foldr_cons, Nat.max_le, ih, List.mem_cons, forall_eq_or_imp]

theorem deg_le_iff (P : Poly V) (d : Nat) : P.deg ≤ d ↔ ∀ t ∈ P.terms, t.2.length ≤ d := by
  unfold Poly.deg; rw [foldr_max_le]
  constructor
  · intro h t ht; exact h _ (List.mem_map_of_mem ht)
  · intro h x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    exact h t ht

theorem deg_mulVar (x : V) (P : Poly V) : (P.mulVar x).deg ≤ P.deg + 1 := by
  rw [deg_le_iff]
  intro t ht
  simp only [Poly.mulVar, List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  have := (deg_le_iff P P.deg).mp (Nat.le_refl _) s hs
  simp; omega

theorem deg_sub (P Q : Poly V) (d : Nat) (hP : P.deg ≤ d) (hQ : Q.deg ≤ d) : (P.sub Q).deg ≤ d := by
  rw [deg_le_iff] at *
  intro t ht
  simp only [Poly.sub, List.mem_append, List.mem_map] at ht
  rcases ht with ht | ⟨s, hs, rfl⟩
  · exact hP t ht
  · exact hQ s hs

theorem clausePoly_eval (a : V → Bool) (C : Clause V) :
    (clausePoly C).eval a = if C.eval a then 0 else 1 := by
  induction C with
  | nil => simp [clausePoly, eval_one, Clause.eval]
  | cons l C ih =>
    have e : Clause.eval a (l :: C) = (l.eval a || Clause.eval a C) := by
      simp only [Clause.eval, List.any_cons]
    rw [e]
    unfold clausePoly
    cases hp : l.pos <;> cases hx : a l.var <;> cases hC : Clause.eval a C <;>
      simp [eval_sub, eval_mulVar, ih, hC, hx, Lit.eval, hp]

theorem clausePoly_deg (C : Clause V) : (clausePoly C).deg ≤ C.length := by
  induction C with
  | nil => simp [clausePoly, deg_one]
  | cons l C ih =>
    unfold clausePoly
    have h1 := deg_mulVar l.var (clausePoly C)
    split
    · exact deg_sub _ _ _ (by simp; omega) (by simp; omega)
    · simp; omega

/-! ## Counting lemmas -/

theorem range_map_getD {α β} (l : List α) (d : α) (f : α → β) :
    (List.range l.length).map (fun i => f (l.getD i d)) = l.map f := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp at h2
    simp [List.getD, List.getElem?_eq_getElem h2]

theorem sum_indicator (a : V → Bool) (l : List (Clause V)) :
    (l.map fun C => (clausePoly C).eval a).sum = ((l.countP fun C => !C.eval a : Nat) : Int) := by
  induction l with
  | nil => simp
  | cons C l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons, clausePoly_eval]
    cases h : Clause.eval a C <;> (try simp) <;> (try omega)

/-- Exactly one clause of `signs L` is falsified by `α`. -/
theorem signs_false (α : Nat → Bool) (L : List Nat) :
    (signs L).countP (fun c => !c.eval α) = 1 := by
  induction L with
  | nil => simp [signs, Clause.eval]
  | cons x L ih =>
    have key : ∀ c : Clause Nat,
        ([(⟨x, true⟩ :: c : Clause Nat), ⟨x, false⟩ :: c]).countP (fun d => !Clause.eval α d)
          = (if Clause.eval α c then 0 else 1) := by
      intro c
      cases hx : α x <;> cases hc : Clause.eval α c <;>
        simp only [Clause.eval] at hc ⊢ <;> simp [Lit.eval, hx, hc]
    unfold signs
    rw [← ih]
    generalize signs L = S
    induction S with
    | nil => simp
    | cons c S ihS =>
      rw [List.flatMap_cons, List.countP_append, key, ihS, List.countP_cons]
      cases h : Clause.eval α c <;> (try simp) <;> (try omega)

theorem signs_cpar {α : Nat → Bool} {L : List Nat} {c : Clause Nat} (hc : c ∈ signs L)
    (hf : c.eval α = false) : cpar c = L.countP α % 2 := by
  have hl := eval_false.mp hf
  have e1 : c.countP (fun l => !l.pos) = (c.map Lit.var).countP α := by
    rw [List.countP_map]
    apply List.countP_congr; intro l hlC
    have := lit_false.mp (hl l hlC)
    simp [this]
  rw [mem_signs hc] at e1
  unfold cpar; rw [e1]

/-- The number of clauses of vertex `v` falsified by `α` is `0` or `1`, by the parity at `v`. -/
theorem vclauses_false (E : List (Nat × Nat)) (χ : Nat → Nat) (α : Nat → Bool) (v : Nat) :
    (vclauses E χ v).countP (fun c => !c.eval α)
      = if (inc E v).countP α % 2 = χ v % 2 then 0 else 1 := by
  unfold vclauses
  rw [List.countP_filter]
  have h := signs_false α (inc E v)
  have hc : ∀ c ∈ signs (inc E v), (!c.eval α) = true →
      cpar c = (inc E v).countP α % 2 := by
    intro c hcm hf; exact signs_cpar hcm (by simpa using hf)
  split
  · rename_i hs
    rw [List.countP_eq_zero]
    intro c hcm
    by_cases hf : (!c.eval α) = true
    · rw [hc c hcm hf, hs]; simp
    · simp at hf; simp [hf]
  · rename_i hs
    rw [← h]
    apply List.countP_congr
    intro c hcm
    constructor
    · intro h1; simp at h1; simp [h1.1]
    · intro hf
      have := hc c hcm hf
      simp at hf
      simp [hf, this]; omega

theorem countP_two (a b : Nat) (hab : a ≠ b) (n : Nat) :
    (List.range n).countP (fun v => a == v || b == v)
      = (if a < n then 1 else 0) + (if b < n then 1 else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih]
    have k : ∀ c, (if c < n + 1 then 1 else 0) = (if c < n then 1 else 0) + (if c = n then 1 else 0) := by
      intro c; by_cases h1 : c < n <;> by_cases h2 : c = n <;> simp [h1, h2] <;> omega
    rw [k a, k b]
    have : [n].countP (fun v => a == v || b == v) = (if a = n then 1 else 0) + (if b = n then 1 else 0) := by
      by_cases h1 : a = n <;> by_cases h2 : b = n <;> simp [h1, h2] <;> omega
    omega

/-- Handshake: `∑_{v<n} (#true incident edges of v) = 2 · #true edges`. -/
theorem handshake (n : Nat) (E : List (Nat × Nat)) (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2)
    (α : Nat → Bool) :
    ((List.range n).map fun v => (inc E v).countP α).sum = 2 * (List.range E.length).countP α := by
  have h1 : ∀ v, (inc E v).countP α = (List.range E.length).countP
      (fun i => α i && ((edge E i).1 == v || (edge E i).2 == v)) := by
    intro v; unfold inc; rw [List.countP_filter]
    try (apply List.countP_congr; intro i _; simp [Bool.and_comm])
  simp only [h1]
  rw [double_count]
  have h2 : ∀ i ∈ List.range E.length, (List.range n).countP
      (fun v => α i && ((edge E i).1 == v || (edge E i).2 == v)) = if α i then 2 else 0 := by
    intro i hi
    have he := hE _ (edge_mem (List.mem_range.mp hi))
    cases h : α i
    · simp
    · simp only [Bool.true_and, ite_true]
      rw [countP_two _ _ he.2.2]; simp [he.1, he.2.1]
      done
  rw [List.map_congr_left h2]
  generalize List.range E.length = R
  induction R with
  | nil => simp
  | cons i R ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    cases h : α i <;> (try simp) <;> (try omega)

theorem sum_parity {α} (l : List α) (f g : α → Nat) (h : ∀ x ∈ l, (f x + g x) % 2 = 0) :
    ((l.map f).sum + (l.map g).sum) % 2 = 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h x List.mem_cons_self
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

theorem sum_flatMap_map {α β} (l : List α) (f : α → List β) (g : β → Int) :
    (((l.flatMap f).map g).sum) = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, ih]

/-! ## The theorem -/

/-- Number of vertices `< n` whose parity constraint `α` violates is odd. -/
theorem violated_odd (n : Nat) (E : List (Nat × Nat)) (χ : Nat → Nat)
    (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2)
    (hχ : ((List.range n).map χ).sum % 2 = 1) (α : Nat → Bool) :
    ((List.range n).map fun v => if (inc E v).countP α % 2 = χ v % 2 then 0 else 1).sum % 2 = 1 := by
  have hp := sum_parity (List.range n)
    (fun v => if (inc E v).countP α % 2 = χ v % 2 then 0 else 1)
    (fun v => (inc E v).countP α + χ v) (by intro v _; split <;> omega)
  have e : ((List.range n).map fun v => (inc E v).countP α + χ v).sum
      = ((List.range n).map fun v => (inc E v).countP α).sum + ((List.range n).map χ).sum := by
    generalize List.range n = R
    induction R with
    | nil => simp
    | cons v R ih => simp only [List.map_cons, List.sum_cons, ih]; omega
  rw [e, handshake n E hE α] at hp
  omega

/-- Tseitin formulas with odd total charge have degree-`Δ` Nullstellensatz refutations over `F_2`
(all multipliers `1`), for every loopless graph with maximum degree `≤ Δ`. -/
noncomputable def tseitinNS (n : Nat) (E : List (Nat × Nat)) (χ : Nat → Nat) (Δ : Nat)
    (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2)
    (hχ : ((List.range n).map χ).sum % 2 = 1)
    (hΔ : ∀ v, v < n → (inc E v).length ≤ Δ) :
    NSRefutation 2 (Tseitin n E χ) Δ where
  g := fun _ => Poly.one
  deg_le := by
    intro i hi
    rw [deg_one, Nat.zero_add]
    obtain ⟨v, hv, hC⟩ := tseitin_mem (List.getElem_mem hi)
    have := mem_signs (List.mem_filter.mp hC).1
    have hl : (Tseitin n E χ)[i].length = (inc E v).length := by
      rw [← this, List.length_map]
    rw [hl]; exact hΔ v hv
  identity := by
    intro a
    simp only [eval_one, Int.one_mul]
    rw [range_map_getD (Tseitin n E χ) [] (fun C => (clausePoly C).eval a)]
    unfold Tseitin
    rw [sum_flatMap_map]
    simp only [sum_indicator, vclauses_false]
    have h := violated_odd n E χ hE hχ a
    have e : ((List.range n).map fun v =>
        (((if (inc E v).countP a % 2 = χ v % 2 then 0 else 1 : Nat)) : Int)).sum
        = ((((List.range n).map fun v =>
            if (inc E v).countP a % 2 = χ v % 2 then 0 else 1).sum : Nat) : Int) := by
      generalize List.range n = R
      induction R with
      | nil => simp
      | cons v R ih => simp only [List.map_cons, List.sum_cons, ih]; omega
    rw [e]
    omega

/-- The Prop form of `tseitinNS`. -/
theorem tseitin_ns2 (n : Nat) (E : List (Nat × Nat)) (χ : Nat → Nat) (Δ : Nat)
    (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2)
    (hχ : ((List.range n).map χ).sum % 2 = 1)
    (hΔ : ∀ v, v < n → (inc E v).length ≤ Δ) :
    Nonempty (NSRefutation 2 (Tseitin n E χ) Δ) :=
  ⟨tseitinNS n E χ Δ hE hχ hΔ⟩

/-- `tseitin_ns2` with the multipliers in the type: a degree-`Δ` refutation over `F_2` whose
multipliers are all the constant polynomial `1`. -/
theorem tseitin_ns2_ones (n : Nat) (E : List (Nat × Nat)) (χ : Nat → Nat) (Δ : Nat)
    (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2)
    (hχ : ((List.range n).map χ).sum % 2 = 1)
    (hΔ : ∀ v, v < n → (inc E v).length ≤ Δ) :
    ∃ R : NSRefutation 2 (Tseitin n E χ) Δ, ∀ i, R.g i = Poly.one :=
  ⟨tseitinNS n E χ Δ hE hχ hΔ, fun _ => rfl⟩

/-- Every Tseitin clause mentions pairwise distinct variables, so its length equals the degree
of `clausePoly` and the measure `deg g_i + |F[i]|` of `NSRefutation` is the standard degree. -/
theorem tseitin_clause_nodup {n : Nat} {E : List (Nat × Nat)} {χ : Nat → Nat} {C : Clause Nat}
    (hC : C ∈ Tseitin n E χ) : (C.map Lit.var).Nodup := by
  obtain ⟨v, _, hC⟩ := tseitin_mem hC
  rw [mem_signs (List.mem_filter.mp hC).1]
  exact (List.nodup_range).filter _

end Programme.«20261024-1633-proof-complexity».NS

#print axioms Programme.«20261024-1633-proof-complexity».NS.tseitin_ns2
#print axioms Programme.«20261024-1633-proof-complexity».NS.tseitinNS
#print axioms Programme.«20261024-1633-proof-complexity».NS.tseitin_ns2_ones
#print axioms Programme.«20261024-1633-proof-complexity».NS.tseitin_clause_nodup
