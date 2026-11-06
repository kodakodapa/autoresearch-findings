import Programme.«20261024-1633-proof-complexity».NS

/-!
# Local Nullstellensatz certificates (the upper-bound tool)

`local_ns`: to build an `NSRefutation p F D` it suffices to give, for every clause `F[i]`, an
integer-valued function `φ i` of the assignment that depends only on the variables of `F[i]`
and on a list `W i` of further variables, with `|W i| + |F[i]| ≤ D`, such that
`∑_i φ_i(a) f_{F[i]}(a) ≡ 1 (mod p)` for every Boolean `a`. The multiplier `g_i` is the
multilinear interpolation of `φ_i` over `W i` with the variables of `F[i]` fixed to their
falsifying values (`interp`, `falsify`), so `g_i f_{F[i]} = φ_i f_{F[i]}` on the cube and
`deg g_i ≤ |W i|`.

This is the converse direction to `Work.NSLower.design_zero`: any refutation whose multipliers are
"local" functions (a choice of violated clause, a count over a vertex's edges) becomes a
Nullstellensatz refutation of the stated degree without writing down polynomials.
-/

namespace Programme.«20261024-1633-proof-complexity».NSLocal

open Classical Programme.«20261024-1110-proof-complexity».Haken
open Programme.«20261024-1633-proof-complexity».NS

/-! ## More polynomial operations -/

def Poly.add (P Q : Poly Nat) : Poly Nat := ⟨P.terms ++ Q.terms⟩

def Poly.const (k : Int) : Poly Nat := ⟨[(k, [])]⟩

theorem eval_add (a : Nat → Bool) (P Q : Poly Nat) : (Poly.add P Q).eval a = P.eval a + Q.eval a := by
  simp [Poly.add, Poly.eval, List.map_append, List.sum_append]

theorem eval_const (a : Nat → Bool) (k : Int) : (Poly.const k).eval a = k := by
  simp [Poly.const, Poly.eval, monoEval]

theorem deg_add (P Q : Poly Nat) (d : Nat) (hP : P.deg ≤ d) (hQ : Q.deg ≤ d) :
    (Poly.add P Q).deg ≤ d := by
  rw [deg_le_iff] at *
  intro t ht
  simp only [Poly.add, List.mem_append] at ht
  rcases ht with ht | ht
  · exact hP t ht
  · exact hQ t ht

theorem deg_const (k : Int) : (Poly.const k).deg = 0 := by simp [Poly.const, Poly.deg]

/-! ## Interpolation over a list of variables -/

def setv (a : Nat → Bool) (x : Nat) (b : Bool) : Nat → Bool := fun j => if j = x then b else a j

/-- `a` on `W`, `false` elsewhere. -/
def restr (W : List Nat) (a : Nat → Bool) : Nat → Bool := fun j => if j ∈ W then a j else false

/-- Shannon expansion of `φ` over the variables `W` (variables outside `W` read as `false`). -/
def interp : List Nat → ((Nat → Bool) → Int) → Poly Nat
  | [], φ => Poly.const (φ fun _ => false)
  | x :: W, φ =>
    Poly.add ((interp W fun b => φ (setv b x true)).mulVar x)
      ((interp W fun b => φ (setv b x false)).sub ((interp W fun b => φ (setv b x false)).mulVar x))

theorem interp_eval (W : List Nat) (φ : (Nat → Bool) → Int) (a : Nat → Bool) :
    (interp W φ).eval a = φ (restr W a) := by
  induction W generalizing φ with
  | nil =>
    simp only [interp, eval_const]
    congr 1
  | cons x W ih =>
    simp only [interp, eval_add, eval_sub, eval_mulVar, ih]
    have e : setv (restr W a) x (a x) = restr (x :: W) a := by
      funext j
      simp only [setv, restr, List.mem_cons]
      by_cases h : j = x
      · subst h; simp
      · simp [h]
    rw [← e]
    cases a x <;> simp

theorem interp_deg (W : List Nat) (φ : (Nat → Bool) → Int) : (interp W φ).deg ≤ W.length := by
  induction W generalizing φ with
  | nil => simp [interp, deg_const]
  | cons x W ih =>
    simp only [interp, List.length_cons]
    have h1 := deg_mulVar x (interp W fun b => φ (setv b x true))
    have h2 := deg_mulVar x (interp W fun b => φ (setv b x false))
    have h3 := ih (fun b => φ (setv b x true))
    have h4 := ih (fun b => φ (setv b x false))
    exact deg_add _ _ _ (by omega) (deg_sub _ _ _ (by omega) (by omega))

/-! ## Fixing the variables of a clause to their falsifying values -/

def falsify : Clause Nat → (Nat → Bool) → (Nat → Bool)
  | [], b => b
  | l :: C, b => setv (falsify C b) l.var (!l.pos)

theorem falsify_out (C : Clause Nat) (b : Nat → Bool) (x : Nat) (h : ∀ l ∈ C, l.var ≠ x) :
    falsify C b x = b x := by
  induction C with
  | nil => rfl
  | cons l C ih =>
    simp only [falsify, setv]
    rw [ite_eq_right (Ne.symm (h l (List.mem_cons_self ..)))]
    exact ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')

theorem falsify_eq (C : Clause Nat) (b a : Nat → Bool) (ha : ∀ l ∈ C, Lit.eval a l = false) :
    ∀ l ∈ C, falsify C b l.var = a l.var := by
  have key : ∀ l : Lit Nat, Lit.eval a l = false → (!l.pos) = a l.var := by
    intro l hl
    unfold Lit.eval at hl
    cases hp : l.pos <;> cases hx : a l.var <;> simp_all
  induction C with
  | nil => intro l hl; cases hl
  | cons l C ih =>
    intro l' hl'
    simp only [falsify, setv]
    by_cases e : l'.var = l.var
    · rw [ite_eq_left e, e]; exact key l (ha l (List.mem_cons_self ..))
    · rw [ite_eq_right e]
      rcases List.mem_cons.mp hl' with h | h
      · exact absurd (h ▸ rfl) e
      · exact ih (fun l'' h'' => ha l'' (List.mem_cons_of_mem _ h'')) l' h

/-! ## The local certificate lemma -/

/-- If `φ i` depends only on `W i` and the variables of `F[i]`, `|W i| + |F[i]| ≤ D`, and
`∑_i φ_i f_{F[i]} ≡ 1 (mod p)` on every Boolean assignment, then `F` has a Nullstellensatz
refutation over `Z/p` of degree `D`. -/
theorem local_ns (p : Nat) (F : CNF Nat) (D : Nat) (W : Nat → List Nat)
    (φ : Nat → (Nat → Bool) → Int)
    (hloc : ∀ i, i < F.length → ∀ a b : Nat → Bool, (∀ x ∈ W i, a x = b x) →
      (∀ l ∈ F.getD i [], a l.var = b l.var) → φ i a = φ i b)
    (hdeg : ∀ i, i < F.length → (W i).length + (F.getD i []).length ≤ D)
    (hid : ∀ a : Nat → Bool,
      ((List.range F.length).map fun i => φ i a * (clausePoly (F.getD i [])).eval a).sum
        % (p : Int) = 1 % (p : Int)) :
    Nonempty (NSRefutation p F D) := by
  refine ⟨⟨fun i => interp (W i) (fun b => φ i (falsify (F.getD i []) b)), ?_, ?_⟩⟩
  · intro i hi
    have h1 := interp_deg (W i) (fun b => φ i (falsify (F.getD i []) b))
    have h2 := hdeg i hi
    have e : F.getD i [] = F[i] := by simp [List.getD, List.getElem?_eq_getElem hi]
    rw [e] at h2
    omega
  · intro a
    rw [← hid a]
    congr 2
    apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    rw [interp_eval, clausePoly_eval]
    generalize hC : F.getD i [] = C at *
    cases hev : Clause.eval a C
    · simp only [Bool.false_eq_true, ite_false, Int.mul_one]
      have hf : ∀ l ∈ C, Lit.eval a l = false := by
        unfold Clause.eval at hev
        intro l hl
        simpa using (List.any_eq_false.mp hev) l hl
      apply hloc i hi _ _ _ _
      · intro x hx
        by_cases hx' : ∃ l ∈ C, l.var = x
        · obtain ⟨l, hl, rfl⟩ := hx'
          exact falsify_eq C _ a hf l hl
        · rw [falsify_out C _ x (fun l hl e => hx' ⟨l, hl, e⟩)]
          simp [restr, hx]
      · rw [hC]
        exact falsify_eq C _ a hf
    · simp


/-! ## Sums of local terms and block-structured CNFs -/

/-- Sum of the interpolations of a list of local terms `(W, ψ)`. -/
def interpSum (C : Clause Nat) : List (List Nat × ((Nat → Bool) → Int)) → Poly Nat
  | [] => Poly.const 0
  | t :: T => Poly.add (interp t.1 fun b => t.2 (falsify C b)) (interpSum C T)

/-- `local_ns` with each multiplier a sum of local terms, each with its own variable list. -/
theorem local_ns_sum (p : Nat) (F : CNF Nat) (D : Nat)
    (T : Nat → List (List Nat × ((Nat → Bool) → Int)))
    (hloc : ∀ i, i < F.length → ∀ t ∈ T i, ∀ a b : Nat → Bool, (∀ x ∈ t.1, a x = b x) →
      (∀ l ∈ F.getD i [], a l.var = b l.var) → t.2 a = t.2 b)
    (hdeg : ∀ i, i < F.length → ∀ t ∈ T i, t.1.length + (F.getD i []).length ≤ D)
    (hwid : ∀ i, i < F.length → (F.getD i []).length ≤ D)
    (hid : ∀ a : Nat → Bool,
      ((List.range F.length).map fun i =>
        ((T i).map fun t => t.2 a).sum * (clausePoly (F.getD i [])).eval a).sum
        % (p : Int) = 1 % (p : Int)) :
    Nonempty (NSRefutation p F D) := by
  refine ⟨⟨fun i => interpSum (F.getD i []) (T i), ?_, ?_⟩⟩
  · intro i hi
    have e : F.getD i [] = F[i] := by simp [List.getD, List.getElem?_eq_getElem hi]
    have key : ∀ T' : List (List Nat × ((Nat → Bool) → Int)), (∀ t ∈ T', t ∈ T i) →
        (interpSum (F.getD i []) T').deg + (F.getD i []).length ≤ D := by
      intro T' hT'
      induction T' with
      | nil => simp only [interpSum, deg_const]; have := hwid i hi; omega
      | cons t T' ih =>
        have h1 := interp_deg t.1 (fun b => t.2 (falsify (F.getD i []) b))
        have h2 := hdeg i hi t (hT' t (List.mem_cons_self ..))
        have h3 := ih (fun t' ht' => hT' t' (List.mem_cons_of_mem _ ht'))
        have := deg_add (interp t.1 fun b => t.2 (falsify (F.getD i []) b))
          (interpSum (F.getD i []) T') (D - (F.getD i []).length) (by omega) (by omega)
        simp only [interpSum]; omega
    have := key (T i) (fun t ht => ht)
    rw [e] at this ⊢; exact this
  · intro a
    rw [← hid a]
    congr 2
    apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    rw [clausePoly_eval]
    have hloc' := hloc i hi
    generalize F.getD i [] = C at *
    cases hev : Clause.eval a C
    · simp only [Bool.false_eq_true, ite_false, Int.mul_one]
      have hf : ∀ l ∈ C, Lit.eval a l = false := by
        unfold Clause.eval at hev
        intro l hl
        simpa using (List.any_eq_false.mp hev) l hl
      have key : ∀ T' : List (List Nat × ((Nat → Bool) → Int)), (∀ t ∈ T', t ∈ T i) →
          (interpSum C T').eval a = (T'.map fun t => t.2 a).sum := by
        intro T' hT'
        induction T' with
        | nil => simp [interpSum, eval_const]
        | cons t T' ih =>
          simp only [interpSum, eval_add, interp_eval, List.map_cons, List.sum_cons]
          rw [ih (fun t' ht' => hT' t' (List.mem_cons_of_mem _ ht'))]
          congr 1
          apply hloc' t (hT' t (List.mem_cons_self ..))
          · intro x hx
            by_cases hx' : ∃ l ∈ C, l.var = x
            · obtain ⟨l, hl, rfl⟩ := hx'
              exact falsify_eq _ _ a hf l hl
            · rw [falsify_out _ _ x (fun l hl e => hx' ⟨l, hl, e⟩)]
              simp [restr, hx]
          · exact falsify_eq _ _ a hf
      exact key (T i) (fun t ht => ht)
    · simp

/-- Block coordinates of position `i` in `Ls.flatten`. -/
def pos {α} : List (List α) → Nat → Nat × Nat
  | [], _ => (0, 0)
  | L :: Ls, i => if i < L.length then (0, i) else ((pos Ls (i - L.length)).1 + 1, (pos Ls (i - L.length)).2)

theorem pos_spec {α} (Ls : List (List α)) (d : α) (i : Nat) (hi : i < Ls.flatten.length) :
    (pos Ls i).1 < Ls.length ∧ (pos Ls i).2 < (Ls.getD (pos Ls i).1 []).length ∧
      Ls.flatten.getD i d = (Ls.getD (pos Ls i).1 []).getD (pos Ls i).2 d := by
  induction Ls generalizing i with
  | nil => simp at hi
  | cons L Ls ih =>
    simp only [List.flatten_cons, List.length_append] at hi
    by_cases h : i < L.length
    · simp [pos, h, List.getD, List.getElem?_append_left h]
    · have h' : i - L.length < Ls.flatten.length := by omega
      obtain ⟨h1, h2, h3⟩ := ih (i - L.length) h'
      simp only [pos, h, ite_false]
      refine ⟨by simp; omega, by simpa [List.getD] using h2, ?_⟩
      simp only [List.flatten_cons, List.getD, List.getElem?_append_right (Nat.le_of_not_lt h)]
      simpa [List.getD] using h3

theorem sum_range_add (m k : Nat) (f : Nat → Int) :
    ((List.range (m + k)).map f).sum = ((List.range m).map f).sum +
      ((List.range k).map fun j => f (m + j)).sum := by
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]; rfl

theorem sum_pos {α} (Ls : List (List α)) (d : α) (G : Nat → Nat → α → Int) :
    ((List.range Ls.flatten.length).map fun i =>
        G (pos Ls i).1 (pos Ls i).2 (Ls.flatten.getD i d)).sum =
      ((List.range Ls.length).map fun b => ((List.range (Ls.getD b []).length).map fun j =>
        G b j ((Ls.getD b []).getD j d)).sum).sum := by
  induction Ls generalizing G with
  | nil => simp
  | cons L Ls ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [sum_range_add, Nat.add_comm Ls.length 1, sum_range_add]
    congr 1
    · simp only [List.range_one, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Int.add_zero, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hi := List.mem_range.mp hi
      simp [pos, hi, List.getD, List.getElem?_append_left hi]
    · calc _ = ((List.range Ls.flatten.length).map fun i =>
              G ((pos Ls i).1 + 1) (pos Ls i).2 (Ls.flatten.getD i d)).sum := by
            congr 1
            apply List.map_congr_left
            intro j _
            simp only [pos, Nat.not_lt.mpr (Nat.le_add_right _ _), ite_false, Nat.add_sub_cancel_left]
            congr 1
            simp [List.getD, List.getElem?_append_right (Nat.le_add_right _ _)]
        _ = _ := ih (fun b j x => G (b + 1) j x)
        _ = _ := by
            congr 1
            apply List.map_congr_left
            intro b _
            simp [Nat.add_comm 1 b, List.getD]

/-- `local_ns_sum` for a CNF made of blocks `B 0, …, B (n-1)` (one per vertex, say): the
multiplier of the `j`-th clause of block `v` is a sum of local terms `T v j`. -/
theorem local_ns_blocks (p n D : Nat) (B : Nat → CNF Nat)
    (T : Nat → Nat → List (List Nat × ((Nat → Bool) → Int)))
    (hloc : ∀ v, v < n → ∀ j, j < (B v).length → ∀ t ∈ T v j, ∀ a b : Nat → Bool,
      (∀ x ∈ t.1, a x = b x) → (∀ l ∈ (B v).getD j [], a l.var = b l.var) → t.2 a = t.2 b)
    (hdeg : ∀ v, v < n → ∀ j, j < (B v).length → ∀ t ∈ T v j,
      t.1.length + ((B v).getD j []).length ≤ D)
    (hwid : ∀ v, v < n → ∀ j, j < (B v).length → ((B v).getD j []).length ≤ D)
    (hid : ∀ a : Nat → Bool,
      ((List.range n).map fun v => ((List.range (B v).length).map fun j =>
        ((T v j).map fun t => t.2 a).sum * (clausePoly ((B v).getD j [])).eval a).sum).sum
        % (p : Int) = 1 % (p : Int)) :
    Nonempty (NSRefutation p ((List.range n).flatMap B) D) := by
  have eF : (List.range n).flatMap B = ((List.range n).map B).flatten := by
    simp [List.flatMap]
  have eB : ∀ b, b < n → ((List.range n).map B).getD b [] = B b := by
    intro b hb; simp [List.getD, hb]
  have hl : ((List.range n).map B).length = n := by simp
  rw [eF]
  generalize (List.range n).map B = Ls at eB hl
  apply local_ns_sum p Ls.flatten D (fun i => T (pos Ls i).1 (pos Ls i).2)
  · intro i hi t ht a b h1 h2
    obtain ⟨hb, hj, he⟩ := pos_spec Ls [] i hi
    have hb' : (pos Ls i).1 < n := hl ▸ hb
    rw [eB _ hb'] at hj he
    rw [he] at h2
    exact hloc _ hb' _ hj t ht a b h1 h2
  · intro i hi t ht
    obtain ⟨hb, hj, he⟩ := pos_spec Ls [] i hi
    have hb' : (pos Ls i).1 < n := hl ▸ hb
    rw [eB _ hb'] at hj he
    rw [he]
    exact hdeg _ hb' _ hj t ht
  · intro i hi
    obtain ⟨hb, hj, he⟩ := pos_spec Ls [] i hi
    have hb' : (pos Ls i).1 < n := hl ▸ hb
    rw [eB _ hb'] at hj he
    rw [he]
    exact hwid _ hb' _ hj
  · intro a
    rw [sum_pos Ls [] (fun b j C => ((T b j).map fun t => t.2 a).sum * (clausePoly C).eval a)]
    rw [← hid a, hl]
    congr 2
    apply List.map_congr_left
    intro b hb
    rw [eB b (List.mem_range.mp hb)]

end Programme.«20261024-1633-proof-complexity».NSLocal

#print axioms Programme.«20261024-1633-proof-complexity».NSLocal.local_ns
#print axioms Programme.«20261024-1633-proof-complexity».NSLocal.local_ns_blocks
