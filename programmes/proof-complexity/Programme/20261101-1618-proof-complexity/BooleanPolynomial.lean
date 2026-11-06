import Programme.«20261101-1618-proof-complexity».LinearCertificate

namespace Programme.«20261101-1618-proof-complexity».BooleanPolynomial
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-1618-proof-complexity».ClauseLinear Programme.«20261101-1618-proof-complexity».LinearCertificate
abbrev Mono := List Var
abbrev Poly := List (Mono × Rat)
def meval (m : Mono) (a : Assignment) : Rat := if m.all a then 1 else 0
def peval (p : Poly) (a : Assignment) : Rat := (p.map fun t => t.2 * meval t.1 a).sum
def vins (v : Var) : Mono → Mono
  | [] => [v]
  | w::ws => if v.1 < w.1 || (v.1 == w.1 && v.2 ≤ w.2) then v::w::ws else w::vins v ws
def vsort : Mono → Mono
  | [] => []
  | v::vs => vins v (vsort vs)
theorem mem_vins (u v : Var) (m : Mono) : u ∈ vins v m ↔ u = v ∨ u ∈ m := by
  induction m with
  | nil => simp [vins]
  | cons w ws ih =>
    simp only [vins]
    split <;> simp only [List.mem_cons, ih, or_left_comm]
theorem mem_vsort (u : Var) (m : Mono) : u ∈ vsort m ↔ u ∈ m := by
  induction m with
  | nil => rfl
  | cons v vs ih => simp only [vsort, mem_vins, ih, List.mem_cons]
def canon (m : Mono) : Mono := (vsort m).eraseDups

theorem canon_eval (m : Mono) (a : Assignment) : meval (canon m) a = meval m a := by
  have h : (canon m).all a = m.all a := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, canon, List.mem_eraseDups, mem_vsort]
  simp only [meval, h]

theorem meval_append (m n : Mono) (a : Assignment) :
    meval (m ++ n) a = meval m a * meval n a := by
  simp only [meval, List.all_append]
  cases m.all a <;> cases n.all a <;> simp [Rat.zero_mul, Rat.mul_zero, Rat.one_mul]

def insert (m : Mono) (r : Rat) : Poly → Poly
  | [] => if r = 0 then [] else [(m,r)]
  | (n,s)::ps => if m = n then (if r+s = 0 then ps else (n,r+s)::ps) else (n,s)::insert m r ps

theorem insert_eval (m r p a) : peval (insert m r p) a = r * meval m a + peval p a := by
  induction p with
  | nil =>
    by_cases h : r = 0 <;> simp [insert, h, peval, Rat.zero_mul, Rat.add_zero]
  | cons t ps ih =>
    rcases t with ⟨n,s⟩
    by_cases h : m = n
    · subst n
      by_cases hh : r+s = 0
      · simp only [insert, ↓reduceIte, hh, peval, List.map_cons, List.sum_cons]
        rw [← Rat.add_assoc, ← Rat.add_mul, hh, Rat.zero_mul, Rat.zero_add]
      · simp [insert, hh, peval, Rat.add_mul, Rat.add_assoc]
    · simp only [insert, h, ↓reduceIte, peval, List.map_cons, List.sum_cons] at *
      rw [ih, ← Rat.add_assoc, Rat.add_comm (s * meval n a), Rat.add_assoc]

def add : Poly → Poly → Poly
  | [], q => q
  | (m,r)::ps, q => insert m r (add ps q)
theorem add_eval (p q a) : peval (add p q) a = peval p a + peval q a := by
  induction p with
  | nil => simp [add, peval, Rat.zero_add]
  | cons t ps ih =>
    rcases t with ⟨m,r⟩
    rw [add, insert_eval, ih]
    simp only [peval, List.map_cons, List.sum_cons, Rat.add_assoc]

def scale (r : Rat) (p : Poly) : Poly := p.map fun t => (t.1, r*t.2)
theorem scale_eval (r p a) : peval (scale r p) a = r * peval p a := by
  induction p with
  | nil => simp [scale, peval]
  | cons t ps ih =>
    simp only [scale, List.map_cons, peval, List.sum_cons, List.map_cons] at *
    rw [ih, Rat.mul_add, Rat.mul_assoc]

def mulMono (m : Mono) (p : Poly) : Poly := p.map fun t => (canon (m ++ t.1), t.2)
theorem mulMono_eval (m p a) : peval (mulMono m p) a = meval m a * peval p a := by
  induction p with
  | nil => simp [mulMono, peval]
  | cons t ps ih =>
    simp only [mulMono, List.map_cons, peval, List.sum_cons, canon_eval, meval_append] at *
    rw [ih, Rat.mul_add, ← Rat.mul_assoc, Rat.mul_comm t.2, Rat.mul_assoc]

def mul : Poly → Poly → Poly
  | [], _ => []
  | (m,r)::ps, q => add (scale r (mulMono m q)) (mul ps q)
theorem mul_eval (p q a) : peval (mul p q) a = peval p a * peval q a := by
  induction p with
  | nil => simp [mul, peval]
  | cons t ps ih =>
    rw [mul, add_eval, scale_eval, mulMono_eval, ih]
    simp only [peval, List.map_cons, List.sum_cons]
    rw [Rat.add_mul, Rat.mul_assoc]

def lit (l : Lit) : Poly := if l.2 then [([l.1],1)] else [([],1),([l.1],-1)]
theorem lit_eval (l : Lit) (a : Assignment) : peval (lit l) a = literal l a := by
  rcases l with ⟨v,b⟩
  cases b <;> cases h : a v <;> simp [lit, peval, meval, literal, holds, h, Rat.add_zero, Rat.add_neg_cancel]

def cell : List Lit → Poly
  | [] => [([],1)]
  | l::ls => mul (lit l) (cell ls)
theorem cell_eval (ls : List Lit) (a : Assignment) : peval (cell ls) a = conjunction ls a := by
  induction ls with
  | nil => simp [cell, peval, meval, conjunction, Rat.add_zero]
  | cons l ls ih =>
    rw [cell, mul_eval, lit_eval, ih]
    simp only [literal, conjunction, List.all_cons]
    by_cases h : holds a l = true <;> by_cases hh : ls.all (holds a) = true <;> simp [h, hh, Rat.zero_mul, Rat.mul_zero, Rat.one_mul]

def clause : Clause → Poly
  | [] => [([],-1)]
  | l::ls => add (lit l) (clause ls)
theorem clause_eval (c : Clause) (a : Assignment) : peval (clause c) a = slack c a := by
  induction c with
  | nil => simp [clause, peval, meval, slack, Rat.add_zero, Rat.sub_eq_add_neg, Rat.zero_add]
  | cons l ls ih =>
    simp only [clause, add_eval, lit_eval, ih, slack, List.map_cons, List.sum_cons]
    simp only [Rat.sub_eq_add_neg, Rat.add_assoc]

def gen : Generator → Poly
  | .cell m => cell m
  | .clause c m => mul (cell m) (clause c)
theorem gen_eval (g : Generator) (a : Assignment) : peval (gen g) a = g.eval a := by
  cases g <;> simp [gen, Generator.eval, cell_eval, mul_eval, clause_eval]

def cert : Certificate → Poly
  | [] => []
  | (r,g)::ts => add (scale r (gen g)) (cert ts)
theorem cert_eval (c : Certificate) (a : Assignment) : peval (cert c) a = LinearCertificate.eval c a := by
  induction c with
  | nil => rfl
  | cons t ts ih => simp [cert, add_eval, scale_eval, gen_eval, ih, LinearCertificate.eval]

def zero (p : Poly) : Bool := p.all fun t => t.2 == 0
theorem zero_eval (p : Poly) (h : zero p = true) (a : Assignment) : peval p a = 0 := by
  induction p with
  | nil => rfl
  | cons t ts ih =>
    have hh : t.2 = 0 ∧ zero ts = true := by simpa [zero] using h
    simp only [peval, List.map_cons, List.sum_cons, hh.1, Rat.zero_mul]
    exact Rat.zero_add _ |>.trans (ih hh.2)

theorem identity (c : Certificate) (h : zero (add (cert c) [([],1)]) = true) :
    ∀ a, LinearCertificate.eval c a = -1 := by
  intro a
  have hh := zero_eval _ h a
  rw [add_eval, cert_eval] at hh
  have hx : peval [([],1)] a = 1 := by simp [peval, meval, Rat.add_zero]
  rw [hx] at hh
  have he := congrArg (fun r : Rat => r + (-1)) hh
  simpa only [Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero, Rat.zero_add] using he

#print axioms cert_eval
#print axioms identity
end Programme.«20261101-1618-proof-complexity».BooleanPolynomial
