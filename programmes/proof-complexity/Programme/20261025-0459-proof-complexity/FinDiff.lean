import Programme.«20261024-1633-proof-complexity».PCTseitin

/-!
# Finite differences of functions on the Boolean cube

`cf g t` (for a list `t` of distinct variables) is the multilinear coefficient of the monomial
`∏_{y∈t} x_y` in `g`, computed from values of `g` at points that are `0` outside `t`, as an
iterated finite difference `Δ_{t₁} ⋯ Δ_{t_r} g` at the all-`0` point. It is defined for any
function, needs no uniqueness of polynomial representations, and satisfies:
* `cf_lin`, `cf_congr`: linear, and respects congruence mod `p` pointwise;
* `cf_cubeDeg`: if `g` agrees mod `p` with a polynomial of degree `≤ d`, then `p ∣ cf g t` for
  `|t| > d`;
* `cf_mul`: `cf (x·g) t = cf g (t.erase x) + cf g t` if `x ∈ t`, else `0`;
* `cf_const`: `cf c t = c` if `t = []`, else `0`.
-/

namespace Programme.«20261025-0459-proof-complexity».FinDiff

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin

def upd (a : Nat → Bool) (y : Nat) (b : Bool) : Nat → Bool := fun z => if z = y then b else a z

def dlt (y : Nat) (g : (Nat → Bool) → Int) : (Nat → Bool) → Int :=
  fun a => g (upd a y true) - g (upd a y false)

def dt : List Nat → ((Nat → Bool) → Int) → (Nat → Bool) → Int
  | [], g => g
  | y :: t, g => dlt y (dt t g)

def z0 : Nat → Bool := fun _ => false

/-- Multilinear coefficient of `∏_{y ∈ t} x_y` in `g`. -/
def cf (g : (Nat → Bool) → Int) (t : List Nat) : Int := dt t g z0

theorem upd_same (a : Nat → Bool) (y : Nat) (b c : Bool) : upd (upd a y b) y c = upd a y c := by
  funext z; simp only [upd]; split <;> rfl

theorem upd_comm (a : Nat → Bool) (y z : Nat) (b c : Bool) (h : y ≠ z) :
    upd (upd a y b) z c = upd (upd a z c) y b := by
  funext w; simp only [upd]
  by_cases h1 : w = z <;> by_cases h2 : w = y <;> simp_all

theorem upd_z0_false (x : Nat) : upd z0 x false = z0 := by
  funext w; simp only [upd, z0]; split <;> rfl

theorem dt_lin (t : List Nat) (f g : (Nat → Bool) → Int) (u v : Int) :
    dt t (fun a => u * f a + v * g a) = fun a => u * dt t f a + v * dt t g a := by
  induction t with
  | nil => rfl
  | cons y t ih =>
    funext a; simp only [dt, dlt, ih, Int.mul_sub]; omega

theorem dt_congr (p : Int) (t : List Nat) (f g : (Nat → Bool) → Int) (h : ∀ a, p ∣ f a - g a) :
    ∀ a, p ∣ dt t f a - dt t g a := by
  induction t with
  | nil => exact h
  | cons y t ih =>
    intro a; simp only [dt, dlt]
    have := Int.dvd_sub (ih (upd a y true)) (ih (upd a y false))
    have e : dt t f (upd a y true) - dt t f (upd a y false) - (dt t g (upd a y true) - dt t g (upd a y false))
      = dt t f (upd a y true) - dt t g (upd a y true) - (dt t f (upd a y false) - dt t g (upd a y false)) := by
      omega
    rw [e]; exact this

theorem cf_lin (f g : (Nat → Bool) → Int) (u v : Int) (t : List Nat) :
    cf (fun a => u * f a + v * g a) t = u * cf f t + v * cf g t := by
  unfold cf; rw [dt_lin]

theorem cf_congr (p : Int) (f g : (Nat → Bool) → Int) (h : ∀ a, p ∣ f a - g a) (t : List Nat) :
    p ∣ cf f t - cf g t := dt_congr p t f g h z0

/-- `g` does not depend on `y`. -/
def Indep (y : Nat) (g : (Nat → Bool) → Int) : Prop := ∀ a b, g (upd a y b) = g a

theorem indep_dlt {y z : Nat} {g : (Nat → Bool) → Int} (h : Indep y g) : Indep y (dlt z g) := by
  intro a b; simp only [dlt]
  by_cases hyz : y = z
  · subst hyz; rw [upd_same, upd_same]
  · rw [upd_comm _ _ _ _ _ hyz, upd_comm _ _ _ _ _ hyz, h, h]

theorem indep_dt {y : Nat} {g : (Nat → Bool) → Int} (h : Indep y g) (t : List Nat) :
    Indep y (dt t g) := by
  induction t with
  | nil => exact h
  | cons z t ih => exact indep_dlt ih

theorem dt_mem_zero {y : Nat} {g : (Nat → Bool) → Int} (h : Indep y g) (t : List Nat) (hy : y ∈ t) :
    ∀ a, dt t g a = 0 := by
  induction t with
  | nil => simp at hy
  | cons z t ih =>
    intro a; simp only [dt, dlt]
    by_cases hyz : y = z
    · subst hyz
      have := indep_dt h t
      rw [this a true, this a false]; omega
    · have hy' : y ∈ t := by
        rcases List.mem_cons.mp hy with h' | h'
        · exact absurd h' hyz
        · exact h'
      rw [ih hy', ih hy']; rfl

theorem monoEval_indep (y : Nat) (m : List Nat) (hy : y ∉ m) : Indep y (fun a => monoEval a m) := by
  intro a b
  induction m with
  | nil => rfl
  | cons v m ih =>
    have hv : v ≠ y := fun e => hy (e ▸ List.mem_cons_self)
    have hm : y ∉ m := fun h => hy (List.mem_cons_of_mem _ h)
    have := ih hm
    simp only [monoEval, List.map_cons, List.prod_cons] at this ⊢
    rw [this]; simp only [upd, hv, if_false]

theorem dt_zero (t : List Nat) : dt t (fun _ => 0) = fun _ => 0 := by
  induction t with
  | nil => rfl
  | cons y t ih => funext a; simp only [dt, dlt, ih]; rfl

theorem dt_sum (t : List Nat) (L : List (Int × List Nat)) :
    dt t (fun a => (L.map fun e => e.1 * monoEval a e.2).sum) =
      fun a => (L.map fun e => e.1 * dt t (fun b => monoEval b e.2) a).sum := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil]; exact dt_zero t
  | cons e L ih =>
    simp only [List.map_cons, List.sum_cons]
    have := dt_lin t (fun b => monoEval b e.2) (fun a => (L.map fun e => e.1 * monoEval a e.2).sum) e.1 1
    simp only [Int.one_mul] at this
    rw [this, ih]

theorem exists_not_mem (t e : List Nat) (ht : t.Nodup) (hl : e.length < t.length) :
    ∃ y ∈ t, y ∉ e := by
  induction t generalizing e with
  | nil => simp at hl
  | cons y t ih =>
    rw [List.nodup_cons] at ht
    by_cases hy : y ∈ e
    · have hlen := List.length_erase_of_mem hy
      simp only [List.length_cons] at hl
      have := List.length_pos_of_mem hy
      obtain ⟨z, hz, hze⟩ := ih (e.erase y) ht.2 (by omega)
      have hzy : z ≠ y := fun h => ht.1 (h ▸ hz)
      refine ⟨z, List.mem_cons_of_mem _ hz, fun h => hze ?_⟩
      exact (List.mem_erase_of_ne hzy).mpr h
    · exact ⟨y, List.mem_cons_self, hy⟩

theorem le_foldr_max (l : List Nat) (x : Nat) (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with h | h
    · subst h; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem sum_map_zero {α : Type} (L : List α) (f : α → Int) (h : ∀ e ∈ L, f e = 0) :
    (L.map f).sum = 0 := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h e List.mem_cons_self, ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]; rfl

theorem cf_cubeDeg {p : Nat} {g : (Nat → Bool) → Int} {d : Nat} (hg : CubeDeg p g d) (t : List Nat)
    (ht : t.Nodup) (hd : d < t.length) : (p : Int) ∣ cf g t := by
  obtain ⟨Q, hQd, hQ⟩ := hg
  have h1 := dt_congr p t _ _ hQ z0
  have h0 : dt t (fun a => Q.eval a) z0 = 0 := by
    unfold Poly.eval
    rw [dt_sum]
    have : ∀ e ∈ Q.terms, e.1 * dt t (fun b => monoEval b e.2) z0 = 0 := by
      intro e he
      have hl : e.2.length ≤ Q.deg := by
        unfold Poly.deg
        exact le_foldr_max _ _ (List.mem_map.mpr ⟨e, he, rfl⟩)
      obtain ⟨y, hy, hye⟩ := exists_not_mem t e.2 ht (by omega)
      rw [dt_mem_zero (monoEval_indep y e.2 hye) t hy]; simp
    exact sum_map_zero _ _ this
  unfold cf
  have e : dt t g z0 = -(dt t (fun a => Q.eval a) z0 - dt t g z0) := by rw [h0]; omega
  rw [e]; exact Int.dvd_neg.mpr h1

theorem dt_mul_notin (x : Nat) (g : (Nat → Bool) → Int) (t : List Nat) (hx : x ∉ t) :
    ∀ a, dt t (fun a => xv x a * g a) a = xv x a * dt t g a := by
  induction t with
  | nil => intro a; rfl
  | cons y t ih =>
    have hxy : x ≠ y := fun e => hx (e ▸ List.mem_cons_self)
    have hx' : x ∉ t := fun h => hx (List.mem_cons_of_mem _ h)
    intro a; simp only [dt, dlt, ih hx']
    have e1 : ∀ b, xv x (upd a y b) = xv x a := by
      intro b; simp only [xv, upd, hxy, if_false]
    rw [e1, e1, Int.mul_sub]

theorem dt_mul_mem (x : Nat) (g : (Nat → Bool) → Int) (t : List Nat) (ht : t.Nodup) (hx : x ∈ t) :
    ∀ a, dt t (fun a => xv x a * g a) a = dt (t.erase x) g (upd a x true) := by
  induction t with
  | nil => simp at hx
  | cons y t ih =>
    rw [List.nodup_cons] at ht
    intro a
    by_cases hxy : y = x
    · subst hxy
      rw [List.erase_cons_head]
      simp only [dt, dlt, dt_mul_notin y g t ht.1]
      simp [xv, upd]
    · have hx' : x ∈ t := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm hxy
        · exact h
      rw [List.erase_cons_tail (by simpa using hxy)]
      simp only [dt, dlt, ih ht.2 hx']
      rw [upd_comm a x y true true (Ne.symm hxy), upd_comm a x y true false (Ne.symm hxy)]

theorem dlt_comm (x y : Nat) (h : (Nat → Bool) → Int) : dlt x (dlt y h) = dlt y (dlt x h) := by
  by_cases hxy : x = y
  · subst hxy; rfl
  · funext a; simp only [dlt]
    rw [upd_comm a x y true true hxy, upd_comm a x y true false hxy,
      upd_comm a x y false true hxy, upd_comm a x y false false hxy]
    omega

theorem dt_erase (x : Nat) (g : (Nat → Bool) → Int) (t : List Nat) (ht : t.Nodup) (hx : x ∈ t) :
    dt t g = dlt x (dt (t.erase x) g) := by
  induction t with
  | nil => simp at hx
  | cons y t ih =>
    rw [List.nodup_cons] at ht
    by_cases hxy : y = x
    · subst hxy; rw [List.erase_cons_head]; rfl
    · have hx' : x ∈ t := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm hxy
        · exact h
      rw [List.erase_cons_tail (by simpa using hxy)]
      simp only [dt]
      rw [ih ht.2 hx', dlt_comm]

theorem cf_mul (x : Nat) (g : (Nat → Bool) → Int) (t : List Nat) (ht : t.Nodup) :
    cf (fun a => xv x a * g a) t = if x ∈ t then cf g (t.erase x) + cf g t else 0 := by
  unfold cf
  by_cases hx : x ∈ t
  · rw [if_pos hx, dt_mul_mem x g t ht hx, dt_erase x g t ht hx]
    simp only [dlt, upd_z0_false]; omega
  · rw [if_neg hx, dt_mul_notin x g t hx]; simp [xv, z0]

theorem cf_const (c : Int) (t : List Nat) : cf (fun _ => c) t = if t = [] then c else 0 := by
  have : ∀ t : List Nat, dt t (fun _ => c) = fun _ => if t = [] then c else 0 := by
    intro t
    induction t with
    | nil => rfl
    | cons y t ih => funext a; simp only [dt, dlt, ih]; simp
  unfold cf; rw [this]

end Programme.«20261025-0459-proof-complexity».FinDiff
