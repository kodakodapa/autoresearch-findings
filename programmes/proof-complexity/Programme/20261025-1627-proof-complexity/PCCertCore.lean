import Programme.«20261025-0459-proof-complexity».PCCert
import Programme.«20261025-0459-proof-complexity».PCCert2

/-!
# Shared core of the bitset R-operator certificate checkers (`Z/2`, `Z/3`)

A certificate for "no degree-`D` PC refutation over `Z/p`" lists monomials `m_i` (entries
`i < N`, entry `0` is the empty monomial), linked by `dn` (`m_i ↦ m_i / x`) and `up`
(`m_i ↦ x · m_i`) pointers, together with a row `R(m_i)` for each entry. Everything that does not
depend on how rows are stored lives here: the monomial index `Idx` and its link check `linkOk`,
lookup of a monomial by walking `up` links from entry `0` (`walk`), and the soundness argument
`Idx.sound`. It takes the rows as a coefficient function `ev i u` (coefficient `u` of `R(m_i)`,
read on the columns `u` with `col u`; entry `j` sits in column `pos j`) and three facts mod `p`:
the axioms are mapped to `0`, the multiplication identities
`R(x·m_s) = ∑_e R(m_s)_{pos e} · R(x·m_e)` hold for `|m_s| < D`, and `R(1)` is nonzero at `u0`.
The `Z/2` checker `Work.PCCertF2` and the `Z/3` checker `Work.PCCertF3` only prove these three
facts for their bit-level row encodings.
-/

namespace Programme.«20261025-1627-proof-complexity».PCCertCore

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».FinDiff Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».PCCert (lsum lsum_add lsum_mul lsum_congr lsum_dvd lsum_zero lsum_sub lsum_swap lsum_ite_eq)
open Programme.«20261025-0459-proof-complexity».PCCert2 (lk lk_mem)

/-! ## Lists, digits and chunked checks -/

def sortedLt : List Nat → Bool
  | a :: b :: l => decide (a < b) && sortedLt (b :: l)
  | _ => true

/-- Decode base-`2^w` digits (each stored as value `+ 1`, least significant first). -/
def decL (B : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else (n % B - 1) :: decL B f (n / B)

/-- `f` holds on `a, a+1, …, a+n-1` (checked in chunks, one kernel run each). -/
def rAll (f : Nat → Bool) (a n : Nat) : Bool := (List.range' a n).all f

theorem rAll_split {f : Nat → Bool} {a n m : Nat} (h1 : rAll f a n = true) (h2 : rAll f (a + n) m = true) :
    rAll f a (n + m) = true := by
  unfold rAll at *
  rw [← List.range'_append, List.all_append, h1, Nat.one_mul, h2]; rfl

theorem rAll_join {f : Nat → Bool} {a n b m k : Nat} (h1 : rAll f a n = true) (h2 : rAll f b m = true)
    (hb : a + n = b) (hk : n + m = k) : rAll f a k = true := by
  subst hb hk; exact rAll_split h1 h2

theorem rAll_spec {f : Nat → Bool} {n : Nat} (h : rAll f 0 n = true) (i : Nat) (hi : i < n) : f i = true := by
  unfold rAll at h
  rw [List.all_eq_true] at h
  exact h i (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)

theorem rAll_mono {f g : Nat → Bool} {a n : Nat} (hfg : ∀ i, f i = true → g i = true)
    (h : rAll f a n = true) : rAll g a n = true := by
  unfold rAll at *
  rw [List.all_eq_true] at *
  exact fun i hi => hfg i (h i hi)

/-- Picking the entry with key `x` from a list with distinct keys. -/
theorem lsum_lk (L : List (Nat × Nat)) (hnd : (L.map (·.1)).Nodup) (x : Nat) (F : Nat → Int) :
    lsum L (fun xt => if xt.1 = x then F xt.2 else 0) =
      (match lk L x with
        | some t => F t
        | none => 0) := by
  induction L with
  | nil => rfl
  | cons ab L ih =>
    obtain ⟨a, b⟩ := ab
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [lsum, lk]
    by_cases hax : a = x
    · subst hax
      rw [if_pos rfl, if_pos rfl, lsum_zero L _ (fun c hc => by
        rw [if_neg (fun (h : c.1 = a) => hnd.1 (h ▸ List.mem_map_of_mem (f := (·.1)) hc))])]
      simp
    · rw [if_neg hax, if_neg hax, ih hnd.2]; omega

theorem lsum_mem (m : List Nat) (hnd : m.Nodup) (x : Nat) (c : Int) :
    lsum m (fun y => if y = x then c else 0) = if x ∈ m then c else 0 := by
  induction m with
  | nil => simp [lsum]
  | cons a m ih =>
    rw [List.nodup_cons] at hnd
    simp only [lsum, ih hnd.2, List.mem_cons]
    by_cases hax : a = x
    · subst hax; simp [hnd.1]
    · have : ¬ x = a := fun h => hax h.symm
      simp [hax, this]

theorem sum_map_lsum {α : Type} (L : List α) (f : α → Int) : (L.map f).sum = lsum L f := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, List.sum_cons, lsum, ih]

theorem sortedLt_nodup : ∀ l : List Nat, sortedLt l = true → l.Nodup ∧ ∀ a, (∀ y ∈ l, a < y) → (a :: l).Nodup
  | [], _ => ⟨List.nodup_nil, fun a _ => List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩⟩
  | [b], _ => ⟨List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, fun a ha =>
      List.nodup_cons.mpr ⟨by simp; exact fun h => by have := ha b (by simp); omega,
        List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩⟩⟩
  | b :: c :: l, h => by
    simp only [sortedLt, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hbc, hrest⟩ := h
    have ih := sortedLt_nodup (c :: l) hrest
    have hb : ∀ y ∈ c :: l, b < y := by
      intro y hy
      -- elements of a sorted list are above its head
      have key : ∀ (l : List Nat) (c : Nat), sortedLt (c :: l) = true → ∀ y ∈ l, c < y := by
        intro l
        induction l with
        | nil => intro _ _ y hy; simp at hy
        | cons d l ihl =>
          intro c hcl y hy
          simp only [sortedLt, Bool.and_eq_true, decide_eq_true_eq] at hcl
          rcases List.mem_cons.mp hy with h | h
          · omega
          · have := ihl d hcl.2 y h; omega
      rcases List.mem_cons.mp hy with h | h
      · omega
      · have := key l c hrest y h; omega
    have h1 := ih.2 b hb
    refine ⟨h1, fun a ha => List.nodup_cons.mpr ⟨fun hm => ?_, h1⟩⟩
    have := ha a hm; omega

/-! ## Bits -/

def bt (b u : Nat) : Int := if b.testBit u then 1 else 0

theorem bt_zero (u : Nat) : bt 0 u = 0 := by simp [bt]

theorem bt_ge {b W u : Nat} (hb : b < 2 ^ W) (hu : W ≤ u) : bt b u = 0 := by
  unfold bt
  rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) hu))]; rfl

theorem bt_shift {b W : Nat} (hb : b < 2 ^ W) (x' x u : Nat) (hu : u < W) :
    bt (b <<< (x' * W)) (x * W + u) = if x' = x then bt b u else 0 := by
  by_cases h : x' = x
  · subst h; rw [if_pos rfl]; unfold bt; rw [Nat.testBit_shiftLeft]
    have : x' * W + u - x' * W = u := by omega
    rw [this]; simp
  · rw [if_neg h]; unfold bt; rw [Nat.testBit_shiftLeft]
    rcases Nat.lt_or_gt_of_ne h with h1 | h1
    · have h2 : (x' + 1) * W ≤ x * W := Nat.mul_le_mul_right W h1
      rw [Nat.succ_mul] at h2
      have h3 : W ≤ x * W + u - x' * W := by omega
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) h3))]; simp
    · have h2 : (x + 1) * W ≤ x' * W := Nat.mul_le_mul_right W h1
      rw [Nat.succ_mul] at h2
      have h3 : ¬ (x * W + u ≥ x' * W) := by omega
      simp [h3]

theorem bt_one_shift (e j : Nat) : bt (1 <<< e) j = if e = j then 1 else 0 := by
  unfold bt; rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : e = j <;> simp [h]

/-! ## Monomial coefficients -/

def sameSet (t m : List Nat) : Bool := t.all (· ∈ m) && m.all (· ∈ t)

theorem sameSet_iff (t m : List Nat) : sameSet t m = true ↔ ∀ y, y ∈ t ↔ y ∈ m := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩ y; exact ⟨h1 y, h2 y⟩
  · intro h; exact ⟨fun y hy => (h y).1 hy, fun y hy => (h y).2 hy⟩

theorem cf_mono (m : List Nat) (hm : m.Nodup) (t : List Nat) (ht : t.Nodup) :
    cf (fun a => monoEval a m) t = if sameSet t m then 1 else 0 := by
  induction m generalizing t with
  | nil =>
    have : (fun a => monoEval a ([] : List Nat)) = fun _ => (1 : Int) := by
      funext a; simp [monoEval]
    rw [this, cf_const]
    cases t with
    | nil => rfl
    | cons y t => simp [sameSet]
  | cons x m ih =>
    rw [List.nodup_cons] at hm
    have : (fun a => monoEval a (x :: m)) = fun a => xv x a * monoEval a m := by
      funext a; simp [monoEval, xv]
    rw [this, cf_mul x _ t ht]
    by_cases hx : x ∈ t
    · rw [if_pos hx, ih hm.2 _ (ht.erase x), ih hm.2 t ht]
      have h1 : sameSet t m = false := by
        cases h : sameSet t m
        · rfl
        · exact absurd (((sameSet_iff t m).mp h x).mp hx) hm.1
      have h2 : sameSet (t.erase x) m = sameSet t (x :: m) := by
        apply Bool.eq_iff_iff.mpr
        rw [sameSet_iff, sameSet_iff]
        constructor
        · intro h y
          rw [List.mem_cons]
          by_cases hyx : y = x
          · subst hyx; simp [hx]
          · rw [← h y, List.Nodup.mem_erase_iff ht]; simp [hyx]
        · intro h y
          rw [List.Nodup.mem_erase_iff ht, h y, List.mem_cons]
          constructor
          · rintro ⟨hyx, h' | h'⟩
            · exact absurd h' hyx
            · exact h'
          · intro hy; exact ⟨fun e => hm.1 (e ▸ hy), Or.inr hy⟩
      rw [h1, h2]; simp
    · rw [if_neg hx]
      have : sameSet t (x :: m) = false := by
        cases h : sameSet t (x :: m)
        · rfl
        · exact absurd (((sameSet_iff t _).mp h x).mpr List.mem_cons_self) hx
      rw [this]; rfl

/-! ## The monomial index -/

/-- Entries `i < N` with monomials `mon i` over variables `< nv`, `dn` and `up` links. -/
structure Idx where
  mon : Nat → List Nat
  dn : Nat → List (Nat × Nat)
  up : Nat → List (Nat × Nat)
  N : Nat
  nv : Nat

namespace Idx

abbrev rg (I : Idx) : List Nat := List.range I.N

/-- Entry of the monomial `m`, by `up` links from entry `0`. -/
def walk (I : Idx) : List Nat → Option Nat
  | [] => some 0
  | x :: m => match I.walk m with
    | some i => lk (I.up i) x
    | none => none

/-- The links of entry `i` are consistent. -/
def linkOk (I : Idx) (i : Nat) : Bool :=
  decide (I.mon i).Nodup && decide ((i = 0) ↔ I.mon i = []) &&
  sortedLt ((I.up i).map (·.1)) &&
  (I.mon i).all (fun x => decide (x < I.nv) &&
    match lk (I.dn i) x with
    | some j => decide (j < I.N) && decide (I.mon j = (I.mon i).erase x) &&
        decide (lk (I.up j) x = some i)
    | none => false) &&
  (I.up i).all (fun xt => decide (xt.2 < I.N) && decide (xt.1 ∈ I.mon xt.2) &&
    decide (lk (I.dn xt.2) xt.1 = some i))

structure OkSpec (I : Idx) (i : Nat) : Prop where
  nodup : (I.mon i).Nodup
  zero : (i = 0 ↔ I.mon i = [])
  upnd : ((I.up i).map (·.1)).Nodup
  dn : ∀ x ∈ I.mon i, x < I.nv ∧ ∃ j, lk (I.dn i) x = some j ∧ j < I.N ∧
    I.mon j = (I.mon i).erase x ∧ lk (I.up j) x = some i
  up : ∀ xt ∈ I.up i, xt.2 < I.N ∧ xt.1 ∈ I.mon xt.2 ∧ lk (I.dn xt.2) xt.1 = some i

theorem okSpec (I : Idx) (i : Nat) (h : I.linkOk i = true) : I.OkSpec i := by
  simp only [linkOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, (sortedLt_nodup _ h4).1, fun x hx => ?_,
    fun xt hxt => ⟨(h6 xt hxt).1.1, (h6 xt hxt).1.2, (h6 xt hxt).2⟩⟩
  obtain ⟨hxn, h5x⟩ := h5 x hx
  refine ⟨hxn, ?_⟩
  revert h5x
  cases hl : lk (I.dn i) x with
  | none => simp
  | some j =>
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rintro ⟨⟨a, b⟩, c⟩; exact ⟨j, rfl, a, b, c⟩

/-- `∑_i cf g (m_i) · ev i u`: coefficient `u` of the image of `g`. -/
def Rc (I : Idx) (ev : Nat → Nat → Int) (g : (Nat → Bool) → Int) (u : Nat) : Int :=
  lsum I.rg (fun i => cf g (I.mon i) * ev i u)

/-- Coefficient `u` of `R(x · m_s)`. -/
def NvC (I : Idx) (ev : Nat → Nat → Int) (x s u : Nat) : Int :=
  (match lk (I.up s) x with
    | some t => ev t u
    | none => 0) + (if x ∈ I.mon s then ev s u else 0)

/-- Coefficient `u` of the row of the monomial `m` (`0` if `m` is not an entry). -/
def wv (I : Idx) (ev : Nat → Nat → Int) (m : List Nat) (u : Nat) : Int :=
  match I.walk m with
  | some i => ev i u
  | none => 0

set_option linter.unusedSectionVars false in
section
variable (I : Idx) (hN : 0 < I.N) (hok : ∀ i, i < I.N → I.OkSpec i)
include hN hok

theorem walk_sound (m : List Nat) (hm : m.Nodup) (i : Nat) (hw : I.walk m = some i) :
    i < I.N ∧ ∀ y, y ∈ I.mon i ↔ y ∈ m := by
  induction m generalizing i with
  | nil =>
    simp only [walk, Option.some.injEq] at hw; subst hw
    refine ⟨hN, fun y => ?_⟩
    rw [(hok 0 hN).zero.mp rfl]
  | cons x m ih =>
    rw [List.nodup_cons] at hm
    simp only [walk] at hw
    cases hj : I.walk m with
    | none => rw [hj] at hw; cases hw
    | some j =>
      rw [hj] at hw
      obtain ⟨hjN, hjm⟩ := ih hm.2 j hj
      obtain ⟨hiN, hxi, hdn⟩ := (hok j hjN).up (x, i) (lk_mem hw)
      obtain ⟨_, j', hj', _, hmj', _⟩ := (hok i hiN).dn x hxi
      rw [hdn] at hj'; cases hj'
      refine ⟨hiN, fun y => ?_⟩
      rw [List.mem_cons]
      by_cases hyx : y = x
      · subst hyx; simp [hxi]
      · have := hjm y
        rw [hmj', List.Nodup.mem_erase_iff (hok i hiN).nodup] at this
        simp only [hyx, false_or]
        rw [← this]; simp [hyx]

theorem walk_complete (m : List Nat) (hm : m.Nodup) (i : Nat) (hi : i < I.N)
    (hs : ∀ y, y ∈ I.mon i ↔ y ∈ m) : I.walk m = some i := by
  induction m generalizing i with
  | nil =>
    have : I.mon i = [] := List.eq_nil_iff_forall_not_mem.mpr (fun y hy => by simpa using (hs y).mp hy)
    rw [(hok i hi).zero.mpr this]; rfl
  | cons x m ih =>
    rw [List.nodup_cons] at hm
    have hxi : x ∈ I.mon i := (hs x).mpr List.mem_cons_self
    obtain ⟨_, j, _, hjN, hmj, hup⟩ := (hok i hi).dn x hxi
    have hjs : ∀ y, y ∈ I.mon j ↔ y ∈ m := by
      intro y
      rw [hmj, List.Nodup.mem_erase_iff (hok i hi).nodup, hs y, List.mem_cons]
      constructor
      · rintro ⟨hyx, h | h⟩
        · exact absurd h hyx
        · exact h
      · intro hy; exact ⟨fun e => hm.1 (e ▸ hy), Or.inr hy⟩
    simp only [walk, ih hm.2 j hjN hjs, hup]

theorem sum_sameSet (m : List Nat) (hm : m.Nodup) (F : Nat → Int) :
    lsum I.rg (fun i => (if sameSet (I.mon i) m then 1 else 0) * F i) =
      (match I.walk m with
        | some i => F i
        | none => 0) := by
  cases hw : I.walk m with
  | none =>
    refine lsum_zero _ _ (fun i hi => ?_)
    have : sameSet (I.mon i) m = false := by
      cases h : sameSet (I.mon i) m
      · rfl
      · rw [I.walk_complete hN hok m hm i (List.mem_range.mp hi) ((sameSet_iff _ _).mp h)] at hw; cases hw
    rw [this]; simp
  | some i =>
    obtain ⟨hiN, his⟩ := I.walk_sound hN hok m hm i hw
    refine Eq.trans ?_ (lsum_ite_eq I.rg i F List.nodup_range (List.mem_range.mpr hiN))
    refine lsum_congr _ _ _ (fun j hj => ?_)
    by_cases hji : j = i
    · rw [if_pos hji]
      have : sameSet (I.mon j) m = true := by
        rw [sameSet_iff, hji]; exact his
      rw [this]; simp
    · rw [if_neg hji]
      have : sameSet (I.mon j) m = false := by
        cases h : sameSet (I.mon j) m
        · rfl
        · rw [I.walk_complete hN hok m hm j (List.mem_range.mp hj) ((sameSet_iff _ _).mp h)] at hw
          exact absurd (Option.some.inj hw) hji
      rw [this]; simp

/-- The image of a polynomial: one row per term, found by `walk`. -/
theorem Rc_eval (ev : Nat → Nat → Int) (P : Poly Nat) (hnd : ∀ cm ∈ P.terms, cm.2.Nodup) (u : Nat) :
    I.Rc ev (fun a => P.eval a) u = lsum P.terms (fun cm => cm.1 * I.wv ev cm.2 u) := by
  unfold Rc
  have : ∀ i ∈ I.rg, cf (fun a => P.eval a) (I.mon i) * ev i u =
      lsum P.terms (fun cm => cm.1 * ((if sameSet (I.mon i) cm.2 then 1 else 0) * ev i u)) := by
    intro i hi
    have hc : cf (fun a => P.eval a) (I.mon i) =
        lsum P.terms (fun cm => cm.1 * cf (fun b => monoEval b cm.2) (I.mon i)) := by
      unfold cf
      have := dt_sum (I.mon i) P.terms
      simp only [Poly.eval]
      rw [this]; exact sum_map_lsum _ _
    rw [hc, Int.mul_comm, ← lsum_mul]
    refine lsum_congr _ _ _ (fun cm hcm => ?_)
    rw [cf_mono cm.2 (hnd cm hcm) _ (hok i (List.mem_range.mp hi)).nodup]
    rw [Int.mul_comm, Int.mul_assoc]
  rw [lsum_congr _ _ _ this, lsum_swap]
  refine lsum_congr _ _ _ (fun cm hcm => ?_)
  rw [lsum_mul, sum_sameSet I hN hok cm.2 (hnd cm hcm) (fun i => ev i u)]
  rfl

end

/-- Soundness: the three row facts mod `p` rule out a degree-`D` refutation. -/
theorem sound (p D : Nat) (A : List (Poly Nat)) (I : Idx) (ev : Nat → Nat → Int) (col : Nat → Prop)
    (pos : Nat → Nat) (u0 : Nat) (hN : 0 < I.N) (hok : ∀ i, i < I.N → I.linkOk i = true)
    (hax : ∀ P ∈ A, P.deg ≤ D → ∀ u, col u → (p : Int) ∣ I.Rc ev (fun a => P.eval a) u)
    (hmul : ∀ s, s < I.N → (I.mon s).length < D → ∀ x, x < I.nv → ∀ u, col u →
      (p : Int) ∣ I.NvC ev x s u - lsum I.rg (fun j => ev s (pos j) * I.NvC ev x j u))
    (hpos : ∀ j, col (pos j)) (hu0 : col u0) (hone : ¬ (p : Int) ∣ ev 0 u0) :
    ¬ PPCRefutation p A D := by
  have hok' : ∀ i, i < I.N → I.OkSpec i := fun i hi => I.okSpec i (hok i hi)
  have key : ∀ g, PPCDerivable p A D g → ∀ u, col u → (p : Int) ∣ I.Rc ev g u := by
    intro g hg
    induction hg with
    | ax P hP hd => exact hax P hP hd
    | lin f g a b _ _ ihf ihg =>
      intro w hw
      have e : I.Rc ev (fun x => a * f x + b * g x) w = a * I.Rc ev f w + b * I.Rc ev g w := by
        unfold Rc; rw [← lsum_mul, ← lsum_mul, ← lsum_add]
        exact lsum_congr _ _ _ (fun i _ => by rw [cf_lin, Int.add_mul, Int.mul_assoc, Int.mul_assoc])
      rw [e]
      exact Int.dvd_add (Int.dvd_trans (ihf w hw) (Int.dvd_mul_left _ _))
        (Int.dvd_trans (ihg w hw) (Int.dvd_mul_left _ _))
    | congr f g _ hfg ih =>
      intro u hu
      have e : I.Rc ev f u = I.Rc ev g u +
          lsum I.rg (fun i => (cf f (I.mon i) - cf g (I.mon i)) * ev i u) := by
        unfold Rc; rw [← lsum_add]
        exact lsum_congr _ _ _ (fun t _ => by rw [Int.sub_mul]; omega)
      rw [e]
      exact Int.dvd_add (ih u hu) (lsum_dvd _ _ _ (fun t _ =>
        Int.dvd_trans (cf_congr p f g hfg _) (Int.dvd_mul_right _ _)))
    | mul x g d _ hcd hdD ih =>
      intro u hu
      have s1 : I.Rc ev (fun a => xv x a * g a) u =
          lsum I.rg (fun i => (if x ∈ I.mon i then cf g ((I.mon i).erase x) + cf g (I.mon i) else 0) *
            ev i u) := by
        unfold Rc
        exact lsum_congr _ _ _ (fun i hi => by rw [cf_mul x g _ (hok' i (List.mem_range.mp hi)).nodup])
      by_cases hx : x < I.nv
      · have hup : ∀ j ∈ I.rg, lsum I.rg (fun i =>
              if x ∈ I.mon i ∧ lk (I.dn i) x = some j then cf g (I.mon j) * ev i u else 0) =
            cf g (I.mon j) * (match lk (I.up j) x with
              | some t => ev t u
              | none => 0) := by
          intro j hj
          cases hl : lk (I.up j) x with
          | none =>
            simp only [Int.mul_zero]
            refine lsum_zero _ _ (fun i hi => ?_)
            rw [if_neg]
            rintro ⟨hxm, hdn⟩
            obtain ⟨_, j', hj', _, _, hupj⟩ := (hok' i (List.mem_range.mp hi)).dn x hxm
            rw [hdn] at hj'; cases hj'
            rw [hl] at hupj; cases hupj
          | some t =>
            have hmt := (hok' j (List.mem_range.mp hj)).up (x, t) (lk_mem hl)
            refine Eq.trans ?_ (lsum_ite_eq I.rg t (fun i => cf g (I.mon j) * ev i u) List.nodup_range
              (List.mem_range.mpr hmt.1))
            refine lsum_congr _ _ _ (fun i hi => ?_)
            by_cases hit : i = t
            · rw [if_pos hit, if_pos]
              rw [hit]; exact ⟨hmt.2.1, hmt.2.2⟩
            · rw [if_neg hit, if_neg]
              rintro ⟨hxm, hdn⟩
              obtain ⟨_, j', hj', _, _, hupj⟩ := (hok' i (List.mem_range.mp hi)).dn x hxm
              rw [hdn] at hj'; cases hj'
              rw [hl] at hupj; cases hupj; exact hit rfl
        have e1 : ∀ j ∈ I.rg, cf g (I.mon j) * I.NvC ev x j u =
            lsum I.rg (fun i =>
              if x ∈ I.mon i ∧ lk (I.dn i) x = some j then cf g (I.mon j) * ev i u else 0) +
            (if x ∈ I.mon j then cf g (I.mon j) * ev j u else 0) := by
          intro j hj
          rw [hup j hj]; unfold NvC; rw [Int.mul_add]
          congr 1
          by_cases hxm : x ∈ I.mon j
          · rw [if_pos hxm, if_pos hxm]
          · rw [if_neg hxm, if_neg hxm, Int.mul_zero]
        have e2 : ∀ i ∈ I.rg, lsum I.rg (fun j =>
              if x ∈ I.mon i ∧ lk (I.dn i) x = some j then cf g (I.mon j) * ev i u else 0) =
            if x ∈ I.mon i then cf g ((I.mon i).erase x) * ev i u else 0 := by
          intro i hi
          by_cases hxm : x ∈ I.mon i
          · rw [if_pos hxm]
            obtain ⟨_, j, hj, hjN, hjm, _⟩ := (hok' i (List.mem_range.mp hi)).dn x hxm
            rw [← hjm]
            refine Eq.trans ?_ (lsum_ite_eq I.rg j (fun j' => cf g (I.mon j') * ev i u) List.nodup_range
              (List.mem_range.mpr hjN))
            refine lsum_congr _ _ _ (fun j' _ => ?_)
            by_cases hjj : j' = j
            · rw [if_pos ⟨hxm, by rw [hj, hjj]⟩, if_pos hjj]
            · rw [if_neg (fun h => hjj (by have h2 := h.2; rw [hj] at h2; exact (Option.some.inj h2).symm)),
                if_neg hjj]
          · rw [if_neg hxm]; exact lsum_zero _ _ (fun j _ => by rw [if_neg (fun h => hxm h.1)])
        have s2 : lsum I.rg (fun i => (if x ∈ I.mon i then cf g ((I.mon i).erase x) + cf g (I.mon i)
              else 0) * ev i u)
            = lsum I.rg (fun j => cf g (I.mon j) * I.NvC ev x j u) := by
          rw [lsum_congr _ _ _ e1, lsum_add, lsum_swap, lsum_congr _ _ _ e2, ← lsum_add]
          exact lsum_congr _ _ _ (fun t _ => by split <;> simp [Int.add_mul])
        have s3 : (p : Int) ∣ lsum I.rg (fun s => cf g (I.mon s) *
            (I.NvC ev x s u - lsum I.rg (fun j => ev s (pos j) * I.NvC ev x j u))) := by
          refine lsum_dvd _ _ _ (fun s hs => ?_)
          have h1 := List.mem_range.mp hs
          by_cases hsD : (I.mon s).length < D
          · exact Int.dvd_trans (hmul s h1 hsD x hx u hu) (Int.dvd_mul_left _ _)
          · exact Int.dvd_trans (cf_cubeDeg hcd _ (hok' s h1).nodup (by omega)) (Int.dvd_mul_right _ _)
        have s4 : lsum I.rg (fun s => cf g (I.mon s) * lsum I.rg (fun j => ev s (pos j) * I.NvC ev x j u)) =
            lsum I.rg (fun j => I.NvC ev x j u * I.Rc ev g (pos j)) := by
          rw [lsum_congr _ _ _ (fun s _ => (lsum_mul _ _ _).symm), lsum_swap]
          refine lsum_congr _ _ _ (fun j _ => ?_)
          unfold Rc; rw [← lsum_mul]
          exact lsum_congr _ _ _ (fun s _ => by simp only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm])
        have h4 : (p : Int) ∣ lsum I.rg (fun j => I.NvC ev x j u * I.Rc ev g (pos j)) :=
          lsum_dvd _ _ _ (fun j _ => Int.dvd_trans (ih (pos j) (hpos j)) (Int.dvd_mul_left _ _))
        have e5 : lsum I.rg (fun j => cf g (I.mon j) * I.NvC ev x j u) =
            lsum I.rg (fun s => cf g (I.mon s) *
              (I.NvC ev x s u - lsum I.rg (fun j => ev s (pos j) * I.NvC ev x j u))) +
            lsum I.rg (fun s => cf g (I.mon s) * lsum I.rg (fun j => ev s (pos j) * I.NvC ev x j u)) := by
          rw [← lsum_add]; exact lsum_congr _ _ _ (fun s _ => by rw [Int.mul_sub]; omega)
        rw [s1, s2, e5, s4]
        exact Int.dvd_add s3 h4
      · rw [s1, lsum_zero _ _ (fun i hi => ?_)]
        · exact ⟨0, by simp⟩
        rw [if_neg]; · simp
        intro h
        exact hx ((hok' i (List.mem_range.mp hi)).dn x h).1
  intro hr
  have h1 := key _ hr u0 hu0
  have h0 : I.Rc ev (fun _ => 1) u0 = ev 0 u0 := by
    unfold Rc
    refine Eq.trans ?_ (lsum_ite_eq I.rg 0 (fun i => ev i u0) List.nodup_range (List.mem_range.mpr hN))
    refine lsum_congr _ _ _ (fun i hi => ?_)
    rw [cf_const]
    have := (hok' i (List.mem_range.mp hi)).zero
    by_cases h : i = 0
    · rw [if_pos (this.mp h), if_pos h, Int.one_mul]
    · rw [if_neg (fun h' => h (this.mpr h')), if_neg h, Int.zero_mul]
  rw [h0] at h1
  exact hone h1

end Idx

end Programme.«20261025-1627-proof-complexity».PCCertCore
