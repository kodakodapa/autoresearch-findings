import Programme.«20261025-1627-proof-complexity».PCCertCore

/-!
# Bit-sliced R-operator certificates over `Z/3` (fast kernel check)

Same argument as `Work.PCCertF2.Cert.sound`, for `p = 3`: the monomial index and the soundness
argument are the shared `Work.PCCertCore.Idx.sound`, and this file only checks the rows. A vector over `Z/3` is a pair of Nats
`(a, b)` ("bit planes"); coordinate `u` has value `a_u + 2 b_u (mod 3)` (`val`). Addition is a
9-operation bit formula (`add3`), correct mod 3 on every input (no invariant needed), negation swaps
the planes, and `isZ` (planes equal) implies every coordinate is `0 mod 3`.

Each entry stores its row `R(m_i)` as a vector `bs`; entries of degree `< D` also store it as a
list `rl` of `(entry, coefficient)` pairs, checked against `bs`. As in the `Z/2` checker, the identities `R(x·m_s) = ∑_e R(m_s)_e · R(x·m_e)`
are checked for all variables `x` at once on rows packed side by side (`bigOf`), and the axioms
through the monomial formula `cf_mono`, finding entries by walking the `up` links from entry `0`.
-/

namespace Programme.«20261025-1627-proof-complexity».PCCertF3

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».FinDiff Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».PCCert (lsum lsum_add lsum_mul lsum_congr lsum_dvd lsum_zero lsum_sub lsum_swap lsum_ite_eq)
open Programme.«20261025-0459-proof-complexity».PCCert2 (lk lk_mem)
open Programme.«20261025-1627-proof-complexity».PCCertCore

/-! ## Vectors over `Z/3` as bit planes -/

abbrev V := Nat × Nat

def add3 (x y : V) : V :=
  let s := x.2 ^^^ y.1
  (x.1 ^^^ (s &&& ((x.1 ^^^ y.1) ||| (x.1 ^^^ y.2))), y.2 ^^^ ((x.1 ^^^ x.2) &&& s))

def neg (v : V) : V := (v.2, v.1)

def sclN (c : Nat) (v : V) : V := if c % 3 = 0 then (0, 0) else if c % 3 = 1 then v else neg v

def scl (c : Int) (v : V) : V := sclN (c % 3).toNat v

def shl (v : V) (k : Nat) : V := (v.1 <<< k, v.2 <<< k)

def unit (e : Nat) : V := (1 <<< e, 0)

def isZ (v : V) : Bool := v.1 == v.2

/-- `f e₁ + f e₂ + … + 0` over `Z/3`. -/
def sumL {α : Type} (L : List α) (f : α → V) : V := L.foldr (fun e acc => add3 (f e) acc) (0, 0)

def val (v : V) (u : Nat) : Int := bt v.1 u + 2 * bt v.2 u

theorem val_add3 (x y : V) (u : Nat) : (3 : Int) ∣ val (add3 x y) u - val x u - val y u := by
  unfold val add3 bt
  simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and]
  cases x.1.testBit u <;> cases x.2.testBit u <;> cases y.1.testBit u <;> cases y.2.testBit u <;>
    simp <;> omega

theorem val_neg (v : V) (u : Nat) : (3 : Int) ∣ val (neg v) u + val v u := by
  simp only [val, neg]; exact ⟨bt v.1 u + bt v.2 u, by omega⟩

theorem val_zero (u : Nat) : val (0, 0) u = 0 := by simp [val, bt_zero]

theorem val_sclN (c : Nat) (v : V) (u : Nat) : (3 : Int) ∣ val (sclN c v) u - (c : Int) * val v u := by
  have e : (c : Int) * val v u = 3 * (((c / 3 : Nat) : Int) * val v u) + ((c % 3 : Nat) : Int) * val v u := by
    rw [← Int.mul_assoc, ← Int.add_mul]; congr 1; omega
  rw [e]
  unfold sclN
  by_cases h0 : c % 3 = 0
  · rw [if_pos h0, val_zero, h0]; exact ⟨-(((c / 3 : Nat) : Int) * val v u), by omega⟩
  · rw [if_neg h0]
    by_cases h1 : c % 3 = 1
    · rw [if_pos h1, h1]; exact ⟨-(((c / 3 : Nat) : Int) * val v u), by omega⟩
    · rw [if_neg h1]
      have h2 : c % 3 = 2 := by omega
      rw [h2]
      obtain ⟨d, hd⟩ := val_neg v u
      exact ⟨d - ((c / 3 : Nat) : Int) * val v u - val v u, by rw [Int.mul_sub, Int.mul_sub, ← hd]; omega⟩

theorem val_scl (c : Int) (v : V) (u : Nat) : (3 : Int) ∣ val (scl c v) u - c * val v u := by
  unfold scl
  have h1 := val_sclN (c % 3).toNat v u
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))] at h1
  have e : c * val v u = 3 * ((c / 3) * val v u) + (c % 3) * val v u := by
    rw [← Int.mul_assoc, ← Int.add_mul, Int.mul_ediv_add_emod]
  rw [e]
  obtain ⟨a, ha⟩ := h1
  exact ⟨a - c / 3 * val v u, by rw [Int.mul_sub]; omega⟩

theorem val_sumL {α : Type} (L : List α) (f : α → V) (u : Nat) :
    (3 : Int) ∣ val (sumL L f) u - lsum L (fun e => val (f e) u) := by
  induction L with
  | nil => exact ⟨0, by simp [sumL, val_zero, lsum]⟩
  | cons a L ih =>
    have e : sumL (a :: L) f = add3 (f a) (sumL L f) := rfl
    rw [e]; simp only [lsum]
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ := val_add3 (f a) (sumL L f) u
    exact ⟨c + d, by rw [Int.mul_add]; omega⟩

theorem val_isZ (v : V) (h : isZ v = true) (u : Nat) : (3 : Int) ∣ val v u := by
  unfold isZ at h; rw [beq_iff_eq] at h
  unfold val; rw [h]; exact ⟨bt v.2 u, by omega⟩

theorem val_unit (e j : Nat) : val (unit e) j = if e = j then 1 else 0 := by
  unfold val unit; rw [bt_one_shift, bt_zero]; simp

theorem val_ge {v : V} {W u : Nat} (h1 : v.1 < 2 ^ W) (h2 : v.2 < 2 ^ W) (hu : W ≤ u) : val v u = 0 := by
  unfold val; rw [bt_ge h1 hu, bt_ge h2 hu]; rfl

theorem val_shl {v : V} {W : Nat} (h1 : v.1 < 2 ^ W) (h2 : v.2 < 2 ^ W) (x' x u : Nat) (hu : u < W) :
    val (shl v (x' * W)) (x * W + u) = if x' = x then val v u else 0 := by
  unfold val shl; simp only
  rw [bt_shift h1 x' x u hu, bt_shift h2 x' x u hu]
  by_cases h : x' = x <;> simp [h]

def shr (v : V) (k : Nat) : V := (v.1 >>> k, v.2 >>> k)

theorem val_shr (v : V) (k j : Nat) : val (shr v k) j = val v (k + j) := by
  simp only [val, shr, bt, Nat.testBit_shiftRight]

/-- Bits `O ≤ u < W` of one block. -/
def blk (W O : Nat) : Nat := (2 ^ (W - O) - 1) <<< O

/-- Bits `x * W + u` with `x < k`, `O ≤ u < W`. -/
def mkM (W O : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => mkM W O k ||| (blk W O <<< (k * W))

def msk (m : Nat) (v : V) : V := (v.1 &&& m, v.2 &&& m)

theorem mk_bit (W O : Nat) {k x u : Nat} (hx : x < k) (h1 : O ≤ u) (h2 : u < W) :
    (mkM W O k).testBit (x * W + u) = true := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [mkM, Nat.testBit_or, Bool.or_eq_true]
    by_cases hxk : x < k
    · exact Or.inl (ih hxk)
    · right
      have hxe : x = k := by omega
      subst hxe
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨by omega, ?_⟩
      have : x * W + u - x * W = u := by omega
      rw [this, blk, Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq,
        Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
      omega

theorem val_msk (m : Nat) (v : V) (j : Nat) (h : m.testBit j = true) : val (msk m v) j = val v j := by
  simp only [val, msk, bt, Nat.testBit_and, h, Bool.and_true]

def Bd (W : Nat) (v : V) : Prop := v.1 < 2 ^ W ∧ v.2 < 2 ^ W

theorem bd_zero (W : Nat) : Bd W (0, 0) := ⟨Nat.two_pow_pos W, Nat.two_pow_pos W⟩

theorem bd_add3 {W : Nat} {x y : V} (hx : Bd W x) (hy : Bd W y) : Bd W (add3 x y) := by
  unfold add3
  exact ⟨Nat.xor_lt_two_pow hx.1 (Nat.and_lt_two_pow _
      (Nat.or_lt_two_pow (Nat.xor_lt_two_pow hx.1 hy.1) (Nat.xor_lt_two_pow hx.1 hy.2))),
    Nat.xor_lt_two_pow hy.2 (Nat.and_lt_two_pow _ (Nat.xor_lt_two_pow hx.2 hy.1))⟩

theorem bd_sclN {W : Nat} (c : Nat) {v : V} (hv : Bd W v) : Bd W (sclN c v) := by
  unfold sclN neg
  split
  · exact bd_zero W
  · split
    · exact hv
    · exact ⟨hv.2, hv.1⟩

theorem bd_unit {W e : Nat} (h : e < W) : Bd W (unit e) := by
  unfold unit
  refine ⟨?_, Nat.two_pow_pos W⟩
  show 1 <<< e < 2 ^ W
  rw [Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by decide) h

theorem bd_sumL {α : Type} {W : Nat} (L : List α) (f : α → V) (h : ∀ e ∈ L, Bd W (f e)) :
    Bd W (sumL L f) := by
  induction L with
  | nil => exact bd_zero W
  | cons a L ih =>
    exact bd_add3 (h a List.mem_cons_self) (ih (fun e he => h e (List.mem_cons_of_mem _ he)))

/-! ## Certificates -/

structure Ent where
  mon : List Nat
  bs : V
  rl : List (Nat × Nat)
  dn : List (Nat × Nat)
  up : List (Nat × Nat)

inductive Tr where
  | lf : Tr
  | nd : Tr → Nat → Ent → Tr → Tr

def dflt : Ent := ⟨[], (0, 0), [], [], []⟩

def Tr.find : Tr → Nat → Ent
  | .lf, _ => dflt
  | .nd l k e r, i => match Nat.blt i k with
    | true => l.find i
    | false => match Nat.blt k i with
      | true => r.find i
      | false => e

/-- Decode pairs `(a, b)` stored as digits `a * S + b + 1`. -/
def decQ (B S : Nat) (f n : Nat) : List (Nat × Nat) := (decL B f n).map fun c => (c / S, c % S)

structure Cert where
  T : Tr
  N : Nat
  M : Nat
  W : Nat
  nv : Nat
  u0 : Nat
  /-- Columns start at bit `O`; bits below it are salt (they keep big literals' low words distinct,
  which the kernel's caches hash on). -/
  O : Nat

namespace Cert

def E (C : Cert) (i : Nat) : Ent := C.T.find i

/-- The monomial index of the certificate. -/
def I (C : Cert) : Idx := ⟨fun i => (C.E i).mon, fun i => (C.E i).dn, fun i => (C.E i).up, C.N, C.nv⟩

/-- Coefficient `u` of the row of entry `i`. -/
def ev (C : Cert) (i u : Nat) : Int := val (C.E i).bs u

/-- The rows `R(x · m_s)`, `x < nv`, side by side. -/
def bigOf (C : Cert) (s : Nat) : V :=
  add3 (sumL (C.E s).up (fun xt => shl (C.E xt.2).bs (xt.1 * C.W)))
    (sumL (C.E s).mon (fun x => shl (C.E s).bs (x * C.W)))

/-- The row of the monomial `m` (`0` if it is not an entry). -/
def wbs (C : Cert) (m : List Nat) : V :=
  match C.I.walk m with
  | some i => (C.E i).bs
  | none => (0, 0)

def axRow (C : Cert) (P : Poly Nat) : V := sumL P.terms (fun cm => scl cm.1 (C.wbs cm.2))

def okMon (C : Cert) (i : Nat) : Bool :=
  C.I.linkOk i && decide ((C.E i).bs.1 < 2 ^ C.W) && decide ((C.E i).bs.2 < 2 ^ C.W)

def okI (D : Nat) (C : Cert) (i : Nat) : Bool :=
  C.okMon i && (decide (i < C.M) || decide (D ≤ (C.E i).mon.length))

def mulI (C : Cert) (s : Nat) : Bool :=
  (C.E s).rl.all (fun ec => decide (ec.1 < C.N)) &&
  isZ (shr (add3 (C.E s).bs (neg (sumL (C.E s).rl (fun ec => sclN ec.2 (unit (ec.1 + C.O)))))) C.O) &&
  isZ (msk (mkM C.W C.O C.nv) (add3 (C.bigOf s) (neg (sumL (C.E s).rl (fun ec => sclN ec.2 (C.bigOf ec.1))))))

def axOk (D : Nat) (A : List (Poly Nat)) (C : Cert) : Bool :=
  A.all (fun P => !decide (P.deg ≤ D) ||
    (P.terms.all (fun cm => decide cm.2.Nodup) && isZ (shr (C.axRow P) C.O)))

def check (D : Nat) (A : List (Poly Nat)) (C : Cert) : Bool :=
  decide (0 < C.N) && rAll (C.okI D) 0 C.N && C.axOk D A && rAll C.mulI 0 C.M && decide (C.O ≤ C.u0) &&
  ((C.E 0).bs.1.testBit C.u0 != (C.E 0).bs.2.testBit C.u0)

abbrev NvC (C : Cert) : Nat → Nat → Nat → Int := C.I.NvC C.ev

theorem NvC_eq (C : Cert) (x s u : Nat) : C.NvC x s u =
    (match lk (C.E s).up x with
      | some t => val (C.E t).bs u
      | none => 0) + (if x ∈ (C.E s).mon then val (C.E s).bs u else 0) := rfl

set_option linter.unusedSectionVars false in
section
variable (C : Cert) (hN : 0 < C.N) (hok : ∀ i, i < C.N → C.I.OkSpec i ∧ Bd C.W (C.E i).bs)
include hN hok

theorem ax_ok (P : Poly Nat) (hnd : ∀ cm ∈ P.terms, cm.2.Nodup) (h0 : isZ (shr (C.axRow P) C.O) = true)
    (u : Nat) (hu : C.O ≤ u) :
    (3 : Int) ∣ C.I.Rc C.ev (fun a => P.eval a) u := by
  have e1 : C.I.Rc C.ev (fun a => P.eval a) u = lsum P.terms (fun cm => cm.1 * val (C.wbs cm.2) u) := by
    rw [Idx.Rc_eval C.I hN (fun i hi => (hok i hi).1) C.ev P hnd u]
    refine lsum_congr _ _ _ (fun cm _ => ?_)
    unfold Idx.wv wbs ev
    cases C.I.walk cm.2 <;> simp [val_zero]
  rw [e1]
  have e2 := val_sumL P.terms (fun cm => scl cm.1 (C.wbs cm.2)) u
  have e3 := val_isZ _ h0 (u - C.O)
  rw [val_shr, show C.O + (u - C.O) = u by omega] at e3
  have e4 : (3 : Int) ∣ lsum P.terms (fun cm => val (scl cm.1 (C.wbs cm.2)) u) -
      lsum P.terms (fun cm => cm.1 * val (C.wbs cm.2) u) := by
    rw [← lsum_sub]; exact lsum_dvd _ _ _ (fun cm _ => val_scl _ _ _)
  unfold axRow at e3
  obtain ⟨a, ha⟩ := e2; obtain ⟨b, hb⟩ := e3; obtain ⟨c, hc⟩ := e4
  exact ⟨b - a - c, by rw [Int.mul_sub, Int.mul_sub]; omega⟩

theorem bigOf_val (s : Nat) (hs : s < C.N) (x u : Nat) (hu : u < C.W) :
    (3 : Int) ∣ val (C.bigOf s) (x * C.W + u) - C.NvC x s u := by
  have hS := (hok s hs).1
  unfold bigOf
  have a0 := val_add3 (sumL (C.E s).up (fun xt => shl (C.E xt.2).bs (xt.1 * C.W)))
    (sumL (C.E s).mon (fun y => shl (C.E s).bs (y * C.W))) (x * C.W + u)
  have a1 := val_sumL (C.E s).up (fun xt => shl (C.E xt.2).bs (xt.1 * C.W)) (x * C.W + u)
  have a2 := val_sumL (C.E s).mon (fun y => shl (C.E s).bs (y * C.W)) (x * C.W + u)
  have b1 : lsum (C.E s).up (fun xt => val (shl (C.E xt.2).bs (xt.1 * C.W)) (x * C.W + u)) =
      (match lk (C.E s).up x with
        | some t => val (C.E t).bs u
        | none => 0) := by
    refine Eq.trans ?_ (lsum_lk _ hS.upnd x (fun t => val (C.E t).bs u))
    exact lsum_congr _ _ _ (fun xt hxt =>
      val_shl (hok _ (hS.up xt hxt).1).2.1 (hok _ (hS.up xt hxt).1).2.2 _ _ _ hu)
  have b2 : lsum (C.E s).mon (fun y => val (shl (C.E s).bs (y * C.W)) (x * C.W + u)) =
      (if x ∈ (C.E s).mon then val (C.E s).bs u else 0) := by
    refine Eq.trans ?_ (lsum_mem _ hS.nodup x (val (C.E s).bs u))
    exact lsum_congr _ _ _ (fun y _ => val_shl (hok s hs).2.1 (hok s hs).2.2 _ _ _ hu)
  rw [b1] at a1; rw [b2] at a2
  rw [NvC_eq]
  obtain ⟨c0, h0⟩ := a0; obtain ⟨c1, h1⟩ := a1; obtain ⟨c2, h2⟩ := a2
  exact ⟨c0 + c1 + c2, by rw [Int.mul_add, Int.mul_add]; omega⟩

theorem NvC_ge (s : Nat) (hs : s < C.N) (x u : Nat) (hu : C.W ≤ u) : C.NvC x s u = 0 := by
  rw [NvC_eq, val_ge (hok s hs).2.1 (hok s hs).2.2 hu]
  cases hl : lk (C.E s).up x with
  | none => simp
  | some t =>
    have := ((hok s hs).1.up (x, t) (lk_mem hl)).1
    simp [val_ge (hok t this).2.1 (hok t this).2.2 hu]

/-- The multiplication identity for one `s`, from the packed check. -/
theorem mul_id (s : Nat) (hs : s < C.N) (hrl : ∀ ec ∈ (C.E s).rl, ec.1 < C.N)
    (hb : isZ (shr (add3 (C.E s).bs (neg (sumL (C.E s).rl (fun ec => sclN ec.2 (unit (ec.1 + C.O)))))) C.O) = true)
    (hz : isZ (msk (mkM C.W C.O C.nv)
      (add3 (C.bigOf s) (neg (sumL (C.E s).rl (fun ec => sclN ec.2 (C.bigOf ec.1)))))) = true)
    (x u : Nat) (hx : x < C.nv) (hO : C.O ≤ u) :
    (3 : Int) ∣ C.NvC x s u - lsum C.I.rg (fun j => val (C.E s).bs (j + C.O) * C.NvC x j u) := by
  -- the right side is `∑_{(e,c) ∈ rl} c · NvC x e u` mod 3
  have r1 : (3 : Int) ∣ lsum C.I.rg (fun j => val (C.E s).bs (j + C.O) * C.NvC x j u) -
      lsum (C.E s).rl (fun ec => (ec.2 : Int) * C.NvC x ec.1 u) := by
    have : lsum (C.E s).rl (fun ec => (ec.2 : Int) * C.NvC x ec.1 u) =
        lsum C.I.rg (fun j => lsum (C.E s).rl (fun ec => (ec.2 : Int) * (if ec.1 = j then 1 else 0)) *
          C.NvC x j u) := by
      rw [lsum_congr C.I.rg _ (fun j => lsum (C.E s).rl
          (fun ec => if j = ec.1 then (ec.2 : Int) * C.NvC x j u else 0))
        (fun j _ => by
          rw [Int.mul_comm, ← lsum_mul]
          exact lsum_congr _ _ _ (fun ec _ => by
            by_cases h : ec.1 = j
            · rw [if_pos h, if_pos h.symm]; simp [Int.mul_comm]
            · rw [if_neg h, if_neg (fun h' => h h'.symm)]; simp))]
      rw [lsum_swap]
      exact lsum_congr _ _ _ (fun ec he =>
        (lsum_ite_eq C.I.rg ec.1 (fun j => (ec.2 : Int) * C.NvC x j u) List.nodup_range
          (List.mem_range.mpr (hrl ec he))).symm)
    rw [this, ← lsum_sub]
    refine lsum_dvd _ _ _ (fun j _ => ?_)
    rw [← Int.sub_mul]
    refine Int.dvd_trans ?_ (Int.dvd_mul_right _ _)
    have h1 := val_sumL (C.E s).rl (fun ec => sclN ec.2 (unit (ec.1 + C.O))) (j + C.O)
    have h2 : (3 : Int) ∣ lsum (C.E s).rl (fun ec => val (sclN ec.2 (unit (ec.1 + C.O))) (j + C.O)) -
        lsum (C.E s).rl (fun ec => (ec.2 : Int) * (if ec.1 = j then 1 else 0)) := by
      rw [← lsum_sub]
      refine lsum_dvd _ _ _ (fun ec _ => ?_)
      have e : (if ec.1 = j then (1 : Int) else 0) = val (unit (ec.1 + C.O)) (j + C.O) := by
        rw [val_unit]; by_cases h : ec.1 = j <;> simp [h]
      rw [e]; exact val_sclN _ _ _
    have h3 : (3 : Int) ∣ val (add3 (C.E s).bs (neg (sumL (C.E s).rl
        (fun ec => sclN ec.2 (unit (ec.1 + C.O)))))) (j + C.O) := by
      have := val_isZ _ hb j
      rwa [val_shr, Nat.add_comm C.O j] at this
    have h4 := val_add3 (C.E s).bs (neg (sumL (C.E s).rl (fun ec => sclN ec.2 (unit (ec.1 + C.O)))))
      (j + C.O)
    have h5 := val_neg (sumL (C.E s).rl (fun ec => sclN ec.2 (unit (ec.1 + C.O)))) (j + C.O)
    obtain ⟨a, ha⟩ := h1; obtain ⟨b, hb⟩ := h2; obtain ⟨c, hc⟩ := h3; obtain ⟨d, hd⟩ := h4
    obtain ⟨e, he⟩ := h5
    exact ⟨c - d - e + a + b, by simp only [Int.mul_add, Int.mul_sub]; omega⟩
  by_cases hu : u < C.W
  · have l1 := C.bigOf_val hN hok s hs x u hu
    have l0 := val_isZ _ hz (x * C.W + u)
    rw [val_msk _ _ _ (mk_bit C.W C.O hx hO hu)] at l0
    have l0a := val_add3 (C.bigOf s) (neg (sumL (C.E s).rl (fun ec => sclN ec.2 (C.bigOf ec.1)))) (x * C.W + u)
    have l0b := val_neg (sumL (C.E s).rl (fun ec => sclN ec.2 (C.bigOf ec.1))) (x * C.W + u)
    have l2 := val_sumL (C.E s).rl (fun ec => sclN ec.2 (C.bigOf ec.1)) (x * C.W + u)
    have l3 : (3 : Int) ∣ lsum (C.E s).rl (fun ec => val (sclN ec.2 (C.bigOf ec.1)) (x * C.W + u)) -
        lsum (C.E s).rl (fun ec => (ec.2 : Int) * C.NvC x ec.1 u) := by
      rw [← lsum_sub]
      refine lsum_dvd _ _ _ (fun ec he => ?_)
      obtain ⟨a, ha⟩ := val_sclN ec.2 (C.bigOf ec.1) (x * C.W + u)
      obtain ⟨b, hb⟩ := C.bigOf_val hN hok ec.1 (hrl ec he) x u hu
      exact ⟨a + ec.2 * b, by rw [Int.mul_add, Int.mul_left_comm, ← hb, Int.mul_sub]; omega⟩
    obtain ⟨a, ha⟩ := l1; obtain ⟨b, hb⟩ := l0; obtain ⟨c, hc⟩ := l0a; obtain ⟨d, hd⟩ := l0b
    obtain ⟨e, he⟩ := l2; obtain ⟨f, hf⟩ := l3; obtain ⟨g, hg⟩ := r1
    exact ⟨b - c - d - a + e + f - g, by
      simp only [Int.mul_sub, Int.mul_add]; omega⟩
  · rw [C.NvC_ge hN hok s hs x u (by omega), lsum_zero _ _ (fun j hj => by
      rw [C.NvC_ge hN hok j (List.mem_range.mp hj) x u (by omega), Int.mul_zero])]
    exact ⟨0, by simp⟩

end

theorem sound (D : Nat) (A : List (Poly Nat)) (C : Cert) (hc : C.check D A = true) :
    ¬ PPCRefutation 3 A D := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hN, hall0⟩, hax0⟩, hmul0⟩, hO0⟩, hone⟩ := hc
  have hall : ∀ i, i < C.N → ((C.I.linkOk i = true ∧ (C.E i).bs.1 < 2 ^ C.W) ∧ (C.E i).bs.2 < 2 ^ C.W) ∧
      (i < C.M ∨ D ≤ (C.E i).mon.length) := by
    intro i hi
    have := rAll_spec hall0 i hi
    simp only [okI, okMon, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
    exact this
  have hax : ∀ P ∈ A, ¬ P.deg ≤ D ∨ ((∀ cm ∈ P.terms, cm.2.Nodup) ∧ isZ (shr (C.axRow P) C.O) = true) := by
    simp only [axOk, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      Bool.and_eq_true, decide_eq_true_eq] at hax0
    exact hax0
  have hmul : ∀ s, s < C.M → ((∀ ec ∈ (C.E s).rl, ec.1 < C.N) ∧
      isZ (shr (add3 (C.E s).bs (neg (sumL (C.E s).rl (fun ec => sclN ec.2 (unit (ec.1 + C.O)))))) C.O) = true) ∧
      isZ (msk (mkM C.W C.O C.nv)
        (add3 (C.bigOf s) (neg (sumL (C.E s).rl (fun ec => sclN ec.2 (C.bigOf ec.1)))))) = true := by
    intro s hs
    have := rAll_spec hmul0 s hs
    simp only [mulI, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
    exact this
  have hok : ∀ i, i < C.N → C.I.OkSpec i ∧ Bd C.W (C.E i).bs :=
    fun i hi => ⟨C.I.okSpec i (hall i hi).1.1.1, (hall i hi).1.1.2, (hall i hi).1.2⟩
  refine Idx.sound 3 D A C.I C.ev (fun u => C.O ≤ u) (fun j => j + C.O) C.u0 hN
    (fun i hi => (hall i hi).1.1.1) (fun P hP hd u hu => ?_) (fun s hs hsD x hx u hu => ?_)
    (fun _ => Nat.le_add_left _ _) hO0 ?_
  · rcases hax P hP with h | ⟨h1, h2⟩
    · exact absurd hd h
    · exact C.ax_ok hN hok P h1 h2 u hu
  · have hM : s < C.M := by
      rcases (hall s hs).2 with h | h
      · exact h
      · exact absurd hsD (Nat.not_lt.mpr h)
    obtain ⟨⟨hrl, hb⟩, hz⟩ := hmul s hM
    exact C.mul_id hN hok s hs hrl hb hz x u hx hu
  · show ¬ (3 : Int) ∣ val (C.E 0).bs C.u0
    unfold val bt
    revert hone
    cases (C.E 0).bs.1.testBit C.u0 <;> cases (C.E 0).bs.2.testBit C.u0 <;> simp <;> omega

end Cert

end Programme.«20261025-1627-proof-complexity».PCCertF3
