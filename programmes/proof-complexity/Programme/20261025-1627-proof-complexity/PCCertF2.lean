import Programme.«20261025-1627-proof-complexity».PCCertCore

/-!
# Bitset R-operator certificates over `Z/2` (fast kernel check)

Same argument as `Programme.«20261025-0459-proof-complexity».PCCert2.Cert.sound`, specialised to
`p = 2`; the monomial index and the soundness argument are the shared `Work.PCCertCore.Idx.sound`,
and this file only checks the rows. Rows `R(m_i)` are bitsets `bs` (bit `u` = coefficient of
entry `u`). The multiplication identities `R(x·m_s) = ∑_e R(m_s)_e · R(x·m_e)` are checked for
all variables `x` at once: `bigOf s` packs the rows `R(x·m_s)` side by side (block `x` at bit
offset `x·W`), so the check is one xor per term of `R(m_s)` (`rl`, the list of its entries).
Axioms are checked through the monomial formula `cf (monoEval m) t = [t and m have the same
elements]`, finding the entry of `m` by walking the `up` links from entry `0`.
-/

namespace Programme.«20261025-1627-proof-complexity».PCCertF2

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».FinDiff Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».PCCert (lsum lsum_add lsum_mul lsum_congr lsum_dvd lsum_zero lsum_sub lsum_swap lsum_ite_eq)
open Programme.«20261025-0459-proof-complexity».PCCert2 (lk lk_mem)
open Programme.«20261025-1627-proof-complexity».PCCertCore

structure Ent where
  mon : List Nat
  bs : Nat
  rl : List Nat
  dn : List (Nat × Nat)
  up : List (Nat × Nat)

inductive Tr where
  | lf : Tr
  | nd : Tr → Nat → Ent → Tr → Tr

def dflt : Ent := ⟨[], 0, [], [], []⟩

def Tr.find : Tr → Nat → Ent
  | .lf, _ => dflt
  | .nd l k e r, i => if i < k then l.find i else if k < i then r.find i else e

/-- `f e₁ ^^^ f e₂ ^^^ … ^^^ 0`. -/
def xf {α : Type} (L : List α) (f : α → Nat) : Nat := L.foldr (fun e acc => f e ^^^ acc) 0

/-- Decode pairs `(a, b)` stored as digits `a * 8192 + b + 1`. -/
def decP (B : Nat) (f n : Nat) : List (Nat × Nat) := (decL B f n).map fun c => (c / 8192, c % 8192)

structure Cert where
  T : Tr
  N : Nat
  M : Nat
  W : Nat
  nv : Nat
  u0 : Nat

namespace Cert

def E (C : Cert) (i : Nat) : Ent := C.T.find i

/-- The monomial index of the certificate. -/
def I (C : Cert) : Idx := ⟨fun i => (C.E i).mon, fun i => (C.E i).dn, fun i => (C.E i).up, C.N, C.nv⟩

/-- Coefficient `u` of the row of entry `i`. -/
def ev (C : Cert) (i u : Nat) : Int := bt (C.E i).bs u

/-- The rows `R(x · m_s)`, `x < nv`, side by side. -/
def bigOf (C : Cert) (s : Nat) : Nat :=
  xf (C.E s).up (fun xt => (C.E xt.2).bs <<< (xt.1 * C.W)) ^^^
  xf (C.E s).mon (fun x => (C.E s).bs <<< (x * C.W))

/-- The row of the monomial `m` (`0` if it is not an entry). -/
def wbs (C : Cert) (m : List Nat) : Nat :=
  match C.I.walk m with
  | some i => (C.E i).bs
  | none => 0

def axRow (C : Cert) (P : Poly Nat) : Nat :=
  xf P.terms (fun cm => if cm.1 % 2 = 0 then 0 else C.wbs cm.2)

def okMon (C : Cert) (i : Nat) : Bool := C.I.linkOk i && decide ((C.E i).bs < 2 ^ C.W)

def okI (D : Nat) (C : Cert) (i : Nat) : Bool :=
  C.okMon i && (decide (i < C.M) || decide (D ≤ (C.E i).mon.length))

def mulI (C : Cert) (s : Nat) : Bool :=
  (C.E s).rl.all (fun e => decide (e < C.N)) &&
  (C.E s).bs == xf (C.E s).rl (fun e => 1 <<< e) &&
  C.bigOf s == xf (C.E s).rl (fun e => C.bigOf e)

def axOk (D : Nat) (A : List (Poly Nat)) (C : Cert) : Bool :=
  A.all (fun P => !decide (P.deg ≤ D) ||
    (P.terms.all (fun cm => decide cm.2.Nodup) && C.axRow P == 0))

def check (D : Nat) (A : List (Poly Nat)) (C : Cert) : Bool :=
  decide (0 < C.N) && rAll (C.okI D) 0 C.N && C.axOk D A && rAll C.mulI 0 C.M &&
  (C.E 0).bs.testBit C.u0

end Cert

/-! ## Bits mod 2 -/

theorem bt_xor (a b u : Nat) : bt (a ^^^ b) u = bt a u + bt b u - 2 * (bt a u * bt b u) := by
  unfold bt; rw [Nat.testBit_xor]
  cases a.testBit u <;> cases b.testBit u <;> decide

theorem bt_xf {α : Type} (L : List α) (f : α → Nat) (u : Nat) :
    (2 : Int) ∣ bt (xf L f) u - lsum L (fun e => bt (f e) u) := by
  induction L with
  | nil => exact ⟨0, by simp [xf, bt, lsum]⟩
  | cons a L ih =>
    have e : xf (a :: L) f = f a ^^^ xf L f := rfl
    rw [e, bt_xor]; simp only [lsum]
    obtain ⟨c, hc⟩ := ih
    exact ⟨c - bt (f a) u * bt (xf L f) u, by rw [Int.mul_sub, ← hc]; omega⟩

namespace Cert

abbrev NvC (C : Cert) : Nat → Nat → Nat → Int := C.I.NvC C.ev

theorem NvC_eq (C : Cert) (x s u : Nat) : C.NvC x s u =
    (match lk (C.E s).up x with
      | some t => bt (C.E t).bs u
      | none => 0) + (if x ∈ (C.E s).mon then bt (C.E s).bs u else 0) := rfl

set_option linter.unusedSectionVars false in
section
variable (C : Cert) (hN : 0 < C.N) (hok : ∀ i, i < C.N → C.I.OkSpec i ∧ (C.E i).bs < 2 ^ C.W)
include hN hok

theorem ax_ok (P : Poly Nat) (hnd : ∀ cm ∈ P.terms, cm.2.Nodup) (h0 : C.axRow P = 0) (u : Nat) :
    (2 : Int) ∣ C.I.Rc C.ev (fun a => P.eval a) u := by
  rw [Idx.Rc_eval C.I hN (fun i hi => (hok i hi).1) C.ev P hnd u]
  have hw : ∀ m, C.I.wv C.ev m u = bt (C.wbs m) u := fun m => by
    unfold Idx.wv wbs ev; cases C.I.walk m <;> simp [bt_zero]
  have e2 := bt_xf P.terms (fun cm => if cm.1 % 2 = 0 then 0 else C.wbs cm.2) u
  have e3 : xf P.terms (fun cm => if cm.1 % 2 = 0 then 0 else C.wbs cm.2) = 0 := h0
  rw [e3, bt_zero, Int.zero_sub, Int.dvd_neg] at e2
  have : (2 : Int) ∣ lsum P.terms (fun cm => cm.1 * C.I.wv C.ev cm.2 u) -
      lsum P.terms (fun cm => bt (if cm.1 % 2 = 0 then 0 else C.wbs cm.2) u) := by
    rw [← lsum_sub]
    refine lsum_dvd _ _ _ (fun cm _ => ?_)
    rw [hw]
    by_cases hc : cm.1 % 2 = 0
    · rw [if_pos hc, bt_zero, Int.sub_zero]
      exact Int.dvd_trans (Int.dvd_of_emod_eq_zero hc) (Int.dvd_mul_right _ _)
    · rw [if_neg hc]
      have : (2 : Int) ∣ cm.1 - 1 := by omega
      obtain ⟨c, hc'⟩ := this
      exact ⟨c * bt (C.wbs cm.2) u, by
        have : cm.1 = 2 * c + 1 := by omega
        rw [this]; rw [Int.add_mul, Int.one_mul, Int.mul_assoc]; omega⟩
  have := Int.dvd_add this e2
  rwa [Int.sub_add_cancel] at this

theorem bigOf_bit (s : Nat) (hs : s < C.N) (x u : Nat) (hu : u < C.W) :
    (2 : Int) ∣ bt (C.bigOf s) (x * C.W + u) - C.NvC x s u := by
  have hS := (hok s hs).1
  unfold bigOf
  rw [bt_xor]
  have a1 := bt_xf (C.E s).up (fun xt => (C.E xt.2).bs <<< (xt.1 * C.W)) (x * C.W + u)
  have a2 := bt_xf (C.E s).mon (fun y => (C.E s).bs <<< (y * C.W)) (x * C.W + u)
  have b1 : lsum (C.E s).up (fun xt => bt ((C.E xt.2).bs <<< (xt.1 * C.W)) (x * C.W + u)) =
      (match lk (C.E s).up x with
        | some t => bt (C.E t).bs u
        | none => 0) := by
    refine Eq.trans ?_ (lsum_lk _ hS.upnd x (fun t => bt (C.E t).bs u))
    exact lsum_congr _ _ _ (fun xt hxt => bt_shift (hok _ (hS.up xt hxt).1).2 _ _ _ hu)
  have b2 : lsum (C.E s).mon (fun y => bt ((C.E s).bs <<< (y * C.W)) (x * C.W + u)) =
      (if x ∈ (C.E s).mon then bt (C.E s).bs u else 0) := by
    refine Eq.trans ?_ (lsum_mem _ hS.nodup x (bt (C.E s).bs u))
    exact lsum_congr _ _ _ (fun y _ => bt_shift (hok s hs).2 _ _ _ hu)
  rw [b1] at a1; rw [b2] at a2
  rw [NvC_eq]
  obtain ⟨c1, h1⟩ := a1; obtain ⟨c2, h2⟩ := a2
  exact ⟨c1 + c2 - bt (xf (C.E s).up fun xt => (C.E xt.2).bs <<< (xt.1 * C.W)) (x * C.W + u) *
    bt (xf (C.E s).mon fun y => (C.E s).bs <<< (y * C.W)) (x * C.W + u), by
    rw [Int.mul_sub, Int.mul_add]; omega⟩

theorem NvC_ge (s : Nat) (hs : s < C.N) (x u : Nat) (hu : C.W ≤ u) : C.NvC x s u = 0 := by
  rw [NvC_eq, bt_ge (hok s hs).2 hu]
  cases hl : lk (C.E s).up x with
  | none => simp
  | some t =>
    have := ((hok s hs).1.up (x, t) (lk_mem hl)).1
    simp [bt_ge (hok t this).2 hu]

/-- The multiplication identity for one `s`, from the packed check. -/
theorem mul_id (s : Nat) (hs : s < C.N) (hrl : ∀ e ∈ (C.E s).rl, e < C.N)
    (hbs : (C.E s).bs = xf (C.E s).rl (fun e => 1 <<< e))
    (hbig : C.bigOf s = xf (C.E s).rl (fun e => C.bigOf e)) (x u : Nat) :
    (2 : Int) ∣ C.NvC x s u - lsum C.I.rg (fun j => bt (C.E s).bs j * C.NvC x j u) := by
  -- the right side is `∑_{e ∈ rl} NvC x e u` mod 2
  have r1 : (2 : Int) ∣ lsum C.I.rg (fun j => bt (C.E s).bs j * C.NvC x j u) -
      lsum (C.E s).rl (fun e => C.NvC x e u) := by
    have : lsum (C.E s).rl (fun e => C.NvC x e u) =
        lsum C.I.rg (fun j => lsum (C.E s).rl (fun e => if e = j then 1 else 0) * C.NvC x j u) := by
      rw [lsum_congr C.I.rg _ (fun j => lsum (C.E s).rl (fun e => if j = e then C.NvC x j u else 0))
        (fun j _ => by
          rw [Int.mul_comm, ← lsum_mul]
          exact lsum_congr _ _ _ (fun e _ => by
            by_cases h : e = j
            · rw [if_pos h, if_pos h.symm]; simp
            · rw [if_neg h, if_neg (fun h' => h h'.symm)]; simp))]
      rw [lsum_swap]
      exact lsum_congr _ _ _ (fun e he =>
        (lsum_ite_eq C.I.rg e (fun j => C.NvC x j u) List.nodup_range (List.mem_range.mpr (hrl e he))).symm)
    rw [this, ← lsum_sub]
    refine lsum_dvd _ _ _ (fun j _ => ?_)
    rw [← Int.sub_mul]
    refine Int.dvd_trans ?_ (Int.dvd_mul_right _ _)
    have := bt_xf (C.E s).rl (fun e => 1 <<< e) j
    rw [← hbs] at this
    simp only [bt_one_shift] at this
    exact this
  by_cases hu : u < C.W
  · have l1 := C.bigOf_bit hN hok s hs x u hu
    rw [hbig] at l1
    have l2 := bt_xf (C.E s).rl (fun e => C.bigOf e) (x * C.W + u)
    have l3 : (2 : Int) ∣ lsum (C.E s).rl (fun e => bt (C.bigOf e) (x * C.W + u)) -
        lsum (C.E s).rl (fun e => C.NvC x e u) := by
      rw [← lsum_sub]
      exact lsum_dvd _ _ _ (fun e he => C.bigOf_bit hN hok e (hrl e he) x u hu)
    obtain ⟨a, ha⟩ := l1; obtain ⟨b, hb⟩ := l2; obtain ⟨c, hc⟩ := l3; obtain ⟨d, hd⟩ := r1
    exact ⟨b + c - a - d, by rw [Int.mul_sub, Int.mul_sub, Int.mul_add]; omega⟩
  · rw [C.NvC_ge hN hok s hs x u (by omega), lsum_zero _ _ (fun j hj => by
      rw [C.NvC_ge hN hok j (List.mem_range.mp hj) x u (by omega), Int.mul_zero])]
    exact ⟨0, by simp⟩

end

theorem sound (D : Nat) (A : List (Poly Nat)) (C : Cert) (hc : C.check D A = true) :
    ¬ PPCRefutation 2 A D := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hN, hall0⟩, hax0⟩, hmul0⟩, hone⟩ := hc
  have hall : ∀ i, i < C.N → (C.I.linkOk i = true ∧ (C.E i).bs < 2 ^ C.W) ∧
      (i < C.M ∨ D ≤ (C.E i).mon.length) := by
    intro i hi
    have := rAll_spec hall0 i hi
    simp only [okI, okMon, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
    exact this
  have hax : ∀ P ∈ A, ¬ P.deg ≤ D ∨ ((∀ cm ∈ P.terms, cm.2.Nodup) ∧ C.axRow P = 0) := by
    simp only [axOk, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hax0
    exact hax0
  have hmul : ∀ s, s < C.M → ((∀ e ∈ (C.E s).rl, e < C.N) ∧ (C.E s).bs = xf (C.E s).rl (fun e => 1 <<< e)) ∧
      C.bigOf s = xf (C.E s).rl (fun e => C.bigOf e) := by
    intro s hs
    have := rAll_spec hmul0 s hs
    simp only [mulI, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact this
  have hok : ∀ i, i < C.N → C.I.OkSpec i ∧ (C.E i).bs < 2 ^ C.W :=
    fun i hi => ⟨C.I.okSpec i (hall i hi).1.1, (hall i hi).1.2⟩
  refine Idx.sound 2 D A C.I C.ev (fun _ => True) (fun j => j) C.u0 hN (fun i hi => (hall i hi).1.1)
    (fun P hP hd u _ => ?_) (fun s hs hsD x _ u _ => ?_) (fun _ => trivial) trivial ?_
  · rcases hax P hP with h | ⟨h1, h2⟩
    · exact absurd hd h
    · exact C.ax_ok hN hok P h1 h2 u
  · have hM : s < C.M := by
      rcases (hall s hs).2 with h | h
      · exact h
      · exact absurd hsD (Nat.not_lt.mpr h)
    obtain ⟨⟨hrl, hbs⟩, hbig⟩ := hmul s hM
    exact C.mul_id hN hok s hs hrl hbs hbig x u
  · show ¬ (2 : Int) ∣ bt (C.E 0).bs C.u0
    unfold bt; rw [hone, if_pos rfl]; decide

end Cert

end Programme.«20261025-1627-proof-complexity».PCCertF2

#print axioms Programme.«20261025-1627-proof-complexity».PCCertF2.Cert.sound
