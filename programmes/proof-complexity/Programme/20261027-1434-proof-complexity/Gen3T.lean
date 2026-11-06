import Programme.«20261027-1434-proof-complexity».Gen3

/-!
# th's `T ⊗ R` generators at level 3

`GTR π` is the block product of the `T` tower (`[s ≥ 2]`) on pigeons `{a1,a2,a3}` × holes
`{h1,h2,h3}`, a rectangle tower (`[s ≥ 1]`) on `{r1,r2} × {s1,s2}`, the all-ones block on the other
`9` pigeons × the remaining hole, and the pin `(pp, ph)`. It is self-balanced at every level
`e ≤ 3` (`gtr_bal`); on a canonical 3-matching its value is the number of occurrences of the code
in `π.supp`, the 72 products of a 2-matching inside the `T` block and a rectangle edge (`gtr_count`).
-/

namespace Programme.«20261027-1434-proof-complexity».Gen3T

set_option linter.unusedVariables false
set_option linter.deprecated false

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ProdExt (SL locL)
open Programme.«20261026-1402-proof-complexity».TExt (lf SL_lf)
open Programme.«20261027-1434-proof-complexity».ProdM Programme.«20261027-1434-proof-complexity».LocLf Programme.«20261027-1434-proof-complexity».Towers Programme.«20261027-1434-proof-complexity».Code3 Programme.«20261027-1434-proof-complexity».Gen3

structure TP where
  a1 : Nat
  a2 : Nat
  a3 : Nat
  r1 : Nat
  r2 : Nat
  pp : Nat
  h1 : Nat
  h2 : Nat
  h3 : Nat
  s1 : Nat
  s2 : Nat
  ph : Nat

def TP.valid (π : TP) : Bool := d6 π.a1 π.a2 π.a3 π.r1 π.r2 π.pp 15 && d6 π.h1 π.h2 π.h3 π.s1 π.s2 π.ph 7

def bt (x1 x2 x3 y1 y2 z i : Nat) : Nat :=
  if i = x1 ∨ i = x2 ∨ i = x3 then 0 else if i = y1 ∨ i = y2 then 1 else if i = z then 3 else 2

def TP.bp (π : TP) : Nat → Nat := bt π.a1 π.a2 π.a3 π.r1 π.r2 π.pp
def TP.bh (π : TP) : Nat → Nat := bt π.h1 π.h2 π.h3 π.s1 π.s2 π.ph

def φTR : Nat → List Nat → Int
  | 0 => lf gT
  | 1 => lf gR
  | _ => lf g1

def gTR (c s : Nat) : Int := if c = 0 then gT s else if c = 1 then gR s else g1 s

theorem φTR_eq (c : Nat) (l : List Nat) : φTR c l = gTR c l.length := by
  match c with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => simp only [gTR, show n + 2 ≠ 0 by omega, show n + 2 ≠ 1 by omega, if_false]; rfl

def GTR (π : TP) : List Nat → Int := ProdM 4 π.bp π.bh 7 φTR

def pc (x y : Nat) : Bool := y < x && x / 7 != y / 7 && x % 7 != y % 7

def TP.ET (π : TP) : List Nat := grid [π.a1, π.a2, π.a3] [π.h1, π.h2, π.h3]
def TP.ER (π : TP) : List Nat := grid [π.r1, π.r2] [π.s1, π.s2]

def TP.supp (π : TP) : List Nat :=
  π.ET.flatMap (fun x => π.ET.flatMap (fun y => if pc x y then π.ER.map (fun z => cd x y z) else []))

theorem bt_iff {x1 x2 x3 y1 y2 z M : Nat} (h : d6 x1 x2 x3 y1 y2 z M = true) (i : Nat) :
    (bt x1 x2 x3 y1 y2 z i = 0 ↔ i ∈ [x1, x2, x3]) ∧ (bt x1 x2 x3 y1 y2 z i = 1 ↔ i ∈ [y1, y2]) ∧
    (bt x1 x2 x3 y1 y2 z i = 3 ↔ i ∈ [z]) ∧ (bt x1 x2 x3 y1 y2 z i = 2 ↔ i ∉ [x1, x2, x3, y1, y2, z]) := by
  have := d6_spec h
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  unfold bt
  split
  · omega
  · split
    · omega
    · split <;> omega

theorem nd3 {a b c : Nat} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) : [a, b, c].Nodup := by
  simp [h1, h2, h3]

theorem d6_ne3 {a b c d e f M : Nat} (h : d6 a b c d e f M = true) : a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ d ≠ e := by
  obtain ⟨-, -, -, -, -, -, h7, h8, -, -, -, h12, -, -, -, -, -, -, h19, -⟩ := d6_spec h
  exact ⟨h7, h8, h12, h19⟩

theorem gtr_bal (π : TP) (hv : π.valid = true) (e : Nat) (he : e ≤ 3) : Bal 2 7 8 (GTR π) (GTR π) e := by
  simp only [TP.valid, Bool.and_eq_true] at hv
  obtain ⟨hp, hh⟩ := hv
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := d6_lt hp; obtain ⟨n1, n2, n3, n4⟩ := d6_ne3 hp
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := d6_lt hh; obtain ⟨o1, o2, o3, o4⟩ := d6_ne3 hh
  have bp := bt_iff hp; have bh := bt_iff hh
  have cP0 : rsum (7 + 8) (fun s => if π.bp s = 0 then (1 : Int) else 0) = (3 : Nat) :=
    rsum_class _ [π.a1, π.a2, π.a3] (nd3 n1 n2 n3) (by simp; omega) _ (fun t => (bp t).1)
  have cH0 : rsum 7 (fun s => if π.bh s = 0 then (1 : Int) else 0) = (3 : Nat) :=
    rsum_class _ [π.h1, π.h2, π.h3] (nd3 o1 o2 o3) (by simp; omega) _ (fun t => (bh t).1)
  have cP1 : rsum (7 + 8) (fun s => if π.bp s = 1 then (1 : Int) else 0) = (2 : Nat) :=
    rsum_class _ [π.r1, π.r2] (nd2 n4) (by simp; omega) _ (fun t => (bp t).2.1)
  have cH1 : rsum 7 (fun s => if π.bh s = 1 then (1 : Int) else 0) = (2 : Nat) :=
    rsum_class _ [π.s1, π.s2] (nd2 o4) (by simp; omega) _ (fun t => (bh t).2.1)
  have cP3 : rsum (7 + 8) (fun s => if π.bp s = 3 then (1 : Int) else 0) = (1 : Nat) :=
    rsum_class _ [π.pp] (by simp) (by simp; omega) _ (fun t => (bp t).2.2.1)
  have cH3 : rsum 7 (fun s => if π.bh s = 3 then (1 : Int) else 0) = (1 : Nat) :=
    rsum_class _ [π.ph] (by simp) (by simp; omega) _ (fun t => (bh t).2.2.1)
  have cP2 : rsum (7 + 8) (fun s => if π.bp s = 2 then (1 : Int) else 0) = (9 : Nat) := by
    rw [rsum_coclass (7 + 8) _ (nd6 hp) (by simp; omega) (fun s => π.bp s = 2) (fun t => (bp t).2.2.2)]; rfl
  have cH2 : rsum 7 (fun s => if π.bh s = 2 then (1 : Int) else 0) = (1 : Nat) := by
    rw [rsum_coclass 7 _ (nd6 hh) (by simp; omega) (fun s => π.bh s = 2) (fun t => (bh t).2.2.2)]; rfl
  apply bal_prodM 2 (fun i _ => by unfold TP.bp bt; split <;> (try split) <;> (try split) <;> omega)
    (fun j _ => by unfold TP.bh bt; split <;> (try split) <;> (try split) <;> omega) φTR
    (fun c => by unfold φTR; split <;> exact SL_lf _)
    (fun c => if c = 0 then 2 else if c = 1 then 1 else 0) (fun c => if c = 2 then 0 else 100)
  · intro c hc l hl
    match c, hc with
    | 0, _ => show gT l.length = 0; unfold gT; simp at hl; simp; omega
    | 1, _ => show gR l.length = 0; unfold gR; simp at hl; simp [hl]
    | 2, _ => simp at hl
    | 3, _ => simp at hl
  · intro c hc
    match c, hc with
    | 0, _ => exact lf_locbal 2 4 _ _ 0 3 3 100 gT (by omega) (by omega) cH0 cP0 (by decide)
    | 1, _ => exact lf_locbal 2 4 _ _ 1 2 2 100 gR (by omega) (by omega) cH1 cP1 (by decide)
    | 2, _ => exact lf_locbal 2 4 _ _ 2 9 1 0 g1 (by omega) (by omega) cH2 cP2 (by decide)
    | 3, _ => exact lf_locbal 2 4 _ _ 3 1 1 100 g1 (by omega) (by omega) cH3 cP3 (by decide)
  · have : ∀ e ≤ 3, ∀ b < 4, e ≤ (fun c => if c = 2 then 0 else 100) b +
        natSum 4 (fun c => if c = b then 0 else (fun c => if c = 0 then 2 else if c = 1 then 1 else 0) c) := by
      decide
    exact this e he

/-- Block pattern of the `T ⊗ R` value: two entries in the `T` block, one in the rectangle. -/
def iT (x y z : Nat) : Int :=
  (if x = 0 ∧ y = 0 ∧ z = 1 then 1 else 0) + (if x = 0 ∧ y = 1 ∧ z = 0 then 1 else 0) +
  (if x = 1 ∧ y = 0 ∧ z = 0 then 1 else 0)

theorem F3T : ∀ x ≤ 4, ∀ y ≤ 4, ∀ z ≤ 4, F3 4 gTR x y z = iT x y z := by decide +kernel

theorem tr_point {a b c : Nat} (hab : pc a b = true) (hac : pc a c = true) (hbc : pc b c = true)
    (hba : pc b a = false) (hca : pc c a = false) (hcb : pc c b = false) (x y z : Nat) :
    (if pc x y = true then ind6 a b c x y z else 0) =
      (if x = a ∧ y = b ∧ z = c then 1 else 0) + (if x = a ∧ y = c ∧ z = b then 1 else 0) +
        (if x = b ∧ y = c ∧ z = a then 1 else 0) := by
  by_cases hp : pc x y = true
  · rw [if_pos hp]
    have z3 : (if x = b ∧ y = a ∧ z = c then (1 : Int) else 0) = 0 :=
      if_neg (fun h => by rw [h.1, h.2.1, hba] at hp; exact Bool.false_ne_true hp)
    have z5 : (if x = c ∧ y = a ∧ z = b then (1 : Int) else 0) = 0 :=
      if_neg (fun h => by rw [h.1, h.2.1, hca] at hp; exact Bool.false_ne_true hp)
    have z6 : (if x = c ∧ y = b ∧ z = a then (1 : Int) else 0) = 0 :=
      if_neg (fun h => by rw [h.1, h.2.1, hcb] at hp; exact Bool.false_ne_true hp)
    unfold ind6; rw [z3, z5, z6]; omega
  · rw [if_neg hp]
    have z1 : (if x = a ∧ y = b ∧ z = c then (1 : Int) else 0) = 0 :=
      if_neg (fun h => by rw [h.1, h.2.1] at hp; exact hp hab)
    have z2 : (if x = a ∧ y = c ∧ z = b then (1 : Int) else 0) = 0 :=
      if_neg (fun h => by rw [h.1, h.2.1] at hp; exact hp hac)
    have z4 : (if x = b ∧ y = c ∧ z = a then (1 : Int) else 0) = 0 :=
      if_neg (fun h => by rw [h.1, h.2.1] at hp; exact hp hbc)
    rw [z1, z2, z4]; rfl

theorem match3 {a b c : Nat} (hcb : c < b) (hba : b < a) (hm : isMatch 7 [a, b, c] = true) :
    pc a b = true ∧ pc a c = true ∧ pc b c = true ∧ pc b a = false ∧ pc c a = false ∧ pc c b = false := by
  simp only [isMatch, cfl, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, bne_eq_false_iff_eq, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hm
  simp only [pc, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.and_eq_false_iff,
    decide_eq_false_iff_not, bne_eq_false_iff_eq]
  omega

theorem iT_eq (I0 I1 : Nat → Int) (bk : Nat → Nat) (hI0 : ∀ t, I0 t = if bk t = 0 then 1 else 0)
    (hI1 : ∀ t, I1 t = if bk t = 1 then 1 else 0) (a b c : Nat) :
    I0 a * (I0 b * I1 c) + I0 a * (I0 c * I1 b) + I0 b * (I0 c * I1 a) = iT (bk a) (bk b) (bk c) := by
  simp only [hI0, hI1, iT]
  by_cases ha0 : bk a = 0 <;> by_cases ha1 : bk a = 1 <;>
  by_cases hb0 : bk b = 0 <;> by_cases hb1 : bk b = 1 <;>
  by_cases hc0 : bk c = 0 <;> by_cases hc1 : bk c = 1 <;>
  simp [ha0, ha1, hb0, hb1, hc0, hc1] <;> omega

theorem gtr_count (π : TP) (hv : π.valid = true) {a b c : Nat} (hcb : c < b) (hba : b < a) (ha : a < 105)
    (hm : isMatch 7 [a, b, c] = true) :
    GTR π [a, b, c] = ((π.supp.count (r3 a b c) : Nat) : Int) := by
  simp only [TP.valid, Bool.and_eq_true] at hv
  obtain ⟨hp, hh⟩ := hv
  obtain ⟨n1, n2, n3, n4⟩ := d6_ne3 hp
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := d6_lt hh; obtain ⟨o1, o2, o3, o4⟩ := d6_ne3 hh
  have bp := bt_iff hp; have bh := bt_iff hh
  have cT := count_grid_blk (m := 4) π.bp π.bh (c := 0) (by omega) (nd3 n1 n2 n3) (nd3 o1 o2 o3)
    (by simp; omega) (fun i => (bp i).1) (fun j => (bh j).1)
  have cR := count_grid_blk (m := 4) π.bp π.bh (c := 1) (by omega) (nd2 n4) (nd2 o4)
    (by simp; omega) (fun i => (bp i).2.1) (fun j => (bh j).2.1)
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := match3 hcb hba hm
  have hv : GTR π [a, b, c] = iT (blkM 4 π.bp π.bh 7 a) (blkM 4 π.bp π.bh 7 b) (blkM 4 π.bp π.bh 7 c) := by
    unfold GTR
    rw [prodM3 4 π.bp π.bh φTR gTR φTR_eq]
    exact F3T _ (blkM_le _) _ (blkM_le _) _ (blkM_le _)
  rw [hv, TP.supp, count_flatMap]
  rw [lsum_congr _ _ (fun x => lsum π.ET (fun y => lsum π.ER (fun z =>
      (if x = a ∧ y = b ∧ z = c then 1 else 0) + (if x = a ∧ y = c ∧ z = b then 1 else 0) +
        (if x = b ∧ y = c ∧ z = a then 1 else 0)))) (fun x _ => by
    rw [count_flatMap]
    exact lsum_congr _ _ _ (fun y _ => by
      by_cases hxy : pc x y = true
      · rw [if_pos hxy, count_map]
        exact lsum_congr _ _ _ (fun z _ => by
          rw [cd_ind hcb hba ha x y z, ← tr_point p1 p2 p3 p4 p5 p6 x y z, if_pos hxy])
      · rw [if_neg hxy, lsum_congr π.ER _ (fun _ => 0) (fun z _ => by
          rw [← tr_point p1 p2 p3 p4 p5 p6 x y z, if_neg hxy]), Gen3.lsum_zero]
        simp))]
  simp only [lsum_add, lsum3_ind]
  unfold TP.ET TP.ER
  simp only [cT, cR]
  exact (iT_eq _ _ _ (fun _ => rfl) (fun _ => rfl) a b c).symm

end Programme.«20261027-1434-proof-complexity».Gen3T
