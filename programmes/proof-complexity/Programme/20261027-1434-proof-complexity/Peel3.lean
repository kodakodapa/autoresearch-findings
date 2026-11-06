import Programme.«20261027-1434-proof-complexity».Gen3T

/-!
# A kernel-checked peeling certificate at level 3 (zero link) on `ontoFPHP 7 8`

Points are canonical 3-matchings `[a, b, c]` (`a > b > c`), coded by `r3 a b c < 187460`. A state is
a residual `r` with zero link (`Bal 2 7 8 r 0 2`), `f - r` in the level-3 span of the parametric
generators `G3` (RRR and `T ⊗ R`, `Gen3`, `Gen3T`), and a bitmask `P` of finalised codes at which
`r` is even. Steps:

* `k1 gs a b c`: subtract `r [a,b,c]` times the sum of the generators `gs`; every code in their
  joint support list is the pivot or not finalised, and the pivot occurs an odd number of times;
* `kx gs a b c`: the same with cancellations, through the XOR mask `bv` of the support list;
* `pr u w row idx a b c`: a free line (row `idx` or column `idx`) at the 2-matching `[u, w]` whose
  codes other than the pivot are finalised, the pivot occurring an odd number of times; the line
  sum is even, so `r [a,b,c]` is even.

`run3_sound` carries a state over `P` to a state over the final mask. If the final mask covers every
canonical 3-matching (`covA`), `f` is in the span (`span_of_cov`).
-/

namespace Programme.«20261027-1434-proof-complexity».Peel3

set_option linter.unusedVariables false
set_option linter.deprecated false

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin
open Programme.«20261027-1434-proof-complexity».F2Lin Programme.«20261027-1434-proof-complexity».PeelBase Programme.«20261027-1434-proof-complexity».ProdM Programme.«20261027-1434-proof-complexity».Towers Programme.«20261027-1434-proof-complexity».Code3 Programme.«20261027-1434-proof-complexity».Gen3 Programme.«20261027-1434-proof-complexity».Gen3T

/-! ## Generators -/

inductive GS where
  | r (π : RP)
  | t (π : TP)

def GS.valid : GS → Bool
  | .r π => π.valid
  | .t π => π.valid

def GS.fn : GS → List Nat → Int
  | .r π => GRR π
  | .t π => GTR π

def GS.supp : GS → List Nat
  | .r π => π.suppF
  | .t π => π.supp

theorem GS.count (x : GS) (hv : x.valid = true) {m : List Nat} (hm : CM 7 8 m) (hl : m.length = 3) :
    x.fn m = ((x.supp.count (code3 m) : Nat) : Int) := by
  obtain ⟨a, b, c, rfl, h1, h2, h3, h4⟩ := CM_three hm hl
  cases x with
  | r π => rw [GS.supp, ← RP.supp_eq]; exact grr_count π hv h1 h2 h3
  | t π => exact gtr_count π hv h1 h2 h3 h4

theorem GS.bal (x : GS) (hv : x.valid = true) (e : Nat) (he : e ≤ 3) : Bal 2 7 8 x.fn x.fn e := by
  cases x with
  | r π => exact grr_bal π hv e he
  | t π => exact gtr_bal π hv e he

theorem prodM_short {m : Nat} {bp bh : Nat → Nat} {n : Nat} (φ : Nat → List Nat → Int) (s : Nat → Nat)
    (hs : ∀ c < m, ∀ l : List Nat, l.length < s c → φ c l = 0) (g : List Nat)
    (hg : g.length < natSum m s) : ProdM m bp bh n φ g = 0 := by
  unfold ProdM
  split
  · next hok =>
    have hl := len_sum g hok
    have hex : ∃ c, c < m ∧ (flM m bp bh n c g).length < s c := by
      apply Classical.byContradiction; intro H
      have := natSum_le m s (fun c => (flM m bp bh n c g).length)
        (fun c hc => Nat.not_lt.mp (fun h => H ⟨c, hc, h⟩))
      omega
    obtain ⟨c, hc, hlt⟩ := hex
    exact prodR_zero m _ c hc (hs c hc _ hlt)
  · rfl

theorem GS.zero2 (x : GS) (g : List Nat) (hl : g.length < 3) : x.fn g = 0 := by
  cases x with
  | r π =>
    refine prodM_short (s := fun c => if c = 3 then 0 else 1) φRRRM ?_ g (by simp [natSum]; omega)
    intro c hc l hl'
    match c, hc with
    | 0, _ | 1, _ | 2, _ => show gR l.length = 0; unfold gR; simp at hl'; simp [hl']
    | 3, _ => simp at hl'
  | t π =>
    refine prodM_short (s := fun c => if c = 0 then 2 else if c = 1 then 1 else 0) φTR ?_ g
      (by simp [natSum]; omega)
    intro c hc l hl'
    match c, hc with
    | 0, _ => show gT l.length = 0; unfold gT; simp at hl'; simp; omega
    | 1, _ => show gR l.length = 0; unfold gR; simp at hl'; simp [hl']
    | 2, _ => simp at hl'
    | 3, _ => simp at hl'

/-- Generators have zero link at level 2. -/
theorem GS.zl (x : GS) (hv : x.valid = true) : Bal 2 7 8 x.fn (fun _ => 0) 2 := by
  intro g hg hl
  have h := GS.bal x hv 2 (by omega) g hg hl
  rw [GS.zero2 x g (by omega)] at h
  exact h

def G3 (g : List Nat → Int) : Prop := ∃ x : GS, x.valid = true ∧ g = x.fn

def x0 : GS := .r ⟨0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5⟩

theorem x0_valid : x0.valid = true := by decide

def sumF (gs : List GS) (m : List Nat) : Int := (gs.map (fun x => x.fn m)).sum

def suppL (gs : List GS) : List Nat := gs.flatMap GS.supp

theorem sumF_count : ∀ (gs : List GS), gs.all GS.valid = true → ∀ {m : List Nat}, CM 7 8 m → m.length = 3 →
    sumF gs m = (((suppL gs).count (code3 m) : Nat) : Int)
  | [], _, m, _, _ => by simp [sumF, suppL]
  | x :: gs, h, m, hm, hl => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [sumF, suppL, List.map_cons, List.sum_cons, List.flatMap_cons, List.count_append, Int.natCast_add]
    rw [GS.count x h.1 hm hl]
    have := sumF_count gs h.2 hm hl
    simp only [sumF, suppL] at this
    rw [this]

theorem bal_zero (e : Nat) : Bal 2 7 8 (fun _ => (0 : Int)) (fun _ => (0 : Int)) e := by
  intro g _ _
  refine ⟨fun i _ _ => ?_, fun j _ _ => ?_⟩
  · unfold rowS lineS; rw [rsum_zero _ _ (fun t _ => by split <;> rfl)]; exact ⟨0, rfl⟩
  · unfold colS lineS; rw [rsum_zero _ _ (fun t _ => by split <;> rfl)]; exact ⟨0, rfl⟩

theorem sumF_zl : ∀ (gs : List GS), gs.all GS.valid = true → Bal 2 7 8 (sumF gs) (fun _ => 0) 2
  | [], _ => by
    have : sumF [] = fun _ => 0 := funext (fun m => by simp [sumF])
    rw [this]; exact bal_zero 2
  | x :: gs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have h1 := Bal_add (GS.zl x h.1) (sumF_zl gs h.2)
    have e1 : (fun g => x.fn g + sumF gs g) = sumF (x :: gs) := funext (fun m => by simp [sumF])
    have e2 : (fun g : List Nat => (0 : Int) + 0) = fun _ => 0 := funext (fun _ => rfl)
    rw [e1, e2] at h1; exact h1

theorem span_zero (f : List Nat → Int) (hf : ∀ m, f m = 0) : InSpan 2 7 8 3 G3 f :=
  InSpan.congr (InSpan.smul 0 (InSpan.gen ⟨x0, x0_valid, rfl⟩)) (fun g _ _ => by rw [hf]; simp)

theorem sumF_span : ∀ (gs : List GS), gs.all GS.valid = true → InSpan 2 7 8 3 G3 (sumF gs)
  | [], _ => span_zero _ (fun m => by simp [sumF])
  | x :: gs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact InSpan.congr (InSpan.add (InSpan.gen ⟨x, h.1, rfl⟩) (sumF_span gs h.2))
      (fun m _ _ => by simp [sumF])

/-! ## Steps -/

def okPt (a b c : Nat) : Bool := decide (c < b) && decide (b < a) && decide (a < 105) && isMatch 7 [a, b, c]

def okLine (u w : Nat) (row : Bool) (idx : Nat) : Bool :=
  decide (w < u) && decide (u < 105) && isMatch 7 [u, w] &&
  (if row then decide (idx < 15) && u / 7 != idx && w / 7 != idx
   else decide (idx < 7) && u % 7 != idx && w % 7 != idx)

/-- Codes of the points of a free line at the 2-matching `[u, w]`. -/
def lc3 (u w : Nat) (row : Bool) (idx : Nat) : List Nat :=
  if row then (List.range 7).filterMap (fun t =>
      if isMatch 7 [var 7 idx t, u, w] then some (cd (var 7 idx t) u w) else none)
  else (List.range 15).filterMap (fun t =>
      if isMatch 7 [var 7 t idx, u, w] then some (cd (var 7 t idx) u w) else none)

/-- A cheaper form of `lc3`: by `okLine`, the only conflicts are in the free coordinate. -/
def lcF (u w : Nat) (row : Bool) (idx : Nat) : List Nat :=
  if row then (List.range 7).filterMap (fun t =>
      cond (!(Nat.beq t (u % 7)) && !(Nat.beq t (w % 7))) (some (cdF (Nat.add (Nat.mul idx 7) t) u w)) none)
  else (List.range 15).filterMap (fun t =>
      cond (!(Nat.beq t (u / 7)) && !(Nat.beq t (w / 7))) (some (cdF (Nat.add (Nat.mul t 7) idx) u w)) none)

theorem fm_congr {f g : Nat → Option Nat} : ∀ L : List Nat, (∀ t ∈ L, f t = g t) → L.filterMap f = L.filterMap g
  | [], _ => rfl
  | t :: L, h => by
    simp only [List.filterMap_cons]
    rw [h t (by simp), fm_congr L (fun t' ht' => h t' (by simp [ht']))]

theorem isMatch3 (v u w : Nat) : isMatch 7 [v, u, w] = true ↔
    ((v = u ∨ (v / 7 ≠ u / 7 ∧ v % 7 ≠ u % 7)) ∧ (v = w ∨ (v / 7 ≠ w / 7 ∧ v % 7 ≠ w % 7)) ∧
      (u = w ∨ (u / 7 ≠ w / 7 ∧ u % 7 ≠ w % 7))) := by
  simp only [isMatch, cfl, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, bne_eq_false_iff_eq, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
    bne_self_eq_false, true_or, true_and, and_true, Bool.false_eq_true, beq_self_eq_true, not_true, false_and, or_false]
  constructor
  · intro h; omega
  · intro h; omega

theorem key2 (t X Y : Nat) : (!(Nat.beq t X) && !(Nat.beq t Y)) = true ↔ (t ≠ X ∧ t ≠ Y) := by
  cases h1 : Nat.beq t X <;> cases h2 : Nat.beq t Y
  · simp only [Bool.not_false, Bool.and_self, true_iff]
    exact ⟨Nat.ne_of_beq_eq_false h1, Nat.ne_of_beq_eq_false h2⟩
  · simp only [Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_eq_true, false_iff, not_and, Decidable.not_not]
    intro _; exact Nat.eq_of_beq_eq_true h2
  · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, false_iff, not_and]
    intro h; exact absurd (Nat.eq_of_beq_eq_true h1) h
  · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, false_iff, not_and]
    intro h; exact absurd (Nat.eq_of_beq_eq_true h1) h

theorem lc3_eq {u w : Nat} {row : Bool} {idx : Nat} (h : okLine u w row idx = true) :
    lc3 u w row idx = lcF u w row idx := by
  simp only [okLine, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hwu, hu⟩, hmw⟩, hrc⟩ := h
  have huw : u / 7 ≠ w / 7 ∧ u % 7 ≠ w % 7 := by
    have := (isMatch3 u u w).mp (by rw [isMatch_congr 7 [u, u, w] [u, w] (fun x => by simp)]; exact hmw)
    omega
  have e : cd = cdF := funext fun x => funext fun y => funext fun z => cd_eq_cdF x y z
  cases row
  · simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hrc
    obtain ⟨⟨hj, hu7⟩, hw7⟩ := hrc
    simp only [lc3, lcF, Bool.false_eq_true, if_false, e]
    apply fm_congr
    intro t ht
    rw [List.mem_range] at ht
    have hv : var 7 t idx = Nat.add (Nat.mul t 7) idx := rfl
    have d1 : Nat.add (Nat.mul t 7) idx / 7 = t := by simp only [Nat.add_eq, Nat.mul_eq]; omega
    have d2 : Nat.add (Nat.mul t 7) idx % 7 = idx := by simp only [Nat.add_eq, Nat.mul_eq]; omega
    rw [hv]
    by_cases hc : t ≠ u / 7 ∧ t ≠ w / 7
    · have hm : isMatch 7 [Nat.add (Nat.mul t 7) idx, u, w] = true := by
        rw [isMatch3, d1, d2]; omega
      rw [if_pos hm, (key2 t _ _).mpr hc]; rfl
    · have hm : ¬ isMatch 7 [Nat.add (Nat.mul t 7) idx, u, w] = true := by
        rw [isMatch3, d1, d2]; omega
      have hb : (!(Nat.beq t (u / 7)) && !(Nat.beq t (w / 7))) = false := by
        cases hk : (!(Nat.beq t (u / 7)) && !(Nat.beq t (w / 7)))
        · rfl
        · exact absurd ((key2 t _ _).mp hk) hc
      rw [if_neg hm, hb]; rfl
  · simp only [if_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hrc
    obtain ⟨⟨hi, hu7⟩, hw7⟩ := hrc
    simp only [lc3, lcF, if_true, e]
    apply fm_congr
    intro t ht
    rw [List.mem_range] at ht
    have hv : var 7 idx t = Nat.add (Nat.mul idx 7) t := rfl
    have d1 : Nat.add (Nat.mul idx 7) t / 7 = idx := by simp only [Nat.add_eq, Nat.mul_eq]; omega
    have d2 : Nat.add (Nat.mul idx 7) t % 7 = t := by simp only [Nat.add_eq, Nat.mul_eq]; omega
    rw [hv]
    by_cases hc : t ≠ u % 7 ∧ t ≠ w % 7
    · have hm : isMatch 7 [Nat.add (Nat.mul idx 7) t, u, w] = true := by
        rw [isMatch3, d1, d2]; omega
      rw [if_pos hm, (key2 t _ _).mpr hc]; rfl
    · have hm : ¬ isMatch 7 [Nat.add (Nat.mul idx 7) t, u, w] = true := by
        rw [isMatch3, d1, d2]; omega
      have hb : (!(Nat.beq t (u % 7)) && !(Nat.beq t (w % 7))) = false := by
        cases hk : (!(Nat.beq t (u % 7)) && !(Nat.beq t (w % 7)))
        · rfl
        · exact absurd ((key2 t _ _).mp hk) hc
      rw [if_neg hm, hb]; rfl

inductive Step3 where
  | k1 (gs : List GS) (a b c : Nat)
  | kx (gs : List GS) (a b c : Nat)
  | pr (u w : Nat) (row : Bool) (idx a b c : Nat)

def chk1 (P piv : Nat) (L : List Nat) : Bool :=
  L.all (fun x => x == piv || !P.testBit x) && L.count piv % 2 == 1

def chkX (P piv : Nat) (L : List Nat) : Bool :=
  ((bv L ^^^ 2 ^ piv) &&& P) == 0 && (bv L).testBit piv

def chkP (P piv : Nat) (L : List Nat) : Bool :=
  L.all (fun x => x == piv || P.testBit x) && L.count piv % 2 == 1

def step3 (P : Nat) : Step3 → Option Nat
  | .k1 gs a b c =>
    if okPt a b c && gs.all GS.valid && chk1 P (r3 a b c) (suppL gs) then some (P ||| 2 ^ r3 a b c) else none
  | .kx gs a b c =>
    if okPt a b c && gs.all GS.valid && chkX P (r3 a b c) (suppL gs) then some (P ||| 2 ^ r3 a b c) else none
  | .pr u w row idx a b c =>
    if okPt a b c && okLine u w row idx && chkP P (r3 a b c) (lcF u w row idx) then some (P ||| 2 ^ r3 a b c)
    else none

def run3 : Nat → List Step3 → Option Nat
  | P, [] => some P
  | P, s :: ss => match step3 P s with
    | some P' => run3 P' ss
    | none => none

/-! ## Invariant -/

def Inv3 (P : Nat) (r : List Nat → Int) : Prop :=
  ∀ m, CM 7 8 m → m.length = 3 → P.testBit (code3 m) = true → (2 : Int) ∣ r m

def State3 (f : List Nat → Int) (P : Nat) : Prop :=
  ∃ r, Inv3 P r ∧ Bal 2 7 8 r (fun _ => 0) 2 ∧ InSpan 2 7 8 3 G3 (fun m => f m - r m)

theorem okPt_CM {a b c : Nat} (h : okPt a b c = true) :
    CM 7 8 [a, b, c] ∧ c < b ∧ b < a ∧ a < 105 ∧ isMatch 7 [a, b, c] = true := by
  simp only [okPt, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨⟨?_, h4⟩, h1, h2, h3, h4⟩
  rw [canon_three _ _ _ _ h1 h2]
  simp [show a < (7 + 8) * 7 by omega, show b < (7 + 8) * 7 by omega, show c < (7 + 8) * 7 by omega]

theorem testBit_or_pow {P c piv : Nat} (h : (P ||| 2 ^ piv).testBit c = true) :
    P.testBit c = true ∨ c = piv := by
  rw [Nat.testBit_or, Nat.testBit_two_pow] at h
  cases hP : P.testBit c
  · simp [hP] at h; exact Or.inr h.symm
  · exact Or.inl rfl

/-- Soundness of a kill, from the parity of the generator sum. -/
theorem kill_sound {f : List Nat → Int} {P : Nat} {gs : List GS} {a b c : Nat} (hpt : okPt a b c = true)
    (hv : gs.all GS.valid = true)
    (hpar : ∀ m, CM 7 8 m → m.length = 3 → P.testBit (code3 m) = true → code3 m ≠ r3 a b c →
      (2 : Int) ∣ sumF gs m)
    (hodd : (2 : Int) ∣ sumF gs [a, b, c] - 1)
    (hst : State3 f P) : State3 f (P ||| 2 ^ r3 a b c) := by
  obtain ⟨r, hI, hb, hsp⟩ := hst
  obtain ⟨hcm, h1, h2, h3, -⟩ := okPt_CM hpt
  obtain ⟨A, hA⟩ : ∃ A, A = r [a, b, c] := ⟨_, rfl⟩
  refine ⟨fun m => r m + (-A) * sumF gs m, ?_, ?_, ?_⟩
  · intro m hm hl hbit
    have hpiv : code3 m = r3 a b c → m = [a, b, c] := fun h => code3_inj hm hl hcm rfl h
    by_cases he : code3 m = r3 a b c
    · have hm' := hpiv he; subst hm'
      show (2 : Int) ∣ r [a, b, c] + -A * sumF gs [a, b, c]
      rw [← hA]
      obtain ⟨t, ht⟩ := hodd
      exact ⟨-A * t, by rw [show sumF gs [a, b, c] = 2 * t + 1 by omega]; rw [Int.mul_add, Int.mul_one,
        Int.mul_left_comm]; omega⟩
    · rcases testBit_or_pow hbit with hP | hc
      · exact Int.dvd_add (hI m hm hl hP) (Int.dvd_trans (hpar m hm hl hP he) (Int.dvd_mul_left _ _))
      · exact absurd hc he
  · have := Bal_add hb (Bal_smul (-A) (sumF_zl gs hv))
    have e : (fun g : List Nat => (0 : Int) + -A * 0) = fun _ => 0 := funext (fun _ => by simp)
    rw [e] at this; exact this
  · exact InSpan.congr (InSpan.add hsp (InSpan.smul A (sumF_span gs hv)))
      (fun m _ _ => ⟨0, by simp only [Int.neg_mul]; omega⟩)

theorem count_par_of_bit {L : List Nat} {c : Nat} (h : (bv L).testBit c = false) :
    (2 : Int) ∣ ((L.count c : Nat) : Int) := by
  have := bitI_bv L c
  unfold bitI at this; rw [h] at this; simp at this
  exact (Int.dvd_neg).mp (by simpa using this)

theorem count_odd_of_bit {L : List Nat} {c : Nat} (h : (bv L).testBit c = true) :
    (2 : Int) ∣ ((L.count c : Nat) : Int) - 1 := by
  have := bitI_bv L c
  unfold bitI at this; rw [h] at this; simp at this
  obtain ⟨t, ht⟩ := this
  exact ⟨-t, by omega⟩

/-! ## Lines -/

theorem rsum_fmc (M : Nat) (Pm : Nat → Bool) (h : Nat → Nat) (F : Nat → Int) (piv : Nat) (X : Int)
    (hF : ∀ t < M, Pm t = true → (h t = piv → F t = X) ∧ (h t ≠ piv → (2 : Int) ∣ F t)) :
    (2 : Int) ∣ rsum M (fun t => if Pm t = true then F t else 0) -
      ((((List.range M).filterMap (fun t => if Pm t = true then some (h t) else none)).count piv : Nat) : Int) * X := by
  induction M with
  | zero => simp [rsum]
  | succ M ih =>
    have ih' := ih (fun t ht hp => hF t (by omega) hp)
    rw [List.range_succ, List.filterMap_append, List.count_append, Int.natCast_add]
    show (2 : Int) ∣ rsum M _ + _ - _
    generalize ((((List.range M).filterMap (fun t => if Pm t = true then some (h t) else none)).count piv : Nat) : Int) = C at ih' ⊢
    obtain ⟨t, ht⟩ := ih'
    by_cases hp : Pm M = true
    · have hFM := hF M (by omega) hp
      simp only [hp, if_true, List.filterMap_cons, List.filterMap_nil, List.count_singleton]
      by_cases he : h M = piv
      · rw [hFM.1 he]; simp only [he, beq_self_eq_true, if_true]
        exact ⟨t, by push_cast; rw [Int.add_mul]; omega⟩
      · have hne : (h M == piv) = false := by simp [he]
        simp only [hne, Bool.false_eq_true, if_false]
        obtain ⟨t2, ht2⟩ := hFM.2 he
        exact ⟨t + t2, by push_cast; simp only [Int.add_mul, Int.zero_mul, Int.add_zero]; omega⟩
    · have hpf : Pm M = false := by simpa using hp
      simp only [hpf, Bool.false_eq_true, if_false, List.filterMap_cons, List.filterMap_nil, List.count_nil]
      exact ⟨t, by push_cast; simp only [Int.add_mul, Int.zero_mul, Int.add_zero]; omega⟩

theorem cm_fc3 {v u w : Nat} (hv : v < 105) (hu : u < 105) (hw : w < 105) (h1 : v ≠ u) (h2 : u ≠ w) (h3 : v ≠ w)
    (hm : isMatch 7 [v, u, w] = true) :
    CM 7 8 (canon ((7 + 8) * 7) [v, u, w]) ∧ (canon ((7 + 8) * 7) [v, u, w]).length = 3 ∧
      code3 (canon ((7 + 8) * 7) [v, u, w]) = cd v u w := by
  have hl : ∀ x ∈ [v, u, w], x < (7 + 8) * 7 := by intro x hx; simp at hx; omega
  refine ⟨⟨canon_idem _, ?_⟩, ?_, code3_canon hv hu hw h1 h2 h3⟩
  · rw [isMatch_congr 7 _ [v, u, w] (mem_canon' hl)]; exact hm
  · rw [canon_fc3 hv hu hw h1 h2 h3]; rfl

theorem line_par {P : Nat} {r : List Nat → Int} {u w : Nat} {row : Bool} {idx a b c : Nat}
    (hI : Inv3 P r) (hb : Bal 2 7 8 r (fun _ => 0) 2) (hln : okLine u w row idx = true)
    (hcm : CM 7 8 [a, b, c]) (h1 : c < b) (h2 : b < a) (h3 : a < 105)
    (hk : chkP P (r3 a b c) (lc3 u w row idx) = true) : (2 : Int) ∣ r [a, b, c] := by
  simp only [chkP, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hk
  obtain ⟨hall, hodd⟩ := hk
  replace hodd : ∃ t, (lc3 u w row idx).count (r3 a b c) = 2 * t + 1 := ⟨(lc3 u w row idx).count (r3 a b c) / 2, by omega⟩
  simp only [okLine, Bool.and_eq_true, decide_eq_true_eq] at hln
  obtain ⟨⟨⟨hwu, hu⟩, hmw⟩, hrc⟩ := hln
  have hcg : CM 7 8 [u, w] := by
    refine ⟨?_, hmw⟩
    rw [canon_two _ _ _ hwu]
    simp [show u < (7 + 8) * 7 by omega, show w < (7 + 8) * 7 by omega]
  -- the point condition for a line term
  have term : ∀ v, v < 105 → v ≠ u → v ≠ w → isMatch 7 [v, u, w] = true → cd v u w ∈ lc3 u w row idx →
      (cd v u w = r3 a b c → r (canon ((7 + 8) * 7) [v, u, w]) = r [a, b, c]) ∧
      (cd v u w ≠ r3 a b c → (2 : Int) ∣ r (canon ((7 + 8) * 7) [v, u, w])) := by
    intro v hv hvu hvw hm hmem
    obtain ⟨hc, hl, hcode⟩ := cm_fc3 hv hu (by omega) hvu (by omega) hvw hm
    refine ⟨fun he => ?_, fun he => ?_⟩
    · rw [code3_inj hc hl hcm rfl (by rw [hcode, he]; rfl)]
    · rcases hall _ hmem with h | h
      · exact absurd h he
      · exact hI _ hc hl (by rw [hcode]; exact h)
  obtain ⟨t0, ht0⟩ := hodd
  cases row
  · simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hrc
    obtain ⟨⟨hj, hu7⟩, hw7⟩ := hrc
    have hbal := (hb [u, w] hcg rfl).2 idx hj (fun v hv => by simp at hv; omega)
    have hpar := rsum_fmc 15 (fun t => isMatch 7 [var 7 t idx, u, w]) (fun t => cd (var 7 t idx) u w)
      (fun t => r (canon ((7 + 8) * 7) [var 7 t idx, u, w])) (r3 a b c) (r [a, b, c]) (fun t ht hp => by
        have hv := var_lt 7 8 t idx ht hj
        have hvm : var 7 t idx % 7 = idx := var_mod _ _ _ hj
        exact term _ hv (fun e => by rw [← e] at hu7; omega) (fun e => by rw [← e] at hw7; omega) hp
          (by simp only [lc3, Bool.false_eq_true, if_false]; exact List.mem_filterMap.mpr ⟨t, List.mem_range.mpr ht, by simp [hp]⟩))
    unfold colS lineS at hbal
    simp only [lc3, Bool.false_eq_true, if_false] at ht0
    rw [ht0] at hpar
    (try simp only at hpar); (try simp only at hbal)
    obtain ⟨s1, hs1⟩ := hbal; obtain ⟨s2, hs2⟩ := hpar
    try rw [show rsum (7 + 8) = rsum 15 from rfl] at hs1
    rw [show ((2 * t0 + 1 : Nat) : Int) * r [a, b, c] = 2 * ((t0 : Int) * r [a, b, c]) + r [a, b, c] by
      push_cast; rw [Int.add_mul, Int.mul_assoc, Int.one_mul]] at hs2
    generalize (t0 : Int) * r [a, b, c] = Y at hs2
    exact ⟨s1 - s2 - Y, by omega⟩
  · simp only [if_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hrc
    obtain ⟨⟨hi, hu7⟩, hw7⟩ := hrc
    have hbal := (hb [u, w] hcg rfl).1 idx hi (fun v hv => by simp at hv; omega)
    have hpar := rsum_fmc 7 (fun t => isMatch 7 [var 7 idx t, u, w]) (fun t => cd (var 7 idx t) u w)
      (fun t => r (canon ((7 + 8) * 7) [var 7 idx t, u, w])) (r3 a b c) (r [a, b, c]) (fun t ht hp => by
        have hv := var_lt 7 8 idx t hi ht
        have hvm : var 7 idx t / 7 = idx := var_div _ _ _ ht
        exact term _ hv (fun e => by rw [← e] at hu7; omega) (fun e => by rw [← e] at hw7; omega) hp
          (by simp only [lc3, if_true]; exact List.mem_filterMap.mpr ⟨t, List.mem_range.mpr ht, by simp [hp]⟩))
    unfold rowS lineS at hbal
    simp only [lc3, if_true] at ht0
    rw [ht0] at hpar
    (try simp only at hpar); (try simp only at hbal)
    obtain ⟨s1, hs1⟩ := hbal; obtain ⟨s2, hs2⟩ := hpar
    try rw [show rsum (7 + 8) = rsum 15 from rfl] at hs1
    rw [show ((2 * t0 + 1 : Nat) : Int) * r [a, b, c] = 2 * ((t0 : Int) * r [a, b, c]) + r [a, b, c] by
      push_cast; rw [Int.add_mul, Int.mul_assoc, Int.one_mul]] at hs2
    generalize (t0 : Int) * r [a, b, c] = Y at hs2
    exact ⟨s1 - s2 - Y, by omega⟩

theorem step_sound {f : List Nat → Int} {P P' : Nat} {s : Step3} (hs : step3 P s = some P')
    (hst : State3 f P) : State3 f P' := by
  cases s with
  | k1 gs a b c =>
    simp only [step3] at hs
    split at hs
    · next hc =>
      simp only [Option.some.injEq] at hs; subst hs
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hpt, hv⟩, hk⟩ := hc
      simp only [chk1, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hk
      obtain ⟨hall, hodd⟩ := hk
      replace hodd : ∃ t, (suppL gs).count (r3 a b c) = 2 * t + 1 := ⟨(suppL gs).count (r3 a b c) / 2, by omega⟩
      obtain ⟨hcm, h1, h2, h3, -⟩ := okPt_CM hpt
      refine kill_sound hpt hv (fun m hm hl hP he => ?_) ?_ hst
      · rw [sumF_count gs hv hm hl]
        have : (suppL gs).count (code3 m) = 0 := by
          apply List.count_eq_zero_of_not_mem
          intro hmem
          rcases hall _ hmem with h | h
          · exact he h
          · rw [hP] at h; exact Bool.false_ne_true h.symm
        rw [this]; exact ⟨0, rfl⟩
      · rw [sumF_count gs hv hcm rfl]
        obtain ⟨t, ht⟩ := hodd
        exact ⟨t, by simp only [code3]; omega⟩
    · simp at hs
  | kx gs a b c =>
    simp only [step3] at hs
    split at hs
    · next hc =>
      simp only [Option.some.injEq] at hs; subst hs
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hpt, hv⟩, hk⟩ := hc
      simp only [chkX, Bool.and_eq_true, beq_iff_eq] at hk
      obtain ⟨hdisj, hpiv⟩ := hk
      obtain ⟨hcm, h1, h2, h3, -⟩ := okPt_CM hpt
      refine kill_sound hpt hv (fun m hm hl hP he => ?_) ?_ hst
      · rw [sumF_count gs hv hm hl]
        apply count_par_of_bit
        have := congrArg (fun z => z.testBit (code3 m)) hdisj
        simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow, hP, Bool.and_true,
          Nat.zero_testBit] at this
        have hne : ¬ (r3 a b c = code3 m) := fun h => he h.symm
        simp only [hne, decide_false, Bool.xor_false] at this
        exact this
      · rw [sumF_count gs hv hcm rfl]
        exact count_odd_of_bit hpiv
    · simp at hs
  | pr u w row idx a b c =>
    simp only [step3] at hs
    split at hs
    · next hc =>
      simp only [Option.some.injEq] at hs; subst hs
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hpt, hln⟩, hk⟩ := hc
      obtain ⟨r, hI, hb, hsp⟩ := hst
      refine ⟨r, ?_, hb, hsp⟩
      obtain ⟨hcm, h1, h2, h3, -⟩ := okPt_CM hpt
      have hX : (2 : Int) ∣ r [a, b, c] := line_par hI hb hln hcm h1 h2 h3 (by rw [lc3_eq hln]; exact hk)
      intro m hm hl hbit
      rcases testBit_or_pow hbit with hP | he
      · exact hI m hm hl hP
      · rw [code3_inj hm hl hcm rfl he]; exact hX
    · simp at hs

theorem run3_sound {f : List Nat → Int} :
    ∀ (ss : List Step3) {P P' : Nat}, run3 P ss = some P' → State3 f P → State3 f P'
  | [], P, P', h, hst => by simp [run3] at h; subst h; exact hst
  | s :: ss, P, P', h, hst => by
    simp only [run3] at h
    split at h
    · next P'' hP => exact run3_sound ss h (step_sound hP hst)
    · simp at h

theorem run3_append : ∀ (s1 : List Step3) {s2 : List Step3} {P P' P'' : Nat}, run3 P s1 = some P' →
    run3 P' s2 = some P'' → run3 P (s1 ++ s2) = some P''
  | [], s2, P, P', P'', h1, h2 => by simp [run3] at h1; subst h1; exact h2
  | s :: s1, s2, P, P', P'', h1, h2 => by
    show run3 P (s :: (s1 ++ s2)) = some P''
    cases hs : step3 P s with
    | none => simp [run3, hs] at h1
    | some Q => simp only [run3, hs] at h1 ⊢; exact run3_append s1 h1 h2

/-! ## Start and coverage -/

theorem state_init (z : List Nat → Int) (hz : Bal 2 7 8 z (fun _ => 0) 2) : State3 z 0 :=
  ⟨z, fun m _ _ h => by simp at h, hz, span_zero _ (fun m => by omega)⟩

/-- All canonical 3-matchings with largest entry `a` are finalised. -/
def covA (P a : Nat) : Bool :=
  (List.range a).all (fun b => (List.range b).all (fun c => !isMatch 7 [a, b, c] || P.testBit (r3 a b c)))

theorem span_of_cov {z : List Nat → Int} {P : Nat} (hst : State3 z P) (hc : ∀ a < 105, covA P a = true) :
    InSpan 2 7 8 3 G3 z := by
  obtain ⟨r, hI, -, hsp⟩ := hst
  refine InSpan.congr hsp (fun m hm hl => ?_)
  obtain ⟨a, b, c, rfl, h1, h2, h3, h4⟩ := CM_three hm hl
  have hcv := hc a h3
  simp only [covA, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at hcv
  have hbit : P.testBit (r3 a b c) = true := by
    rcases hcv b h2 c h1 with h | h
    · rw [h4] at h; exact absurd h (by simp)
    · exact h
  have := hI _ hm hl hbit
  rw [show z [a, b, c] - (z [a, b, c] - r [a, b, c]) = r [a, b, c] by omega]
  exact this

end Programme.«20261027-1434-proof-complexity».Peel3
