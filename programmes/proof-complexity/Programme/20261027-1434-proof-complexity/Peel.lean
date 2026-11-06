import Programme.«20261027-1434-proof-complexity».PeelBase

/-!
# A kernel-checked peeling certificate for the span condition of `EXT_of_span`

Points are canonical `e`-matchings of `ontoFPHP 7 8` (`e = 1, 2`), coded by `code`, plus the
reserved code `K` standing for the link constant `κ`. A *state* is a residual `r` with
`Bal 2 7 8 r (const κ) (e-1)`, `f - r` in the span of `G`, and a bitmask `P` of finalised codes at
which `r` (or `κ`) is even. Two kinds of steps:

* `kill gs piv`: subtract `R(piv)` times the sum of relabelled base functions listed in `gs`; its
  parity mask (computed from the support lists, `gmask`) must vanish on `P` and be odd at `piv`;
* `prop ls piv`: a list of free line sums (each `≡ κ`, so line + `κ` is even) whose total parity
  mask is `piv` plus finalised codes, so `R(piv)` is even.

`run_sound`: a successful run carries a state over `P` to a state over the final mask. If the
final mask covers every point, `f` is in the span (`span_of_run`).
-/

namespace Programme.«20261027-1434-proof-complexity».Peel

set_option linter.deprecated false
set_option linter.unusedVariables false

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (rsum_dvd)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin
open Programme.«20261026-1402-proof-complexity».Relabel
open Programme.«20261027-1434-proof-complexity».F2Lin Programme.«20261027-1434-proof-complexity».PeelBase

/-- A relabelled base function: base index, pigeon and hole permutations as transposition lists. -/
structure Gen where
  b : Nat
  sp : List (Nat × Nat)
  tp : List (Nat × Nat)

def gσ (x : Gen) : Perm (7 + 8) := mkP 15 x.sp
def gτ (x : Gen) : Perm 7 := mkP 7 x.tp

def gfun (Fb : Nat → List Nat → Int) (x : Gen) : List Nat → Int := relab (gσ x) (gτ x) (Fb x.b)

def gmask (Sb : Nat → List (List Nat)) (κb : Nat → Nat) (x : Gen) : Nat :=
  bv ((Sb x.b).map (icode (gσ x) (gτ x))) ^^^ (if κb x.b % 2 = 1 then 2 ^ K else 0)

def sumF (Fb : Nat → List Nat → Int) (gs : List Gen) (m : List Nat) : Int := (gs.map (fun x => gfun Fb x m)).sum
def sumK (κb : Nat → Nat) (gs : List Gen) : Int := (gs.map (fun x => (κb x.b : Int))).sum
def sumM (Sb : Nat → List (List Nat)) (κb : Nat → Nat) : List Gen → Nat
  | [] => 0
  | x :: gs => gmask Sb κb x ^^^ sumM Sb κb gs

def lineL (l : List Nat × Bool × Nat) : List Nat := lcodes l.1 l.2.1 l.2.2 ++ [K]

inductive Step where
  | kill (gs : List Gen) (piv : Nat)
  | prop (ls : List (List Nat × Bool × Nat)) (piv : Nat)

def stepB (e nb : Nat) (Sb : Nat → List (List Nat)) (κb : Nat → Nat) (P : Nat) : Step → Option Nat
  | .kill gs piv =>
    if gs.all (fun x => decide (x.b < nb)) && valid e piv && (sumM Sb κb gs &&& P == 0) &&
        (sumM Sb κb gs).testBit piv then some (P ||| 2 ^ piv) else none
  | .prop ls piv =>
    if valid e piv && ls.all (lineOK e) && (bv (ls.flatMap lineL)).testBit piv &&
        ((bv (ls.flatMap lineL) ^^^ 2 ^ piv) &&& P == bv (ls.flatMap lineL) ^^^ 2 ^ piv)
    then some (P ||| 2 ^ piv) else none

def runB (e nb : Nat) (Sb : Nat → List (List Nat)) (κb : Nat → Nat) : Nat → List Step → Option Nat
  | P, [] => some P
  | P, s :: ss => match stepB e nb Sb κb P s with
    | some P' => runB e nb Sb κb P' ss
    | none => none

/-! ## Invariant -/

def Inv (e P : Nat) (r : List Nat → Int) (κ : Int) : Prop :=
  ∀ c, P.testBit c = true → valid e c = true ∧ (2 : Int) ∣ R e r κ c

/-- Hypotheses on the base functions. -/
structure Bases (e nb : Nat) (Fb : Nat → List Nat → Int) (Sb : Nat → List (List Nat)) (κb : Nat → Nat)
    (G : (List Nat → Int) → Prop) : Prop where
  he : e = 1 ∨ e = 2
  nb0 : 0 < nb
  hS : ∀ b < nb, ∀ s ∈ Sb b, CM 7 8 s ∧ s.length = e
  hF : ∀ b < nb, ∀ x, CM 7 8 x → x.length = e → (2 : Int) ∣ Fb b x - (((Sb b).map code).count (code x) : Int)
  hB : ∀ b < nb, Bal 2 7 8 (Fb b) (fun _ => (κb b : Int)) (e - 1)
  hG : ∀ b < nb, ∀ (σ : Perm (7 + 8)) (τ : Perm 7), G (relab σ τ (Fb b))

def State (e : Nat) (G : (List Nat → Int) → Prop) (f : List Nat → Int) (P : Nat) : Prop :=
  ∃ r κ, Inv e P r κ ∧ Bal 2 7 8 r (fun _ => κ) (e - 1) ∧ InSpan 2 7 8 e G (fun m => f m - r m)

variable {e nb : Nat} {Fb : Nat → List Nat → Int} {Sb : Nat → List (List Nat)} {κb : Nat → Nat}
  {G : (List Nat → Int) → Prop}

theorem R_lin (r g : List Nat → Int) (κ κg a : Int) (c : Nat) :
    R e (fun m => r m + a * g m) (κ + a * κg) c = R e r κ c + a * R e g κg c := by
  unfold R; split <;> rfl

theorem bit_K_bv (L : List Nat) (hL : ∀ c ∈ L, c < K) : (bv L).testBit K = false := by
  rw [testBit_bv]; simp only [decide_eq_false_iff_not]
  rw [List.count_eq_zero_of_not_mem (fun h => by have := hL _ h; omega)]; omega

theorem gen_par (hB : Bases e nb Fb Sb κb G) (x : Gen) (hx : x.b < nb) (c : Nat) (hc : valid e c = true) :
    (2 : Int) ∣ R e (gfun Fb x) (κb x.b) c - bitI (gmask Sb κb x) c := by
  have hxor := bitI_xor (bv ((Sb x.b).map (icode (gσ x) (gτ x)))) (if κb x.b % 2 = 1 then 2 ^ K else 0) c
  unfold gmask
  have hcodes : ∀ c' ∈ (Sb x.b).map (icode (gσ x) (gτ x)), c' < K := by
    intro c' hc'
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc'
    obtain ⟨hsc, hsl⟩ := hB.hS _ hx s hs
    have := CM_image (Perm.inv (gσ x)) (Perm.inv (gτ x)) hsc
    rw [icode_eq _ _ hsc (by rcases hB.he with h | h <;> omega)]
    exact (code_pt hB.he this.1 (this.2.trans hsl)).2.2.1
  by_cases hK : c = K
  · subst hK
    have h0 : bitI (bv ((Sb x.b).map (icode (gσ x) (gτ x)))) K = 0 := by
      unfold bitI; rw [bit_K_bv _ hcodes]; rfl
    have h1 : (2 : Int) ∣ (κb x.b : Int) - bitI (if κb x.b % 2 = 1 then 2 ^ K else 0) K := by
      unfold bitI
      by_cases hk : κb x.b % 2 = 1
      · simp [hk]; omega
      · simp [hk]; omega
    simp only [R, if_true]
    have := Int.dvd_sub h1 hxor
    rw [h0] at this
    rw [show ∀ a b c : Int, a - b - (c - 0 - b) = a - c by intros; omega] at this
    exact this
  · obtain ⟨hcm, hcl, hcode, hcK⟩ := valid_pt hB.he hc hK
    have hp := relab_par hB.he (gσ x) (gτ x) (Fb x.b) (Sb x.b) (hB.hS _ hx) (hB.hF _ hx) hcm hcl
    rw [hcode] at hp
    have hb := bitI_bv ((Sb x.b).map (icode (gσ x) (gτ x))) c
    have h0 : bitI (if κb x.b % 2 = 1 then 2 ^ K else 0) c = 0 := by
      unfold bitI; split
      · rw [Nat.testBit_two_pow]; simp; omega
      · simp
    simp only [R, hK, if_false]
    rw [h0] at hxor
    have := Int.dvd_sub hp (Int.dvd_add hb hxor)
    rw [show ∀ a b c d : Int, a - b - (c - b + (d - c - 0)) = a - d by intros; omega] at this
    exact this

theorem sum_par (hB : Bases e nb Fb Sb κb G) : ∀ gs : List Gen, (∀ x ∈ gs, x.b < nb) →
    ∀ c, valid e c = true → (2 : Int) ∣ R e (sumF Fb gs) (sumK κb gs) c - bitI (sumM Sb κb gs) c
  | [], _, c, _ => by unfold R; split <;> simp [sumF, sumK, sumM, bitI]
  | x :: gs, h, c, hc => by
    have h1 := gen_par hB x (h x (by simp)) c hc
    have h2 := sum_par hB gs (fun y hy => h y (by simp [hy])) c hc
    have h3 := bitI_xor (gmask Sb κb x) (sumM Sb κb gs) c
    have e1 : R e (sumF Fb (x :: gs)) (sumK κb (x :: gs)) c =
        R e (gfun Fb x) (κb x.b) c + R e (sumF Fb gs) (sumK κb gs) c := by
      unfold R; split <;> simp [sumF, sumK]
    rw [e1, show sumM Sb κb (x :: gs) = gmask Sb κb x ^^^ sumM Sb κb gs from rfl]
    have := Int.dvd_sub (Int.dvd_add h1 h2) h3
    rw [show ∀ A a B b c : Int, A - a + (B - b) - (c - a - b) = A + B - c by intros; omega] at this
    exact this

theorem Bal_ext {f f' c : List Nat → Int} {d : Nat} (h : Bal 2 7 8 f c d) (hf : ∀ m, f m = f' m) :
    Bal 2 7 8 f' c d := by
  have : f = f' := funext hf
  subst this; exact h

theorem Bal_cext {f c c' : List Nat → Int} {d : Nat} (h : Bal 2 7 8 f c d) (hc : ∀ m, c m = c' m) :
    Bal 2 7 8 f c' d := by
  have : c = c' := funext hc
  subst this; exact h

theorem sum_bal (hB : Bases e nb Fb Sb κb G) : ∀ gs : List Gen, (∀ x ∈ gs, x.b < nb) →
    Bal 2 7 8 (sumF Fb gs) (fun _ => sumK κb gs) (e - 1)
  | [], _ => by
    intro g _ _
    refine ⟨fun i _ _ => ?_, fun j _ _ => ?_⟩
    · unfold rowS lineS; rw [rsum_zero _ _ (fun t _ => by split <;> simp [sumF])]; simp [sumK]
    · unfold colS lineS; rw [rsum_zero _ _ (fun t _ => by split <;> simp [sumF])]; simp [sumK]
  | x :: gs, h => by
    have h1 : Bal 2 7 8 (gfun Fb x) (fun _ => (κb x.b : Int)) (e - 1) :=
      bal_relab (gσ x) (gτ x) (hB.hB _ (h x (by simp)))
    have h2 := sum_bal hB gs (fun y hy => h y (by simp [hy]))
    exact Bal_cext (Bal_ext (Bal_add h1 h2) (fun m => by simp [sumF])) (fun m => by simp [sumK])

theorem span_zero (hB : Bases e nb Fb Sb κb G) (f' : List Nat → Int) (hf : ∀ m, f' m = 0) :
    InSpan 2 7 8 e G f' :=
  InSpan.congr (InSpan.smul 0 (InSpan.gen (hB.hG 0 hB.nb0 (gσ ⟨0, [], []⟩) (gτ ⟨0, [], []⟩))))
    (fun g _ _ => by rw [hf]; simp)

theorem sum_span (hB : Bases e nb Fb Sb κb G) : ∀ gs : List Gen, (∀ x ∈ gs, x.b < nb) →
    InSpan 2 7 8 e G (sumF Fb gs)
  | [], _ => span_zero hB _ (fun m => by simp [sumF])
  | x :: gs, h => InSpan.congr (InSpan.add (InSpan.gen (hB.hG x.b (h x (by simp)) (gσ x) (gτ x)))
      (sum_span hB gs (fun y hy => h y (by simp [hy])))) (fun m _ _ => by simp [sumF, gfun])

/-! ## Step soundness -/

theorem lines_even (he : e = 1 ∨ e = 2) {r : List Nat → Int} {κ : Int}
    (hb : Bal 2 7 8 r (fun _ => κ) (e - 1)) :
    ∀ ls : List (List Nat × Bool × Nat), ls.all (lineOK e) = true →
      (2 : Int) ∣ ev (R e r κ) (ls.flatMap lineL)
  | [], _ => ⟨0, by simp [ev]⟩
  | l :: ls, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := lines_even he hb ls h.2
    obtain ⟨hcm, hlen, hrow, hcol⟩ := line_ev he r κ h.1
    have hl : (2 : Int) ∣ ev (R e r κ) (lineL l) := by
      have hlk : R e r κ K = κ := by simp [R]
      unfold lineL; unfold ev; rw [List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hlk]
      obtain ⟨hr, hc⟩ := hb l.1 hcm (by omega)
      cases hrl : l.2.1
      · obtain ⟨hj, hfr, hs⟩ := hcol hrl
        have := hc _ hj hfr; rw [hs] at this; unfold ev at this
        have h2 : (2 : Int) ∣ 2 * κ := ⟨κ, rfl⟩
        have := Int.dvd_add this h2
        rw [show ∀ a : Int, a - κ + 2 * κ = a + (κ + 0) by intros; omega] at this; exact this
      · obtain ⟨hi, hfr, hs⟩ := hrow hrl
        have := hr _ hi hfr; rw [hs] at this; unfold ev at this
        have h2 : (2 : Int) ∣ 2 * κ := ⟨κ, rfl⟩
        have := Int.dvd_add this h2
        rw [show ∀ a : Int, a - κ + 2 * κ = a + (κ + 0) by intros; omega] at this; exact this
    rw [List.flatMap_cons]; unfold ev at *; rw [List.map_append, List.sum_append]
    exact Int.dvd_add hl ih

theorem lineL_lt (he : e = 1 ∨ e = 2) : ∀ ls : List (List Nat × Bool × Nat), ls.all (lineOK e) = true →
    ∀ c ∈ ls.flatMap lineL, c < K + 1
  | [], _ => by simp
  | l :: ls, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    intro c hc
    rw [List.flatMap_cons, List.mem_append] at hc
    rcases hc with hc | hc
    · unfold lineL at hc
      rw [List.mem_append] at hc
      rcases hc with hc | hc
      · have := lcodes_lt he h.1 c hc; omega
      · simp at hc; omega
    · exact lineL_lt he ls h.2 c hc

theorem evB_sub_even {F : Nat → Int} {M Y P : Nat} (hY : Y &&& P = Y)
    (hP : ∀ c, P.testBit c = true → (2 : Int) ∣ F c) : (2 : Int) ∣ evB F M Y := by
  unfold evB
  apply rsum_dvd
  intro c _
  split
  · next h =>
    apply hP
    have := congrArg (fun z => z.testBit c) hY
    simp only [Nat.testBit_and, h, Bool.true_and] at this
    exact this
  · exact ⟨0, rfl⟩

theorem step_sound (hB : Bases e nb Fb Sb κb G) {f : List Nat → Int} {P P' : Nat} {s : Step}
    (hs : stepB e nb Sb κb P s = some P') (hst : State e G f P) : State e G f P' := by
  obtain ⟨r, κ, hI, hb, hsp⟩ := hst
  cases s with
  | kill gs piv =>
    simp only [stepB] at hs
    split at hs
    · next hc =>
      simp only [Option.some.injEq] at hs; subst hs
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      obtain ⟨⟨⟨hgb, hvp⟩, hdisj⟩, hpiv⟩ := hc
      obtain ⟨a, ha⟩ : ∃ a, a = R e r κ piv := ⟨_, rfl⟩
      have hpar := sum_par hB gs hgb
      refine ⟨fun m => r m + (-a) * sumF Fb gs m, κ + (-a) * sumK κb gs, ?_, ?_, ?_⟩
      · intro c hcb
        rw [R_lin]
        rw [Nat.testBit_or] at hcb
        by_cases hcP : P.testBit c = true
        · obtain ⟨hv, hr⟩ := hI c hcP
          refine ⟨hv, ?_⟩
          have h1 := hpar c hv
          have h0 : bitI (sumM Sb κb gs) c = 0 := by
            unfold bitI
            have := congrArg (fun z => z.testBit c) hdisj
            simp only [Nat.testBit_and, hcP, Bool.and_true, Nat.zero_testBit] at this
            simp [this]
          rw [h0, Int.sub_zero] at h1
          exact Int.dvd_add hr (Int.dvd_trans h1 (Int.dvd_mul_left _ _))
        · have hcp : c = piv := by
            simp only [hcP, Bool.false_or, Nat.testBit_two_pow, decide_eq_true_eq] at hcb; exact hcb.symm
          subst hcp
          refine ⟨hvp, ?_⟩
          have h1 := hpar c hvp
          have h1' : bitI (sumM Sb κb gs) c = 1 := by unfold bitI; simp [hpiv]
          rw [h1'] at h1
          have := Int.dvd_trans h1 (Int.dvd_mul_left (-a) _)
          rw [Int.mul_sub] at this
          rw [← ha, show a + -a * R e (sumF Fb gs) (sumK κb gs) c = -a * R e (sumF Fb gs) (sumK κb gs) c - -a * 1 by omega]
          exact this
      · exact Bal_add hb (Bal_smul (-a) (sum_bal hB gs hgb))
      · exact InSpan.congr (InSpan.add hsp (InSpan.smul a (sum_span hB gs hgb)))
          (fun m _ _ => ⟨0, by
            show f m - (r m + -a * sumF Fb gs m) - ((f m - r m) + a * sumF Fb gs m) = 2 * 0
            rw [Int.neg_mul]; omega⟩)
    · simp at hs
  | prop ls piv =>
    simp only [stepB] at hs
    split at hs
    · next hc =>
      simp only [Option.some.injEq] at hs; subst hs
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨hvp, hls⟩, hbit⟩, hsub⟩ := hc
      refine ⟨r, κ, ?_, hb, hsp⟩
      intro c hcb
      rw [Nat.testBit_or] at hcb
      by_cases hcP : P.testBit c = true
      · exact hI c hcP
      · have hcp : c = piv := by
          simp only [hcP, Bool.false_or, Nat.testBit_two_pow, decide_eq_true_eq] at hcb; exact hcb.symm
        subst hcp
        refine ⟨hvp, ?_⟩
        have hev := lines_even hB.he hb ls hls
        have hbv := ev_bv (R e r κ) (K + 1) (ls.flatMap lineL) (lineL_lt hB.he ls hls)
        have hplt : c < K + 1 := by
          by_cases hK : c = K
          · omega
          · have := (valid_pt hB.he hvp hK).2.2.2; omega
        have hx := evB_xor (R e r κ) (K + 1) (bv (ls.flatMap lineL) ^^^ 2 ^ c) c hplt
        rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at hx
        have hY := evB_sub_even (F := R e r κ) (M := K + 1) hsub (fun c' hc' => (hI c' hc').2)
        have := Int.dvd_sub (Int.dvd_sub hev hbv) (Int.dvd_add hx hY)
        rw [show ∀ a b c d : Int, a - (a - b) - (b - d - c + d) = c by intros; omega] at this
        exact this
    · simp at hs

theorem run_sound (hB : Bases e nb Fb Sb κb G) {f : List Nat → Int} :
    ∀ (ss : List Step) {P P' : Nat}, runB e nb Sb κb P ss = some P' → State e G f P → State e G f P'
  | [], P, P', h, hst => by simp [runB] at h; subst h; exact hst
  | s :: ss, P, P', h, hst => by
    simp only [runB] at h
    split at h
    · next P'' hP => exact run_sound hB ss h (step_sound hB hP hst)
    · simp at h

/-- A state whose mask covers every point gives the span. -/
theorem span_of_state (hB : Bases e nb Fb Sb κb G) {f : List Nat → Int} {P : Nat} (hst : State e G f P)
    (hcov : ∀ m, CM 7 8 m → m.length = e → P.testBit (code m) = true) : InSpan 2 7 8 e G f := by
  obtain ⟨r, κ, hI, -, hsp⟩ := hst
  refine InSpan.congr hsp (fun m hm hl => ?_)
  obtain ⟨-, hr⟩ := hI _ (hcov m hm hl)
  obtain ⟨-, hK, -, hd⟩ := code_pt hB.he hm hl
  simp only [R, hK, if_false, hd] at hr
  rw [show f m - (f m - r m) = r m by omega]; exact hr

/-! ## Finite checks for coverage and for the base functions -/

def allpts : Nat → List (List Nat)
  | 1 => (List.range 105).map (fun a => [a])
  | _ => (List.range 105).flatMap (fun a => (List.range a).filterMap
      (fun b => if isMatch 7 [a, b] then some [a, b] else none))

theorem mem_allpts {e : Nat} (he : e = 1 ∨ e = 2) {m : List Nat} (hm : CM 7 8 m) (hl : m.length = e) :
    m ∈ allpts e := by
  rcases he with rfl | rfl
  · obtain ⟨a, rfl, ha⟩ := CM_one (m := id) hm hl
    simp [allpts, ha]
  · obtain ⟨a, b, rfl, hba, ha, hmt⟩ := CM_two hm hl
    simp only [allpts, List.mem_flatMap, List.mem_range, List.mem_filterMap]
    exact ⟨a, ha, b, hba, by simp [hmt]⟩

def allCov (e P : Nat) : Bool := (allpts e).all (fun m => P.testBit (code m))

theorem cov_of {e P : Nat} (he : e = 1 ∨ e = 2) (h : allCov e P = true) :
    ∀ m, CM 7 8 m → m.length = e → P.testBit (code m) = true := by
  intro m hm hl
  unfold allCov at h; rw [List.all_eq_true] at h
  exact h m (mem_allpts he hm hl)

def parOK (e : Nat) (F : List Nat → Int) (S : List (List Nat)) : Bool :=
  (allpts e).all (fun m => (F m - ((S.map code).count (code m) : Int)) % 2 == 0)

theorem par_of {e : Nat} (he : e = 1 ∨ e = 2) {F : List Nat → Int} {S : List (List Nat)} (h : parOK e F S = true) :
    ∀ x, CM 7 8 x → x.length = e → (2 : Int) ∣ F x - ((S.map code).count (code x) : Int) := by
  intro x hx hl
  unfold parOK at h; rw [List.all_eq_true] at h
  have := h x (mem_allpts he hx hl)
  simp only [beq_iff_eq] at this
  exact Int.dvd_of_emod_eq_zero this

def suppOK (e : Nat) (S : List (List Nat)) : Bool :=
  S.all (fun s => s.length == e && canon ((7 + 8) * 7) s == s && isMatch 7 s)

theorem supp_of {e : Nat} {S : List (List Nat)} (h : suppOK e S = true) : ∀ s ∈ S, CM 7 8 s ∧ s.length = e := by
  intro s hs
  unfold suppOK at h; rw [List.all_eq_true] at h
  have := h s hs
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨⟨this.1.2, this.2⟩, this.1.1⟩

def zlOK (F : List Nat → Int) : Bool :=
  (List.range 105).all (fun w =>
    (List.range 15).all (fun i => w / 7 == i || ev (R 2 F 0) (lcodes [w] true i) % 2 == 0) &&
    (List.range 7).all (fun j => w % 7 == j || ev (R 2 F 0) (lcodes [w] false j) % 2 == 0))

theorem zl_of {F : List Nat → Int} (h : zlOK F = true) : Bal 2 7 8 F (fun _ => 0) 1 := by
  intro g hg hl
  obtain ⟨w, rfl, hw⟩ := CM_one (m := id) hg hl
  unfold zlOK at h; rw [List.all_eq_true] at h
  have hw' := h w (List.mem_range.mpr hw)
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at hw'
  refine ⟨fun i hi hf => ?_, fun j hj hf => ?_⟩
  · have hne : w / 7 ≠ i := hf w (by simp)
    have hok : lineOK 2 ([w], true, i) = true := by simp [lineOK, hw, show i < 15 by omega, hne]
    obtain ⟨-, -, hrow, -⟩ := line_ev (Or.inr rfl) F 0 hok
    rw [(hrow rfl).2.2]
    rcases hw'.1 i (by omega) with h1 | h1
    · exact absurd h1 hne
    · rw [Int.sub_zero]; exact Int.dvd_of_emod_eq_zero (by simpa using h1)
  · have hne : w % 7 ≠ j := hf w (by simp)
    have hok : lineOK 2 ([w], false, j) = true := by simp [lineOK, hw, hj, hne]
    obtain ⟨-, -, -, hcol⟩ := line_ev (Or.inr rfl) F 0 hok
    rw [(hcol rfl).2.2]
    rcases hw'.2 j hj with h1 | h1
    · exact absurd h1 hne
    · rw [Int.sub_zero]; exact Int.dvd_of_emod_eq_zero (by simpa using h1)

/-- **Span from a checked run**: a state over `P0`, a run to `P1` and coverage give the span. -/
theorem span_of_run (hB : Bases e nb Fb Sb κb G) {f : List Nat → Int} {P0 P1 : Nat} (ss : List Step)
    (hst : State e G f P0) (hr : runB e nb Sb κb P0 ss = some P1) (hc : allCov e P1 = true) :
    InSpan 2 7 8 e G f :=
  span_of_state hB (run_sound hB ss hr hst) (cov_of hB.he hc)

end Programme.«20261027-1434-proof-complexity».Peel
