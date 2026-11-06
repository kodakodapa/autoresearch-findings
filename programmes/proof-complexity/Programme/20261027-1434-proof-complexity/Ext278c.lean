import Programme.«20261027-1434-proof-complexity».L1bData
import Programme.«20261027-1434-proof-complexity».Cong
import Programme.«20261027-1434-proof-complexity».Ext278b
import Programme.«20261027-1434-proof-complexity».Lift

/-!
# `EXT 2 7 8 3` from the level-3 zero-link span alone

Generators are self-balanced functions: `SB1` (balanced against themselves at levels 1, 2, 3),
`SB23` (levels 2, 3), `SB3` (level 3). Members are the library K5 design `D` (`K5Bal`) and the
product towers `RBd`, `TB`, `RRM`, `RRRM` (`Towers`), and all their relabellings.

`span2b`: every level-1 balanced `c` (on 2-matchings) is in the level-2 span of `SB23`:
* its link `h` is level-0 balanced (`Ext278a.link_bal`), so the new level-1 certificate (`L1bData`,
  bases `D` and `RBd`) puts `h` in the level-1 span of `SB1`, which lifts to `u ∈ span SB23` with
  `Bal u h 1` (each generator extends itself);
* `c - u` has zero link, so the existing level-2 certificate (`L2C0` .. `L2C8`) puts it in the span
  of relabellings of `R0` and `T`; these agree mod 2 on 2-matchings with relabellings of `RRM` and
  of `relab πT ρT TB` (`Cong`), which are in `SB23`.

`ext3_of_z3` (via `Lift.EXT_lift`, `d = 1`): if every zero-link level-2 balanced function on
3-matchings is in the level-3 span of `SB3`, then `EXT 2 7 8 3`; `hard_of_z3` then gives: no
degree-4 `PPCRefutation 2` of `ontoFPHP n 8` for any `n ≥ 7`. `hard_of_rrr` states the hypothesis
with relabellings of `RRRM` only (th's RRR generators).
-/

namespace Programme.«20261027-1434-proof-complexity».Ext278c

set_option linter.deprecated false

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin
open Programme.«20261026-1402-proof-complexity».Relabel
open Programme.«20261027-1434-proof-complexity».PeelBase Programme.«20261027-1434-proof-complexity».Peel

def SB1 (g : List Nat → Int) : Prop := Bal 2 7 8 g g 1 ∧ Bal 2 7 8 g g 2 ∧ Bal 2 7 8 g g 3
def SB23 (g : List Nat → Int) : Prop := Bal 2 7 8 g g 2 ∧ Bal 2 7 8 g g 3
def SB3 (g : List Nat → Int) : Prop := Bal 2 7 8 g g 3

theorem sb1_of {g : List Nat → Int} (h : ∀ e ≤ 3, Bal 2 7 8 g g e) (σ : Perm (7 + 8)) (τ : Perm 7) :
    SB1 (relab σ τ g) :=
  ⟨bal_relab σ τ (h 1 (by omega)), bal_relab σ τ (h 2 (by omega)), bal_relab σ τ (h 3 (by omega))⟩

theorem sb23_of {g : List Nat → Int} (h : ∀ e ≤ 3, Bal 2 7 8 g g e) (σ : Perm (7 + 8)) (τ : Perm 7) :
    SB23 (relab σ τ g) :=
  ⟨bal_relab σ τ (h 2 (by omega)), bal_relab σ τ (h 3 (by omega))⟩

theorem len0 {g : List Nat} (hl : g.length = 0) : g = [] := List.eq_nil_of_length_eq_zero hl

theorem rbd_nil : Programme.«20261027-1434-proof-complexity».Towers.RBd [] = 0 := by decide

theorem bases1b : Bases 1 2 L1bData.Fb L1bData.Sb L1bData.κb SB1 where
  he := Or.inl rfl
  nb0 := by omega
  hS := fun b hb => by
    match b, hb with
    | 0, _ => exact supp_of L1bData.supp_D
    | 1, _ => exact supp_of L1bData.supp_R
  hF := fun b hb => by
    match b, hb with
    | 0, _ => exact par_of (Or.inl rfl) L1bData.par_D
    | 1, _ => exact par_of (Or.inl rfl) L1bData.par_R
  hB := fun b hb => by
    match b, hb with
    | 0, _ => exact Bal_congr (Programme.«20261027-1434-proof-complexity».K5Bal.d_bal 0 (by omega)) (fun g _ hl => by
        rw [len0 hl, Programme.«20261027-1434-proof-complexity».K5Bal.D_nil]; exact ⟨0, rfl⟩)
    | 1, _ => exact Bal_congr (Programme.«20261027-1434-proof-complexity».Towers.rbd_bal 0 (by omega)) (fun g _ hl => by
        rw [len0 hl, rbd_nil]; exact ⟨0, rfl⟩)
  hG := fun b hb σ τ => by
    match b, hb with
    | 0, _ => exact sb1_of Programme.«20261027-1434-proof-complexity».K5Bal.d_bal σ τ
    | 1, _ => exact sb1_of Programme.«20261027-1434-proof-complexity».Towers.rbd_bal σ τ

/-- **Level-1 span** over `SB1`. -/
theorem span1b (c : List Nat → Int) (κ : Int) (hc : Bal 2 7 8 c (fun _ => κ) 0) : InSpan 2 7 8 1 SB1 c := by
  have hst : State 1 SB1 c 0 := ⟨c, κ, fun x hx => by simp at hx, hc,
    span_zero bases1b _ (fun m => by omega)⟩
  have h := L1bData.run_ok
  split at h
  · next P hP => exact span_of_run bases1b L1bData.cert hst hP h
  · simp at h

theorem lift1b {c : List Nat → Int} (hc : InSpan 2 7 8 1 SB1 c) :
    ∃ u, InSpan 2 7 8 2 SB23 u ∧ Bal 2 7 8 u c 1 := by
  induction hc with
  | gen h => exact ⟨_, InSpan.gen ⟨h.2.1, h.2.2⟩, h.1⟩
  | add _ _ ih ih' =>
    obtain ⟨u, hu, hb⟩ := ih; obtain ⟨u', hu', hb'⟩ := ih'
    exact ⟨_, InSpan.add hu hu', Bal_add hb hb'⟩
  | smul a _ ih =>
    obtain ⟨u, hu, hb⟩ := ih
    exact ⟨_, InSpan.smul a hu, Bal_smul a hb⟩
  | congr _ hcg ih =>
    obtain ⟨u, hu, hb⟩ := ih
    exact ⟨u, hu, Bal_congr hb hcg⟩

theorem span_mono {e : Nat} {A B : (List Nat → Int) → Prop} (hAB : ∀ g, A g → InSpan 2 7 8 e B g)
    {f : List Nat → Int} (h : InSpan 2 7 8 e A f) : InSpan 2 7 8 e B f := by
  induction h with
  | gen h => exact hAB _ h
  | add _ _ ih ih' => exact InSpan.add ih ih'
  | smul a _ ih => exact InSpan.smul a ih
  | congr _ hc ih => exact InSpan.congr ih hc

/-- The zero-link part of `Ext278b.span2`: level-2 certificate over relabellings of `R0` and `T`. -/
theorem zl2 (z : List Nat → Int) (hz : Bal 2 7 8 z (fun _ => (0 : Int)) 1) : InSpan 2 7 8 2 Programme.«20261027-1434-proof-complexity».Ext278b.GZ z := by
  have s0 : State 2 Programme.«20261027-1434-proof-complexity».Ext278b.GZ z Programme.«20261027-1434-proof-complexity».L2C0.P0 := by
    refine ⟨_, 0, ?_, hz, span_zero Programme.«20261027-1434-proof-complexity».Ext278b.bases2 _ (fun m => by show z m - z m = 0; omega)⟩
    intro x hx
    have hxK : x = K := by
      rw [Programme.«20261027-1434-proof-complexity».Ext278b.p0, Nat.testBit_two_pow] at hx; exact (of_decide_eq_true hx).symm
    subst hxK
    exact ⟨by decide +kernel, by simp [R]⟩
  have s1 := run_sound Programme.«20261027-1434-proof-complexity».Ext278b.bases2 Programme.«20261027-1434-proof-complexity».L2C0.cert Programme.«20261027-1434-proof-complexity».L2C0.ok s0
  have s2 := run_sound Programme.«20261027-1434-proof-complexity».Ext278b.bases2 Programme.«20261027-1434-proof-complexity».L2C1.cert Programme.«20261027-1434-proof-complexity».L2C1.ok s1
  have s3 := run_sound Programme.«20261027-1434-proof-complexity».Ext278b.bases2 Programme.«20261027-1434-proof-complexity».L2C2.cert Programme.«20261027-1434-proof-complexity».L2C2.ok s2
  have s4 := run_sound Programme.«20261027-1434-proof-complexity».Ext278b.bases2 Programme.«20261027-1434-proof-complexity».L2C3.cert Programme.«20261027-1434-proof-complexity».L2C3.ok s3
  have s5 := run_sound Programme.«20261027-1434-proof-complexity».Ext278b.bases2 Programme.«20261027-1434-proof-complexity».L2C4.cert Programme.«20261027-1434-proof-complexity».L2C4.ok s4
  have s6 := run_sound Programme.«20261027-1434-proof-complexity».Ext278b.bases2 Programme.«20261027-1434-proof-complexity».L2C5.cert Programme.«20261027-1434-proof-complexity».L2C5.ok s5
  have s7 := run_sound Programme.«20261027-1434-proof-complexity».Ext278b.bases2 Programme.«20261027-1434-proof-complexity».L2C6.cert Programme.«20261027-1434-proof-complexity».L2C6.ok s6
  have s8 := run_sound Programme.«20261027-1434-proof-complexity».Ext278b.bases2 Programme.«20261027-1434-proof-complexity».L2C7.cert Programme.«20261027-1434-proof-complexity».L2C7.ok s7
  have s9 := run_sound Programme.«20261027-1434-proof-complexity».Ext278b.bases2 Programme.«20261027-1434-proof-complexity».L2C8.cert Programme.«20261027-1434-proof-complexity».L2C8.ok s8
  exact span_of_state Programme.«20261027-1434-proof-complexity».Ext278b.bases2 s9 (cov_of (Or.inr rfl) Programme.«20261027-1434-proof-complexity».Ext278b.cov)

/-- Relabellings of `R0` and `T` are in the level-2 span of `SB23`. -/
theorem gz_span (g : List Nat → Int) (hg : Programme.«20261027-1434-proof-complexity».Ext278b.GZ g) : InSpan 2 7 8 2 SB23 g := by
  obtain ⟨σ, τ, rfl | rfl⟩ := hg
  · exact InSpan.congr (InSpan.gen (sb23_of Programme.«20261027-1434-proof-complexity».Towers.rrm_bal σ τ))
      (Programme.«20261027-1434-proof-complexity».Cong.relab_cong σ τ Programme.«20261027-1434-proof-complexity».Cong.r0_cong)
  · have h : ∀ e ≤ 3, Bal 2 7 8 (relab Programme.«20261027-1434-proof-complexity».Cong.πT Programme.«20261027-1434-proof-complexity».Cong.ρT Programme.«20261027-1434-proof-complexity».Towers.TB)
        (relab Programme.«20261027-1434-proof-complexity».Cong.πT Programme.«20261027-1434-proof-complexity».Cong.ρT Programme.«20261027-1434-proof-complexity».Towers.TB) e :=
      fun e he => bal_relab _ _ (Programme.«20261027-1434-proof-complexity».Towers.tb_bal e he)
    exact InSpan.congr (InSpan.gen (sb23_of h σ τ)) (Programme.«20261027-1434-proof-complexity».Cong.relab_cong σ τ Programme.«20261027-1434-proof-complexity».Cong.t_cong)

/-- **Level-2 span over self-balanced generators.** -/
theorem span2b (c h : List Nat → Int) (hb : Bal 2 7 8 c h 1) : InSpan 2 7 8 2 SB23 c := by
  obtain ⟨u, hu, hbu⟩ := lift1b (span1b h _ (Programme.«20261027-1434-proof-complexity».Ext278a.link_bal hb))
  have hz : Bal 2 7 8 (fun m => c m + (-1) * u m) (fun _ => (0 : Int)) 1 :=
    Bal_cext (Bal_add hb (Bal_smul (-1) hbu)) (fun m => by omega)
  exact InSpan.congr (InSpan.add (span_mono gz_span (zl2 _ hz)) hu) (fun m _ _ => ⟨0, by omega⟩)

/-- **`EXT 2 7 8 3` from the level-3 zero-link span.** -/
theorem ext3_of_z3 (hZ : ∀ z, Bal 2 7 8 z (fun _ => 0) 2 → InSpan 2 7 8 3 SB3 z) : EXT 2 7 8 3 :=
  Programme.«20261027-1434-proof-complexity».Lift.EXT_lift (d := 1) (by omega) (G := SB23) (Gz := SB3)
    (fun γ hγ => ⟨γ, hγ.1, γ, hγ.2⟩) span2b (fun z hz => ⟨z, hz⟩) hZ

/-- **The l = 3 step over `Z/2` from the level-3 zero-link span.** -/
theorem hard_of_z3 (hZ : ∀ z, Bal 2 7 8 z (fun _ => 0) 2 → InSpan 2 7 8 3 SB3 z) (n : Nat) (hn : 7 ≤ n) :
    ¬ PPCRefutation 2 (ontoFPHP n 8) 4 :=
  Programme.«20261027-1434-proof-complexity».Ext278b.hard_of_ext3 (ext3_of_z3 hZ) n hn

/-- Relabellings of `RRRM` (three disjoint rectangles times the `9 × 1` block). -/
def GR (g : List Nat → Int) : Prop := ∃ (σ : Perm (7 + 8)) (τ : Perm 7), g = relab σ τ Programme.«20261027-1434-proof-complexity».Towers.RRRM

/-- The same with th's RRR generators: it suffices that every zero-link level-2 balanced function on
3-matchings is a level-3 span of relabellings of `RRRM`. -/
theorem hard_of_rrr (hZ : ∀ z, Bal 2 7 8 z (fun _ => 0) 2 → InSpan 2 7 8 3 GR z) (n : Nat) (hn : 7 ≤ n) :
    ¬ PPCRefutation 2 (ontoFPHP n 8) 4 :=
  hard_of_z3 (fun z hz => span_mono (fun g hg => by
    obtain ⟨σ, τ, rfl⟩ := hg
    exact InSpan.gen (bal_relab σ τ (Programme.«20261027-1434-proof-complexity».Towers.rrrm_bal 3 (by omega)))) (hZ z hz)) n hn

end Programme.«20261027-1434-proof-complexity».Ext278c

#print axioms Programme.«20261027-1434-proof-complexity».Ext278c.span2b
#print axioms Programme.«20261027-1434-proof-complexity».Ext278c.ext3_of_z3
#print axioms Programme.«20261027-1434-proof-complexity».Ext278c.hard_of_z3
#print axioms Programme.«20261027-1434-proof-complexity».Ext278c.hard_of_rrr
