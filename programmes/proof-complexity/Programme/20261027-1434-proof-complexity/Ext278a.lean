import Programme.«20261027-1434-proof-complexity».L1Data
import Programme.«20261026-1402-proof-complexity».RowCol

/-!
# `EXT 2 7 8 1`, and lifting level-1 spans of relabelled `H` to level 2

`span1`: over `Z/2`, every function on the edges of `ontoFPHP 7 8` whose row and column sums at
`[]` are all `≡ κ` lies in the level-1 span of the relabellings of th's `H` (kernel-checked
peeling certificate `L1Data.cert`, sound by `Peel.span_of_run`). With `bal_relab` and
`HDes.h_design` this gives `ext1 : EXT 2 7 8 1`.

`lift1`: a level-1 span of relabelled `H` comes from a function `u` in the level-2 span of the same
generators whose level-1 sums are balanced against it (each generator extends itself, `Bal H H 1`).
-/

namespace Programme.«20261027-1434-proof-complexity».Ext278a

set_option linter.deprecated false

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin
open Programme.«20261026-1402-proof-complexity».Relabel
open Programme.«20261027-1434-proof-complexity».PeelBase Programme.«20261027-1434-proof-complexity».Peel

/-- Relabellings of th's `H`. -/
def GH (g : List Nat → Int) : Prop := ∃ (σ : Perm (7 + 8)) (τ : Perm 7), g = relab σ τ Programme.«20261027-1434-proof-complexity».HDes.H

theorem len0 {g : List Nat} (hl : g.length = 0) : g = [] := List.eq_nil_of_length_eq_zero hl

theorem H_bal0 : Bal 2 7 8 Programme.«20261027-1434-proof-complexity».HDes.H (fun _ => ((1 : Nat) : Int)) 0 :=
  Bal_congr (Programme.«20261027-1434-proof-complexity».HDes.h_design.2 0 (by omega)) (fun g _ hl => by
    rw [len0 hl, Programme.«20261027-1434-proof-complexity».HDes.h_design.1]; exact ⟨0, rfl⟩)

theorem bases1 : Bases 1 1 (fun _ => Programme.«20261027-1434-proof-complexity».HDes.H) (fun _ => L1Data.S1) (fun _ => 1) GH where
  he := Or.inl rfl
  nb0 := by omega
  hS := fun _ _ => supp_of L1Data.supp_ok
  hF := fun _ _ => par_of (Or.inl rfl) L1Data.par_ok
  hB := fun _ _ => H_bal0
  hG := fun _ _ σ τ => ⟨σ, τ, rfl⟩

/-- **Level-1 span.** -/
theorem span1 (c : List Nat → Int) (κ : Int) (hc : Bal 2 7 8 c (fun _ => κ) 0) : InSpan 2 7 8 1 GH c := by
  have hst : State 1 GH c 0 := ⟨c, κ, fun x hx => by simp at hx, hc,
    span_zero bases1 _ (fun m => by omega)⟩
  have h := L1Data.run_ok
  split at h
  · next P hP => exact span_of_run bases1 L1Data.cert hst hP h
  · simp at h

theorem gh_ext {d : Nat} (hd : d ≤ 2) {g : List Nat → Int} (hg : GH g) : Bal 2 7 8 g g d := by
  obtain ⟨σ, τ, rfl⟩ := hg
  exact bal_relab σ τ (Programme.«20261027-1434-proof-complexity».HDes.h_design.2 d hd)

/-- **`EXT 2 7 8 1`**: every `f` with all row and column sums at `[]` congruent to `c []` mod 2
has a level-1 extension. -/
theorem ext1 : EXT 2 7 8 1 := by
  apply EXT_of_span (G := GH) (fun f hf => ⟨f, gh_ext (by omega) hf⟩)
  intro f c hb
  have h0 := hb 0 rfl
  exact span1 f (c []) (Bal_congr h0 (fun g _ hl => by rw [len0 hl]; exact ⟨0, by omega⟩))

/-- A level-1 span of relabelled `H` lifts to a level-2 span balanced against it. -/
theorem lift1 {c : List Nat → Int} (hc : InSpan 2 7 8 1 GH c) :
    ∃ u, InSpan 2 7 8 2 GH u ∧ Bal 2 7 8 u c 1 := by
  induction hc with
  | gen h => exact ⟨_, InSpan.gen h, gh_ext (by omega) h⟩
  | add _ _ ih ih' =>
    obtain ⟨u, hu, hb⟩ := ih; obtain ⟨u', hu', hb'⟩ := ih'
    exact ⟨_, InSpan.add hu hu', Bal_add hb hb'⟩
  | smul a _ ih =>
    obtain ⟨u, hu, hb⟩ := ih
    exact ⟨_, InSpan.smul a hu, Bal_smul a hb⟩
  | congr _ hcg ih =>
    obtain ⟨u, hu, hb⟩ := ih
    exact ⟨u, hu, Bal_congr hb hcg⟩

/-- The link of a level-1 balanced pair is level-0 balanced (K157, `RowCol.row_col`). -/
theorem link_bal {f c : List Nat → Int} (hb : Bal 2 7 8 f c 1) :
    Bal 2 7 8 c (fun _ => rowS 7 8 c [] 0) 0 := by
  have rc := fun i j (hi : i < 7 + 8) (hj : j < 7) =>
    Programme.«20261026-1402-proof-complexity».RowCol.row_col (p := 2) (n := 7) (k := 8) (f := f) (c := c) hb hi hj
  intro g _ hl
  rw [len0 hl]
  refine ⟨fun i hi _ => ?_, fun j hj _ => ?_⟩
  · have h1 := rc i 0 hi (by omega)
    have h2 := rc 0 0 (by omega) (by omega)
    have := Int.dvd_sub h1 h2
    rw [show ∀ a b c : Int, a - c - (b - c) = a - b by intros; omega] at this
    exact this
  · have h2 := rc 0 j (by omega) hj
    have := Int.dvd_neg.mpr h2
    rw [show ∀ a b : Int, -(a - b) = b - a by intros; omega] at this
    exact this

end Programme.«20261027-1434-proof-complexity».Ext278a

#print axioms Programme.«20261027-1434-proof-complexity».Ext278a.ext1
#print axioms Programme.«20261027-1434-proof-complexity».Ext278a.span1
