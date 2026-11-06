import Programme.«20261027-1434-proof-complexity».RowColG
import Programme.«20261026-1402-proof-complexity».ExtLin

/-!
# EXT at level `d + 2` from liftable generators and a zero-link span

th's route to `EXT 2 7 8 3` (P27), as a generic reduction. Take `f` with `Bal f c (d+1)`.

1. The link `c` is level-`d` balanced (`RowColG.link_bal`, needs `d < n`), so by the level-`(d+1)`
   span condition `hS` it lies in the span of `G`.
2. Every generator `γ ∈ G` has a lift `L` (`Bal L γ (d+1)`) that itself extends to level `d+2`.
   Lifts are linear (`lift_of_span`), so `c` has such a lift `L`.
3. `f - L` has zero link at level `d+1`, so by `hZ` it lies in the span of `Gz`, whose members
   extend to level `d+2`; `ExtLin.ext_of_span` extends it.

The two extensions add up to an extension of `f`: `EXT p n k (d + 2)` (`EXT_lift`).
-/

namespace Programme.«20261027-1434-proof-complexity».Lift

open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin

variable {p n k : Nat}

/-- `Bal` reads its target only at canonical `e`-matchings and only mod `p`. -/
theorem Bal_tcongr {e : Nat} {y c c' : List Nat → Int} (h : Bal p n k y c e)
    (hc : ∀ g, CM n k g → g.length = e → (p : Int) ∣ c' g - c g) : Bal p n k y c' e := by
  intro g hg hl
  obtain ⟨hr, hcol⟩ := h g hg hl
  have hd := hc g hg hl
  refine ⟨fun i hi hp => ?_, fun j hj hp => ?_⟩
  · have := Int.dvd_sub (hr i hi hp) hd
    rw [show ∀ a b c : Int, a - c - (b - c) = a - b by intros; omega] at this; exact this
  · have := Int.dvd_sub (hcol j hj hp) hd
    rw [show ∀ a b c : Int, a - c - (b - c) = a - b by intros; omega] at this; exact this

/-- `L` lifts `γ` at level `e` and extends to level `e + 1`. -/
def Lifts (p n k e : Nat) (γ : List Nat → Int) : Prop :=
  ∃ L, Bal p n k L γ e ∧ ∃ y, Bal p n k y L (e + 1)

/-- **Lifts are linear.** -/
theorem lift_of_span {e : Nat} {G : (List Nat → Int) → Prop} (hG : ∀ γ, G γ → Lifts p n k e γ)
    {c : List Nat → Int} (hc : InSpan p n k e G c) : Lifts p n k e c := by
  induction hc with
  | gen h => exact hG _ h
  | add _ _ ih ih' =>
    obtain ⟨L, hL, y, hy⟩ := ih; obtain ⟨L', hL', y', hy'⟩ := ih'
    exact ⟨_, Bal_add hL hL', _, Bal_add hy hy'⟩
  | smul a _ ih =>
    obtain ⟨L, hL, y, hy⟩ := ih
    exact ⟨_, Bal_smul a hL, _, Bal_smul a hy⟩
  | congr _ hcg ih =>
    obtain ⟨L, hL, y, hy⟩ := ih
    exact ⟨L, Bal_tcongr hL hcg, y, hy⟩

/-- **EXT at level `d + 2`** from liftable generators of the level-`(d+1)` span and an extendable
spanning set of the zero-link space at level `d + 2`. -/
theorem EXT_lift {d : Nat} (hd : d < n) {G Gz : (List Nat → Int) → Prop}
    (hG : ∀ γ, G γ → Lifts p n k (d + 1) γ)
    (hS : ∀ c h : List Nat → Int, Bal p n k c h d → InSpan p n k (d + 1) G c)
    (hGz : ∀ z, Gz z → ∃ y, Bal p n k y z (d + 2))
    (hZ : ∀ z, Bal p n k z (fun _ => 0) (d + 1) → InSpan p n k (d + 2) Gz z) :
    EXT p n k (d + 2) := by
  intro f c hb
  have hf : Bal p n k f c (d + 1) := hb (d + 1) rfl
  obtain ⟨L, hL, y, hy⟩ := lift_of_span hG (hS c _ (Programme.«20261027-1434-proof-complexity».RowColG.link_bal hd hf))
  have hz : Bal p n k (fun g => f g + -1 * L g) (fun _ => 0) (d + 1) :=
    Bal_tcongr (Bal_add hf (Bal_smul (-1) hL)) (fun g _ _ => ⟨0, by omega⟩)
  obtain ⟨y', hy'⟩ := ext_of_span hGz (hZ _ hz)
  refine ⟨fun g => y g + y' g, ?_⟩
  exact Bal_tcongr (Bal_add hy hy') (fun g _ _ => ⟨0, by omega⟩)

end Programme.«20261027-1434-proof-complexity».Lift

#print axioms Programme.«20261027-1434-proof-complexity».Lift.EXT_lift
