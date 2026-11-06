import Programme.«20261027-1434-proof-complexity».L2C0
import Programme.«20261027-1434-proof-complexity».L2C1
import Programme.«20261027-1434-proof-complexity».L2C2
import Programme.«20261027-1434-proof-complexity».L2C3
import Programme.«20261027-1434-proof-complexity».L2C4
import Programme.«20261027-1434-proof-complexity».L2C5
import Programme.«20261027-1434-proof-complexity».L2C6
import Programme.«20261027-1434-proof-complexity».L2C7
import Programme.«20261027-1434-proof-complexity».L2C8
import Programme.«20261027-1434-proof-complexity».Ext278a
import Programme.«20261026-1402-proof-complexity».RectExt
import Programme.«20261026-1402-proof-complexity».TImage
import Programme.«20261026-1402-proof-complexity».Ext0

/-!
# `EXT 2 7 8 2`, and the l = 3 step reduced to `EXT 2 7 8 3`

For `f` with `Bal 2 7 8 f c 1`: the link `c` is level-0 balanced (`link_bal`, K157), so it is a
level-1 span of relabelled `H` (`span1`), which lifts to `u` with `Bal u c 1` (`lift1`). Then
`f - u` has zero link, and the kernel-checked level-2 peeling certificate (`L2C0` .. `L2C8`, from th's
certificate) puts it in the span of relabellings of the rectangle product `R0` and of `T`. Every
generator has a level-2 extension (`rect_ext`, `t_image_ext`, `Bal H H 2`), so `EXT_of_span` gives
`ext2 : EXT 2 7 8 2`.

`hard_of_ext3`: with `Ext0.ext0`, `Ext278a.ext1` and `ext2`, the single remaining hypothesis
`EXT 2 7 8 3` gives: for every `n ≥ 7`, `ontoFPHP n 8` has no degree-4 `PPCRefutation 2`.
-/

namespace Programme.«20261027-1434-proof-complexity».Ext278b

set_option linter.deprecated false

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin
open Programme.«20261026-1402-proof-complexity».Relabel
open Programme.«20261027-1434-proof-complexity».PeelBase Programme.«20261027-1434-proof-complexity».Peel Programme.«20261027-1434-proof-complexity».Ext278a

/-- Relabellings of `R0` and of `T`. -/
def GZ (g : List Nat → Int) : Prop :=
  ∃ (σ : Perm (7 + 8)) (τ : Perm 7), g = relab σ τ Programme.«20261027-1434-proof-complexity».L2Base.R0 ∨
    g = relab σ τ (Programme.«20261026-1402-proof-complexity».TExt.T 7)

def G (g : List Nat → Int) : Prop := GZ g ∨ GH g

theorem bases2 : Bases 2 2 Programme.«20261027-1434-proof-complexity».L2Base.Fb Programme.«20261027-1434-proof-complexity».L2Base.Sb (fun _ => 0) GZ where
  he := Or.inr rfl
  nb0 := by omega
  hS := fun b hb => by
    rcases b with _ | _ | b
    · exact supp_of Programme.«20261027-1434-proof-complexity».L2Base.supp0
    · exact supp_of Programme.«20261027-1434-proof-complexity».L2Base.supp1
    · omega
  hF := fun b hb => by
    rcases b with _ | _ | b
    · exact par_of (Or.inr rfl) Programme.«20261027-1434-proof-complexity».L2Base.par0
    · exact par_of (Or.inr rfl) Programme.«20261027-1434-proof-complexity».L2Base.par1
    · omega
  hB := fun b hb => by
    rcases b with _ | _ | b
    · exact zl_of Programme.«20261027-1434-proof-complexity».L2Base.zl0
    · exact zl_of Programme.«20261027-1434-proof-complexity».L2Base.zl1
    · omega
  hG := fun b hb σ τ => by
    rcases b with _ | _ | b
    · exact ⟨σ, τ, Or.inl rfl⟩
    · exact ⟨σ, τ, Or.inr rfl⟩
    · omega

theorem mono {e : Nat} {A B : (List Nat → Int) → Prop} (hAB : ∀ g, A g → B g) {f : List Nat → Int}
    (h : InSpan 2 7 8 e A f) : InSpan 2 7 8 e B f := by
  induction h with
  | gen h => exact InSpan.gen (hAB _ h)
  | add _ _ ih ih' => exact InSpan.add ih ih'
  | smul a _ ih => exact InSpan.smul a ih
  | congr _ hc ih => exact InSpan.congr ih hc

theorem cov : allCov 2 Programme.«20261027-1434-proof-complexity».L2C8.P1 = true := by decide +kernel

theorem p0 : Programme.«20261027-1434-proof-complexity».L2C0.P0 = 2 ^ K := by decide +kernel

/-- **Level-2 span.** -/
theorem span2 (f c : List Nat → Int) (hb : Bal 2 7 8 f c 1) : InSpan 2 7 8 2 G f := by
  obtain ⟨u, hu, hbu⟩ := lift1 (span1 c _ (link_bal hb))
  have hz : Bal 2 7 8 (fun m => f m + (-1) * u m) (fun _ => (0 : Int)) 1 :=
    Bal_cext (Bal_add hb (Bal_smul (-1) hbu)) (fun m => by omega)
  have s0 : State 2 GZ (fun m => f m + (-1) * u m) Programme.«20261027-1434-proof-complexity».L2C0.P0 := by
    refine ⟨_, 0, ?_, hz, span_zero bases2 _ (fun m => by show f m + -1 * u m - (f m + -1 * u m) = 0; omega)⟩
    intro x hx
    have hxK : x = K := by
      rw [p0, Nat.testBit_two_pow] at hx; exact (of_decide_eq_true hx).symm
    subst hxK
    exact ⟨by decide +kernel, by simp [R]⟩
  have s1 := run_sound bases2 Programme.«20261027-1434-proof-complexity».L2C0.cert Programme.«20261027-1434-proof-complexity».L2C0.ok s0
  have s2 := run_sound bases2 Programme.«20261027-1434-proof-complexity».L2C1.cert Programme.«20261027-1434-proof-complexity».L2C1.ok s1
  have s3 := run_sound bases2 Programme.«20261027-1434-proof-complexity».L2C2.cert Programme.«20261027-1434-proof-complexity».L2C2.ok s2
  have s4 := run_sound bases2 Programme.«20261027-1434-proof-complexity».L2C3.cert Programme.«20261027-1434-proof-complexity».L2C3.ok s3
  have s5 := run_sound bases2 Programme.«20261027-1434-proof-complexity».L2C4.cert Programme.«20261027-1434-proof-complexity».L2C4.ok s4
  have s6 := run_sound bases2 Programme.«20261027-1434-proof-complexity».L2C5.cert Programme.«20261027-1434-proof-complexity».L2C5.ok s5
  have s7 := run_sound bases2 Programme.«20261027-1434-proof-complexity».L2C6.cert Programme.«20261027-1434-proof-complexity».L2C6.ok s6
  have s8 := run_sound bases2 Programme.«20261027-1434-proof-complexity».L2C7.cert Programme.«20261027-1434-proof-complexity».L2C7.ok s7
  have s9 := run_sound bases2 Programme.«20261027-1434-proof-complexity».L2C8.cert Programme.«20261027-1434-proof-complexity».L2C8.ok s8
  have hz' := span_of_state bases2 s9 (cov_of (Or.inr rfl) cov)
  exact InSpan.congr (InSpan.add (mono (fun g h => Or.inl h) hz') (mono (fun g h => Or.inr h) hu))
    (fun m _ _ => ⟨0, by omega⟩)

theorem g_ext {g : List Nat → Int} (hg : G g) : ∃ y, Bal 2 7 8 y g 2 := by
  rcases hg with ⟨σ, τ, rfl | rfl⟩ | hg
  · exact ext_relab σ τ (Programme.«20261026-1402-proof-complexity».RectExt.rect_ext (by omega) (by decide)
      Programme.«20261027-1434-proof-complexity».L2Base.R0 ⟨0, 1, 2, 3, 0, 1, 2, 3, by decide, by decide, by decide, by decide, rfl⟩)
  · exact ⟨_, Programme.«20261026-1402-proof-complexity».TImage.t_image_ext (by omega) (by decide) σ τ⟩
  · exact ⟨g, gh_ext (by omega) hg⟩

/-- **`EXT 2 7 8 2`**. -/
theorem ext2 : EXT 2 7 8 2 :=
  EXT_of_span (G := G) (fun f hf => g_ext hf) (fun f c hb => span2 f c (hb 1 rfl))

/-- **The l = 3 step from level 3 alone.** If `EXT 2 7 8 3` holds, then for every `n ≥ 7`,
`ontoFPHP n 8` (functional encoding) has no degree-4 polynomial-calculus refutation over `Z/2`. -/
theorem hard_of_ext3 (h3 : EXT 2 7 8 3) (n : Nat) (hn : 7 ≤ n) : ¬ PPCRefutation 2 (ontoFPHP n 8) 4 :=
  no_refutation_of_ext_ge (by omega) (by omega) (by omega) (fun d hd => by
    rcases d with _ | _ | _ | d
    · exact Programme.«20261026-1402-proof-complexity».Ext0.ext0 (by omega) ⟨4, rfl⟩
    · exact ext1
    · exact ext2
    · rcases d with _ | d
      · exact h3
      · omega) n hn

end Programme.«20261027-1434-proof-complexity».Ext278b

#print axioms Programme.«20261027-1434-proof-complexity».Ext278b.ext2
#print axioms Programme.«20261027-1434-proof-complexity».Ext278b.hard_of_ext3
