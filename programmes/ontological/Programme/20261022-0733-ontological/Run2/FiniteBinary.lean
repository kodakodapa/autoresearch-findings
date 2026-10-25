import Programme.«20261022-0733-ontological».Run2.Binary
import Programme.«20261022-0733-ontological».Run2.Th4Route

/-! # A finite separator for Gödel's binary conjunction axiom (sk P355)

sk's hand model: worlds `Bool` (`false` = world 0, `true` = world 1), one entity, always
actual, `R w v :↔ v = false` (both worlds see only world 0), all carriers full (so `𝓛`-general),
and rigid positivity `P φ w :↔ φ () false`.

* `fb_sep`: the model is `LGenF` and `Closed` and satisfies `Ax1Bin`, `Ax2a`, `Ax2b`, `Ax3`
  (variant 2) and `Ax4`; it refutes `Ax1GenTwo` (at world 1), `Ax1Gen`, `Ax3v3` and admitted `MC`;
  at world 1 there is no actual God-like being, no `UF` and no `Princ`; at world 0 there is.
* The `Ax1GenTwo` failure uses a world-dependent collection: `Φ(1) = {⊤, at₀}`, `Φ(0) = {⊥}`.
  World 1 only sees world 0, so a conjunction of `Φ` must be false at world 0, hence not positive.

So in variant 2 the gap between binary A1 and `Ax1GenTwo` already has a finite (two-world)
witness; `Binary.binary_gap` (`rx`, infinite) is stronger: it also satisfies `Ax3v3` and has
no God at any world. -/

namespace Programme.«20261022-0733-ontological».Run2.FiniteBinary

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.Ultrafilter Programme.«20261022-0733-ontological».Run2.Principal
  Programme.«20261022-0733-ontological».Run2.Binary
open Programme.«20261022-0733-ontological».Run2.LGeneralFull (LGenF)
open Programme.«20261022-0733-ontological».Run2.LGeneralFullInst (lgenF_full)

def fb : Model Bool Unit where
  R := fun _ v => v = false
  act := fun _ _ => True
  AS := fun _ => True
  AT := fun _ => True
  AH := fun _ => True
  P := fun φ _ => φ () false

/-- "the world is world 0". -/
def at0 : Unit → Bool → Prop := fun _ v => v = false
def at1 : Unit → Bool → Prop := fun _ v => v = true

theorem closed_fb : Closed fb :=
  Th4Route.closed_full _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)

theorem bin_fb : Ax1Bin fb := fun _ _ _ _ _ h1 h2 => ⟨h1, h2⟩

theorem ax2a_fb : Ax2a fb := fun φ _ _ =>
  ⟨(Classical.em (φ () false)).imp id id, fun ⟨a, b⟩ => b a⟩

theorem ax2b_fb : Ax2b fb := fun _ _ _ h _ _ => h

theorem ax4_fb : Ax4 fb := fun _ _ _ _ _ hφ hinc => hinc false rfl () trivial hφ

theorem ax3_fb : Ax3 fb := fun _ φ _ hess v hv => by
  subst hv; exact ⟨(), trivial, hess.1⟩

theorem not_ax3v3_fb : ¬ Ax3v3 fb := fun h => by
  have := h false at1 trivial (fun _ _ _ _ _ => ⟨fun e => by
      have := congrFun (congrFun e ()) true
      simp [at1, bot] at this, fun _ _ hv => by
      simp only [fb] at *; subst_vars; simp [at1] at hv⟩) false rfl
  obtain ⟨_, _, hv⟩ := this
  simp [at1] at hv

/-- The world-dependent collection `Φ(1) = {⊤, at₀}`, `Φ(0) = {⊥}`. -/
def Φ₀ : (Unit → Bool → Prop) → Bool → Prop := fun ψ v =>
  (v = true ∧ (ψ = top ∨ ψ = at0)) ∨ (v = false ∧ ψ = bot)

theorem top_ne_at0 : (top : Unit → Bool → Prop) ≠ at0 := fun e => by
  have := congrFun (congrFun e ()) true
  simp [top, at0] at this

theorem not_two_fb : ¬ Ax1GenTwo fb := fun h => by
  have := h Φ₀ bot trivial trivial true
    ⟨top, at0, trivial, trivial, Or.inl ⟨rfl, Or.inl rfl⟩, Or.inl ⟨rfl, Or.inr rfl⟩, top_ne_at0⟩
    (fun ψ _ hm => by
      rcases hm with ⟨-, rfl | rfl⟩ | ⟨h, -⟩
      · trivial
      · rfl
      · exact Bool.noConfusion h)
    (fun v hv z _ => by
      subst hv
      refine ⟨fun hb => hb.elim, fun hall => hall bot trivial (Or.inr ⟨rfl, rfl⟩)⟩)
  exact this

theorem not_gen_fb : ¬ Ax1Gen fb := fun h => not_two_fb (fun Φ φ hH hA w _ => h Φ φ hH hA w)

theorem not_G1 (x : Unit) : ¬ G fb x true := fun h => by
  have := h at0 trivial rfl
  simp [at0] at this

theorem not_exG1 : ¬ ExG fb true := fun ⟨x, _, hx⟩ => not_G1 x hx

theorem exG0 : ExG fb false := ⟨(), trivial, fun φ _ h => h⟩

theorem not_uf1 : ¬ UF fb true := fun ⟨_, _, up, _, _⟩ => by
  have := up top at1 trivial trivial trivial (fun _ _ _ => rfl)
  simp [fb, at1] at this

theorem not_princ1 : ¬ Princ fb true := fun ⟨g, _, hp⟩ => by
  have := (hp at0 trivial).1 rfl
  simp [at0] at this

theorem not_mc_fb : ¬ MC fb := fun h => by
  have := h (fun v => v = true) trivial true rfl false rfl
  exact Bool.noConfusion this

/-- **Finite binary separator** (variant 2). -/
theorem fb_sep :
    LGenF fb ∧ Closed fb ∧ Ax1Bin fb ∧ Ax2a fb ∧ Ax2b fb ∧ Ax3 fb ∧ Ax4 fb ∧
    ¬ Ax1GenTwo fb ∧ ¬ Ax1Gen fb ∧ ¬ Ax3v3 fb ∧ ¬ MC fb ∧
    ¬ ExG fb true ∧ ¬ UF fb true ∧ ¬ Princ fb true ∧ ExG fb false :=
  ⟨lgenF_full _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial), closed_fb, bin_fb,
    ax2a_fb, ax2b_fb, ax3_fb, ax4_fb, not_two_fb, not_gen_fb, not_ax3v3_fb, not_mc_fb,
    not_exG1, not_uf1, not_princ1, exG0⟩

end Programme.«20261022-0733-ontological».Run2.FiniteBinary

#print axioms Programme.«20261022-0733-ontological».Run2.FiniteBinary.fb_sep
