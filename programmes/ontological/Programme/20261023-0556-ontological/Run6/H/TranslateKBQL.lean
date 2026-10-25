import Lean
import OpenQuestions.Ax1GenTwoVariant2
import Programme.«20261023-0556-ontological».Run6.H.TranslateKBF4

/-! # Thread H (run 6, pr): frame hypotheses (C7) — `Ax1GenTwoVariant2` on symmetric frames

One self-contained file, as `TranslateTwo.lean`: the library's `WitnessDeep.lean` verbatim, then the
meta-program (namespace `Programme.H`), then translations of the module's KB theorems *with the
module's own proofs*: `Th3` (`◇∃ᴱG → □∃ᴱG`), `Th5_KB` (`□∃ᴱG`) and `MC_KB` (modal collapse), each
taking the frame hypothesis `symm : ∀ x y, x 𝗿 y → y 𝗿 x`.

**Frame hypotheses (th's C7).**  A statement hypothesis whose image is a closed frame formula
(`RelOnly`: `rel` between world variables, connectives, world quantifiers) is not read as an
`𝓛`-sentence of `T`; it stays in the derivation's hypothesis list, weakened into the world context.
For `#deep_translate X as N` the tool then adds `N.Fs` (the frame formulas), `N.Fs_ok : AllRel N.Fs`,
`N.deep : DW N.Tfull [.w] (N.Fs.map wk) (holds (emb nilR N.φ) var0)` and
`N.validF : ValidV4Fs N.Fs N.T N.φ`: `N.φ` holds at every world of every v4 `𝓛`-general model of
`N.T` with nonempty individuals whose frame satisfies every formula of `N.Fs` (`sound_v4_wt_frames`,
th's `sound_v4_wt_frame` for a list).

**Structural image check (th's C8).**  `N.struct<k> : type_of% @X = shV R existsAt P n N.ax<k> ()`
for each module axiom `X`, `N.struct_φ` for the statement, by `rfl` after δ-unfolding the module
side and at most the rewrites `↔` to two implications and `◇` to `¬□¬`; and
`N.of_struct : type_of% @Th3` (etc.) re-proved from `N.validF` through `of_validFs_full`, the
structural checks, and `frame_hold` (the module's `symm` gives `FrameHolds R F`). -/


-- [cleanup 2026-10-23] shared block (11220 lines) now imported from Programme.«20261023-0556-ontological».Run6.H.TranslateKBF4
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
open Programme.Run6.H Programme.H

#print axioms Programme.Run6.H.F4.not_validFs_F4
#print axioms Programme.Run6.H.F4.F4_Qt

/-! ## Q_L, part (ii): a closed uniform set violating `Q_L` refutes Th3 𝓛-generally (th's P125, ThH14)

Generic form of the F4 argument.  On any frame `R'` with a quasi-terminal `c` seen from `w`
together with some `u ≠ c`, the full model with one always-actual entity and `P φ := φ () c`
satisfies `Th3K.T` and refutes Th3 at `w` (ThH12b's model).  th's collapse map `col B` (ThH14,
copied with renamed namespace) is a surjective bounded morphism from `(W,R)` onto such a frame
whenever `B` is `R`-closed, uniform and violates `Q_L`; pulling the full model back along it gives
an 𝓛-general model on `(W,R)` itself refuting Th3. -/
namespace Programme.Run6.H.QL
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
open Programme.Run6.H.F4 (pull pullL)

section Gen
variable {V : Type} (R' : V → V → Prop) (c : V)

def act (_ : Unit) (_ : V) : Prop := True
def P (φ : Unit → V → Prop) : V → Prop := fun _ => φ () c
def box (φ : V → Prop) : V → Prop := fun w => ∀ v, R' w v → φ v
def dia (φ : V → Prop) : V → Prop := fun w => ∃ v, R' w v ∧ φ v
def exE (Φ : Unit → V → Prop) : V → Prop := fun w => ∃ x, act x w ∧ Φ x w
def allE (Φ : Unit → V → Prop) : V → Prop := fun w => ∀ x, act x w → Φ x w
def G (x : Unit) : V → Prop := fun w => ∀ φ : Unit → V → Prop, P c φ w → φ x w
def PInc (φ ψ : Unit → V → Prop) : V → Prop := box R' (allE fun y w => φ y w → ψ y w)
def Ess (φ : Unit → V → Prop) (x : Unit) : V → Prop :=
  fun w => φ x w ∧ ∀ ψ : Unit → V → Prop, ψ x w → PInc R' φ ψ w
def E (x : Unit) : V → Prop := fun w => ∀ φ : Unit → V → Prop, Ess R' φ x w → box R' (exE φ) w

theorem Ax2a (φ : Unit → V → Prop) (w : V) :
    (P c φ w ∨ P c (fun x v => ¬ φ x v) w) ∧ ¬ (P c φ w ∧ P c (fun x v => ¬ φ x v) w) := by
  unfold P; exact ⟨Classical.em _, fun ⟨a, b⟩ => b a⟩
theorem Ax2b (φ : Unit → V → Prop) (w : V) : P c φ w → box R' (P c φ) w := fun h _ _ => h
theorem Ax3 (qt : ∀ y, R' c y → y = c) (w : V) : P c (E R') w := by
  intro φ hφ v hv
  rw [qt v hv]; exact ⟨(), trivial, hφ.1⟩
theorem G_iff (w : V) : G c () w ↔ w = c :=
  ⟨fun h => h (fun _ v => v = c) rfl, fun h => by subst h; exact fun _ h => h⟩
theorem Th3_fails {w u : V} (hwc : R' w c) (hwu : R' w u) (huc : u ≠ c) :
    ¬ (dia R' (exE (G c)) w → box R' (exE (G c)) w) := fun h => by
  obtain ⟨_, _, hg⟩ := h ⟨c, hwc, (), trivial, (G_iff c c).2 rfl⟩ u hwu
  exact huc ((G_iff c u).1 hg)

theorem hT (qt : ∀ y, R' c y → y = c) :
    ∀ ψ, Th3K.T ψ → ∀ w, shR R' act (P c) ψ () w := by
  intro ψ hψ w
  have h' : ψ ∈ [Th3K.ax0, Th3K.ax1, Th3K.ax2] := hψ
  rcases List.mem_cons.1 h' with rfl | h'
  · exact Ax3 R' c qt w
  rcases List.mem_cons.1 h' with rfl | h'
  · intro φ; exact Ax2b R' c φ w
  rcases List.mem_cons.1 h' with rfl | h'
  · intro φ; exact Ax2a c φ w
  cases h'
end Gen

/-! th's collapse map (ThH14). -/
section Col
variable {W : Type} (R : W → W → Prop) (B : W → Prop)

open Classical in
noncomputable def col (x : W) : {x // ¬ B x} ⊕ Unit :=
  if h : B x then .inr () else .inl ⟨x, h⟩

def RC (a b : {x // ¬ B x} ⊕ Unit) : Prop := ∃ x y, col B x = a ∧ col B y = b ∧ R x y

variable {B}
theorem col_in {x : W} (h : B x) : col B x = .inr () := by simp [col, h]
theorem col_out {x : W} (h : ¬ B x) : col B x = .inl ⟨x, h⟩ := by simp [col, h]
theorem in_of_col {x : W} (h : col B x = .inr ()) : B x := by
  by_cases hx : B x
  · exact hx
  · rw [col_out hx] at h; cases h
theorem eq_of_col {x y : W} (hy : ¬ B y) (h : col B x = col B y) : x = y := by
  by_cases hx : B x
  · rw [col_in hx, col_out hy] at h; cases h
  · rw [col_out hx, col_out hy] at h; cases h; rfl

theorem col_surj (hb : ∃ b, B b) : Function.Surjective (col B) := by
  intro a
  match a with
  | .inr () => obtain ⟨b, hb⟩ := hb; exact ⟨b, col_in hb⟩
  | .inl ⟨x, hx⟩ => exact ⟨x, col_out hx⟩

theorem col_forth : ∀ w v, R w v → RC R B (col B w) (col B v) := fun w v h => ⟨w, v, rfl, rfl, h⟩

theorem col_back (closed : ∀ x y, B x → R x y → B y)
    (unif : (∀ x, B x → ∃ y, R x y) ∨ (∀ x y, B x → ¬ R x y)) :
    ∀ w v', RC R B (col B w) v' → ∃ v, R w v ∧ col B v = v' := by
  rintro w v' ⟨x, y, hx, rfl, hxy⟩
  by_cases hw : B w
  · rw [col_in hw] at hx
    have hxB := in_of_col hx
    have hyB := closed x y hxB hxy
    rcases unif with s | d
    · obtain ⟨v, hv⟩ := s w hw
      exact ⟨v, hv, by rw [col_in (closed w v hw hv), col_in hyB]⟩
    · exact absurd hxy (d x y hxB)
  · exact ⟨y, by rw [← eq_of_col hw hx]; exact hxy, rfl⟩

theorem pt_qt (closed : ∀ x y, B x → R x y → B y) :
    ∀ y, RC R B (.inr ()) y → y = .inr () := by
  rintro _ ⟨x, y, hx, rfl, hxy⟩
  exact col_in (closed x y (in_of_col hx) hxy)
end Col

/-- 𝓛-general validity of `φ` from `T` on the frame `(W,R)` (th's `ThH13.ValidOn`). -/
def ValidOn {W : Type} (R : W → W → Prop) (T : Tm [] .s → Prop) (φ : Tm [] .s) : Prop :=
  ∀ (M : VM W) (L : LGen M), M.R = R → Nonempty (M.C .e) →
    (∀ ψ, T ψ → ∀ w, M.pr (L.ev ψ ()) w) → ∀ w, M.pr (L.ev φ ()) w

/-- **Q_L (ii).** On any frame `(W,R)` with an `R`-closed uniform set `B` and worlds `w`, `b ∈ B`,
`u ∉ B` with `R w b` and `R w u` (failure of `Q_L`), Th3 is not valid in all v4 𝓛-general models
of K7's `Th3K.T` (Ax3, Ax2b, Ax2a) on `(W,R)` with nonempty individuals. -/
theorem not_validOn {W : Type} (R : W → W → Prop) (B : W → Prop)
    (closed : ∀ x y, B x → R x y → B y)
    (unif : (∀ x, B x → ∃ y, R x y) ∨ (∀ x y, B x → ¬ R x y))
    {w b u : W} (hb : B b) (hu : ¬ B u) (hwb : R w b) (hwu : R w u) :
    ¬ ValidOn R Th3K.T Th3K.φ := by
  intro h
  let R' := RC R B
  let c : {x // ¬ B x} ⊕ Unit := .inr ()
  have qt : ∀ y, R' c y → y = c := pt_qt R closed
  have hC : Closed (fullStr R' act (P c)) := (full_closed_resp R' act (P c)).1
  have hR : Resp (fullStr R' act (P c)) := (full_closed_resp R' act (P c)).2.1
  have hE : ∀ x, (fullStr R' act (P c)).A .e x := fun _ => trivial
  let M := ofStr (fullStr R' act (P c)) hC hR
  let L := ofStr_lgen (fullStr R' act (P c)) hC hR hE
  have hs := col_surj (B := B) ⟨b, hb⟩
  have hne : Nonempty ((pull M (col B) hs R).C .e) := ⟨Quotient.mk (setoidT _ .e) ⟨(), hE ()⟩⟩
  have hT3 : ∀ ψ, Th3K.T ψ → ∀ v, M.pr (L.ev ψ ()) v := fun ψ hψ v =>
    (ofStr_truth _ hC hR hE ψ v).2 (by rw [eval_full_eq]; exact hT R' c qt ψ hψ v)
  have h4 := h (pull M (col B) hs R) (pullL M L (col B) hs R (col_forth R) (col_back R closed unif))
    rfl hne (fun ψ hψ v => hT3 ψ hψ (col B v)) w
  have h3 : shR R' act (P c) Th3K.φ () (col B w) := by
    have := (ofStr_truth _ hC hR hE Th3K.φ (col B w)).1 h4
    rwa [eval_full_eq] at this
  apply Th3_fails R' c (w := col B w) (u := col B u) ⟨w, b, rfl, col_in hb, hwb⟩
    (col_forth R w u hwu) (fun h => hu (in_of_col h))
  intro hd
  refine h3 (fun hn => ?_)
  obtain ⟨v, hv, x, hx, hg⟩ := hd
  exact hn v hv ⟨x, hx, fun φ hp => hg φ hp⟩

/-- `ValidV4Fs` form: for every list `Fs` of frame formulas true on such a frame. -/
theorem not_validFs {W : Type} (R : W → W → Prop) (B : W → Prop)
    (closed : ∀ x y, B x → R x y → B y)
    (unif : (∀ x, B x → ∃ y, R x y) ∨ (∀ x y, B x → ¬ R x y))
    {w b u : W} (hb : B b) (hu : ¬ B u) (hwb : R w b) (hwu : R w u)
    (Fs : List (HTerm [] .o)) (hF : FramesHold R Fs) :
    ¬ ValidV4Fs Fs Th3K.T Th3K.φ := fun h =>
  not_validOn R B closed unif hb hu hwb hwu (fun M L hR hne hT => by
    subst hR; exact h W M L hne hF hT)

end Programme.Run6.H.QL
#print axioms Programme.Run6.H.QL.not_validOn
#print axioms Programme.Run6.H.QL.not_validFs
