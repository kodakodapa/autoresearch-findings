import Programme.«20261021-1639-ontological».Theorist.ScottDeep
import Programme.«20261021-1639-ontological».Theorist.HenkinVariant2

/-! D16: Goedel variant 2 (world-dependent Ax1Gen) in plain deep Henkin semantics (K36 closed
models), no interface hypothesis.
* `tAx1Gen a` quantifies over the carrier at type `(e → o) → o`; `tAx2a`; Ax2b is `tA4`.
* `bridge_Ax1Gen`: for any presentation, deep Ax1Gen ↔ GModel `Ax1Gen` with `admH m` (the truth
  images of higher carrier elements, on admitted properties).
* `cloV2_of_presents`: every `CloV2` member is the denotation of a closed definable term.
* `deep_v2`: deep Ax1Gen + Ax2a ⇒ deep `∀p. □p → p` and deep `□ ∃^a x. G x`;
  `deep_v2_mc`: + Ax2b (= tA4) ⇒ deep modal collapse, on every frame. -/

namespace Programme.«20261021-1639-ontological».Theorist.V2Deep
open Programme.«20261021-1639-ontological».Deep Programme.«20261021-1639-ontological».Deep.Henkin Programme.«20261021-1639-ontological».Theorist.HenkinScott
open Programme.«20261021-1639-ontological».Theorist.SymmetricModels Programme.«20261021-1639-ontological».Theorist.ScottBridge
open Programme.«20261021-1639-ontological».Theorist.ScottDeep

abbrev HP := Ty.arr Property .prop

variable {W : Type} {m : Henkin.Model OntConst W}

/-- Inversion for primitive equality. -/
def InvEq (m : Henkin.Model OntConst W) {Γ} (ρ : Assignment m.frame Γ) :
    {a : Ty} → Term OntConst Γ a → m.frame.D a → Prop
  | _, .equal s t, r => m.frame.truth r = fun _ =>
      translate m.frame m.interp s ρ = translate m.frame m.interp t ρ
  | _, _, _ => True

theorem invEq {ρ : Assignment m.frame Γ} {t : Term OntConst Γ a} {r}
    (d : Denotes m.frame m.interp @ρ t r) : InvEq m ρ t r := by
  induction d with
  | equal ds dt hr => simp only [InvEq, agreement ds, agreement dt]; exact hr
  | _ => trivial

theorem sem_equal (ρ : Assignment m.frame Γ) (s t : T Γ a) (w : W) :
    sem m ρ (.equal s t) w ↔ translate m.frame m.interp s ρ = translate m.frame m.interp t ρ :=
  Iff.of_eq (congrFun (invEq (translate_denotes m ρ (.equal s t))) w)

def v3 : T (d :: c :: b :: a :: Γ) a := .var (.there (.there (.there .here)))
@[simp] theorem tr_v3 (ρ : Assignment m.frame Γ) (x : m.frame.D a) (y : m.frame.D b)
    (z : m.frame.D c) (u : m.frame.D d) :
    translate m.frame m.interp (v3 : T (d :: c :: b :: a :: Γ) a)
      (push (push (push (push ρ x) y) z) u) = x := rfl

def iff' (s t : T Γ .prop) : T Γ .prop := conj (.imp s t) (.imp t s)
def disj (s t : T Γ .prop) : T Γ .prop := .imp (neg s) t

theorem sem_iff (ρ : Assignment m.frame Γ) (s t : T Γ .prop) (w : W) :
    sem m ρ (iff' s t) w ↔ (sem m ρ s w ↔ sem m ρ t w) := by
  simp only [iff', sem_conj, sem_imp]; exact ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

theorem sem_disj (ρ : Assignment m.frame Γ) (s t : T Γ .prop) (w : W) :
    sem m ρ (disj s t) w ↔ (sem m ρ s w ∨ sem m ρ t w) := by
  simp only [disj, sem_imp, sem_neg]
  exact ⟨fun h => (Classical.em _).elim Or.inl fun hn => Or.inr (h hn),
    fun h hn => h.resolve_left hn⟩

/-! ### Variant-2 axioms as deep terms. -/

/-- Ax1Gen: `∀S P. (∀Q. S Q → 𝒫 Q) → □(∀ᵍx. P x ↔ ∀Q. S Q → Q x) → 𝒫 P`. -/
def tAx1Gen (a : Bool) : T [] .prop :=
  .all (a := HP) (.all (a := Property) (.imp
    (.all (a := Property) (.imp (.app v2 v0) (pos v0)))
    (.imp (.box (.all (a := .entity) (gimp a v0 (iff' (.app v1 v0)
        (.all (a := Property) (.imp (.app v3 v0) (.app v0 v1))))))) (pos v0))))
/-- Ax2a: `∀P. (𝒫 P ∨ 𝒫 ¬P) ∧ ¬(𝒫 P ∧ 𝒫 ¬P)`. -/
def tAx2a : T [] .prop :=
  .all (a := Property) (conj (disj (pos v0) (pos (.lam (neg (.app v1 v0)))))
    (neg (conj (pos v0) (pos (.lam (neg (.app v1 v0)))))))
/-- T schema `∀p. □p → p`. -/
def tT : T [] .prop := .all (.imp (.box (v0 : T [.prop] .prop)) v0)
/-- God-like, in any context. -/
def tGg : T Γ Property := .lam (.all (.imp (pos v0) (.app v0 v1)))
/-- Necessary guarded existence of a God-like being `□ ∃ᵍx. G x`. -/
def tNecEx (a : Bool) : T [] .prop :=
  .box (neg (.all (a := .entity) (gimp a v0 (neg (.app tGg v0)))))

/-- Higher carrier truth images, read on admitted properties. -/
def admH (m : Henkin.Model OntConst W) :
    ((m.frame.D .entity → W → Prop) → W → Prop) → Prop :=
  fun s => ∃ S : m.frame.D HP, ∀ Q w, s (img m Q) w ↔ m.frame.truth (m.frame.app S Q) w

variable {gm : GModel W (m.frame.D .entity)}

theorem adm_iff (hp : Presents m gm) (f) : gm.adm f ↔ ∃ P, img m P = f := (hp.2.1 f).symm

theorem bridge_Ax1Gen (hp : Presents m gm) (a : Bool) (ρ : Assignment m.frame []) :
    DeepValid m ρ (tAx1Gen a) ↔ HenkinVariant2.Ax1Gen gm a (admH m) := by
  rw [deepValid_iff]
  simp only [tAx1Gen, sem_all, sem_imp, sem_box, sem_pos hp, sem_gimp hp, sem_iff, sem_app,
    tr_v0, tr_v1, tr_v2, tr_v3]
  constructor
  · intro h s p w ⟨S, hS⟩ hpa hpos hconj
    obtain ⟨P, rfl⟩ := (adm_iff hp p).1 hpa
    refine h w S P (fun Q hQ => hpos _ ((adm_iff hp _).2 ⟨Q, rfl⟩) ((hS Q w).2 hQ)) ?_
    intro v hv x hx
    refine (hconj v ((hp.2.2.1 w v).1 hv) x hx).trans ?_
    constructor
    · intro hq Q hSQ; exact hq _ ((adm_iff hp _).2 ⟨Q, rfl⟩) ((hS Q v).2 hSQ)
    · intro hq q hqa hsq
      obtain ⟨Q, rfl⟩ := (adm_iff hp q).1 hqa
      exact hq Q ((hS Q v).1 hsq)
  · intro h w S P hpos hbox
    let s : (m.frame.D .entity → W → Prop) → W → Prop :=
      fun q v => ∃ Q, img m Q = q ∧ m.frame.truth (m.frame.app S Q) v
    have hs : ∀ Q v, s (img m Q) v ↔ m.frame.truth (m.frame.app S Q) v := fun Q v =>
      ⟨fun ⟨Q', hQ', h'⟩ => img_inj m Q' Q hQ' ▸ h', fun h' => ⟨Q, rfl, h'⟩⟩
    refine h s (img m P) w ⟨S, hs⟩ ((adm_iff hp _).2 ⟨P, rfl⟩) ?_ ?_
    · intro q hqa hsq
      obtain ⟨Q, rfl⟩ := (adm_iff hp q).1 hqa
      exact hpos Q ((hs Q w).1 hsq)
    · intro v hv x hx
      rw [show img m P x v = m.frame.truth (m.frame.app P x) v from rfl,
        hbox v ((hp.2.2.1 w v).2 hv) x hx]
      constructor
      · intro hq q hqa hsq
        obtain ⟨Q, rfl⟩ := (adm_iff hp q).1 hqa
        exact hq Q ((hs Q v).1 hsq)
      · intro hq Q hSQ; exact hq _ ((adm_iff hp _).2 ⟨Q, rfl⟩) ((hs Q v).2 hSQ)

theorem bridge_Ax2a (hp : Presents m gm) (ρ : Assignment m.frame []) :
    DeepValid m ρ tAx2a ↔ HenkinVariant2.Ax2a gm := by
  rw [deepValid_iff]
  simp only [tAx2a, sem_all, sem_conj, sem_disj, sem_neg, sem_pos hp, img_lam, sem_app,
    tr_v0, tr_v1]
  constructor
  · intro h p w hpa
    obtain ⟨P, rfl⟩ := (adm_iff hp p).1 hpa
    exact h w P
  · intro h w P
    exact h _ w ((adm_iff hp _).2 ⟨P, rfl⟩)

theorem bridge_T (hp : Presents m gm) (ρ : Assignment m.frame []) :
    DeepValid m ρ tT ↔ ∀ c, gm.admP c → ∀ w, (∀ v, gm.rel w v → c v) → c w := by
  rw [deepValid_iff]
  simp only [tT, sem_all, sem_imp, sem_box]
  constructor
  · intro h c hca w hb
    obtain ⟨q, rfl⟩ := (hp.1 c).2 hca
    exact h w q fun v hv => hb v ((hp.2.2.1 w v).1 hv)
  · intro h w q hb
    exact h _ ((hp.1 _).1 ⟨q, rfl⟩) w fun v hv => hb v ((hp.2.2.1 w v).2 hv)

theorem img_Gg (hp : Presents m gm) (ρ : Assignment m.frame Γ) :
    (fun x => m.frame.truth (m.frame.app (translate m.frame m.interp (tGg : T Γ Property) ρ) x))
      = GH gm := by
  rw [tGg, img_lam]
  funext x w
  simp only [sem_all, sem_imp, sem_pos hp, sem_app, tr_v0, tr_v1]
  apply propext
  constructor
  · intro h p ha hpw
    obtain ⟨P, rfl⟩ := (hp.2.1 p).2 ha
    exact h P hpw
  · intro h P hpw
    exact h _ ((hp.2.1 _).1 ⟨P, rfl⟩) hpw

theorem bridge_NecEx (hp : Presents m gm) (a : Bool) (ρ : Assignment m.frame []) :
    DeepValid m ρ (tNecEx a) ↔ ∀ w v, gm.rel w v → ∃ x, guard gm a x v ∧ GH gm x v := by
  rw [deepValid_iff]
  simp only [tNecEx, sem_box, sem_neg, sem_all, sem_gimp hp, sem_app, tr_v0]
  have hG := fun (x : m.frame.D .entity) (v : W) =>
    congrFun (congrFun (img_Gg hp (Γ := [.entity]) (push ρ x)) x) v
  simp only [hG]
  constructor
  · intro h w v hv
    exact Classical.byContradiction fun hn =>
      h w v ((hp.2.2.1 w v).2 hv) fun x hx hg => hn ⟨x, hx, hg⟩
  · intro h w v hv hn
    obtain ⟨x, hx, hg⟩ := h w v ((hp.2.2.1 w v).1 hv)
    exact hn x hx hg

/-! ### Every CloV2 member is definable. -/

theorem img_bot (ρ : Assignment m.frame Γ) :
    img m (translate m.frame m.interp (.lam .falsum : T Γ Property) ρ) = HenkinVariant2.botP := by
  unfold img; rw [img_lam]; funext x w; exact propext (sem_falsum _ w)

theorem cloV2_of_presents (hp : Presents m gm) (a : Bool) (ρ : Assignment m.frame []) :
    HenkinVariant2.CloV2 gm a (admH m) := by
  have adm_img : ∀ P, gm.adm (img m P) := fun P => (adm_iff hp _).2 ⟨P, rfl⟩
  refine ⟨?_, fun p ha => ?_, (hp.2.1 _).1 ⟨_, img_G hp ρ⟩, fun c ha => ?_, ?_,
    fun φ ha => ?_, ?_, fun φ ha => ?_⟩
  · rw [← img_bot ρ]; exact adm_img _
  · obtain ⟨P, rfl⟩ := (hp.2.1 p).2 ha
    refine (hp.2.1 _).1 ⟨translate m.frame m.interp
      (.lam (neg (.app v1 v0)) : T [Property] Property) (push ρ P), ?_⟩
    rw [img_lam]; funext x w
    simp only [sem_neg, sem_app, tr_v0, tr_v1]; rfl
  · obtain ⟨q, rfl⟩ := (hp.1 c).2 ha
    exact (hp.2.1 _).1 ⟨translate m.frame m.interp
      (.lam v1 : T [.prop] Property) (push ρ q), by rw [img_lam]; rfl⟩
  · refine ⟨translate m.frame m.interp (.lam .falsum : T [] HP) ρ, fun Q w => ?_⟩
    rw [tr_lam]; exact (sem_falsum _ w).symm
  · obtain ⟨P, rfl⟩ := (adm_iff hp φ).1 ha
    refine ⟨translate m.frame m.interp (.lam (.equal v0 v1) : T [Property] HP) (push ρ P),
      fun Q w => ?_⟩
    rw [tr_lam]
    show _ ↔ sem m _ _ w
    rw [sem_equal]
    exact ⟨fun h => img_inj m _ _ h, fun h => congrArg (img m) h⟩
  · refine ⟨m.interp OntConst.positive, fun Q w => (hp.2.2.2.2 Q w).symm⟩
  · obtain ⟨P, rfl⟩ := (adm_iff hp φ).1 ha
    let body : T [Property, Property] .prop :=
      disj (.equal v0 v1) (conj (neg (.all (a := .entity) (gimp a v0 (neg (.app v2 v0)))))
        (.equal v0 (.lam .falsum)))
    refine ⟨translate m.frame m.interp (.lam body : T [Property] HP) (push ρ P),
      fun Q w => ?_⟩
    rw [tr_lam]
    show _ ↔ sem m _ body w
    simp only [body, sem_disj, sem_conj, sem_equal, sem_neg, sem_all, sem_gimp hp, sem_app,
      tr_v0, tr_v1, tr_v2]
    have hb : img m Q = HenkinVariant2.botP ↔
        Q = translate m.frame m.interp (.lam .falsum : T [Property, Property] Property)
          (push (push ρ P) Q) := by
      rw [← img_bot (push (push ρ P) Q)]
      exact ⟨fun h => img_inj m _ _ h, fun h => congrArg (img m) h⟩
    have he : (∃ y, guard gm a y w ∧ img m P y w) ↔
        ¬ ∀ y, guard gm a y w → ¬ m.frame.truth (m.frame.app P y) w :=
      ⟨fun ⟨y, hy, h⟩ hn => hn y hy h,
        fun hn => Classical.byContradiction fun h' => hn fun y hy hpy => h' ⟨y, hy, hpy⟩⟩
    rw [hb, he]
    exact or_congr ⟨fun h => img_inj m _ _ h, fun h => congrArg (img m) h⟩ Iff.rfl

/-! ### D16: variant 2 in deep Henkin semantics. -/

theorem deep_v2 (a : Bool) (ρ : Assignment m.frame [])
    (h1 : DeepValid m ρ (tAx1Gen a)) (h2 : DeepValid m ρ tAx2a) :
    DeepValid m ρ tT ∧ DeepValid m ρ (tNecEx a) := by
  have hp := canon_presents m
  have hc := cloV2_of_presents hp a ρ
  have g1 := (bridge_Ax1Gen hp a ρ).1 h1
  have g2 := (bridge_Ax2a hp ρ).1 h2
  refine ⟨(bridge_T hp ρ).2 fun c hca w hb => HenkinVariant2.T_adm hc g1 g2 c hca w hb,
    (bridge_NecEx hp a ρ).2 fun _ v _ => HenkinVariant2.god_everywhere_H hc g1 g2 v⟩

theorem deep_v2_mc (a : Bool) (ρ : Assignment m.frame [])
    (h1 : DeepValid m ρ (tAx1Gen a)) (h2 : DeepValid m ρ tAx2a) (h2b : DeepValid m ρ tA4) :
    DeepValid m ρ tMC := by
  have hp := canon_presents m
  exact (bridge_MC hp ρ).2 (HenkinVariant2.mc_of_ax2b_H (cloV2_of_presents hp a ρ)
    ((bridge_Ax1Gen hp a ρ).1 h1) ((bridge_Ax2a hp ρ).1 h2) ((bridge_A4 hp ρ).1 h2b))

/-! ### Deep variant-2 witnesses (closed models). -/
section witnesses
open Programme.«20261021-1639-ontological».Theorist.SymmetricFinite Programme.«20261021-1639-ontological».Theorist.HenkinMinimal

theorem ax1Gen_mono {E : Type} {g : GModel W E} {a : Bool} {S S' : ((E → W → Prop) → W → Prop) → Prop}
    (hS : ∀ s, S' s → S s) (h : HenkinVariant2.Ax1Gen g a S) : HenkinVariant2.Ax1Gen g a S' :=
  fun s p w hs => h s p w (hS s hs)

theorem swap_admH (s) (h : admH swapModel s) : HenkinVariant2.swapS s := by
  obtain ⟨S, hS⟩ := h
  intro q hq
  obtain ⟨Q, rfl⟩ := (swap_presentation.2.1 q).2 hq
  refine (hS Q true).trans (Iff.trans ?_ (hS Q false).symm)
  obtain ⟨n, hn⟩ := (S.1 Q).2
  exact Iff.of_eq (hn true trivial false)

/-- Swap: a closed model on an irreflexive symmetric two-world frame validating deep Ax1Gen,
Ax2a, Ax2b (`tA4`), Ax3 (`tA5`), hence deep T and deep modal collapse. -/
theorem deep_swap (a : Bool) (ρ : Assignment swapModel.frame []) :
    (∀ w, ¬ swapModel.frame.rel w w) ∧ (∀ w v, swapModel.frame.rel w v → swapModel.frame.rel v w) ∧
    DeepValid swapModel ρ (tAx1Gen a) ∧ DeepValid swapModel ρ tAx2a ∧
    DeepValid swapModel ρ tA4 ∧ DeepValid swapModel ρ (tA5 a) ∧
    DeepValid swapModel ρ tT ∧ DeepValid swapModel ρ tMC := by
  obtain ⟨hp, -, -, h1, h2, h2b, h3, -, -, sy, irr, mc⟩ := closed_swap a
  have d1 := (bridge_Ax1Gen hp a ρ).2 (ax1Gen_mono swap_admH h1)
  have d2 := (bridge_Ax2a hp ρ).2 h2
  exact ⟨fun w h => irr w ((hp.2.2.1 w w).1 h),
    fun w v h => (hp.2.2.1 v w).2 (sy w v ((hp.2.2.1 w v).1 h)), d1, d2,
    (bridge_A4 hp ρ).2 h2b, (bridge_A5 hp a ρ).2 h3, (deep_v2 a ρ d1 d2).1, (bridge_MC hp ρ).2 mc⟩

/-- Current-world Cantor: a closed S5 model validating deep Ax1Gen, Ax2a and Ax3 (`tA5`), hence
deep T and necessary existence, but not Ax2b (`tA4`) and not deep modal collapse. -/
theorem deep_cw (a : Bool) (ρ : Assignment cantorCWModel.frame []) :
    (∀ w v, cantorCWModel.frame.rel w v) ∧
    DeepValid cantorCWModel ρ (tAx1Gen a) ∧ DeepValid cantorCWModel ρ tAx2a ∧
    DeepValid cantorCWModel ρ (tA5 a) ∧ DeepValid cantorCWModel ρ (tNecEx a) ∧
    ¬ DeepValid cantorCWModel ρ tA4 ∧ ¬ DeepValid cantorCWModel ρ tMC := by
  have hp := cantorCW_presentation
  obtain ⟨-, h1, h2, h3, -, -, univ, -, n2b, nmc⟩ := HenkinVariant2.cw_props a
  have d1 := (bridge_Ax1Gen hp a ρ).2 (ax1Gen_mono (fun _ _ => trivial) h1)
  have d2 := (bridge_Ax2a hp ρ).2 h2
  exact ⟨fun w v => (hp.2.2.1 w v).2 (univ w v), d1, d2, (bridge_A5 hp a ρ).2 h3,
    (deep_v2 a ρ d1 d2).2, fun h => n2b ((bridge_A4 hp ρ).1 h), fun h => nmc ((bridge_MC hp ρ).1 h)⟩

end witnesses

#print axioms deep_swap
#print axioms deep_cw
#print axioms sem_equal
#print axioms bridge_Ax1Gen
#print axioms bridge_Ax2a
#print axioms bridge_T
#print axioms bridge_NecEx
#print axioms cloV2_of_presents
#print axioms deep_v2
#print axioms deep_v2_mc
end Programme.«20261021-1639-ontological».Theorist.V2Deep
