import Programme.«20261022-0733-ontological».Run2.FM
import Programme.«20261022-0733-ontological».Run2.Separating

/-! # Fact (a) of arXiv 2609.36279 v4 `ex:separating`, for the fragment `Frag` of `𝓛`

v4 `ex:separating` asserts (fact (a), proved on paper) that the hereditarily finitely supported
objects for the flip group on `W = 2^ℕ` are closed under every `𝓛`-term.  Here the same is proved
in Lean for `LGeneral.Tm`: every model on `2^ℕ` with one individual, the carriers of `FM.fm`
(finitely based propositions and properties, `FMH` collections) and accessibility, actuality and
positivity fixed by some `G_m`, is `LGeneral` (`lgeneral_of_sym`).

Proof: flips act on every type (`actTy`), denotation commutes with the action of every symmetry
of the model (`eval_act`, induction on terms; the quantifier cases use that each carrier is closed
under every flip), and at each type admission is exactly "fixed by some `G_n`" (`adm_iff_fix`).
An admitted environment is fixed by some `G_n`, so its denotations are fixed by `G_{max n m}`.

Consequences: `fm` (K8, K10, K13), `gfm` (K9) and sk's identity-frame model `fmId` are `LGeneral`,
so the K8, K9, K10, K13 separations hold in models closed under the fragment. -/
namespace Programme.«20261022-0733-ontological».Run2.FMGeneral

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.DropDagger Programme.«20261022-0733-ontological».Run2.OneHF
  Programme.«20261022-0733-ontological».Run2.BoxIdle Programme.«20261022-0733-ontological».Run2.UniqueEss Programme.«20261022-0733-ontological».Run2.RigidFree Programme.«20261022-0733-ontological».Run2.FM
open Programme.«20261022-0733-ontological».Run2.LGeneral

/-- A model with the carriers of `fm`. -/
def mk (R : Cw → Cw → Prop) (ac : Unit → Cw → Prop) (P : (Unit → Cw → Prop) → Cw → Prop) :
    Model Cw Unit where
  R := R
  act := ac
  AS := Based
  AT := fun φ => Based (φ ())
  AH := FMH
  P := P

/-! ## The action of flips -/

theorem xorw_comm (w d e : Cw) : xorw (xorw w d) e = xorw (xorw w e) d := by
  funext i; simp only [xorw]; cases w i <;> cases d i <;> cases e i <;> rfl

theorem act_comm (d e : Cw) (ψ : Unit → Cw → Prop) : act d (act e ψ) = act e (act d ψ) := by
  funext x v; simp only [act, xorw_comm]

def actH (d : Cw) (Φ : (Unit → Cw → Prop) → Cw → Prop) : (Unit → Cw → Prop) → Cw → Prop :=
  fun ψ w => Φ (act d ψ) (xorw w d)

def actTy (d : Cw) : (t : Ty) → Den Cw Unit t → Den Cw Unit t
  | .e, x => x
  | .s, q => fun w => q (xorw w d)
  | .p, φ => act d φ
  | .h, Φ => actH d Φ

theorem actTy_invol (d : Cw) : (t : Ty) → (x : Den Cw Unit t) → actTy d t (actTy d t x) = x
  | .e, _ => rfl
  | .s, q => by funext w; simp [actTy, xorw_xorw]
  | .p, φ => act_act d φ
  | .h, Φ => by funext ψ w; simp [actTy, actH, act_act, xorw_xorw]

def actEnv (d : Cw) : (Γ : List Ty) → Env Cw Unit Γ → Env Cw Unit Γ
  | [], ρ => ρ
  | t :: Γ, ρ => (actTy d t ρ.1, actEnv d Γ ρ.2)

/-- Environment extension. -/
def ec {t : Ty} {Γ : List Ty} (x : Den Cw Unit t) (ρ : Env Cw Unit Γ) : Env Cw Unit (t :: Γ) :=
  (x, ρ)

theorem get_act (d : Cw) : {Γ : List Ty} → {t : Ty} → (i : Var Γ t) → (ρ : Env Cw Unit Γ) →
    i.get (actEnv d Γ ρ) = actTy d t (i.get ρ)
  | _, _, .zero, _ => rfl
  | _, _, .succ i, ρ => get_act d i ρ.2

/-- Every carrier is closed under every flip. -/
theorem adm_act (R ac P) (d : Cw) :
    (t : Ty) → (x : Den Cw Unit t) → Adm (mk R ac P) t x → Adm (mk R ac P) t (actTy d t x)
  | .e, _, _ => trivial
  | .s, _, h => by
      obtain ⟨n, hn⟩ := h
      exact ⟨n, fun w v hwv => hn _ _ fun i hi => by simp [xorw, hwv i hi]⟩
  | .p, _, h => act_based h d
  | .h, Φ, h => by
      obtain ⟨n, hn⟩ := h
      refine ⟨n, fun e he ψ w => ?_⟩
      show Φ (act d ψ) (xorw w d) ↔ Φ (act d (act e ψ)) (xorw (xorw w e) d)
      rw [act_comm, xorw_comm]
      exact hn e he _ _

theorem adm_act_iff (R ac P) (d : Cw) (t : Ty) (x : Den Cw Unit t) :
    Adm (mk R ac P) t (actTy d t x) ↔ Adm (mk R ac P) t x :=
  ⟨fun h => by have := adm_act R ac P d t _ h; rwa [actTy_invol] at this,
   adm_act R ac P d t x⟩

/-- `d` is a symmetry of accessibility, actuality and positivity. -/
structure Sym (R : Cw → Cw → Prop) (ac : Unit → Cw → Prop) (P : (Unit → Cw → Prop) → Cw → Prop)
    (d : Cw) : Prop where
  R : ∀ w v, R (xorw w d) (xorw v d) ↔ R w v
  ac : ∀ y w, ac y (xorw w d) ↔ ac y w
  P : actH d P = P

/-- **Equivariance.** Denotation commutes with the action of every symmetry of the model. -/
theorem eval_act {R ac P} {d : Cw} (hs : Sym R ac P d) :
    {Γ : List Ty} → {t : Ty} → (tm : Tm Γ t) → (ρ : Env Cw Unit Γ) →
      eval (mk R ac P) tm (actEnv d Γ ρ) = actTy d t (eval (mk R ac P) tm ρ)
  | _, _, .var i, ρ => get_act d i ρ
  | _, _, .appP f a, ρ => by
      show eval _ f (actEnv d _ ρ) (eval _ a (actEnv d _ ρ)) = _
      rw [eval_act hs f, eval_act hs a]; rfl
  | _, _, .appH F f, ρ => by
      show eval _ F (actEnv d _ ρ) (eval _ f (actEnv d _ ρ)) = _
      rw [eval_act hs F, eval_act hs f]
      funext w; show eval _ F ρ (act d (act d (eval _ f ρ))) (xorw w d) = _
      rw [act_act]; rfl
  | _, _, .lamP b, ρ => by
      funext x w; cases x
      exact congrFun (eval_act hs b (ec () ρ)) w
  | _, _, .lamH b, ρ => by
      funext ψ w
      have h := congrFun (eval_act hs b (ec (act d ψ) ρ)) w
      rw [show actEnv d (.p :: _) (ec (act d ψ) ρ) = ec ψ (actEnv d _ ρ) from by
        show (act d (act d ψ), _) = (ψ, _); rw [act_act]; rfl] at h
      exact h
  | _, _, .top, _ => rfl
  | _, _, .bot, _ => rfl
  | _, _, .neg a, ρ => by
      funext w; show (¬ eval _ a (actEnv d _ ρ) w) = _; rw [eval_act hs a]; rfl
  | _, _, .and a b, ρ => by
      funext w; show (eval _ a (actEnv d _ ρ) w ∧ eval _ b (actEnv d _ ρ) w) = _
      rw [eval_act hs a, eval_act hs b]; rfl
  | _, _, .or a b, ρ => by
      funext w; show (eval _ a (actEnv d _ ρ) w ∨ eval _ b (actEnv d _ ρ) w) = _
      rw [eval_act hs a, eval_act hs b]; rfl
  | _, _, .imp a b, ρ => by
      funext w; show (eval _ a (actEnv d _ ρ) w → eval _ b (actEnv d _ ρ) w) = _
      rw [eval_act hs a, eval_act hs b]; rfl
  | _, _, .box a, ρ => by
      funext w
      show (∀ v, R w v → eval _ a (actEnv d _ ρ) v) = (∀ v, R (xorw w d) v → eval _ a ρ v)
      rw [eval_act hs a]
      apply propext; constructor
      · intro h v hv
        have := h (xorw v d) (by rw [← hs.R, xorw_xorw]; exact hv)
        rwa [show actTy d .s (eval _ a ρ) (xorw v d) = eval _ a ρ v from by
          show eval _ a ρ (xorw (xorw v d) d) = _; rw [xorw_xorw]] at this
      · intro h v hv
        exact h (xorw v d) ((hs.R w v).2 hv)
  | _, _, .all a b, ρ => by
      funext w
      have key : ∀ x w', eval (mk R ac P) b (ec (actTy d a x) (actEnv d _ ρ)) w' =
          eval (mk R ac P) b (ec x ρ) (xorw w' d) := fun x w' => congrFun (eval_act hs b (ec x ρ)) w'
      show (∀ x, Adm _ a x → eval _ b (ec x (actEnv d _ ρ)) w) =
        (∀ x, Adm _ a x → eval _ b (ec x ρ) (xorw w d))
      apply propext; constructor
      · intro h x hx
        have := h (actTy d a x) ((adm_act_iff R ac P d a x).2 hx)
        rw [key] at this; exact this
      · intro h x hx
        have := h (actTy d a x) ((adm_act_iff R ac P d a x).2 hx)
        have k := key (actTy d a x) w
        rw [actTy_invol] at k
        rw [k]; exact this
  | _, _, .ex a b, ρ => by
      funext w
      have key : ∀ x w', eval (mk R ac P) b (ec (actTy d a x) (actEnv d _ ρ)) w' =
          eval (mk R ac P) b (ec x ρ) (xorw w' d) := fun x w' => congrFun (eval_act hs b (ec x ρ)) w'
      show (∃ x, Adm _ a x ∧ eval _ b (ec x (actEnv d _ ρ)) w) =
        (∃ x, Adm _ a x ∧ eval _ b (ec x ρ) (xorw w d))
      apply propext; constructor
      · rintro ⟨x, hx, h⟩
        refine ⟨actTy d a x, (adm_act_iff R ac P d a x).2 hx, ?_⟩
        have k := key (actTy d a x) w
        rw [actTy_invol] at k
        rw [k] at h; exact h
      · rintro ⟨x, hx, h⟩
        refine ⟨actTy d a x, (adm_act_iff R ac P d a x).2 hx, ?_⟩
        rw [key]; exact h
  | _, _, .allE b, ρ => by
      funext w
      have key : ∀ y w', eval (mk R ac P) b (ec y (actEnv d _ ρ)) w' =
          eval (mk R ac P) b (ec y ρ) (xorw w' d) := fun y w' => congrFun (eval_act hs b (ec y ρ)) w'
      show (∀ y, ac y w → eval _ b (ec y (actEnv d _ ρ)) w) =
        (∀ y, ac y (xorw w d) → eval _ b (ec y ρ) (xorw w d))
      apply propext; constructor
      · intro h y hy; have := h y ((hs.ac y w).1 hy); rw [key] at this; exact this
      · intro h y hy; rw [key]; exact h y ((hs.ac y w).2 hy)
  | _, _, .exE b, ρ => by
      funext w
      have key : ∀ y w', eval (mk R ac P) b (ec y (actEnv d _ ρ)) w' =
          eval (mk R ac P) b (ec y ρ) (xorw w' d) := fun y w' => congrFun (eval_act hs b (ec y ρ)) w'
      show (∃ y, ac y w ∧ eval _ b (ec y (actEnv d _ ρ)) w) =
        (∃ y, ac y (xorw w d) ∧ eval _ b (ec y ρ) (xorw w d))
      apply propext; constructor
      · rintro ⟨y, hy, h⟩; rw [key] at h; exact ⟨y, (hs.ac y w).2 hy, h⟩
      · rintro ⟨y, hy, h⟩; exact ⟨y, (hs.ac y w).1 hy, by rw [key]; exact h⟩
  | _, _, .eqE a b, ρ => by
      funext w
      show (eval _ a (actEnv d _ ρ) = eval _ b (actEnv d _ ρ)) = _
      rw [eval_act hs a, eval_act hs b]; rfl
  | _, _, .eqP a b, ρ => by
      funext w
      show (eval _ a (actEnv d _ ρ) = eval _ b (actEnv d _ ρ)) = _
      rw [eval_act hs a, eval_act hs b]
      apply propext
      exact ⟨fun h => by have := congrArg (actTy d .p) h; rwa [actTy_invol, actTy_invol] at this,
        fun h => by rw [h]⟩
  | _, _, .pos, _ => hs.P.symm

/-! ## Admission is support -/

/-- `x` is fixed by `G_n`. -/
def Fix (n : Nat) (t : Ty) (x : Den Cw Unit t) : Prop := ∀ d, Fixes n d → actTy d t x = x

theorem fix_mono {n m : Nat} (h : n ≤ m) {t x} (hx : Fix n t x) : Fix m t x :=
  fun d hd => hx d (fixes_mono h hd)

theorem adm_iff_fix (R ac P) : (t : Ty) → (x : Den Cw Unit t) →
    (Adm (mk R ac P) t x ↔ ∃ n, Fix n t x)
  | .e, _ => ⟨fun _ => ⟨0, fun _ _ => rfl⟩, fun _ => trivial⟩
  | .s, q => by
      show Based q ↔ _
      rw [based_iff]
      constructor
      · rintro ⟨n, hn⟩; exact ⟨n, fun d hd => funext fun w => propext (hn d hd w).symm⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, fun d hd w => iff_of_eq (congrFun (hn d hd) w).symm⟩
  | .p, φ => by
      show Based (φ ()) ↔ _
      rw [based_iff]
      constructor
      · rintro ⟨n, hn⟩; exact ⟨n, fun d hd => act_fix hn hd⟩
      · rintro ⟨n, hn⟩
        refine ⟨n, fun d hd w => ?_⟩
        have := congrFun (congrFun (hn d hd) ()) w
        rw [← this]; exact Iff.rfl
  | .h, Φ => by
      show FMH Φ ↔ _
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, fun d hd => funext fun ψ => funext fun w => propext (hn d hd ψ w).symm⟩
      · rintro ⟨n, hn⟩
        refine ⟨n, fun d hd ψ w => ?_⟩
        have := congrFun (congrFun (hn d hd) ψ) w
        rw [← this]; exact Iff.rfl

theorem env_fix (R ac P) : (Γ : List Ty) → (ρ : Env Cw Unit Γ) → EnvAdm (mk R ac P) Γ ρ →
    ∃ n, ∀ d, Fixes n d → actEnv d Γ ρ = ρ
  | [], _, _ => ⟨0, fun _ _ => rfl⟩
  | t :: Γ, ρ, ⟨h1, h2⟩ => by
      obtain ⟨n, hn⟩ := (adm_iff_fix R ac P t ρ.1).1 h1
      obtain ⟨m, hm⟩ := env_fix R ac P Γ ρ.2 h2
      refine ⟨max n m, fun d hd => ?_⟩
      show (actTy d t ρ.1, actEnv d Γ ρ.2) = ρ
      rw [hn d (fixes_mono (Nat.le_max_left n m) hd), hm d (fixes_mono (Nat.le_max_right n m) hd)]
      rfl

/-- **Fact (a) for `Frag`.** A model with the finitely supported carriers whose accessibility,
actuality and positivity are fixed by some `G_m` is closed under the fragment of `𝓛`. -/
theorem lgeneral_of_sym {R ac P} (hsym : ∃ m, ∀ d, Fixes m d → Sym R ac P d) :
    LGeneral (mk R ac P) := by
  intro Γ t tm ρ hρ
  obtain ⟨m, hm⟩ := hsym
  obtain ⟨n, hn⟩ := env_fix R ac P Γ ρ hρ
  refine (adm_iff_fix R ac P t _).2 ⟨max n m, fun d hd => ?_⟩
  have := eval_act (hm d (fixes_mono (Nat.le_max_right n m) hd)) tm ρ
  rw [hn d (fixes_mono (Nat.le_max_left n m) hd)] at this
  exact this.symm

/-! ## The models -/

theorem sym_total {P : (Unit → Cw → Prop) → Cw → Prop} {d : Cw} (hP : actH d P = P) :
    Sym (fun _ _ => True) (fun _ _ => True) P d :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, hP⟩

/-- `fm` (K8, K10, K13) is closed under the fragment of `𝓛`. -/
theorem lgeneral_fm : LGeneral fm :=
  lgeneral_of_sym (R := fun _ _ => True) (ac := fun _ _ => True) (P := fm.P)
    ⟨0, fun d _ => sym_total (funext fun ψ => funext fun w => by
      show act d ψ () (xorw w d) = ψ () w
      simp [act, xorw_xorw])⟩

/-- `gfm` (K9) is closed under the fragment of `𝓛`. -/
theorem lgeneral_gfm : LGeneral gfm :=
  lgeneral_of_sym (R := fun _ _ => True) (ac := fun _ _ => True) (P := gfm.P)
    ⟨1, fun d hd => sym_total (funext fun ψ => funext fun w => by
      show act d ψ () (GodlessL.f (xorw w d)) = ψ () (GodlessL.f w)
      simp [act, f_xorw hd, xorw_xorw])⟩

/-- sk's identity-frame model (P120) on the same carriers. -/
def fmId : Model Cw Unit := mk (fun w v => v = w) (fun _ _ => True) (fun φ w => φ () w)

theorem lgeneral_fmId : LGeneral fmId :=
  lgeneral_of_sym ⟨0, fun d _ => ⟨fun w v => ⟨fun h => by
      have := congrArg (fun u => xorw u d) h; simpa [xorw_xorw] using this,
      fun h => by rw [h]⟩, fun _ _ => Iff.rfl,
    funext fun ψ => funext fun w => by
      show act d ψ () (xorw w d) = ψ () w
      simp [act, xorw_xorw]⟩⟩

/-! ## K8, K9, K10, K13 in models closed under the fragment -/

/-- K8 with closure under the fragment of `𝓛`. -/
theorem k8_lgeneral : LGeneral fm ∧ Ax2a fm ∧ Ax3 fm ∧ Ax3v3 fm ∧ Ax4 fm ∧ Ax4c fm ∧ Th4 fm ∧
    L fm ∧ Ax1Gen fm ∧ Ax1GenTwo fm ∧ Ax1GenOne fm ∧ Ax1GenBoxTwo fm ∧ (∀ w, ExG fm w) ∧
    ¬ Ax2b fm ∧ ¬ MC fm := by
  obtain ⟨_, _, _, _, h2a, h3, h3', h4, h4c, ht4, hl, hg, hg2, hg1, hgb, hex, _, _, hn2b, hnmc⟩ :=
    rigidity_independent_fm
  exact ⟨lgeneral_fm, h2a, h3, h3', h4, h4c, ht4, hl, hg, hg2, hg1, hgb, hex, hn2b, hnmc⟩

/-- K9 with closure under the fragment of `𝓛`. -/
theorem k9_lgeneral : LGeneral gfm ∧ Ax2a gfm ∧ Ax3 gfm ∧ Ax3v3 gfm ∧ Ax4 gfm ∧ Ax4c gfm ∧
    Th4 gfm ∧ L gfm ∧ Ax1GenBoxTwo gfm ∧ ¬ ExG gfm (fun _ => false) ∧ ¬ Ax2b gfm ∧ ¬ MC gfm ∧
    ¬ Ax1Gen gfm ∧ ¬ Ax1GenTwo gfm ∧ ¬ Ax1GenOne gfm := by
  obtain ⟨_, _, _, _, h2a, h3, h3', h4, h4c, ht4, hl, hgb, _, _, hng, hn2b, hnmc, hn1, hn2, hn3⟩ :=
    godless_fm
  exact ⟨lgeneral_gfm, h2a, h3, h3', h4, h4c, ht4, hl, hgb, hng, hn2b, hnmc, hn1, hn2, hn3⟩

/-- K10 (thread D) with closure under the fragment of `𝓛`. -/
theorem k10_lgeneral : LGeneral fm ∧ (∀ φ w, fm.P φ w ↔ ∀ x, G fm x w → φ x w) ∧
    Ax2a fm ∧ Ax3 fm ∧ Ax3v3 fm ∧ Ax4 fm ∧ L fm ∧ Ax1Gen fm ∧ (∀ w, ExG fm w) ∧
    (∀ w v, fm.R w v) ∧ ¬ Ax2b fm ∧ ¬ MC fm :=
  ⟨lgeneral_fm, rigidity_exit_fm.2⟩

/-- K13 with closure under the fragment of `𝓛`: with all properties and collections admitted,
Ax1Gen, Ax2a, Ax3 force `R w v → v = w`, MC and Ax2b; the finitely supported model `fm`, closed under the fragment,
satisfies Ax1Gen, Ax2a, Ax3, Ax3v3, Ax4, `L` but neither. -/
theorem k13_lgeneral :
    (∀ (W D : Type) (M : Model W D), Separating.FullTH M → Ax1Gen M → Ax2a M →
      (Ax3 M ∨ Ax3v3 M) → (∀ w v, M.R w v → v = w) ∧ MC M ∧ Ax2b M) ∧
    (LGeneral fm ∧ Ax1Gen fm ∧ Ax2a fm ∧ Ax3 fm ∧ Ax3v3 fm ∧ Ax4 fm ∧ L fm ∧
      ¬ MC fm ∧ ¬ Ax2b fm) :=
  ⟨fun _ _ _ hF h1 h2a h3 => Separating.standard_collapse hF h1 h2a h3, lgeneral_fm, Separating.separating.2.2⟩

end Programme.«20261022-0733-ontological».Run2.FMGeneral

#print axioms Programme.«20261022-0733-ontological».Run2.FMGeneral.lgeneral_of_sym
#print axioms Programme.«20261022-0733-ontological».Run2.FMGeneral.lgeneral_fm
#print axioms Programme.«20261022-0733-ontological».Run2.FMGeneral.lgeneral_gfm
#print axioms Programme.«20261022-0733-ontological».Run2.FMGeneral.lgeneral_fmId
#print axioms Programme.«20261022-0733-ontological».Run2.FMGeneral.k8_lgeneral
#print axioms Programme.«20261022-0733-ontological».Run2.FMGeneral.k9_lgeneral
#print axioms Programme.«20261022-0733-ontological».Run2.FMGeneral.k10_lgeneral
#print axioms Programme.«20261022-0733-ontological».Run2.FMGeneral.k13_lgeneral
