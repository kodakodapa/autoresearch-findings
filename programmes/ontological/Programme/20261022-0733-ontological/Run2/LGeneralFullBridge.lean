import Programme.«20261022-0733-ontological».Run2.LGeneralFull
/-! # The full language extends pr's fragment: `LGenF M → LGeneral M`

pr's `Run2.LGeneral.Tm` embeds into `LGeneralFull.Tm` (`trTm`: `p ↦ e → σ`, `h ↦ (e → σ) → σ`,
`eqE`/`eqP` to the primitive equality at `e`/`e → σ`), with the same denotation (`eval_tr`).
So every model that is `𝓛`-general in the full sense is closed under the fragment, and all
results proved from `LGeneral` (K1, K3, K12, ...) hold in it. -/

namespace Programme.«20261022-0733-ontological».Run2.LGeneralFullBridge

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.LGeneralFull


variable {W D : Type}

@[reducible] def tr : Programme.«20261022-0733-ontological».Run2.LGeneral.Ty → FTy
  | .e => .e
  | .s => .s
  | .p => tp
  | .h => th

@[reducible] def cv : (t : Programme.«20261022-0733-ontological».Run2.LGeneral.Ty) → Programme.«20261022-0733-ontological».Run2.LGeneral.Den W D t → Den W D (tr t)
  | .e, x => x
  | .s, x => x
  | .p, x => x
  | .h, x => x

def trEnv : (Γ : List Programme.«20261022-0733-ontological».Run2.LGeneral.Ty) → Programme.«20261022-0733-ontological».Run2.LGeneral.Env W D Γ → Env W D (Γ.map tr)
  | [], _ => ()
  | t :: Γ, ρ => (cv t ρ.1, trEnv Γ ρ.2)

def trVar : {Γ : List Programme.«20261022-0733-ontological».Run2.LGeneral.Ty} → {t : Programme.«20261022-0733-ontological».Run2.LGeneral.Ty} → Programme.«20261022-0733-ontological».Run2.LGeneral.Var Γ t → Var (Γ.map tr) (tr t)
  | _, _, .zero => .zero
  | _, _, .succ i => .succ (trVar i)

def trTm : {Γ : List Programme.«20261022-0733-ontological».Run2.LGeneral.Ty} → {t : Programme.«20261022-0733-ontological».Run2.LGeneral.Ty} → Programme.«20261022-0733-ontological».Run2.LGeneral.Tm Γ t → Tm (Γ.map tr) (tr t)
  | _, _, .var i => .var (trVar i)
  | _, _, .appP f a => .app (a := .e) (b := .s) (trTm f) (trTm a)
  | _, _, .appH F f => .app (a := tp) (b := .s) (trTm F) (trTm f)
  | _, _, .lamP b => .lam (a := .e) (b := .s) (trTm b)
  | _, _, .lamH b => .lam (a := tp) (b := .s) (trTm b)
  | _, _, .top => .top
  | _, _, .bot => .bot
  | _, _, .neg a => .neg (trTm a)
  | _, _, .and a b => .and (trTm a) (trTm b)
  | _, _, .or a b => .or (trTm a) (trTm b)
  | _, _, .imp a b => .imp (trTm a) (trTm b)
  | _, _, .box a => .box (trTm a)
  | _, _, .all a b => .all (tr a) (trTm b)
  | _, _, .ex a b => .ex (tr a) (trTm b)
  | _, _, .allE b => .allE (trTm b)
  | _, _, .exE b => .exE (trTm b)
  | _, _, .eqE a b => .eq .e (trTm a) (trTm b)
  | _, _, .eqP a b => .eq tp (trTm a) (trTm b)
  | _, _, .pos => .pos

variable (M : Model W D) (A : (t : FTy) → Den W D t → Prop)
  (he : ∀ x, A .e x) (hs : ∀ q, A .s q ↔ M.AS q) (hp : ∀ φ, A tp φ ↔ M.AT φ)
  (hh : ∀ Φ, A th Φ ↔ M.AH Φ)

include he hs hp hh

theorem adm_cv : ∀ (t : Programme.«20261022-0733-ontological».Run2.LGeneral.Ty) (x : Programme.«20261022-0733-ontological».Run2.LGeneral.Den W D t), A (tr t) (cv t x) ↔ Programme.«20261022-0733-ontological».Run2.LGeneral.Adm M t x
  | .e, x => iff_of_true (he x) trivial
  | .s, x => hs x
  | .p, x => hp x
  | .h, x => hh x

theorem forall_cv : ∀ (t : Programme.«20261022-0733-ontological».Run2.LGeneral.Ty) (Q : Den W D (tr t) → Prop),
    (∀ x, A (tr t) x → Q x) ↔ (∀ x, Programme.«20261022-0733-ontological».Run2.LGeneral.Adm M t x → Q (cv t x))
  | .e, Q => ⟨fun h x _ => h x (he x), fun h x _ => h x trivial⟩
  | .s, Q => forall_congr' fun x => imp_congr_left (hs x)
  | .p, Q => forall_congr' fun x => imp_congr_left (hp x)
  | .h, Q => forall_congr' fun x => imp_congr_left (hh x)

theorem exists_cv : ∀ (t : Programme.«20261022-0733-ontological».Run2.LGeneral.Ty) (Q : Den W D (tr t) → Prop),
    (∃ x, A (tr t) x ∧ Q x) ↔ (∃ x, Programme.«20261022-0733-ontological».Run2.LGeneral.Adm M t x ∧ Q (cv t x))
  | .e, Q => ⟨fun ⟨x, _, h⟩ => ⟨x, trivial, h⟩, fun ⟨x, _, h⟩ => ⟨x, he x, h⟩⟩
  | .s, Q => exists_congr fun x => and_congr_left fun _ => hs x
  | .p, Q => exists_congr fun x => and_congr_left fun _ => hp x
  | .h, Q => exists_congr fun x => and_congr_left fun _ => hh x

omit he hs hp hh in
theorem get_tr : ∀ {Γ t} (i : Programme.«20261022-0733-ontological».Run2.LGeneral.Var Γ t) (ρ : Programme.«20261022-0733-ontological».Run2.LGeneral.Env W D Γ),
    (trVar i).get (trEnv Γ ρ) = cv t (i.get ρ)
  | _, _, .zero, _ => rfl
  | _, _, .succ i, ρ => get_tr i ρ.2

/-- The embedding preserves denotation. -/
theorem eval_tr : ∀ {Γ t} (tm : Programme.«20261022-0733-ontological».Run2.LGeneral.Tm Γ t) (ρ : Programme.«20261022-0733-ontological».Run2.LGeneral.Env W D Γ),
    eval ⟨M.R, M.act, M.P, A⟩ (trTm tm) (trEnv Γ ρ) = cv t (Programme.«20261022-0733-ontological».Run2.LGeneral.eval M tm ρ)
  | _, _, .var i, ρ => get_tr i ρ
  | _, _, .appP f a, ρ => by
      show eval _ (trTm f) _ (eval _ (trTm a) _) = _
      rw [eval_tr f ρ, eval_tr a ρ]; rfl
  | _, _, .appH F f, ρ => by
      show eval _ (trTm F) _ (eval _ (trTm f) _) = _
      rw [eval_tr F ρ, eval_tr f ρ]; rfl
  | _, _, .lamP b, ρ => by
      funext z; exact eval_tr b (z, ρ)
  | _, _, .lamH b, ρ => by
      funext z; exact eval_tr b (z, ρ)
  | _, _, .top, _ => rfl
  | _, _, .bot, _ => rfl
  | _, _, .neg a, ρ => by
      funext w; show (¬ _) = _; rw [eval_tr a ρ]; rfl
  | _, _, .and a b, ρ => by
      funext w; show (_ ∧ _) = _; rw [eval_tr a ρ, eval_tr b ρ]; rfl
  | _, _, .or a b, ρ => by
      funext w; show (_ ∨ _) = _; rw [eval_tr a ρ, eval_tr b ρ]; rfl
  | _, _, .imp a b, ρ => by
      funext w; show (_ → _) = _; rw [eval_tr a ρ, eval_tr b ρ]; rfl
  | _, _, .box a, ρ => by
      funext w; show (∀ v, M.R w v → _) = _; rw [eval_tr a ρ]; rfl
  | _, _, .all a b, ρ => by
      funext w
      show (∀ x, A (tr a) x → eval _ (trTm b) (x, trEnv _ ρ) w) =
        (∀ x, Programme.«20261022-0733-ontological».Run2.LGeneral.Adm M a x → Programme.«20261022-0733-ontological».Run2.LGeneral.eval M b (x, ρ) w)
      apply propext
      rw [forall_cv M A he hs hp hh a]
      refine forall_congr' fun x => imp_congr_right fun _ => ?_
      exact Iff.of_eq (congrFun (eval_tr b (x, ρ)) w)
  | _, _, .ex a b, ρ => by
      funext w
      show (∃ x, A (tr a) x ∧ eval _ (trTm b) (x, trEnv _ ρ) w) =
        (∃ x, Programme.«20261022-0733-ontological».Run2.LGeneral.Adm M a x ∧ Programme.«20261022-0733-ontological».Run2.LGeneral.eval M b (x, ρ) w)
      apply propext
      rw [exists_cv M A he hs hp hh a]
      refine exists_congr fun x => and_congr_right fun _ => ?_
      exact Iff.of_eq (congrFun (eval_tr b (x, ρ)) w)
  | _, _, .allE b, ρ => by
      funext w
      show (∀ y, M.act y w → eval _ (trTm b) (y, trEnv _ ρ) w) = _
      apply propext
      exact forall_congr' fun y => imp_congr_right fun _ => Iff.of_eq (congrFun (eval_tr b (y, ρ)) w)
  | _, _, .exE b, ρ => by
      funext w
      show (∃ y, M.act y w ∧ eval _ (trTm b) (y, trEnv _ ρ) w) = _
      apply propext
      exact exists_congr fun y => and_congr_right fun _ => Iff.of_eq (congrFun (eval_tr b (y, ρ)) w)
  | _, _, .eqE a b, ρ => by
      funext w
      show (eval _ (trTm a) _ = eval _ (trTm b) _) = _
      rw [eval_tr a ρ, eval_tr b ρ]; rfl
  | _, _, .eqP a b, ρ => by
      funext w
      show (∀ z, A .e z → eval _ (trTm a) _ z = eval _ (trTm b) _ z) = _
      rw [eval_tr a ρ, eval_tr b ρ]
      exact propext ⟨fun h => funext fun z => h z (he z), fun h z _ => by
        show Programme.«20261022-0733-ontological».Run2.LGeneral.eval M a ρ z = Programme.«20261022-0733-ontological».Run2.LGeneral.eval M b ρ z
        exact congrFun h z⟩
  | _, _, .pos, _ => rfl

theorem envA_tr : ∀ (Γ : List Programme.«20261022-0733-ontological».Run2.LGeneral.Ty) (ρ : Programme.«20261022-0733-ontological».Run2.LGeneral.Env W D Γ), Programme.«20261022-0733-ontological».Run2.LGeneral.EnvAdm M Γ ρ →
    EnvA ⟨M.R, M.act, M.P, A⟩ (Γ.map tr) (trEnv Γ ρ)
  | [], _, _ => trivial
  | t :: Γ, ρ, ⟨h1, h2⟩ => ⟨(adm_cv M A he hs hp hh t ρ.1).2 h1, envA_tr Γ ρ.2 h2⟩

end Programme.«20261022-0733-ontological».Run2.LGeneralFullBridge

namespace Programme.«20261022-0733-ontological».Run2.LGeneralFull
open Programme.«20261022-0733-ontological».Run2.LGeneralFullBridge

/-- **Full `𝓛`-generality implies pr's `LGeneral`.** -/
theorem lgeneral_of_lgenF {W D : Type} {M : Programme.«20261022-0733-ontological».Run2.TwoClosed.Model W D} (h : LGenF M) :
    Programme.«20261022-0733-ontological».Run2.LGeneral.LGeneral M := by
  obtain ⟨A, he, hs, hp, hh, hc⟩ := h
  intro Γ t tm ρ hρ
  have := hc (trTm tm) (trEnv Γ ρ) (envA_tr M A he hs hp hh Γ ρ hρ)
  rw [eval_tr M A he hs hp hh tm ρ] at this
  exact (adm_cv M A he hs hp hh t _).1 this

end Programme.«20261022-0733-ontological».Run2.LGeneralFull

#print axioms Programme.«20261022-0733-ontological».Run2.LGeneralFull.lgeneral_of_lgenF
