import Programme.«20261022-1724-ontological».Run3.DeepND
-- Verbatim copy of agents/pr/lean/Programme/Run3/DeepND.lean (pr, round 1), for import.
/-! # Deep derivations in the embedding, and soundness over 𝓛-general structures

v4 (arXiv 2609.36279v4) `prop:lgeneral` concerns a proof `π` in HOL of `⟦φ⟧` from `T`: the
embedding's world type is visible to `π`, so `π` may mention a nominal `λu. u = w`; the
proposition says that if the terms `π` uses as elements of an `𝓛`-domain are `𝓛`-terms with
`𝓛`-parameters, then `⟦φ⟧` holds in every `𝓛`-general model of `T`.

Here the HOL side is deep.  Types `HTy`: the types of `𝓛` (`L t`), the world type `w` and the
truth values `o`.  Terms `HTerm` contain the `𝓛`-level application/abstraction, `P`, world
abstraction `wabs` (so `λu. u = w` is `wabs (eq w (var 0) (var 1))`), application of a
proposition to a world (`holds`), `R`, actuality, the connectives at `o`, quantifiers and
equality at every type.  `emb` is the embedding `⟦-⟧` of `𝓛`-terms (`L.Tm`), connectives
unfolded.  Semantics: over an `L.Str` (worlds, entities, `R`, actuality, `P`, carriers `A t`
at every type of `𝓛`); quantifiers at `L t` range over `A t`, equality at `L t` is `L.eqT`
(agreement on admitted arguments), everything else standard.

`Deriv T ok` is natural deduction for this HOL with the theory `T` (a set of `𝓛`-sentences) as
axioms; its `∀`-elimination and `∃`-introduction at a type of `𝓛` require `ok t` of the instance.
`Cert t`: `t` is `emb r s` for an `𝓛`-term `s` whose parameters are mapped by `r` to variables of
`𝓛`-types.  **`soundness`**: every `Deriv T Cert` derivation is valid in every closed structure
(`L.Closed`) satisfying `T`.  `Deriv T Any` is the unrestricted calculus.

Equality substitution (`subst`) is restricted to *plain* types, where relativised equality is
identity (`e`, `σ`, `e → … → σ`, `w`, `o`); at other types of `𝓛` equality is used through
`funApp`/`funExt` only.  The β-rules, extensionality at `σ` and at arrow types of `𝓛`, and
classical logic are included. -/

-- [cleanup 2026-10-23] shared block (1540 lines) now imported from Programme.«20261022-1724-ontological».Run3.DeepND




/-! # Leibniz's law at `σ → σ` is not derivable in pr's certified deep calculus

pr's `Deriv T Cert` (copied verbatim above from agents/pr/lean/Programme/Run3/DeepND.lean) is sound over every closed `L.Str` admitting
all entities (`valid_of_deriv`).  Here: a closed flip structure on `W = 2^ℕ` (one entity,
identity frame, `P φ w = φ () w`, carriers = supported, admitted-to-admitted objects as in the
library's `Run2.LGeneralFull`) in which the `𝓛`-sentence
  `∀ f₁ f₂ : σ→σ. ∀ F : (σ→σ)→σ. f₁ = f₂ → F f₁ = F f₂`
fails at every world.  Witnesses: `f₁ = id`, `f₂ p = p` if `p` is supported else `⊥`,
`F f = {x | x ∈ f {x}}`.  Hence no certified derivation of it exists (`leib_not_derivable`),
although it holds in every closed structure whose admitted functions respect `eqT`
(`leib_of_resp`), in particular in every model of v4's def:lgeneral.

The section "Symmetric structures" is copied verbatim from the library module
`Programme.«20261022-0733-ontological».Run2.LGeneralFull` (not built in the mount). -/

namespace Programme.«20261022-1724-ontological».Run3.LeibnizGap

open Programme.«20261022-1724-ontological».Run3.L Programme.«20261022-1724-ontological».Run3.HOL

variable {W D : Type}

/-! ## Symmetric structures -/

/-- A filtration of world bijections (pairs `(f, g)`, `g` the inverse of `f`). -/
structure Sym (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) where
  Fx : Nat → (W → W) → (W → W) → Prop
  mono : ∀ {n m f g}, n ≤ m → Fx m f g → Fx n f g
  inv : ∀ {n f g}, Fx n f g → Fx n g f
  fg : ∀ {f g}, Fx 0 f g → ∀ w, f (g w) = w
  hR : ∀ {f g}, Fx 0 f g → ∀ w v, R (f w) (f v) ↔ R w v
  hact : ∀ {f g}, Fx 0 f g → ∀ y w, act y (f w) ↔ act y w
  hP : ∀ {f g}, Fx 0 f g → fl f g th P = P
  conj : ∀ {f g}, Fx 0 f g → ∀ n, ∃ m, ∀ c d, Fx m c d →
    Fx n (fun w => f (c (g w))) (fun w => f (d (g w)))

variable {R : W → W → Prop} {act : D → W → Prop} {P : Den W D th}

def Sup (S : Sym R act P) (t : FTy) (x : Den W D t) : Prop :=
  ∃ n, ∀ f g, S.Fx n f g → fl f g t x = x

/-- Carriers: supported, and admitted-to-admitted at arrow types. -/
def AdmF (S : Sym R act P) : (t : FTy) → Den W D t → Prop
  | .e, _ => True
  | .s, q => Sup S .s q
  | .arr a b, F => Sup S (.arr a b) F ∧ ∀ z, AdmF S a z → AdmF S b (F z)

def str (S : Sym R act P) : Str W D := ⟨R, act, P, AdmF S⟩

variable (S : Sym R act P)

theorem sup_of_adm : ∀ (t : FTy) (x : Den W D t), AdmF S t x → Sup S t x
  | .e, _, _ => ⟨0, fun _ _ _ => rfl⟩
  | .s, _, h => h
  | .arr _ _, _, h => h.1

theorem sup_fl {f g : W → W} (h : S.Fx 0 f g) (t : FTy) (x : Den W D t) (hx : Sup S t x) :
    Sup S t (fl f g t x) := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := S.conj h n
  refine ⟨m, fun c d hcd => ?_⟩
  have h1 : fl g f t (fl c d t (fl f g t x)) = x := by
    rw [fl_comp, fl_comp]; exact hn _ _ (hm c d hcd)
  have h2 := fl_inv (S.fg (S.inv h)) t (fl c d t (fl f g t x))
  rw [h1] at h2; exact h2.symm

theorem adm_fl : ∀ (t : FTy) {f g : W → W}, S.Fx 0 f g → ∀ x, AdmF S t x → AdmF S t (fl f g t x)
  | .e, _, _, _, _, _ => trivial
  | .s, _, _, h, x, hx => sup_fl S h .s x hx
  | .arr a b, f, g, h, F, hF =>
      ⟨sup_fl S h _ F hF.1, fun z hz =>
        adm_fl b h (F (fl g f a z)) (hF.2 _ (adm_fl a (S.inv h) z hz))⟩

theorem forall_fl {f g : W → W} (h : S.Fx 0 f g) (t : FTy) (Q : Den W D t → Prop) :
    (∀ x, AdmF S t x → Q (fl f g t x)) ↔ (∀ x, AdmF S t x → Q x) :=
  ⟨fun hq x hx => by
    have := hq _ (adm_fl S t (S.inv h) x hx)
    rwa [fl_inv (S.fg (S.inv h))] at this,
   fun hq x hx => hq _ (adm_fl S t h x hx)⟩

theorem exists_fl {f g : W → W} (h : S.Fx 0 f g) (t : FTy) (Q : Den W D t → Prop) :
    (∃ x, AdmF S t x ∧ Q (fl f g t x)) ↔ (∃ x, AdmF S t x ∧ Q x) :=
  ⟨fun ⟨x, hx, hq⟩ => ⟨_, adm_fl S t h x hx, hq⟩,
   fun ⟨x, hx, hq⟩ => ⟨fl g f t x, adm_fl S t (S.inv h) x hx, by
     rw [fl_inv (S.fg (S.inv h))]; exact hq⟩⟩

theorem eqT_fl : ∀ (t : FTy) {f g : W → W}, S.Fx 0 f g → ∀ x y,
    eqT (str S) t (fl f g t x) (fl f g t y) ↔ eqT (str S) t x y
  | .e, _, _, _, _, _ => Iff.rfl
  | .s, f, g, h, x, y =>
      ⟨fun e => by
        have := congrArg (fl g f .s) e
        rwa [fl_inv (S.fg h), fl_inv (S.fg h)] at this,
       fun e => e ▸ rfl⟩
  | .arr a b, f, g, h, F, G => by
      show (∀ z, AdmF S a z → eqT (str S) b (fl f g b (F (fl g f a z))) (fl f g b (G (fl g f a z))))
        ↔ ∀ z, AdmF S a z → eqT (str S) b (F z) (G z)
      rw [← forall_fl S h a]
      refine forall_congr' fun z => imp_congr_right fun _ => ?_
      rw [fl_inv (S.fg h), eqT_fl b h]

def flEnv (f g : W → W) : (Γ : List FTy) → Env W D Γ → Env W D Γ
  | [], _ => ()
  | t :: Γ, ρ => (fl f g t ρ.1, flEnv f g Γ ρ.2)

theorem get_fl (f g : W → W) : ∀ {Γ t} (i : Var Γ t) (ρ : Env W D Γ),
    i.get (flEnv f g Γ ρ) = fl f g t (i.get ρ)
  | _, _, .zero, _ => rfl
  | _, _, .succ i, ρ => get_fl f g i ρ.2

/-- **Equivariance** of evaluation under every symmetry. -/
theorem eval_act {f g : W → W} (h : S.Fx 0 f g) :
    ∀ {Γ t} (tm : Tm Γ t) (ρ : Env W D Γ),
      eval (str S) tm (flEnv f g Γ ρ) = fl f g t (eval (str S) tm ρ)
  | _, _, .var i, ρ => get_fl f g i ρ
  | _, _, .app (a := a) F x, ρ => by
      show eval _ F _ (eval _ x _) = _
      rw [eval_act h F ρ, eval_act h x ρ]
      show fl f g _ (eval _ F ρ (fl g f a (fl f g a (eval _ x ρ)))) = _
      rw [fl_inv (S.fg h)]; rfl
  | _, _, .lam (a := a) b, ρ => by
      funext z
      have e := eval_act h b (fl g f a z, ρ)
      have e2 : flEnv f g (a :: _) (fl g f a z, ρ) = (z, flEnv f g _ ρ) := by
        show (fl f g a (fl g f a z), _) = _
        rw [fl_inv (S.fg (S.inv h))]
      rw [e2] at e
      exact e
  | _, _, .top, _ => rfl
  | _, _, .bot, _ => rfl
  | _, _, .neg x, ρ => by
      funext w; show (¬ _) = _; rw [eval_act h x ρ]; rfl
  | _, _, .and x y, ρ => by
      funext w; show (_ ∧ _) = _; rw [eval_act h x ρ, eval_act h y ρ]; rfl
  | _, _, .or x y, ρ => by
      funext w; show (_ ∨ _) = _; rw [eval_act h x ρ, eval_act h y ρ]; rfl
  | _, _, .imp x y, ρ => by
      funext w; show (_ → _) = _; rw [eval_act h x ρ, eval_act h y ρ]; rfl
  | _, _, .box x, ρ => by
      funext w
      show (∀ v, R w v → eval (str S) x (flEnv f g _ ρ) v) = (∀ v, R (f w) v → eval (str S) x ρ v)
      rw [eval_act h x ρ]
      apply propext
      constructor
      · intro hv v hr
        have := hv (g v) (by rw [← S.hR h, S.fg h]; exact hr)
        simpa [fl, S.fg h] using this
      · intro hv v hr
        exact hv _ ((S.hR h w v).2 hr)
  | _, _, .all t b, ρ => by
      funext w
      show (∀ x, AdmF S t x → eval (str S) b (x, flEnv f g _ ρ) w) =
        (∀ x, AdmF S t x → eval (str S) b (x, ρ) (f w))
      apply propext
      rw [← forall_fl S h t]
      refine forall_congr' fun x => imp_congr_right fun _ => ?_
      exact Iff.of_eq (congrFun (eval_act h b (x, ρ)) w)
  | _, _, .ex t b, ρ => by
      funext w
      show (∃ x, AdmF S t x ∧ eval (str S) b (x, flEnv f g _ ρ) w) =
        (∃ x, AdmF S t x ∧ eval (str S) b (x, ρ) (f w))
      apply propext
      rw [← exists_fl S h t]
      refine exists_congr fun x => and_congr_right fun _ => ?_
      exact Iff.of_eq (congrFun (eval_act h b (x, ρ)) w)
  | _, _, .allE b, ρ => by
      funext w
      show (∀ y, act y w → eval (str S) b (y, flEnv f g _ ρ) w) =
        (∀ y, act y (f w) → eval (str S) b (y, ρ) (f w))
      apply propext
      refine forall_congr' fun y => ?_
      rw [S.hact h]
      exact imp_congr_right fun _ => Iff.of_eq (congrFun (eval_act h b (y, ρ)) w)
  | _, _, .exE b, ρ => by
      funext w
      show (∃ y, act y w ∧ eval (str S) b (y, flEnv f g _ ρ) w) =
        (∃ y, act y (f w) ∧ eval (str S) b (y, ρ) (f w))
      apply propext
      refine exists_congr fun y => ?_
      rw [S.hact h]
      exact and_congr_right fun _ => Iff.of_eq (congrFun (eval_act h b (y, ρ)) w)
  | _, _, .eq a x y, ρ => by
      funext w
      show eqT (str S) a (eval _ x _) (eval _ y _) = eqT (str S) a (eval _ x ρ) (eval _ y ρ)
      rw [eval_act h x ρ, eval_act h y ρ]
      exact propext (eqT_fl S a h _ _)
  | _, _, .pos, _ => (S.hP h).symm

theorem env_sup : ∀ (Γ : List FTy) (ρ : Env W D Γ), EnvA (str S) Γ ρ →
    ∃ N, ∀ f g, S.Fx N f g → flEnv f g Γ ρ = ρ
  | [], _, _ => ⟨0, fun _ _ _ => rfl⟩
  | t :: Γ, (x, r), ⟨h1, h2⟩ => by
      obtain ⟨n, hn⟩ := sup_of_adm S t x h1
      obtain ⟨m, hm⟩ := env_sup Γ r h2
      refine ⟨max n m, fun f g hfg => ?_⟩
      show (fl f g t x, flEnv f g Γ r) = (x, r)
      rw [hn f g (S.mono (Nat.le_max_left n m) hfg), hm f g (S.mono (Nat.le_max_right n m) hfg)]

theorem sup_eval {Γ t} (tm : Tm Γ t) (ρ : Env W D Γ) (hρ : EnvA (str S) Γ ρ) :
    Sup S t (eval (str S) tm ρ) := by
  obtain ⟨N, hN⟩ := env_sup S Γ ρ hρ
  refine ⟨N, fun f g hfg => ?_⟩
  rw [← eval_act S (S.mono (Nat.zero_le N) hfg) tm ρ, hN f g hfg]

theorem sup_app {a b : FTy} {F : Den W D (.arr a b)} {x : Den W D a}
    (hF : Sup S (.arr a b) F) (hx : Sup S a x) : Sup S b (F x) := by
  obtain ⟨n, hn⟩ := hF
  obtain ⟨m, hm⟩ := hx
  refine ⟨max n m, fun f g hfg => ?_⟩
  have e1 := hn f g (S.mono (Nat.le_max_left n m) hfg)
  have e2 := hm g f (S.inv (S.mono (Nat.le_max_right n m) hfg))
  have := congrFun e1 x
  show fl f g b (F x) = F x
  calc fl f g b (F x) = fl f g b (F (fl g f a x)) := by rw [e2]
    _ = F x := this

theorem get_adm : ∀ {Γ t} (i : Var Γ t) (ρ : Env W D Γ), EnvA (str S) Γ ρ →
    AdmF S t (i.get ρ)
  | _, _, .zero, _, h => h.1
  | _, _, .succ i, ρ, h => get_adm i ρ.2 h.2

/-- **Fact (a), full language.** -/
theorem closed : Closed (str S)
  | _, _, .var i, ρ, hρ => get_adm S i ρ hρ
  | _, _, .app F x, ρ, hρ => (closed F ρ hρ).2 _ (closed x ρ hρ)
  | _, _, .lam b, ρ, hρ => ⟨sup_eval S (.lam b) ρ hρ, fun z hz => closed b (z, ρ) ⟨hz, hρ⟩⟩
  | _, _, .pos, ρ, hρ => ⟨sup_eval S .pos ρ hρ, fun ψ hψ =>
      sup_app S (sup_eval S .pos ρ hρ) (sup_of_adm S _ ψ hψ)⟩
  | _, _, .top, ρ, hρ => sup_eval S .top ρ hρ
  | _, _, .bot, ρ, hρ => sup_eval S .bot ρ hρ
  | _, _, .neg x, ρ, hρ => sup_eval S (.neg x) ρ hρ
  | _, _, .and x y, ρ, hρ => sup_eval S (.and x y) ρ hρ
  | _, _, .or x y, ρ, hρ => sup_eval S (.or x y) ρ hρ
  | _, _, .imp x y, ρ, hρ => sup_eval S (.imp x y) ρ hρ
  | _, _, .box x, ρ, hρ => sup_eval S (.box x) ρ hρ
  | _, _, .all a b, ρ, hρ => sup_eval S (.all a b) ρ hρ
  | _, _, .ex a b, ρ, hρ => sup_eval S (.ex a b) ρ hρ
  | _, _, .allE b, ρ, hρ => sup_eval S (.allE b) ρ hρ
  | _, _, .exE b, ρ, hρ => sup_eval S (.exE b) ρ hρ
  | _, _, .eq a x y, ρ, hρ => sup_eval S (.eq a x y) ρ hρ


/-! ## The flip structure on `2^ℕ` -/

def Cw : Type := Nat → Bool

def xorw (w d : Cw) : Cw := fun n => xor (w n) (d n)

theorem xorw_xorw (w d : Cw) : xorw (xorw w d) d = w := by
  funext n; simp [xorw]

def Rf : Cw → Cw → Prop := fun w v => v = w
def actf : Unit → Cw → Prop := fun _ _ => True
def Pf : Den Cw Unit th := fun φ w => φ () w

/-- `Fx n f g`: `f = g` is the flip by some `d` vanishing below `n`. -/
def Fxf (n : Nat) (f g : Cw → Cw) : Prop :=
  ∃ d : Cw, (∀ k, k < n → d k = false) ∧ f = (fun w => xorw w d) ∧ g = (fun w => xorw w d)

def symf : Sym (W := Cw) (D := Unit) Rf actf Pf where
  Fx := Fxf
  mono := by
    intro n m f g hnm ⟨d, hd, hf, hg⟩
    exact ⟨d, fun k hk => hd k (Nat.lt_of_lt_of_le hk hnm), hf, hg⟩
  inv := by
    intro n f g ⟨d, hd, hf, hg⟩
    exact ⟨d, hd, hg, hf⟩
  fg := by
    intro f g ⟨d, _, hf, hg⟩ w
    subst hf; subst hg; exact xorw_xorw w d
  hR := by
    intro f g ⟨d, _, hf, _⟩ w v
    subst hf
    show xorw v d = xorw w d ↔ v = w
    constructor
    · intro h; have := congrArg (fun u => xorw u d) h; simpa [xorw_xorw] using this
    · intro h; rw [h]
  hact := by intro _ _ _ _ _; exact Iff.rfl
  hP := by
    intro f g ⟨d, _, hf, hg⟩
    subst hf; subst hg
    funext z w
    show z () (xorw (xorw w d) d) = z () w
    rw [xorw_xorw]
  conj := by
    intro f g ⟨d, _, hf, hg⟩ n
    refine ⟨n, fun c c' ⟨e, he, hc, hc'⟩ => ⟨e, he, ?_, ?_⟩⟩ <;>
    · subst hf; subst hg; subst hc; subst hc'
      funext w; funext k; simp only [xorw]; cases w k <;> cases d k <;> cases e k <;> rfl

abbrev SF : Str Cw Unit := str symf

theorem closed_SF : Closed SF := closed symf

theorem allE_SF : ∀ x, SF.A .e x := fun _ => trivial

/-! ## The witnesses -/

open Classical in
noncomputable def f₂ : Den Cw Unit (.arr .s .s) := fun p => if Sup symf .s p then p else fun _ => False

def f₁ : Den Cw Unit (.arr .s .s) := fun p => p

def Fw : Den Cw Unit (.arr (.arr .s .s) .s) := fun f x => f (fun y => y = x) x

theorem fx0 {f g : Cw → Cw} (h : Fxf 0 f g) : ∃ d : Cw, f = (fun w => xorw w d) ∧ g = (fun w => xorw w d) :=
  let ⟨d, _, hf, hg⟩ := h; ⟨d, hf, hg⟩

theorem sup_fl_iff {f g : Cw → Cw} (h : symf.Fx 0 f g) (q : Den Cw Unit .s) :
    Sup symf .s (fl f g .s q) ↔ Sup symf .s q := by
  constructor
  · intro hq
    have := sup_fl symf (symf.inv h) .s _ hq
    rwa [fl_inv (symf.fg h)] at this
  · exact sup_fl symf h .s q

theorem adm_f₁ : SF.A (.arr .s .s) f₁ :=
  ⟨⟨0, fun f g h => by
    funext z; show fl f g .s (fl g f .s z) = z; exact fl_inv (symf.fg (symf.inv h)) .s z⟩,
   fun _ hz => hz⟩

theorem adm_f₂ : SF.A (.arr .s .s) f₂ := by
  refine ⟨⟨0, fun f g h => ?_⟩, fun z hz => ?_⟩
  · funext z
    show fl f g .s (f₂ (fl g f .s z)) = f₂ z
    unfold f₂
    by_cases hz : Sup symf .s z
    · have hz' : Sup symf .s (fl g f .s z) := (sup_fl_iff (symf.inv h) z).2 hz
      rw [if_pos hz', if_pos hz]; exact fl_inv (symf.fg (symf.inv h)) .s z
    · have hz' : ¬ Sup symf .s (fl g f .s z) := fun h' => hz ((sup_fl_iff (symf.inv h) z).1 h')
      rw [if_neg hz', if_neg hz]; rfl
  · show AdmF symf .s (f₂ z)
    have hz' : Sup symf .s z := hz
    unfold f₂; rw [if_pos hz']; exact hz

theorem adm_Fw : SF.A (.arr (.arr .s .s) .s) Fw := by
  have hsup : Sup symf (.arr (.arr .s .s) .s) Fw := by
    refine ⟨0, fun f g h => ?_⟩
    obtain ⟨d, hf, hg⟩ := fx0 h
    subst hf; subst hg
    funext k x
    show k (fun w => (fun y => y = xorw x d) (xorw w d)) (xorw (xorw x d) d) = k (fun y => y = x) x
    rw [xorw_xorw]
    congr 1
    funext w; apply propext; constructor
    · intro e; have := congrArg (fun u => xorw u d) e; simpa [xorw_xorw] using this
    · intro e; rw [e]
  exact ⟨hsup, fun z hz => sup_app symf hsup (sup_of_adm symf _ z hz)⟩

theorem eq_f₁f₂ : eqT SF (.arr .s .s) f₁ f₂ := by
  intro z hz
  show z = f₂ z
  have hz' : Sup symf .s z := hz
  unfold f₂; rw [if_pos hz']

/-- Singletons are not supported. -/
theorem not_sup_singleton (x : Cw) : ¬ Sup symf .s (fun y => y = x) := by
  rintro ⟨n, hn⟩
  let d : Cw := fun k => decide (k = n)
  have hd : symf.Fx n (fun w => xorw w d) (fun w => xorw w d) :=
    ⟨d, fun k hk => by simp [d, Nat.ne_of_lt hk], rfl, rfl⟩
  have e := congrFun (hn _ _ hd) x
  have e' : xorw x d = x := by
    have : (xorw x d = x) = (x = x) := e
    rw [this]
  have := congrFun e' n
  simp [xorw, d] at this

theorem Fw_f₁ (w : Cw) : Fw f₁ w := rfl

theorem Fw_f₂ (w : Cw) : ¬ Fw f₂ w := by
  show ¬ f₂ (fun y => y = w) w
  unfold f₂; rw [if_neg (not_sup_singleton w)]; exact id

/-! ## The sentence -/

/-- `∀ f₁ f₂ : σ→σ. ∀ F : (σ→σ)→σ. f₁ = f₂ → F f₁ = F f₂`, in pr's copy of `𝓛`. -/
def Leib : Tm [] .s :=
  .all (.arr .s .s) (.all (.arr .s .s) (.all (.arr (.arr .s .s) .s)
    (.imp (.eq (.arr .s .s) (.var (.succ (.succ .zero))) (.var (.succ .zero)))
          (.eq .s (.app (.var .zero) (.var (.succ (.succ .zero))))
                  (.app (.var .zero) (.var (.succ .zero)))))))

theorem leib_fails (w : Cw) : ¬ eval SF Leib () w := by
  intro h
  have := h f₁ adm_f₁ f₂ adm_f₂ Fw adm_Fw eq_f₁f₂
  have e : Fw f₁ = Fw f₂ := this
  exact Fw_f₂ w (e ▸ Fw_f₁ w)

/-- **Main theorem.** No certified deep derivation of Leibniz's law at `σ → σ`, from any theory
true in the flip structure (e.g. the empty theory), exists. -/
theorem leib_not_derivable {T : Tm [] .s → Prop} (hT : ∀ φ, T φ → ∀ w, eval SF φ () w) :
    ¬ Deriv T (fun a t => Cert a t) [.w] [] (.holds (emb nilR Leib) var0) := fun d =>
  leib_fails (fun _ => false) (valid_of_deriv SF allE_SF closed_SF hT d _)

theorem leib_not_derivable_empty :
    ¬ Deriv (fun _ => False) (fun a t => Cert a t) [.w] [] (.holds (emb nilR Leib) var0) :=
  leib_not_derivable (fun _ h => h.elim)

/-- Leibniz's law holds in every structure whose admitted functions respect `eqT`
(the model class of v4's def:lgeneral, where functions live on the carriers). -/
theorem leib_of_resp (S : Str W D)
    (hresp : ∀ (a b : FTy) F, S.A (.arr a b) F → ∀ z z', S.A a z → S.A a z' →
      eqT S a z z' → eqT S b (F z) (F z')) (w : W) : eval S Leib () w := by
  intro f₁ h₁ f₂ h₂ F hF e
  exact hresp _ _ F hF f₁ f₂ h₁ h₂ e

end Programme.«20261022-1724-ontological».Run3.LeibnizGap

#print axioms Programme.«20261022-1724-ontological».Run3.LeibnizGap.closed_SF
#print axioms Programme.«20261022-1724-ontological».Run3.LeibnizGap.leib_fails
#print axioms Programme.«20261022-1724-ontological».Run3.LeibnizGap.leib_not_derivable_empty
#print axioms Programme.«20261022-1724-ontological».Run3.LeibnizGap.leib_of_resp
