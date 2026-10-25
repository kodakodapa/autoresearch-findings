import Programme.«20261022-1724-ontological».Run3.Canon
/-! WholeTerm.lean (th, round 9): Canon.lean (checks/completeness.py) lines 1-4339 verbatim, plus target C (b):
v4 prop:lgeneral for a deep calculus with Leibniz at every type and motive (namespace Programme.ThWhole). -/
/-! # M3: Henkin completeness of K4's certified calculus over v4's 𝓛-general models (th, thread C)

Assembly, in order:
1. pr's `agents/pr/lean/Programme/Run3/DeepV4.lean` lines 1-1891 verbatim: K4's calculus `Deriv T Cert`
   (`DC T`), its soundness over closed `Resp` structures, `Deriv.ren`;
2. the same file's lines 2904-3309 verbatim: th's bridge (v4's models `VM`/`LGen`, `ValidV4`, `ValidStr`,
   `valid_iff`), and lines 3315-3325 (`sound_v4`);
3. th's `Henkin.lean` (namespace `Programme.ThHenkin`): coding, Lindenbaum chain with Henkin witnesses;
4. new, namespace `Programme.ThCanon`: the canonical model.
   * `cert_nf`: every certified term is `emb canonR s` for an 𝓛-term `s` over the 𝓛-part of the context.
   * `Seed`: a consistent start `(Γ0, hs0)` with a world term; `Seed.G t`: 𝓛-terms over the 𝓛-part of
     some stage; `Seed.Eqv`: provable equality in the limit (stage independent, `transfer`).
   * `VMc`: worlds = world terms of the stages; carriers `C t` = `G t` modulo `Eqv`; `R`, actuality and
     truth read off membership; `pr_inj` (from `wExt` and a world witness) and `ap_ext` (from `funExt` and
     an 𝓛-witness) by Henkin witnesses; `ap` well defined by `funApp` and K4's Leibniz rule.
   * `LGc : LGen (VMc Z)`: the truth lemma, one clause per field of `LGen` (`ev_all`, `ev_box`, ...).
   * `completeness`: if `∃x.⊤ ∈ T` and `ValidV4 T φ`, then `DC T [w] [] ⟦φ⟧(w)`;
     `sound_complete` (with `sound_v4`), `sound_complete_str` (closed `Resp` structures), and
     `sound_complete_all`: for every theory `T`, `DC (T ∪ {∃x.⊤}) ⟦φ⟧ ↔ ValidV4 T φ`. -/

-- [cleanup 2026-10-23] shared block (4318 lines) now imported from Programme.«20261022-1724-ontological».Run3.Canon




/-! # Target C (b): v4's `prop:lgeneral` for a calculus with unrestricted Leibniz (th, round 9)

`DG T ok okL`: K4's natural deduction, except that the two equality-substitution rules (`subst` at
plain types, `leib` with an `𝓛`-motive) are replaced by one **Leibniz rule at every type with an
arbitrary motive** `φ : HTerm (a :: Γ) o`, as Lean's `Eq.mpr`/`congrArg` allow.  `ok` constrains
the instances of `∀E`/`∃I`, `okL a φ s t` the Leibniz steps.

`WT u` (whole-term): every argument of an application at a type of `𝓛` anywhere in `u` is a term
of `𝓛` (`Cert`).  This is v4's position clause: an argument of a constant of the signature (`pos`)
or of a variable of a type of `𝓛`, or of any other head (stricter than v4, which reads terms
modulo β, where every application is headed by a constant or a variable).

`LeibOK a φ s t`: `a` is a type at which relativised equality is identity, or the motive is `WT`
and both sides are terms of `𝓛`.  Soundness (`sound_wt`, `sound_v4_wt`) needs `WT` only for
Leibniz motives; v4's hypothesis asks it of every line. -/

namespace Programme.«20261022-1724-ontological».ThWhole
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX Programme.«20261022-1724-ontological».Run3.V4 Programme.«20261022-1724-ontological».ThCanon

variable {W D : Type}

def WT : {Γ : List HTy} → {a : HTy} → HTerm Γ a → Prop
  | _, _, .var _ => True
  | _, _, .appL f x => WT f ∧ Cert _ x
  | _, _, .lamL b => WT b
  | _, _, .pos => True
  | _, _, .wabs φ => WT φ
  | _, _, .holds p i => WT p ∧ WT i
  | _, _, .rel i j => WT i ∧ WT j
  | _, _, .act x i => WT x ∧ WT i
  | _, _, .bot => True
  | _, _, .imp p q => WT p ∧ WT q
  | _, _, .and p q => WT p ∧ WT q
  | _, _, .or p q => WT p ∧ WT q
  | _, _, .all _ p => WT p
  | _, _, .ex _ p => WT p
  | _, _, .eq _ s t => WT s ∧ WT t

def LeibOK {Γ : List HTy} (a : HTy) (φ : HTerm (a :: Γ) .o) (s t : HTerm Γ a) : Prop :=
  plain a = true ∨ (WT φ ∧ Cert a s ∧ Cert a t)

/-- K4's calculus with Leibniz at every type and every motive (side condition `okL`). -/
inductive DG (T : Tm [] .s → Prop) (ok : ∀ {Γ : List HTy} (a : HTy), HTerm Γ a → Prop)
    (okL : ∀ {Γ : List HTy} (a : HTy), HTerm (a :: Γ) .o → HTerm Γ a → HTerm Γ a → Prop) :
    (Γ : List HTy) → List (HTerm Γ .o) → HTerm Γ .o → Prop
  | hyp {Γ hs φ} : φ ∈ hs → DG T ok okL Γ hs φ
  | ax {Γ hs} (φ : Tm [] .s) (i : HTerm Γ .w) : T φ → DG T ok okL Γ hs (.holds (emb nilR φ) i)
  | impI {Γ hs φ ψ} : DG T ok okL Γ (φ :: hs) ψ → DG T ok okL Γ hs (.imp φ ψ)
  | impE {Γ hs φ ψ} : DG T ok okL Γ hs (.imp φ ψ) → DG T ok okL Γ hs φ → DG T ok okL Γ hs ψ
  | byContra {Γ hs φ} : DG T ok okL Γ (.imp φ .bot :: hs) .bot → DG T ok okL Γ hs φ
  | andI {Γ hs φ ψ} : DG T ok okL Γ hs φ → DG T ok okL Γ hs ψ → DG T ok okL Γ hs (.and φ ψ)
  | andL {Γ hs φ ψ} : DG T ok okL Γ hs (.and φ ψ) → DG T ok okL Γ hs φ
  | andR {Γ hs φ ψ} : DG T ok okL Γ hs (.and φ ψ) → DG T ok okL Γ hs ψ
  | orL {Γ hs φ ψ} : DG T ok okL Γ hs φ → DG T ok okL Γ hs (.or φ ψ)
  | orR {Γ hs φ ψ} : DG T ok okL Γ hs ψ → DG T ok okL Γ hs (.or φ ψ)
  | orE {Γ hs φ ψ χ} : DG T ok okL Γ hs (.or φ ψ) → DG T ok okL Γ (φ :: hs) χ →
      DG T ok okL Γ (ψ :: hs) χ → DG T ok okL Γ hs χ
  | allI {Γ hs} (a : HTy) {φ : HTerm (a :: Γ) .o} :
      DG T ok okL (a :: Γ) (hs.map wk) φ → DG T ok okL Γ hs (.all a φ)
  | allE {Γ hs} (a : HTy) {φ : HTerm (a :: Γ) .o} (t : HTerm Γ a) :
      DG T ok okL Γ hs (.all a φ) → ok a t → DG T ok okL Γ hs (inst φ t)
  | exI {Γ hs} (a : HTy) {φ : HTerm (a :: Γ) .o} (t : HTerm Γ a) :
      ok a t → DG T ok okL Γ hs (inst φ t) → DG T ok okL Γ hs (.ex a φ)
  | exE {Γ hs} (a : HTy) {φ : HTerm (a :: Γ) .o} {χ : HTerm Γ .o} :
      DG T ok okL Γ hs (.ex a φ) → DG T ok okL (a :: Γ) (φ :: hs.map wk) (wk χ) →
      DG T ok okL Γ hs χ
  | refl {Γ hs} (a : HTy) (t : HTerm Γ a) : DG T ok okL Γ hs (.eq a t t)
  | symm {Γ hs} (a : HTy) {s t : HTerm Γ a} : DG T ok okL Γ hs (.eq a s t) → DG T ok okL Γ hs (.eq a t s)
  | trans {Γ hs} (a : HTy) {s t u : HTerm Γ a} : DG T ok okL Γ hs (.eq a s t) →
      DG T ok okL Γ hs (.eq a t u) → DG T ok okL Γ hs (.eq a s u)
  | leibG {Γ hs} (a : HTy) {s t : HTerm Γ a} (φ : HTerm (a :: Γ) .o) : okL a φ s t →
      DG T ok okL Γ hs (.eq a s t) → DG T ok okL Γ hs (inst φ s) → DG T ok okL Γ hs (inst φ t)
  | funExt {Γ hs a b} {f g : HTerm Γ (.L (.arr a b))} :
      DG T ok okL Γ hs (.all (.L a) (.eq (.L b) (.appL (wk f) var0) (.appL (wk g) var0))) →
      DG T ok okL Γ hs (.eq (.L (.arr a b)) f g)
  | funApp {Γ hs a b} {f g : HTerm Γ (.L (.arr a b))} :
      DG T ok okL Γ hs (.eq (.L (.arr a b)) f g) →
      DG T ok okL Γ hs (.all (.L a) (.eq (.L b) (.appL (wk f) var0) (.appL (wk g) var0)))
  | wExt {Γ hs} {p q : HTerm Γ (.L .s)} :
      DG T ok okL Γ hs (.all .w (.eq .o (.holds (wk p) var0) (.holds (wk q) var0))) →
      DG T ok okL Γ hs (.eq (.L .s) p q)
  | wApp {Γ hs} {p q : HTerm Γ (.L .s)} :
      DG T ok okL Γ hs (.eq (.L .s) p q) →
      DG T ok okL Γ hs (.all .w (.eq .o (.holds (wk p) var0) (.holds (wk q) var0)))
  | propExt {Γ hs φ ψ} : DG T ok okL Γ (φ :: hs) ψ → DG T ok okL Γ (ψ :: hs) φ →
      DG T ok okL Γ hs (.eq .o φ ψ)
  | betaL {Γ hs a b} (body : HTerm (.L a :: Γ) (.L b)) (x : HTerm Γ (.L a)) :
      DG T ok okL Γ hs (.eq (.L b) (.appL (.lamL body) x) (inst body x))
  | betaWI {Γ hs} (φ : HTerm (.w :: Γ) .o) (i : HTerm Γ .w) :
      DG T ok okL Γ hs (inst φ i) → DG T ok okL Γ hs (.holds (.wabs φ) i)
  | betaWE {Γ hs} (φ : HTerm (.w :: Γ) .o) (i : HTerm Γ .w) :
      DG T ok okL Γ hs (.holds (.wabs φ) i) → DG T ok okL Γ hs (inst φ i)

/-- The whole-term calculus: `∀E`/`∃I` instances and Leibniz steps as in v4's hypothesis. -/
abbrev DW (T : Tm [] .s → Prop) := DG T (fun a t => Cert a t) (fun a φ s t => LeibOK a φ s t)

/-! ## A logical relation for relativised equality -/

/-- `LR t x y`: `x`, `y` send admitted `eqT`-equal arguments to related values. -/
def LR (S : Str W D) : (t : FTy) → Den W D t → Den W D t → Prop
  | .e, x, y => x = y
  | .s, x, y => x = y
  | .arr a b, F, G => ∀ z z', S.A a z → S.A a z' → eqT S a z z' → LR S b (F z) (G z')

def RH (S : Str W D) : (a : HTy) → HDen W D a → HDen W D a → Prop
  | .L t, x, y => LR S t x y
  | .w, x, y => x = y
  | .o, x, y => (x ↔ y)

theorem LR_eqT_iff (S : Str W D) : ∀ (t : FTy) {x x' y y' : Den W D t},
    LR S t x x' → LR S t y y' → (eqT S t x y ↔ eqT S t x' y')
  | .e, _, _, _, _, hx, hy => by
      show _ = _ ↔ _ = _
      have hx' : _ = _ := hx; have hy' : _ = _ := hy; rw [hx', hy']
  | .s, _, _, _, _, hx, hy => by
      show _ = _ ↔ _ = _
      have hx' : _ = _ := hx; have hy' : _ = _ := hy; rw [hx', hy']
  | .arr a b, x, x', y, y', hx, hy => by
      show (∀ z, S.A a z → eqT S b (x z) (y z)) ↔ (∀ z, S.A a z → eqT S b (x' z) (y' z))
      exact ⟨fun H z hz => (LR_eqT_iff S b (hx z z hz hz (eqT_refl S a z))
          (hy z z hz hz (eqT_refl S a z))).1 (H z hz),
        fun H z hz => (LR_eqT_iff S b (hx z z hz hz (eqT_refl S a z))
          (hy z z hz hz (eqT_refl S a z))).2 (H z hz)⟩

theorem adm_LR (S : Str W D) (hC : Closed S) (hR : Resp S) : ∀ (t : FTy) {x y : Den W D t},
    S.A t x → S.A t y → eqT S t x y → LR S t x y
  | .e, _, _, _, _, h => h
  | .s, _, _, _, _, h => h
  | .arr a b, F, G, hF, hG, h => fun z z' hz hz' hzz =>
      adm_LR S hC hR b (adm_app S hC F z hF hz) (adm_app S hC G z' hG hz')
        (eqT_trans S b (hR a b F hF z z' hz hz' hzz) (h z' hz'))

theorem envR_pull (S : Str W D) {ρ ρ' : HEnv W D Γ}
    (h : ∀ {b} (v : HVar Γ b), EqH S b (ρ v) (ρ' v)) :
    ∀ {Γ' : List FTy} (r : LRen Γ' Γ), EnvR S Γ' (pull r ρ) (pull r ρ')
  | [], _ => trivial
  | _ :: _, r => ⟨h (r .zero), envR_pull S h (fun v => r (.succ v))⟩

theorem rel_cons (S : Str W D) {ρ ρ' : HEnv W D Γ}
    (h : ∀ {b} (v : HVar Γ b), EqH S b (ρ v) (ρ' v)) {x x' : HDen W D a} (hx : EqH S a x x') :
    ∀ {b} (v : HVar (a :: Γ) b), EqH S b (cons x ρ v) (cons x' ρ' v) := by
  intro b v; cases v with
  | zero => exact hx
  | succ v => exact h v

/-- **Congruence for whole-term formulas**: a `WT` term sends pointwise `EqH`-related admitted
environments to `RH`-related values. -/
theorem cong (S : Str W D) (hE : ∀ x, S.A .e x) (hC : Closed S) (hR : Resp S) :
    ∀ {Γ a} (u : HTerm Γ a), WT u → ∀ (ρ ρ' : HEnv W D Γ), AdmEnv S ρ → AdmEnv S ρ' →
      (∀ {b} (v : HVar Γ b), EqH S b (ρ v) (ρ' v)) → RH S a (heval S u ρ) (heval S u ρ')
  | _, .L t, .var v, _, ρ, ρ', hA, hA', h => adm_LR S hC hR t (hA v) (hA' v) (h v)
  | _, .w, .var v, _, ρ, ρ', _, _, h => h v
  | _, .o, .var v, _, ρ, ρ', _, _, h => h v
  | _, _, .appL f x, hw, ρ, ρ', hA, hA', h => by
      obtain ⟨hf, hx⟩ : WT f ∧ Cert _ x := hw
      have hF := cong S hE hC hR f hf ρ ρ' hA hA' h
      have ha := cert_rng S hE hC hA _ x hx
      have ha' := cert_rng S hE hC hA' _ x hx
      obtain ⟨_, s, r, rfl⟩ := hx
      have e : eqT S _ (heval S (emb r s) ρ) (heval S (emb r s) ρ') := by
        rw [heval_emb S hE, heval_emb S hE]
        exact fund S hE hC hR s _ _ (envA_pull S hA r) (envA_pull S hA' r) (envR_pull S h r)
      exact hF _ _ ha ha' e
  | _, _, .lamL b, hb, ρ, ρ', hA, hA', h => fun z z' hz hz' hzz => by
      show RH S (.L _) (heval S b (cons (a := .L _) z ρ)) (heval S b (cons (a := .L _) z' ρ'))
      exact cong S hE hC hR b hb (cons z ρ) (cons z' ρ') (admEnv_cons S hA (a := .L _) hz) (admEnv_cons S hA' (a := .L _) hz')
        (rel_cons S h (a := .L _) hzz)
  | _, _, .pos, _, _, _, _, _, _ => adm_LR S hC hR th (hC (Γ := []) .pos () trivial)
      (hC (Γ := []) .pos () trivial) (eqT_refl S th _)
  | _, _, .wabs φ, hφ, ρ, ρ', hA, hA', h => by
      show (fun u => heval S φ (cons (a := .w) u ρ)) = (fun u => heval S φ (cons (a := .w) u ρ'))
      funext u; apply propext
      exact cong S hE hC hR φ hφ (cons u ρ) (cons u ρ') (admEnv_cons S hA (a := .w) trivial)
        (admEnv_cons S hA' (a := .w) trivial) (rel_cons S h (a := .w) rfl)
  | _, _, .holds p i, hw, ρ, ρ', hA, hA', h => by
      simp only [WT] at hw; obtain ⟨hp, hi⟩ := hw
      have e1 : heval S p ρ = heval S p ρ' := cong S hE hC hR p hp ρ ρ' hA hA' h
      have e2 : heval S i ρ = heval S i ρ' := cong S hE hC hR i hi ρ ρ' hA hA' h
      show heval S p ρ (heval S i ρ) ↔ heval S p ρ' (heval S i ρ')
      rw [e1, e2]
  | _, _, .rel i j, hw, ρ, ρ', hA, hA', h => by
      simp only [WT] at hw; obtain ⟨hi, hj⟩ := hw
      have e1 : heval S i ρ = heval S i ρ' := cong S hE hC hR i hi ρ ρ' hA hA' h
      have e2 : heval S j ρ = heval S j ρ' := cong S hE hC hR j hj ρ ρ' hA hA' h
      show S.R (heval S i ρ) (heval S j ρ) ↔ S.R (heval S i ρ') (heval S j ρ')
      rw [e1, e2]
  | _, _, .act x i, hw, ρ, ρ', hA, hA', h => by
      simp only [WT] at hw; obtain ⟨hx, hi⟩ := hw
      have e1 : heval S x ρ = heval S x ρ' := cong S hE hC hR x hx ρ ρ' hA hA' h
      have e2 : heval S i ρ = heval S i ρ' := cong S hE hC hR i hi ρ ρ' hA hA' h
      show S.act (heval S x ρ) (heval S i ρ) ↔ S.act (heval S x ρ') (heval S i ρ')
      rw [e1, e2]
  | _, _, .bot, _, _, _, _, _, _ => Iff.rfl
  | _, _, .imp p q, hw, ρ, ρ', hA, hA', h => by
      simp only [WT] at hw; obtain ⟨hp, hq⟩ := hw
      exact imp_congr (cong S hE hC hR p hp ρ ρ' hA hA' h) (cong S hE hC hR q hq ρ ρ' hA hA' h)
  | _, _, .and p q, hw, ρ, ρ', hA, hA', h => by
      simp only [WT] at hw; obtain ⟨hp, hq⟩ := hw
      exact and_congr (cong S hE hC hR p hp ρ ρ' hA hA' h) (cong S hE hC hR q hq ρ ρ' hA hA' h)
  | _, _, .or p q, hw, ρ, ρ', hA, hA', h => by
      simp only [WT] at hw; obtain ⟨hp, hq⟩ := hw
      exact or_congr (cong S hE hC hR p hp ρ ρ' hA hA' h) (cong S hE hC hR q hq ρ ρ' hA hA' h)
  | _, _, .all a p, hp, ρ, ρ', hA, hA', h => by
      have e : ∀ x, Rng S a x → (heval S p (cons x ρ) ↔ heval S p (cons x ρ')) := fun x hx =>
        cong S hE hC hR p hp (cons x ρ) (cons x ρ') (admEnv_cons S hA hx) (admEnv_cons S hA' hx)
          (rel_cons S h (EqH_refl S a x))
      exact ⟨fun H x hx => (e x hx).1 (H x hx), fun H x hx => (e x hx).2 (H x hx)⟩
  | _, _, .ex a p, hp, ρ, ρ', hA, hA', h => by
      have e : ∀ x, Rng S a x → (heval S p (cons x ρ) ↔ heval S p (cons x ρ')) := fun x hx =>
        cong S hE hC hR p hp (cons x ρ) (cons x ρ') (admEnv_cons S hA hx) (admEnv_cons S hA' hx)
          (rel_cons S h (EqH_refl S a x))
      exact ⟨fun ⟨x, hx, H⟩ => ⟨x, hx, (e x hx).1 H⟩, fun ⟨x, hx, H⟩ => ⟨x, hx, (e x hx).2 H⟩⟩
  | _, _, .eq (.L t) s u, hw, ρ, ρ', hA, hA', h => by
      simp only [WT] at hw; obtain ⟨hs, hu⟩ := hw
      exact LR_eqT_iff S t (cong S hE hC hR s hs ρ ρ' hA hA' h) (cong S hE hC hR u hu ρ ρ' hA hA' h)
  | _, _, .eq .w s u, hw, ρ, ρ', hA, hA', h => by
      simp only [WT] at hw; obtain ⟨hs, hu⟩ := hw
      have e1 : heval S s ρ = heval S s ρ' := cong S hE hC hR s hs ρ ρ' hA hA' h
      have e2 : heval S u ρ = heval S u ρ' := cong S hE hC hR u hu ρ ρ' hA hA' h
      show heval S s ρ = heval S u ρ ↔ heval S s ρ' = heval S u ρ'
      rw [e1, e2]
  | _, _, .eq .o s u, hw, ρ, ρ', hA, hA', h => by
      simp only [WT] at hw; obtain ⟨hs, hu⟩ := hw
      have e1 := cong S hE hC hR s hs ρ ρ' hA hA' h
      have e2 := cong S hE hC hR u hu ρ ρ' hA hA' h
      show (heval S s ρ ↔ heval S u ρ) ↔ (heval S s ρ' ↔ heval S u ρ')
      exact iff_congr e1 e2

/-! ## Soundness of the whole-term calculus -/

theorem sound_wt (S : Str W D) (hE : ∀ x, S.A .e x) (hC : Closed S) (hR : Resp S)
    {T : Tm [] .s → Prop} (hT : ∀ φ, T φ → ∀ w, eval S φ () w) :
    ∀ {Γ hs φ}, DW T Γ hs φ →
      ∀ (ρ : HEnv W D Γ), AdmEnv S ρ → (∀ h ∈ hs, heval S h ρ) → heval S φ ρ := by
  intro Γ hs φ d
  induction d with
  | hyp m => exact fun ρ _ hh => hh _ m
  | ax φ i hφ =>
      intro ρ _ _
      show heval S (emb nilR φ) ρ (heval S i ρ)
      rw [heval_emb S hE]; exact hT φ hφ _
  | impI _ ih => exact fun ρ hρ hh hφ => ih ρ hρ (fun h m => by
      rcases List.mem_cons.1 m with rfl | m
      · exact hφ
      · exact hh h m)
  | impE _ _ ih1 ih2 => exact fun ρ hρ hh => ih1 ρ hρ hh (ih2 ρ hρ hh)
  | byContra _ ih =>
      intro ρ hρ hh
      apply Classical.byContradiction
      intro hn
      exact ih ρ hρ (fun h m => by
        rcases List.mem_cons.1 m with rfl | m
        · exact hn
        · exact hh h m)
  | andI _ _ ih1 ih2 => exact fun ρ hρ hh => ⟨ih1 ρ hρ hh, ih2 ρ hρ hh⟩
  | andL _ ih => exact fun ρ hρ hh => (ih ρ hρ hh).1
  | andR _ ih => exact fun ρ hρ hh => (ih ρ hρ hh).2
  | orL _ ih => exact fun ρ hρ hh => Or.inl (ih ρ hρ hh)
  | orR _ ih => exact fun ρ hρ hh => Or.inr (ih ρ hρ hh)
  | orE _ _ _ ih ih1 ih2 =>
      intro ρ hρ hh
      rcases ih ρ hρ hh with h | h
      · exact ih1 ρ hρ fun k m => by
          rcases List.mem_cons.1 m with rfl | m
          · exact h
          · exact hh k m
      · exact ih2 ρ hρ fun k m => by
          rcases List.mem_cons.1 m with rfl | m
          · exact h
          · exact hh k m
  | allI a _ ih =>
      intro ρ hρ hh x hx
      exact ih (cons x ρ) (admEnv_cons S hρ hx) fun k m => by
        obtain ⟨k', m', rfl⟩ := mem_map_wk m
        rw [heval_wk]; exact hh k' m'
  | allE a t _ hok ih =>
      intro ρ hρ hh
      rw [heval_inst]
      exact ih ρ hρ hh _ (cert_rng S hE hC hρ a t hok)
  | exI a t hok _ ih =>
      intro ρ hρ hh
      have := ih ρ hρ hh
      rw [heval_inst] at this
      exact ⟨_, cert_rng S hE hC hρ a t hok, this⟩
  | exE a _ _ ih1 ih2 =>
      intro ρ hρ hh
      obtain ⟨x, hx, hφ⟩ := ih1 ρ hρ hh
      have := ih2 (cons x ρ) (admEnv_cons S hρ hx) fun k m => by
        rcases List.mem_cons.1 m with rfl | m
        · exact hφ
        · obtain ⟨k', m', rfl⟩ := mem_map_wk m
          rw [heval_wk]; exact hh k' m'
      rwa [heval_wk] at this
  | refl a t => exact fun ρ _ _ => EqH_refl S a _
  | symm a _ ih => exact fun ρ hρ hh => EqH_symm S a (ih ρ hρ hh)
  | trans a _ _ ih1 ih2 => exact fun ρ hρ hh => EqH_trans S a (ih1 ρ hρ hh) (ih2 ρ hρ hh)
  | @leibG Γ _ a s t φ hok _ _ ih1 ih2 =>
      intro ρ hρ hh
      have e : EqH S a (heval S s ρ) (heval S t ρ) := ih1 ρ hρ hh
      have d := ih2 ρ hρ hh
      rw [heval_inst] at d ⊢
      rcases hok with hp | ⟨hφ, hs, ht⟩
      · rwa [← EqH_plain S hE a hp e]
      · exact (cong S hE hC hR φ hφ (cons (heval S s ρ) ρ) (cons (heval S t ρ) ρ)
          (admEnv_cons S hρ (cert_rng S hE hC hρ a s hs))
          (admEnv_cons S hρ (cert_rng S hE hC hρ a t ht))
          (rel_cons S (fun v => EqH_refl S _ (ρ v)) e)).1 d
  | funExt _ ih =>
      intro ρ hρ hh z hz
      have := ih ρ hρ hh z hz
      simpa only [heval, heval_wk, var0, cons, EqH] using this
  | funApp _ ih =>
      intro ρ hρ hh z hz
      have := ih ρ hρ hh z hz
      simpa only [heval, heval_wk, var0, cons, EqH] using this
  | wExt _ ih =>
      intro ρ hρ hh
      funext u
      have := ih ρ hρ hh u trivial
      simp only [heval, heval_wk, cons, EqH] at this
      exact propext this
  | wApp _ ih =>
      intro ρ hρ hh u _
      have := ih ρ hρ hh
      simp only [heval, heval_wk, cons, EqH]
      show _ ↔ _
      exact Iff.of_eq (congrFun this u)
  | propExt _ _ ih1 ih2 =>
      intro ρ hρ hh
      constructor
      · intro h; exact ih1 ρ hρ fun k m => by
          rcases List.mem_cons.1 m with rfl | m
          · exact h
          · exact hh k m
      · intro h; exact ih2 ρ hρ fun k m => by
          rcases List.mem_cons.1 m with rfl | m
          · exact h
          · exact hh k m
  | betaL body x =>
      intro ρ _ _
      show eqT S _ _ _
      simp only [heval, heval_inst]
      exact eqT_refl S _ _
  | betaWI φ i _ ih =>
      intro ρ hρ hh
      have := ih ρ hρ hh
      rw [heval_inst] at this
      exact this
  | betaWE φ i _ ih =>
      intro ρ hρ hh
      rw [heval_inst]
      exact ih ρ hρ hh

/-- **v4 `prop:lgeneral`, deep form.**  A derivation of `⟦φ⟧` at a world variable from the
`𝓛`-theory `T`, with Leibniz at every type and every motive, whose `∀E`/`∃I` instances at types
of `𝓛` are terms of `𝓛` and whose Leibniz steps at non-plain types have whole-term motives and
`𝓛`-term sides, makes `φ` true at every world of every v4 `𝓛`-general model of `T` with
nonempty individuals. -/
theorem sound_v4_wt {T : Tm [] .s → Prop} {φ : Tm [] .s}
    (d : DW T [.w] [] (.holds (emb nilR φ) var0)) : ValidV4 T φ := by
  refine (valid_iff T φ).2 fun _ _ S _ hE hC hR hT w => ?_
  have := sound_wt S hE hC hR hT d (cons (a := .w) w emptyEnv)
    (admEnv_cons (a := .w) S (fun v => by cases v) trivial) (fun _ m => by cases m)
  simp only [heval, heval_emb S hE] at this
  exact this

/-! ## K4's calculus is a fragment; by completeness, the two derive the same 𝓛-sentences -/

theorem wt_w : ∀ {Γ} (i : HTerm Γ .w), WT i
  | _, .var _ => trivial

theorem wt_emb : ∀ {Γ' Γ t} (r : LRen Γ' Γ) (tm : Tm Γ' t), WT (emb r tm)
  | _, _, _, _, .var _ => trivial
  | _, _, _, r, .app F x => ⟨wt_emb r F, ⟨_, x, r, rfl⟩⟩
  | _, _, _, r, .lam b => wt_emb (liftL r) b
  | _, _, _, _, .top => ⟨trivial, trivial⟩
  | _, _, _, _, .bot => trivial
  | _, _, _, r, .neg x => ⟨⟨wt_emb _ x, trivial⟩, trivial⟩
  | _, _, _, r, .and x y => ⟨⟨wt_emb _ x, trivial⟩, ⟨wt_emb _ y, trivial⟩⟩
  | _, _, _, r, .or x y => ⟨⟨wt_emb _ x, trivial⟩, ⟨wt_emb _ y, trivial⟩⟩
  | _, _, _, r, .imp x y => ⟨⟨wt_emb _ x, trivial⟩, ⟨wt_emb _ y, trivial⟩⟩
  | _, _, _, r, .box x => ⟨⟨trivial, trivial⟩, ⟨wt_emb _ x, trivial⟩⟩
  | _, _, _, r, .all a b => ⟨wt_emb _ b, trivial⟩
  | _, _, _, r, .ex a b => ⟨wt_emb _ b, trivial⟩
  | _, _, _, r, .allE b => ⟨⟨trivial, trivial⟩, ⟨wt_emb _ b, trivial⟩⟩
  | _, _, _, r, .exE b => ⟨⟨trivial, trivial⟩, ⟨wt_emb _ b, trivial⟩⟩
  | _, _, _, r, .eq a x y => ⟨wt_emb _ x, wt_emb _ y⟩
  | _, _, _, _, .pos => trivial

theorem of_DC {T : Tm [] .s → Prop} : ∀ {Γ hs φ}, DC T Γ hs φ → DW T Γ hs φ := by
  intro Γ hs φ d
  induction d with
  | hyp m => exact .hyp m
  | ax φ i h => exact .ax φ i h
  | impI _ ih => exact .impI ih
  | impE _ _ ih1 ih2 => exact .impE ih1 ih2
  | byContra _ ih => exact .byContra ih
  | andI _ _ ih1 ih2 => exact .andI ih1 ih2
  | andL _ ih => exact .andL ih
  | andR _ ih => exact .andR ih
  | orL _ ih => exact .orL ih
  | orR _ ih => exact .orR ih
  | orE _ _ _ ih ih1 ih2 => exact .orE ih ih1 ih2
  | allI a _ ih => exact .allI a ih
  | allE a t _ hok ih => exact .allE a t ih hok
  | exI a t hok _ ih => exact .exI a t hok ih
  | exE a _ _ ih1 ih2 => exact .exE a ih1 ih2
  | refl a t => exact .refl a t
  | symm a _ ih => exact .symm a ih
  | trans a _ _ ih1 ih2 => exact .trans a ih1 ih2
  | subst a φ hp _ _ ih1 ih2 => exact .leibG a φ (.inl hp) ih1 ih2
  | funExt _ ih => exact .funExt ih
  | funApp _ ih => exact .funApp ih
  | wExt _ ih => exact .wExt ih
  | wApp _ ih => exact .wApp ih
  | propExt _ _ ih1 ih2 => exact .propExt ih1 ih2
  | betaL body x => exact .betaL body x
  | betaWI φ i _ ih => exact .betaWI φ i ih
  | betaWE φ i _ ih => exact .betaWE φ i ih
  | leib a r M i hs ht _ _ ih1 ih2 =>
      exact .leibG (.L a) _ (.inr ⟨⟨wt_emb _ M, wt_w _⟩, hs, ht⟩) ih1 ih2

/-- **Sound and complete, and conservative over K4's calculus**: for every `𝓛`-theory `T`, the
whole-term calculus derives `⟦φ⟧` from `T ∪ {∃x.⊤}` iff K4's certified calculus does iff `φ`
holds in every v4 `𝓛`-general model of `T` with nonempty individuals. -/
theorem wt_sound_complete {T : Tm [] .s → Prop} {φ : Tm [] .s} :
    (DW (withNE T) [.w] [] (.holds (emb nilR φ) var0) ↔ ValidV4 T φ) ∧
    (DW (withNE T) [.w] [] (.holds (emb nilR φ) var0) ↔ DC (withNE T) [.w] [] (.holds (emb nilR φ) var0)) :=
  have h1 : DW (withNE T) [.w] [] (.holds (emb nilR φ) var0) ↔ ValidV4 T φ :=
    ⟨fun d => validV4_withNE.1 (sound_v4_wt d), fun H => of_DC (sound_complete_all.2 H)⟩
  ⟨h1, h1.trans sound_complete_all.symm⟩

end Programme.«20261022-1724-ontological».ThWhole

#print axioms Programme.«20261022-1724-ontological».ThWhole.cong
#print axioms Programme.«20261022-1724-ontological».ThWhole.sound_wt
#print axioms Programme.«20261022-1724-ontological».ThWhole.sound_v4_wt
#print axioms Programme.«20261022-1724-ontological».ThWhole.of_DC
#print axioms Programme.«20261022-1724-ontological».ThWhole.wt_sound_complete
