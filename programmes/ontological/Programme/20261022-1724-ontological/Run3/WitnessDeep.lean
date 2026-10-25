import Programme.«20261022-1724-ontological».Run3.SepLS
/-! # WitnessDeep.lean (th, run 3, round 10): target C (d) in deep form

Lines after this header: pr's `SepLS.lean` (K14 evidence; contains K8's `sep_not_valid_v4` and K12/K13's
`Canon`/`LS`) minus its final `#print`, then th's `WholeTerm.lean` section `Programme.ThWhole` (round 9:
`DG`, `DW`, `sound_v4_wt`, `of_DC`) minus `#print`s, both verbatim; then section `Programme.ThWit`:
the witness-only calculus `DG3` derives v4's separating sentence from every theory. -/

/-! # SepLS.lean (pr, run 3, round 9)

`DeepSep.lean` (K11, minus `#print`s) verbatim, then th's `LS.lean` from `namespace Programme.ThHenkin`
to its end (K12 completeness, LS, compactness; minus `#print`s) verbatim, then section `Programme.Run3.SepLS`:
the separating sentence has a countermodel of variant 2 with countably many worlds and countable carriers,
and no countermodel with finitely many worlds. -/

-- [cleanup 2026-10-23] shared block (7193 lines) now imported from Programme.«20261022-1724-ontological».Run3.SepLS





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


namespace Programme.«20261022-1724-ontological».ThWit
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX Programme.«20261022-1724-ontological».Run3.V4 Programme.«20261022-1724-ontological».ThCanon Programme.«20261022-1724-ontological».ThWhole

/-- `D p := ∃q. ¬q ∧ ((q ∧ p) ≠ ⊥)`, `p` the variable `0`. -/
def dT : Tm (.s :: Γ') .s :=
  .ex .s (.and (.neg (.var .zero)) (.neg (.eq .s (.and (.var .zero) (.var (.succ .zero))) .bot)))
/-- `Atom p := (p ≠ ⊥) ∧ ¬((p ∧ D p) ≠ ⊥)`. -/
def atT : Tm (.s :: Γ') .s :=
  .and (.neg (.eq .s (.var .zero) .bot)) (.neg (.neg (.eq .s (.and (.var .zero) dT) .bot)))
def bodyT : Tm (.s :: Γ') .s := .and atT (.var .zero)
/-- `∃p. Atom p ∧ p`. -/
def XT : Tm Γ' .s := .ex .s bodyT
/-- `A ∃p. (Atom p ∧ p)`. -/
def phiT : Tm Γ' .s := .eq .s XT .top

theorem phiT_eq : (phiT : Tm [] .s) = Programme.«20261022-1724-ontological».Run3.SepV2.Sep.phiSep := rfl

/-- `F := λp. (Atom p ∧ p) ∧ ¬X` and `G := λp. ⊥`, closed terms of `𝓛` of type `σ → σ`. -/
def FT : Tm Γ' (.arr .s .s) := .lam (.and bodyT (.neg XT))
def GT : Tm Γ' (.arr .s .s) := .lam .bot

variable {T : Tm [] .s → Prop}

theorem wk_emb {Γ' : List FTy} {Γ : List HTy} (r : LRen Γ' Γ) (x : Tm Γ' t) :
    wk (b := b) (emb r x) = emb (shL r) x :=
  rename_emb x _ r (shL r) (fun _ => rfl)

/-- Extensionality at `σ` for embedded terms. -/
theorem L_ext {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)} {r : LRen Γ' Γ} {x y : Tm Γ' .s}
    (d1 : DC T (.w :: Γ) (Lf (shL r) x var0 :: hs.map wk) (Lf (shL r) y var0))
    (d2 : DC T (.w :: Γ) (Lf (shL r) y var0 :: hs.map wk) (Lf (shL r) x var0)) :
    DC T Γ hs (.eq (.L .s) (emb r x) (emb r y)) := by
  refine Deriv.wExt (Deriv.allI _ (Deriv.propExt ?_ ?_))
  · rw [wk_emb, wk_emb]; exact d1
  · rw [wk_emb, wk_emb]; exact d2

theorem hyp0 {Γ : List HTy} {hs : List (HTerm Γ .o)} {φ : HTerm Γ .o} : DC T Γ (φ :: hs) φ :=
  Deriv.hyp (List.mem_cons_self ..)

/-- `F = G` in K4's certified calculus (every quantifier instance a term of `𝓛`). -/
theorem FG {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)} (r : LRen Γ' Γ) :
    DC T Γ hs (.eq (.L (.arr .s .s)) (emb r FT) (emb r GT)) := by
  refine Deriv.funExt (Deriv.allI _ ?_)
  show DC T _ _ (.eq (.L .s) (emb (liftL r) (.app FT (.var .zero))) (emb (liftL r) (.app GT (.var .zero))))
  refine L_ext ?_ ?_
  · have h0 : DC T _ (Lf (shL (liftL r)) (.app FT (.var .zero)) var0 :: (hs.map wk).map wk) (Lf (shL (liftL r)) (instL (Γ := .s :: Γ') (.and bodyT (.neg XT)) (.var .zero)) var0) :=
      L_betaE hyp0
    have h := L_andE (x := bodyT) (y := .neg XT) h0
    have hb := Deriv.andL h
    have hn := L_negE (Deriv.andR h)
    exact Deriv.exFalso (Deriv.impE hn (L_exI (b := bodyT) (.var .zero) hb))
  · exact L_botE (L_betaE (b := .bot) hyp0)

/-- Witness criterion alone: `∀E`/`∃I` instances at types of `𝓛` are terms of `𝓛`, Leibniz unrestricted. -/
abbrev DG3 (T : Tm [] .s → Prop) := DG T (fun a t => Cert a t) (fun _ _ _ _ => True)

theorem DG.mono {T : Tm [] .s → Prop} {ok : ∀ {Γ : List HTy} (a : HTy), HTerm Γ a → Prop}
    {okL okL' : ∀ {Γ : List HTy} (a : HTy), HTerm (a :: Γ) .o → HTerm Γ a → HTerm Γ a → Prop}
    (hL : ∀ {Γ : List HTy} (a : HTy) (φ : HTerm (a :: Γ) .o) s t, okL a φ s t → okL' a φ s t) :
    ∀ {Γ hs φ}, DG T ok okL Γ hs φ → DG T ok okL' Γ hs φ := by
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
  | leibG a φ h _ _ ih1 ih2 => exact .leibG a φ (hL a φ _ _ h) ih1 ih2
  | funExt _ ih => exact .funExt ih
  | funApp _ ih => exact .funApp ih
  | wExt _ ih => exact .wExt ih
  | wApp _ ih => exact .wApp ih
  | propExt _ _ ih1 ih2 => exact .propExt ih1 ih2
  | betaL body x => exact .betaL body x
  | betaWI φ i _ ih => exact .betaWI φ i ih
  | betaWE φ i _ ih => exact .betaWE φ i ih

/-- K4's certified calculus is a fragment of the witness-only calculus. -/
theorem lift {Γ hs φ} (d : DC T Γ hs φ) : DG3 T Γ hs φ :=
  DG.mono (fun _ _ _ _ _ => trivial) (of_DC d)

/-- The nominal `λv. v = u` of the world variable `u` (not a term of `𝓛`). -/
def Nom : HTerm (.w :: Γ0) (.L .s) := .wabs (.eq .w var0 (.var (.succ .zero)))

/-- Normalise substitutions and embeddings in the goal. -/
macro "nrm" : tactic => `(tactic| simp only [inst, subst, sub0, liftS, wk, rename, liftR, emb, shL, liftL,
  XT, bodyT, atT, dT, Nom, Lf, FT, GT, List.map_cons])
macro "nrm" "at" h:ident : tactic => `(tactic| simp only [inst, subst, sub0, liftS, wk, rename, liftR, emb,
  shL, liftL, XT, bodyT, atT, dT, Nom, Lf, FT, GT, List.map_cons] at $h:ident)

theorem withHyp {Γ : List HTy} {hs : List (HTerm Γ .o)} {φ ψ : HTerm Γ .o}
    (k : DG3 T Γ (φ :: hs) φ → DG3 T Γ (φ :: hs) ψ) : DG3 T Γ (φ :: hs) ψ :=
  k (DG.hyp (List.mem_cons_self ..))

theorem withHyp12 {Γ : List HTy} {hs : List (HTerm Γ .o)} {φ φ' ψ : HTerm Γ .o}
    (k : DG3 T Γ (φ :: φ' :: hs) φ → DG3 T Γ (φ :: φ' :: hs) φ' → DG3 T Γ (φ :: φ' :: hs) ψ) :
    DG3 T Γ (φ :: φ' :: hs) ψ :=
  k (DG.hyp (List.mem_cons_self ..)) (DG.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem withHyp123 {Γ : List HTy} {hs : List (HTerm Γ .o)} {φ φ' φ'' ψ : HTerm Γ .o}
    (k : DG3 T Γ (φ :: φ' :: φ'' :: hs) φ → DG3 T Γ (φ :: φ' :: φ'' :: hs) φ' →
      DG3 T Γ (φ :: φ' :: φ'' :: hs) φ'' → DG3 T Γ (φ :: φ' :: φ'' :: hs) ψ) :
    DG3 T Γ (φ :: φ' :: φ'' :: hs) ψ :=
  k (DG.hyp (List.mem_cons_self ..)) (DG.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (DG.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

/-- Ex falso from the second hypothesis `⊥` at a world (`⟦⊥⟧ i`). -/
theorem botHyp {Γ : List HTy} {hs : List (HTerm Γ .o)} {i : HTerm Γ .w} {ψ : HTerm Γ .o} :
    DG3 T Γ (.holds (.wabs .bot) i :: hs) ψ :=
  DG.byContra (DG.betaWE _ _ (DG.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

/-- The cut rule. -/
theorem cutG {Γ : List HTy} {hs : List (HTerm Γ .o)} {φ ψ : HTerm Γ .o}
    (d : DG3 T Γ hs φ) (k : DG3 T Γ (φ :: hs) ψ) : DG3 T Γ hs ψ := DG.impE (DG.impI k) d

theorem cut2 {Γ : List HTy} {hs : List (HTerm Γ .o)} {φ φ' ψ : HTerm Γ .o}
    (d : DG3 T Γ hs φ) (d' : DG3 T Γ hs φ') (k : DG3 T Γ (φ' :: φ :: hs) ψ) : DG3 T Γ hs ψ :=
  DG.impE (DG.impE (DG.impI (DG.impI k)) d) d'

/-- `(F N)(u)` for the nominal `N` of `u`, given `¬X(u)`: `N` is an atom true at `u`. -/
theorem FN {Γ0 : List HTy} {hs : List (HTerm (.w :: Γ0) .o)} :
    DG3 T (.w :: Γ0) (.imp (Lf nilR XT var0) .bot :: hs) (.holds (.appL (emb nilR FT) Nom) var0) := by
  have e := DG.betaL (T := T) (ok := fun a t => Cert a t) (okL := fun _ _ _ _ => True)
    (hs := .imp (Lf nilR XT var0) .bot :: hs) (emb (liftL nilR) (.and bodyT (.neg XT))) Nom
  refine DG.leibG (.L .s) (.holds var0 (.var (.succ .zero))) trivial (DG.symm _ e) ?_
  refine DG.betaWI _ _ ?_
  refine DG.andI ?_ ?_
  · refine DG.betaWI _ _ (DG.andI ?_ (DG.betaWI _ _ (DG.refl .w var0)))
    refine DG.betaWI _ _ (DG.andI ?_ ?_)
    · -- `N ≠ ⊥` at `u`
      refine DG.betaWI _ _ (DG.impI ?_)
      nrm
      refine withHyp fun h => ?_
      have h1 := DG.betaWE _ _ h
      nrm at h1
      have h3 := DG.allE .w var0 (DG.wApp h1) trivial
      nrm at h3
      exact DG.betaWE _ _ (DG.leibG .o var0 trivial h3 (DG.betaWI _ _ (DG.refl .w var0)))
    · -- `¬((N ∧ D N) ≠ ⊥)` at `u`
      refine DG.betaWI _ _ (DG.impI ?_)
      nrm
      refine withHyp fun h => ?_
      have h1 := DG.betaWE _ _ h
      nrm at h1
      refine DG.impE h1 (DG.betaWI _ _ ?_)
      nrm
      refine DG.wExt (DG.allI _ (DG.propExt ?_ botHyp))
      nrm
      refine withHyp fun h => ?_
      have h2 := DG.betaWE _ _ h
      nrm at h2
      have hvu := DG.betaWE _ _ (DG.andL h2)
      nrm at hvu
      have hD := DG.betaWE _ _ (DG.andR h2)
      nrm at hD
      refine DG.exE _ hD ?_
      nrm
      refine withHyp12 fun hq0 hh => ?_
      have hq := DG.betaWE _ _ hq0
      nrm at hq
      have h2' := DG.betaWE _ _ hh
      nrm at h2'
      have hvu := DG.betaWE _ _ (DG.andL h2')
      nrm at hvu
      have hnq := DG.betaWE _ _ (DG.andL hq)
      nrm at hnq
      have hne := DG.betaWE _ _ (DG.andR hq)
      nrm at hne
      refine DG.betaWI _ _ (DG.impE hne ?_)
      refine cut2 hvu hnq ?_
      refine DG.betaWI _ _ ?_
      nrm
      refine DG.wExt (DG.allI _ (DG.propExt ?_ botHyp))
      nrm
      refine withHyp123 fun ht hnq' hvu' => ?_
      have h5 := DG.betaWE _ _ ht
      nrm at h5
      have htu := DG.betaWE _ _ (DG.andR h5)
      nrm at htu
      have hqv := DG.leibG .w (.holds (.var (.succ (.succ .zero))) var0) trivial
        (DG.trans .w htu (DG.symm .w hvu')) (DG.andL h5)
      exact DG.betaWI _ _ (DG.impE hnq' hqv)
  · refine DG.betaWI _ _ ?_
    nrm
    exact DG.hyp (List.mem_cons_self ..)

/-- **The separating body `X = ∃p. Atom p ∧ p` at any world variable**, in the witness-only
calculus, from any theory.  The single step outside v4's whole-term hypothesis is a Leibniz
step at `σ → σ` from `F = G` (both sides closed terms of `𝓛`) whose motive `f(N)(u)` applies the
hole to the nominal `N = λv. v = u`. -/
theorem sepX {Γ0 : List HTy} {hs : List (HTerm (.w :: Γ0) .o)} :
    DG3 T (.w :: Γ0) hs (Lf nilR XT var0) := by
  refine DG.byContra ?_
  have h := DG.leibG (.L (.arr .s .s)) (.holds (.appL var0 (wk Nom)) (.var (.succ .zero))) trivial
    (lift (FG (T := T) (hs := .imp (Lf nilR XT var0) .bot :: hs) nilR)) FN
  nrm at h
  have eb := DG.betaL (T := T) (ok := fun a t => Cert a t) (okL := fun _ _ _ _ => True)
    (hs := .imp (Lf nilR XT var0) .bot :: hs) (.wabs .bot) (Nom (Γ0 := Γ0))
  nrm at eb
  exact DG.betaWE _ _ (DG.leibG (.L .s) (.holds var0 (.var (.succ .zero))) trivial eb h)

/-- **v4's separating sentence `A ∃p.(Atom p ∧ p)` is derivable from every theory in the
witness-only calculus.** -/
theorem sep_deep : DG3 T [.w] [] (.holds (emb nilR phiT) var0) := by
  refine DG.betaWI _ _ ?_
  nrm
  refine DG.wExt (DG.allI _ (DG.propExt ?_ ?_))
  · nrm
    exact DG.betaWI _ _ (DG.impI (DG.hyp (List.mem_cons_self ..)))
  · have := sepX (T := T) (Γ0 := [.w]) (hs := [.holds (emb (nilR (Γ := [.w, .w])) .top) var0])
    nrm at this
    nrm
    exact this

/-- The nominal is not a term of `𝓛`. -/
theorem nom_not_cert {Γ : List HTy} {k : HTerm (.w :: Γ) .w} : ¬ Cert (.L .s) (HTerm.wabs (.eq .w var0 k)) := by
  rintro ⟨Γ', t, r, h⟩
  cases t <;> simp [emb] at h

/-- The one Leibniz step of `sepX` outside the plain types: its sides are terms of `𝓛`, its type is
not plain, and its motive is not whole-term, so it violates exactly v4's motive clause. -/
theorem step_profile {Γ0 : List HTy} :
    Cert (.L (.arr .s .s)) (emb (nilR (Γ := .w :: Γ0)) FT) ∧ Cert (.L (.arr .s .s)) (emb (nilR (Γ := .w :: Γ0)) GT) ∧
    plain (.L (.arr .s .s)) = false ∧
    ¬ LeibOK (.L (.arr .s .s)) (.holds (.appL var0 (wk (Nom (Γ0 := Γ0)))) (.var (.succ .zero)))
      (emb nilR FT) (emb nilR GT) := by
  refine ⟨cert_emb _ _, cert_emb _ _, rfl, ?_⟩
  rintro (h | ⟨⟨⟨_, hc⟩, _⟩, _⟩)
  · exact Bool.false_ne_true h
  · exact nom_not_cert (k := .var (.succ (.succ .zero))) hc

/-- **Target C (d), deep form: the witness criterion alone does not suffice for variant 2.**
The calculus whose `∀E`/`∃I` instances at types of `𝓛` are terms of `𝓛` but whose Leibniz steps are
unrestricted derives `A ∃p.(Atom p ∧ p)` from variant 2 (indeed from every theory), while the
sentence fails in a v4 `𝓛`-general model of variant 2 (K8); with v4's motive clause added
(`DW`) every derivation is sound (`sound_v4_wt`). -/
theorem witness_alone_unsound :
    DG3 Programme.«20261022-1724-ontological».Run3.SepV2.V2.T2 [.w] [] (.holds (emb nilR Programme.«20261022-1724-ontological».Run3.SepV2.Sep.phiSep) var0) ∧
    ¬ ValidV4 Programme.«20261022-1724-ontological».Run3.SepV2.V2.T2 Programme.«20261022-1724-ontological».Run3.SepV2.Sep.phiSep ∧
    ¬ (∀ φ : Tm [] .s, DG3 Programme.«20261022-1724-ontological».Run3.SepV2.V2.T2 [.w] [] (.holds (emb nilR φ) var0) →
        ValidV4 Programme.«20261022-1724-ontological».Run3.SepV2.V2.T2 φ) ∧
    (∀ φ : Tm [] .s, DW Programme.«20261022-1724-ontological».Run3.SepV2.V2.T2 [.w] [] (.holds (emb nilR φ) var0) →
        ValidV4 Programme.«20261022-1724-ontological».Run3.SepV2.V2.T2 φ) :=
  ⟨sep_deep, Programme.«20261022-1724-ontological».Run3.SepV2.V2.sep_not_valid_v4,
    fun H => Programme.«20261022-1724-ontological».Run3.SepV2.V2.sep_not_valid_v4 (H _ sep_deep), fun _ d => sound_v4_wt d⟩

end Programme.«20261022-1724-ontological».ThWit

#print axioms Programme.«20261022-1724-ontological».ThWit.FG
#print axioms Programme.«20261022-1724-ontological».ThWit.sepX
#print axioms Programme.«20261022-1724-ontological».ThWit.sep_deep
#print axioms Programme.«20261022-1724-ontological».ThWit.step_profile
#print axioms Programme.«20261022-1724-ontological».ThWit.witness_alone_unsound
