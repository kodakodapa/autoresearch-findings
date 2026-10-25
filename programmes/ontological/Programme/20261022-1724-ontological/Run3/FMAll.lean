import Programme.«20261022-1724-ontological».Run3.SepLS
/-! # FMAll.lean (th, run 3, round 11): target C (c), ex:separating at all types of 𝓛

Lines after this header up to `namespace Programme.ThFM`: pr's `SepLS.lean` (K14 evidence) minus its
final `#print`, verbatim.  It supplies `VM`, `LGen`, `ValidV4` (K9) and `phiSep`, `atomTm`, `dTm`,
`phiSep_iff`, `atom_iff`, `dTm_iff` (K8/K11).  New: namespace `Programme.ThFM`, v4's flip model with
the hereditarily finitely supported hierarchy `P_τ` at every type, built directly (not via K6's
carriers mod eqT). -/
/-! # SepLS.lean (pr, run 3, round 9)

`DeepSep.lean` (K11, minus `#print`s) verbatim, then th's `LS.lean` from `namespace Programme.ThHenkin`
to its end (K12 completeness, LS, compactness; minus `#print`s) verbatim, then section `Programme.Run3.SepLS`:
the separating sentence has a countermodel of variant 2 with countably many worlds and countable carriers,
and no countermodel with finitely many worlds. -/

-- [cleanup 2026-10-23] shared block (7193 lines) now imported from Programme.«20261022-1724-ontological».Run3.SepLS



namespace Programme.«20261022-1724-ontological».ThFM
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.SepR
open Programme.«20261022-1724-ontological».Run3.SepV2.Sep (phiSep atomTm dTm)

/-! ## v4's flip model at all types (ex:separating, literally)

Worlds: infinite 0-1-sequences.  The flip by `d` is `w ↦ w ⊕ d`; `G_n` = flips fixing the first `n`
coordinates (`Fix n d`).  The group acts on every type by conjugation; `P_τ` is the hereditarily
finitely supported hierarchy: at `σ` the sets fixed by some `G_n`, at `a → b` the functions
`P_a → P_b` fixed by some `G_n`.  One individual, every world sees every world, `Pos` empty. -/

abbrev Wd : Type := Nat → Bool

def dx (w d : Wd) : Wd := fun n => xor (w n) (d n)

def Fix (n : Nat) (d : Wd) : Prop := ∀ k, k < n → d k = false

theorem dx_dx (w d : Wd) : dx (dx w d) d = w := by
  funext n; simp [dx]

theorem dx_comm (w d e : Wd) : dx (dx w d) e = dx (dx w e) d := by
  funext n; simp only [dx]; cases w n <;> cases d n <;> cases e n <;> rfl

theorem dx_assoc (w d e : Wd) : dx (dx w e) d = dx w (dx d e) := by
  funext n; simp only [dx]; cases w n <;> cases d n <;> cases e n <;> rfl

theorem dx_zero (w : Wd) : dx w (fun _ => false) = w := by
  funext n; simp [dx]

theorem dx_self (d : Wd) : dx d d = fun _ => false := by
  funext n; simp [dx]

theorem dx_symm (d e : Wd) : dx d e = dx e d := by
  funext n; simp only [dx]; cases d n <;> cases e n <;> rfl

theorem fix_mono {n m : Nat} {d : Wd} (h : Fix m d) (hnm : n ≤ m) : Fix n d :=
  fun k hk => h k (Nat.lt_of_lt_of_le hk hnm)

/-- A set with an action of the flip group. -/
structure GS where
  car : Type
  act : Wd → car → car
  act_comp : ∀ d e x, act d (act e x) = act (dx d e) x
  act_zero : ∀ x, act (fun _ => false) x = x

theorem GS.inv (G : GS) (d : Wd) (x : G.car) : G.act d (G.act d x) = x := by
  rw [G.act_comp, dx_self, G.act_zero]

theorem GS.comm (G : GS) (d e : Wd) (x : G.car) : G.act d (G.act e x) = G.act e (G.act d x) := by
  rw [G.act_comp, G.act_comp, dx_symm]

def He : GS where
  car := Unit
  act _ x := x
  act_comp _ _ _ := rfl
  act_zero _ := rfl

/-- `P_σ`: the sets of worlds fixed by some `G_n` (the action `d · X = {w | X (w ⊕ d)}`). -/
def Hs : GS where
  car := {X : Wd → Prop // ∃ n, ∀ d, Fix n d → (fun w => X (dx w d)) = X}
  act d X := ⟨fun w => X.1 (dx w d), by
    obtain ⟨n, hn⟩ := X.2
    exact ⟨n, fun e he => funext fun w => by
      show X.1 (dx (dx w e) d) = X.1 (dx w d)
      rw [dx_comm]; exact congrFun (hn e he) (dx w d)⟩⟩
  act_comp d e X := Subtype.ext (funext fun w => by
    show X.1 (dx (dx w d) e) = X.1 (dx w (dx d e))
    rw [dx_comm, dx_assoc])
  act_zero X := Subtype.ext (funext fun w => by
    show X.1 (dx w _) = X.1 w
    rw [dx_zero])

/-- `P_{a→b}`: the functions `P_a → P_b` fixed by some `G_n` (conjugation `d · f = d ∘ f ∘ d⁻¹`). -/
def Harr (A B : GS) : GS where
  car := {f : A.car → B.car // ∃ n, ∀ d, Fix n d → ∀ x, B.act d (f (A.act d x)) = f x}
  act d f := ⟨fun x => B.act d (f.1 (A.act d x)), by
    obtain ⟨n, hn⟩ := f.2
    exact ⟨n, fun e he x => by
      show B.act e (B.act d (f.1 (A.act d (A.act e x)))) = B.act d (f.1 (A.act d x))
      rw [B.comm, A.comm, hn e he]⟩⟩
  act_comp d e f := Subtype.ext (funext fun x => by
    show B.act d (B.act e (f.1 (A.act e (A.act d x)))) = B.act (dx d e) (f.1 (A.act (dx d e) x))
    rw [B.act_comp, A.act_comp, dx_symm e d])
  act_zero f := Subtype.ext (funext fun x => by
    show B.act _ (f.1 (A.act _ x)) = f.1 x
    rw [A.act_zero, B.act_zero])

def H : FTy → GS
  | .e => He
  | .s => Hs
  | .arr a b => Harr (H a) (H b)

/-- Every object of the hierarchy is finitely supported. -/
theorem fs_all : ∀ (t : FTy) (x : (H t).car), ∃ n, ∀ d, Fix n d → (H t).act d x = x
  | .e, _ => ⟨0, fun _ _ => rfl⟩
  | .s, X => by
      obtain ⟨n, hn⟩ := X.2
      exact ⟨n, fun d hd => Subtype.ext (hn d hd)⟩
  | .arr _ _, f => by
      obtain ⟨n, hn⟩ := f.2
      exact ⟨n, fun d hd => Subtype.ext (funext (hn d hd))⟩

def botS : Hs.car := ⟨fun _ => False, 0, fun _ _ => rfl⟩

def posE : (H th).car :=
  ⟨fun _ => botS, 0, fun _ _ _ => Subtype.ext rfl⟩

/-- The model: total frame, one always-existing individual, empty positivity, carriers `P_τ`. -/
abbrev fm : VM Wd where
  R _ _ := True
  C t := (H t).car
  act _ _ := True
  pr X := X.1
  pr_inj _ _ h := Subtype.ext h
  ap f x := f.1 x
  ap_ext f g h := Subtype.ext (funext h)
  P := posE

/-! ### Equivariance of the term semantics -/

def envAct (d : Wd) : {Γ : List FTy} → VEnv fm Γ → VEnv fm Γ
  | [], _ => ()
  | t :: _, ρ => ((H t).act d ρ.1, envAct d ρ.2)

theorem env_fs : ∀ {Γ : List FTy} (ρ : VEnv fm Γ), ∃ n, ∀ d, Fix n d → envAct d ρ = ρ
  | [], _ => ⟨0, fun _ _ => rfl⟩
  | t :: _, ρ => by
      obtain ⟨n, hn⟩ := fs_all t ρ.1
      obtain ⟨m, hm⟩ := env_fs ρ.2
      refine ⟨max n m, fun d hd => ?_⟩
      show ((H t).act d ρ.1, envAct d ρ.2) = ρ
      rw [hn d (fix_mono hd (Nat.le_max_left _ _)), hm d (fix_mono hd (Nat.le_max_right _ _))]

theorem env_inv (d : Wd) : ∀ {Γ : List FTy} (ρ : VEnv fm Γ), envAct d (envAct d ρ) = ρ
  | [], _ => rfl
  | t :: _, ρ => by
      show ((H t).act d ((H t).act d ρ.1), envAct d (envAct d ρ.2)) = ρ
      rw [GS.inv, env_inv d ρ.2]

theorem vget_act (d : Wd) : ∀ {Γ : List FTy} {t : FTy} (i : Var Γ t) (ρ : VEnv fm Γ),
    i.vget fm (envAct d ρ) = (H t).act d (i.vget fm ρ)
  | _, _, .zero, _ => rfl
  | _, _, .succ i, ρ => vget_act d i ρ.2

def Eqv {Γ : List FTy} {t : FTy} (F : VEnv fm Γ → (H t).car) : Prop :=
  ∀ d ρ, F (envAct d ρ) = (H t).act d (F ρ)

/-- A proposition-valued equivariant map lands in `P_σ`. -/
def mkS {Γ : List FTy} (F : VEnv fm Γ → Wd → Prop)
    (hF : ∀ d ρ w, F (envAct d ρ) w ↔ F ρ (dx w d)) (ρ : VEnv fm Γ) : Hs.car :=
  ⟨F ρ, by
    obtain ⟨n, hn⟩ := env_fs ρ
    exact ⟨n, fun d hd => funext fun w => propext <| by rw [← hF d ρ w, hn d hd]⟩⟩

theorem mkS_eqv {Γ : List FTy} (F : VEnv fm Γ → Wd → Prop) (hF) :
    Eqv (t := .s) (mkS (Γ := Γ) F hF) :=
  fun d ρ => Subtype.ext (funext fun w => propext (hF d ρ w))

def mkF {Γ : List FTy} {a b : FTy} (F : VEnv fm (a :: Γ) → (H b).car) (hF : Eqv F)
    (ρ : VEnv fm Γ) : (H (.arr a b)).car :=
  ⟨fun x => F ((x, ρ) : VEnv fm (a :: Γ)), by
    obtain ⟨n, hn⟩ := env_fs ρ
    refine ⟨n, fun d hd x => ?_⟩
    have h := hF d (((H a).act d x, ρ) : VEnv fm (a :: Γ))
    have e : @envAct d (a :: Γ) (((H a).act d x, ρ) : VEnv fm (a :: Γ)) = ((x, ρ) : VEnv fm (a :: Γ)) := by
      show ((H a).act d ((H a).act d x), envAct d ρ) = (x, ρ)
      rw [GS.inv, hn d hd]
    rw [e] at h
    exact h.symm⟩

theorem mkF_eqv {Γ : List FTy} {a b : FTy} (F : VEnv fm (a :: Γ) → (H b).car) (hF : Eqv F) :
    Eqv (t := .arr a b) (mkF F hF) := fun d ρ => Subtype.ext (funext fun x => by
  show F (x, envAct d ρ) = (H b).act d (F ((H a).act d x, ρ))
  rw [← hF d]
  show F (x, envAct d ρ) = F ((H a).act d ((H a).act d x), envAct d ρ)
  rw [GS.inv])

theorem act_inj (G : GS) (d : Wd) (x y : G.car) : G.act d x = G.act d y ↔ x = y :=
  ⟨fun h => by rw [← G.inv d x, h, G.inv], fun h => h ▸ rfl⟩

theorem all_bij (G : GS) (d : Wd) (p : G.car → Prop) : (∀ x, p (G.act d x)) ↔ ∀ x, p x :=
  ⟨fun h x => G.inv d x ▸ h (G.act d x), fun h x => h _⟩

theorem ex_bij (G : GS) (d : Wd) (p : G.car → Prop) : (∃ x, p (G.act d x)) ↔ ∃ x, p x :=
  ⟨fun ⟨x, hx⟩ => ⟨_, hx⟩, fun ⟨x, hx⟩ => ⟨G.act d x, by rw [G.inv]; exact hx⟩⟩

theorem allW (d : Wd) (p : Wd → Prop) : (∀ v, p (dx v d)) ↔ ∀ v, p v :=
  ⟨fun h v => dx_dx v d ▸ h (dx v d), fun h v => h _⟩

theorem binder_eqv {Γ : List FTy} {a : FTy} (F : VEnv fm (a :: Γ) → Hs.car) (hF : Eqv (t := .s) F)
    (d : Wd) (x : (H a).car) (ρ : VEnv fm Γ) (w : Wd) :
    (F ((x, envAct d ρ) : VEnv fm (a :: Γ))).1 w ↔ (F (((H a).act d x, ρ) : VEnv fm (a :: Γ))).1 (dx w d) := by
  have h := hF d (((H a).act d x, ρ) : VEnv fm (a :: Γ))
  have e : @envAct d (a :: Γ) (((H a).act d x, ρ) : VEnv fm (a :: Γ)) = ((x, envAct d ρ) : VEnv fm (a :: Γ)) := by
    show ((H a).act d ((H a).act d x), envAct d ρ) = _
    rw [GS.inv]
  rw [e] at h
  rw [h]; exact Iff.rfl

/-- The semantics, together with its equivariance. -/
def sem : {Γ : List FTy} → {t : FTy} → Tm Γ t → {F : VEnv fm Γ → (H t).car // Eqv F}
  | _, _, .var i => ⟨fun ρ => i.vget fm ρ, fun d ρ => vget_act d i ρ⟩
  | _, _, .app (a := a) (b := b) f x =>
      ⟨fun ρ => ((sem f).1 ρ).1 ((sem x).1 ρ), fun d ρ => by
        show ((sem f).1 (envAct d ρ)).1 ((sem x).1 (envAct d ρ)) = _
        rw [(sem f).2, (sem x).2]
        show (H b).act d (((sem f).1 ρ).1 ((H a).act d ((H a).act d ((sem x).1 ρ)))) = _
        rw [GS.inv]⟩
  | _, _, .lam t => ⟨mkF (sem t).1 (sem t).2, mkF_eqv _ _⟩
  | _, _, .top => ⟨mkS (fun _ _ => True) (fun _ _ _ => Iff.rfl), mkS_eqv _ _⟩
  | _, _, .bot => ⟨mkS (fun _ _ => False) (fun _ _ _ => Iff.rfl), mkS_eqv _ _⟩
  | _, _, .neg x => ⟨mkS (fun ρ w => ¬ ((sem x).1 ρ).1 w) (fun d ρ w => by
        rw [(sem x).2]; exact Iff.rfl), mkS_eqv _ _⟩
  | _, _, .and x y => ⟨mkS (fun ρ w => ((sem x).1 ρ).1 w ∧ ((sem y).1 ρ).1 w) (fun d ρ w => by
        rw [(sem x).2, (sem y).2]; exact Iff.rfl), mkS_eqv _ _⟩
  | _, _, .or x y => ⟨mkS (fun ρ w => ((sem x).1 ρ).1 w ∨ ((sem y).1 ρ).1 w) (fun d ρ w => by
        rw [(sem x).2, (sem y).2]; exact Iff.rfl), mkS_eqv _ _⟩
  | _, _, .imp x y => ⟨mkS (fun ρ w => ((sem x).1 ρ).1 w → ((sem y).1 ρ).1 w) (fun d ρ w => by
        rw [(sem x).2, (sem y).2]; exact Iff.rfl), mkS_eqv _ _⟩
  | _, _, .box x => ⟨mkS (fun ρ _ => ∀ v, True → ((sem x).1 ρ).1 v) (fun d ρ w => by
        rw [(sem x).2]
        show (∀ v, True → ((sem x).1 ρ).1 (dx v d)) ↔ _
        exact allW d (fun v => True → ((sem x).1 ρ).1 v)), mkS_eqv _ _⟩
  | _, _, .all a b => ⟨mkS (fun ρ w => ∀ x : (H a).car, ((sem b).1 (x, ρ)).1 w) (fun d ρ w => by
        show (∀ x, ((sem b).1 (x, envAct d ρ)).1 w) ↔ _
        simp only [binder_eqv _ (sem b).2]
        exact all_bij (H a) d (fun x => ((sem b).1 (x, ρ)).1 (dx w d))), mkS_eqv _ _⟩
  | _, _, .ex a b => ⟨mkS (fun ρ w => ∃ x : (H a).car, ((sem b).1 (x, ρ)).1 w) (fun d ρ w => by
        show (∃ x, ((sem b).1 (x, envAct d ρ)).1 w) ↔ _
        simp only [binder_eqv _ (sem b).2]
        exact ex_bij (H a) d (fun x => ((sem b).1 (x, ρ)).1 (dx w d))), mkS_eqv _ _⟩
  | _, _, .allE b => ⟨mkS (fun ρ w => ∀ y : (H .e).car, True → ((sem b).1 (y, ρ)).1 w)
        (fun d ρ w => by
          show (∀ y, True → ((sem b).1 (y, envAct d ρ)).1 w) ↔ _
          simp only [binder_eqv _ (sem b).2]
          exact Iff.rfl), mkS_eqv _ _⟩
  | _, _, .exE b => ⟨mkS (fun ρ w => ∃ y : (H .e).car, True ∧ ((sem b).1 (y, ρ)).1 w)
        (fun d ρ w => by
          show (∃ y, True ∧ ((sem b).1 (y, envAct d ρ)).1 w) ↔ _
          simp only [binder_eqv _ (sem b).2]
          exact Iff.rfl), mkS_eqv _ _⟩
  | _, _, .eq a x y => ⟨mkS (fun ρ _ => (sem x).1 ρ = (sem y).1 ρ) (fun d ρ w => by
        show (sem x).1 (envAct d ρ) = (sem y).1 (envAct d ρ) ↔ _
        rw [(sem x).2, (sem y).2]; exact act_inj _ _ _ _), mkS_eqv _ _⟩
  | _, _, .pos => ⟨fun _ => posE, fun d _ => Subtype.ext (funext fun _ => Subtype.ext rfl)⟩

/-- `fm` is 𝓛-general (v4 def:lgeneral): every term of 𝓛 with parameters in the `P_τ` denotes in them. -/
def fmL : LGen fm where
  ev t ρ := (sem t).1 ρ
  var _ _ := rfl
  app _ _ _ := rfl
  lam _ _ _ := rfl
  top _ _ := Iff.rfl
  bot _ _ := Iff.rfl
  neg _ _ _ := Iff.rfl
  and _ _ _ _ := Iff.rfl
  or _ _ _ _ := Iff.rfl
  imp _ _ _ _ := Iff.rfl
  box _ _ _ := ⟨fun h v _ => h v trivial, fun h v _ => h v trivial⟩
  all _ _ _ _ := Iff.rfl
  ex _ _ _ _ := Iff.rfl
  allE _ _ _ := Iff.rfl
  exE _ _ _ := Iff.rfl
  eq _ _ _ _ _ := Iff.rfl
  pos _ := rfl

/-! ### The carriers are v4's `P_τ` -/

/-- At an arrow type the carrier is exactly the finitely supported functions `P_a → P_b`. -/
theorem carrier_arr (a b : FTy) : fm.C (.arr a b) =
    {f : fm.C a → fm.C b // ∃ n, ∀ d, Fix n d → ∀ x, (H b).act d (f ((H a).act d x)) = f x} := rfl

/-- The action at an arrow type is conjugation by the flip (flips are involutions). -/
theorem act_arr (a b : FTy) (d : Wd) (f : fm.C (.arr a b)) (x : fm.C a) :
    fm.ap ((H (.arr a b)).act d f) x = (H b).act d (fm.ap f ((H a).act d x)) := rfl

/-- v4's fact (b): at `σ`, finitely supported means finitary. -/
theorem carrier_s (X : Wd → Prop) : (∃ p : fm.C .s, fm.pr p = X) ↔
    ∃ n, ∀ w v, (∀ k, k < n → w k = v k) → (X w ↔ X v) := by
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨n, hn⟩ := p.2
    refine ⟨n, fun w v hwv => ?_⟩
    have hd : Fix n (dx w v) := fun k hk => by simp [dx, hwv k hk]
    have e : dx w (dx w v) = v := by funext k; simp only [dx]; cases w k <;> cases v k <;> rfl
    have := congrFun (hn _ hd) w
    simp only [e] at this
    exact Iff.of_eq this.symm
  · rintro ⟨n, hn⟩
    refine ⟨⟨X, n, fun d hd => funext fun w => propext (hn _ _ fun k hk => ?_)⟩, rfl⟩
    simp [dx, hd k hk]

def flipAt (n : Nat) : Wd := fun k => decide (k = n)

theorem fix_flipAt (n : Nat) : Fix n (flipAt n) := fun k hk => by
  simp [flipAt, Nat.ne_of_lt hk]

/-- v4's fact (c): no atoms.  Every `p ∈ P_σ` containing `w` has a proper `P_σ`-part omitting `w`. -/
theorem no_singleton (v : Wd) : ¬ ∃ p : fm.C .s, ∀ u, fm.pr p u ↔ u = v := by
  rintro ⟨p, hp⟩
  obtain ⟨n, hn⟩ := p.2
  have h1 : p.1 (dx v (flipAt n)) := by
    rw [congrFun (hn _ (fix_flipAt n)) v]; exact (hp v).2 rfl
  have h2 := congrArg (· n) ((hp _).1 h1)
  simp [dx, flipAt] at h2

theorem d_holds (x : fm.C .s) (v : Wd) (hx : fm.pr x v) :
    ∃ ψ : fm.C .s, ¬ fm.pr ψ v ∧ ∃ u', fm.pr ψ u' ∧ fm.pr x u' := by
  obtain ⟨n, hn⟩ := x.2
  let ψ : fm.C .s := ⟨fun y => y n ≠ v n, n + 1, fun d hd => funext fun y => by
    show (xor (y n) (d n) ≠ v n) = (y n ≠ v n)
    rw [hd n (Nat.lt_succ_self n)]; simp⟩
  refine ⟨ψ, fun h => h rfl, dx v (flipAt n), ?_, ?_⟩
  · show xor (v n) (decide (n = n)) ≠ v n
    cases v n <;> simp
  · show x.1 (dx v (flipAt n))
    rw [congrFun (hn _ (fix_flipAt n)) v]; exact hx

/-- **Example ex:separating at all types.**  v4's flip model — total frame, one individual existing
everywhere, empty `Pos`, carriers the hereditarily finitely supported `P_τ` at every type of 𝓛 — is
an 𝓛-general model in which `A ∃p.(Atom p ∧ p)` fails at every world. -/
theorem sep_all_types :
    (∀ w v, fm.R w v) ∧ (∀ y w, fm.act y w) ∧ Nonempty (fm.C .e) ∧ Subsingleton (fm.C .e) ∧
    (∀ (φ : fm.C tp) w, ¬ fm.pr (fm.ap fm.P φ) w) ∧
    (∀ v, ¬ ∃ p : fm.C .s, ∀ u, fm.pr p u ↔ u = v) ∧
    ∀ w, ¬ fm.pr (fmL.ev phiSep (() : VEnv fm [])) w := by
  refine ⟨fun _ _ => trivial, fun _ _ => trivial, ⟨()⟩, ⟨fun _ _ => rfl⟩, fun _ _ h => h,
    no_singleton, fun w h => ?_⟩
  obtain ⟨x, hat, hxv⟩ := (phiSep_iff fm fmL w).1 h w
  obtain ⟨_, hno⟩ := (atom_iff fm fmL x w).1 hat
  exact hno w ⟨hxv, (dTm_iff fm fmL x w).2 (d_holds x w hxv)⟩

/-- Hence the separating sentence is not valid over v4's 𝓛-general models of the empty theory. -/
theorem sep_not_valid_empty : ¬ ValidV4 (fun _ => False) phiSep := fun h =>
  sep_all_types.2.2.2.2.2.2 (fun _ => false)
    (h Wd fm fmL ⟨()⟩ (fun _ hψ => hψ.elim) (fun _ => false))

end Programme.«20261022-1724-ontological».ThFM

#print axioms Programme.«20261022-1724-ontological».ThFM.fmL
#print axioms Programme.«20261022-1724-ontological».ThFM.sep_all_types
#print axioms Programme.«20261022-1724-ontological».ThFM.carrier_s
#print axioms Programme.«20261022-1724-ontological».ThFM.sep_not_valid_empty
