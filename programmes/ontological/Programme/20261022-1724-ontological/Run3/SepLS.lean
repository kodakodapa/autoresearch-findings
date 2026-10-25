import Programme.«20261022-1724-ontological».Run3.DeepSep
/-! # SepLS.lean (pr, run 3, round 9)

`DeepSep.lean` (K11, minus `#print`s) verbatim, then th's `LS.lean` from `namespace Programme.ThHenkin`
to its end (K12 completeness, LS, compactness; minus `#print`s) verbatim, then section `Programme.Run3.SepLS`:
the separating sentence has a countermodel of variant 2 with countably many worlds and countable carriers,
and no countermodel with finitely many worlds. -/

/-! # DeepSep.lean (run 3, round 7)

`DeepE.lean` (claims K8-K10) verbatim, followed by section `SepR`: v4's remarks in Example
`ex:separating` (finite models do not separate; the example's model is not a model of variant 2,
whatever `Pos` is) and the example itself as a v4 `VM`+`LGen` model. -/

-- [cleanup 2026-10-23] shared block (4679 lines) now imported from Programme.«20261022-1724-ontological».Run3.DeepSep





namespace Programme.«20261022-1724-ontological».ThHenkin
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
def pair (a b : Nat) : Nat := 2 ^ a * (2 * b + 1)

theorem pow_succ' (c : Nat) (x : Nat) : 2 ^ (c + 1) * x = 2 * (2 ^ c * x) := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ c) 2, Nat.mul_assoc]

theorem pair_inj : ∀ {a b c d : Nat}, pair a b = pair c d → a = c ∧ b = d
  | 0, b, 0, d, h => by simp [pair] at h; omega
  | 0, b, c + 1, d, h => by
      simp only [pair, pow_succ'] at h; generalize 2 ^ c * (2 * d + 1) = X at h; simp at h; omega
  | a + 1, b, 0, d, h => by
      simp only [pair, pow_succ'] at h; generalize 2 ^ a * (2 * b + 1) = X at h; simp at h; omega
  | a + 1, b, c + 1, d, h => by
      simp only [pair, pow_succ'] at h
      have h' : pair a b = pair c d := by unfold pair; omega
      have := pair_inj h'; omega

theorem pair_iff {a b c d : Nat} : pair a b = pair c d ↔ a = c ∧ b = d :=
  ⟨pair_inj, fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩

theorem lt_pair (a b : Nat) : b < pair a b := by
  have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  unfold pair
  have : 1 * (2 * b + 1) ≤ 2 ^ a * (2 * b + 1) := Nat.mul_le_mul_right _ this
  omega

def codeF : FTy → Nat
  | .e => pair 0 0
  | .s => pair 1 0
  | .arr a b => pair 2 (pair (codeF a) (codeF b))

theorem codeF_inj : ∀ {a b : FTy}, codeF a = codeF b → a = b
  | .e, b, h => by cases b <;> simp_all [codeF, pair_iff]
  | .s, b, h => by cases b <;> simp_all [codeF, pair_iff]
  | .arr a b, c, h => by
      cases c with
      | arr c d =>
          simp only [codeF, pair_iff] at h
          rw [codeF_inj h.2.1, codeF_inj h.2.2]
      | _ => simp_all [codeF, pair_iff]

def codeH : HTy → Nat
  | .L t => pair 0 (codeF t)
  | .w => pair 1 0
  | .o => pair 2 0

theorem codeH_inj : ∀ {a b : HTy}, codeH a = codeH b → a = b
  | .L t, b, h => by
      cases b with
      | L u => simp only [codeH, pair_iff] at h; rw [codeF_inj h.2]
      | _ => simp_all [codeH, pair_iff]
  | .w, b, h => by cases b <;> simp_all [codeH, pair_iff]
  | .o, b, h => by cases b <;> simp_all [codeH, pair_iff]

def codeV : {Γ : List HTy} → {a : HTy} → HVar Γ a → Nat
  | _, _, .zero => 0
  | _, _, .succ v => codeV v + 1

theorem codeV_inj : ∀ {Γ a} (v v' : HVar Γ a), codeV v = codeV v' → v = v'
  | _, _, .zero, .zero, _ => rfl
  | _, _, .zero, .succ _, h => by simp [codeV] at h
  | _, _, .succ _, .zero, h => by simp [codeV] at h
  | _, _, .succ v, .succ v', h => by
      simp only [codeV, Nat.add_right_cancel_iff] at h; rw [codeV_inj v v' h]

def codeT : {Γ : List HTy} → {a : HTy} → HTerm Γ a → Nat
  | _, _, .var v => pair 0 (codeV v)
  | _, _, @HTerm.appL _ a _ f x => pair 1 (pair (codeF a) (pair (codeT f) (codeT x)))
  | _, _, .lamL b => pair 2 (codeT b)
  | _, _, .pos => pair 3 0
  | _, _, .wabs φ => pair 4 (codeT φ)
  | _, _, .holds p i => pair 5 (pair (codeT p) (codeT i))
  | _, _, .rel i j => pair 6 (pair (codeT i) (codeT j))
  | _, _, .act x i => pair 7 (pair (codeT x) (codeT i))
  | _, _, .bot => pair 8 0
  | _, _, .imp p q => pair 9 (pair (codeT p) (codeT q))
  | _, _, .and p q => pair 10 (pair (codeT p) (codeT q))
  | _, _, .or p q => pair 11 (pair (codeT p) (codeT q))
  | _, _, .all a p => pair 12 (pair (codeH a) (codeT p))
  | _, _, .ex a p => pair 13 (pair (codeH a) (codeT p))
  | _, _, .eq a s t => pair 14 (pair (codeH a) (pair (codeT s) (codeT t)))

theorem codeT_inj : ∀ {Γ a} (t t' : HTerm Γ a), codeT t = codeT t' → t = t'
  | _, _, .var v, t', h => by
      cases t' <;> simp only [codeT, pair_iff] at h <;> first | omega | rw [codeV_inj _ _ h.2]
  | _, _, @HTerm.appL _ a _ f x, t', h => by
      cases t' with
      | @appL _ a' _ f' x' =>
          simp only [codeT, pair_iff] at h
          obtain ⟨_, ha, hf, hx⟩ := h
          cases codeF_inj ha
          rw [codeT_inj f f' hf, codeT_inj x x' hx]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .lamL b, t', h => by
      cases t' with
      | lamL b' => simp only [codeT, pair_iff] at h; rw [codeT_inj b b' h.2]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .pos, t', h => by cases t' <;> simp only [codeT, pair_iff] at h <;> first | omega | rfl
  | _, _, .wabs φ, t', h => by
      cases t' with
      | wabs φ' => simp only [codeT, pair_iff] at h; rw [codeT_inj φ φ' h.2]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .holds p i, t', h => by
      cases t' with
      | holds p' i' =>
          simp only [codeT, pair_iff] at h; rw [codeT_inj p p' h.2.1, codeT_inj i i' h.2.2]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .rel p i, t', h => by
      cases t' with
      | rel p' i' =>
          simp only [codeT, pair_iff] at h; rw [codeT_inj p p' h.2.1, codeT_inj i i' h.2.2]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .act p i, t', h => by
      cases t' with
      | act p' i' =>
          simp only [codeT, pair_iff] at h; rw [codeT_inj p p' h.2.1, codeT_inj i i' h.2.2]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .bot, t', h => by cases t' <;> simp only [codeT, pair_iff] at h <;> first | omega | rfl
  | _, _, .imp p i, t', h => by
      cases t' with
      | imp p' i' =>
          simp only [codeT, pair_iff] at h; rw [codeT_inj p p' h.2.1, codeT_inj i i' h.2.2]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .and p i, t', h => by
      cases t' with
      | and p' i' =>
          simp only [codeT, pair_iff] at h; rw [codeT_inj p p' h.2.1, codeT_inj i i' h.2.2]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .or p i, t', h => by
      cases t' with
      | or p' i' =>
          simp only [codeT, pair_iff] at h; rw [codeT_inj p p' h.2.1, codeT_inj i i' h.2.2]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .all a p, t', h => by
      cases t' with
      | all a' p' =>
          simp only [codeT, pair_iff] at h
          obtain ⟨_, ha, hp⟩ := h
          cases codeH_inj ha
          rw [codeT_inj p p' hp]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .ex a p, t', h => by
      cases t' with
      | ex a' p' =>
          simp only [codeT, pair_iff] at h
          obtain ⟨_, ha, hp⟩ := h
          cases codeH_inj ha
          rw [codeT_inj p p' hp]
      | _ => simp only [codeT, pair_iff] at h; omega
  | _, _, .eq a s t, t', h => by
      cases t' with
      | eq a' s' t'' =>
          simp only [codeT, pair_iff] at h
          obtain ⟨_, ha, hs, ht⟩ := h
          cases codeH_inj ha
          rw [codeT_inj s s' hs, codeT_inj t t'' ht]
      | _ => simp only [codeT, pair_iff] at h; omega


/-! ## A locally nameless code: bound variables by index, free variables by level.
It is invariant under weakening of the context, so the Lindenbaum enumeration at stage `k` can
work over the current context only. -/

theorem codeV_lt : ∀ {Γ a} (v : HVar Γ a), codeV v < Γ.length
  | _, _, .zero => by simp [codeV]
  | _, _, .succ v => by have := codeV_lt v; simp [codeV]; omega

def vcode (d : Nat) (v : HVar Γ a) : Nat :=
  if codeV v < d then pair 0 (codeV v) else pair 1 (Γ.length - 1 - codeV v)

theorem vcode_inj (d : Nat) (v v' : HVar Γ a) (h : vcode d v = vcode d v') : v = v' := by
  have l := codeV_lt v; have l' := codeV_lt v'
  apply codeV_inj
  unfold vcode at h
  split at h <;> split at h <;> simp only [pair_iff] at h <;> omega

def codeL : {Γ : List HTy} → {a : HTy} → Nat → HTerm Γ a → Nat
  | _, _, d, .var v => pair 0 (vcode d v)
  | _, _, d, @HTerm.appL _ a _ f x => pair 1 (pair (codeF a) (pair (codeL d f) (codeL d x)))
  | _, _, d, .lamL b => pair 2 (codeL (d + 1) b)
  | _, _, d, .pos => pair 3 0
  | _, _, d, .wabs φ => pair 4 (codeL (d + 1) φ)
  | _, _, d, .holds p i => pair 5 (pair (codeL d p) (codeL d i))
  | _, _, d, .rel i j => pair 6 (pair (codeL d i) (codeL d j))
  | _, _, d, .act x i => pair 7 (pair (codeL d x) (codeL d i))
  | _, _, d, .bot => pair 8 0
  | _, _, d, .imp p q => pair 9 (pair (codeL d p) (codeL d q))
  | _, _, d, .and p q => pair 10 (pair (codeL d p) (codeL d q))
  | _, _, d, .or p q => pair 11 (pair (codeL d p) (codeL d q))
  | _, _, d, .all a p => pair 12 (pair (codeH a) (codeL (d + 1) p))
  | _, _, d, .ex a p => pair 13 (pair (codeH a) (codeL (d + 1) p))
  | _, _, d, .eq a s t => pair 14 (pair (codeH a) (pair (codeL d s) (codeL d t)))

theorem codeL_inj : ∀ {Γ a} (d : Nat) (t t' : HTerm Γ a), codeL d t = codeL d t' → t = t'
  | _, _, d, .var v, t', h => by
      cases t' with
      | var v' => simp only [codeL, pair_iff] at h; rw [vcode_inj d v v' h.2]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, @HTerm.appL _ a _ f x, t', h => by
      cases t' with
      | @appL _ a' _ f' x' =>
          simp only [codeL, pair_iff] at h
          obtain ⟨_, ha, hf, hx⟩ := h
          cases codeF_inj ha
          rw [codeL_inj d f f' hf, codeL_inj d x x' hx]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .lamL b, t', h => by
      cases t' with
      | lamL b' => simp only [codeL, pair_iff] at h; rw [codeL_inj (d + 1) b b' h.2]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .pos, t', h => by cases t' <;> first | rfl | (simp only [codeL, pair_iff] at h; omega)
  | _, _, d, .wabs φ, t', h => by
      cases t' with
      | wabs φ' => simp only [codeL, pair_iff] at h; rw [codeL_inj (d + 1) φ φ' h.2]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .holds p i, t', h => by
      cases t' with
      | holds p' i' =>
          simp only [codeL, pair_iff] at h; rw [codeL_inj d p p' h.2.1, codeL_inj d i i' h.2.2]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .rel p i, t', h => by
      cases t' with
      | rel p' i' =>
          simp only [codeL, pair_iff] at h; rw [codeL_inj d p p' h.2.1, codeL_inj d i i' h.2.2]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .act p i, t', h => by
      cases t' with
      | act p' i' =>
          simp only [codeL, pair_iff] at h; rw [codeL_inj d p p' h.2.1, codeL_inj d i i' h.2.2]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .bot, t', h => by cases t' <;> first | rfl | (simp only [codeL, pair_iff] at h; omega)
  | _, _, d, .imp p i, t', h => by
      cases t' with
      | imp p' i' =>
          simp only [codeL, pair_iff] at h; rw [codeL_inj d p p' h.2.1, codeL_inj d i i' h.2.2]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .and p i, t', h => by
      cases t' with
      | and p' i' =>
          simp only [codeL, pair_iff] at h; rw [codeL_inj d p p' h.2.1, codeL_inj d i i' h.2.2]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .or p i, t', h => by
      cases t' with
      | or p' i' =>
          simp only [codeL, pair_iff] at h; rw [codeL_inj d p p' h.2.1, codeL_inj d i i' h.2.2]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .all a p, t', h => by
      cases t' with
      | all a' p' =>
          simp only [codeL, pair_iff] at h
          obtain ⟨_, ha, hp⟩ := h
          cases codeH_inj ha
          rw [codeL_inj (d + 1) p p' hp]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .ex a p, t', h => by
      cases t' with
      | ex a' p' =>
          simp only [codeL, pair_iff] at h
          obtain ⟨_, ha, hp⟩ := h
          cases codeH_inj ha
          rw [codeL_inj (d + 1) p p' hp]
      | _ => simp only [codeL, pair_iff] at h; omega
  | _, _, d, .eq a s t, t', h => by
      cases t' with
      | eq a' s' t'' =>
          simp only [codeL, pair_iff] at h
          obtain ⟨_, ha, hs, ht⟩ := h
          cases codeH_inj ha
          rw [codeL_inj d s s' hs, codeL_inj d t t'' ht]
      | _ => simp only [codeL, pair_iff] at h; omega


/-- A renaming preserving the code of variables at depth `d`. -/
def Good (d : Nat) (r : HRen Γ Δ) : Prop := ∀ {b} (v : HVar Γ b), vcode d (r v) = vcode d v

theorem good_lift {d : Nat} {r : HRen Γ Δ} (h : Good d r) : Good (d + 1) (liftR (a := c) r) := by
  intro b v
  cases v with
  | zero => simp [vcode, liftR, codeV]
  | succ v =>
      have hv := h v
      have l := codeV_lt v; have l' := codeV_lt (r v)
      simp only [vcode, liftR, codeV, List.length_cons] at hv ⊢
      by_cases h1 : codeV v < d <;> by_cases h2 : codeV (r v) < d <;>
        simp only [h1, h2, ite_true, ite_false, Nat.add_lt_add_iff_right, pair_iff] at hv ⊢ <;>
        (obtain ⟨hv1, hv2⟩ := hv; exact ⟨by first | trivial | omega, by omega⟩)

theorem good_succ : Good 0 (fun v => (HVar.succ v : HVar (c :: Γ) _)) := by
  intro b v
  have l := codeV_lt v
  simp only [vcode, codeV, List.length_cons, Nat.not_lt_zero, ite_false, pair_iff]
  exact ⟨trivial, by omega⟩

theorem codeL_rename : ∀ {Γ Δ a} (t : HTerm Γ a) (d : Nat) (r : HRen Γ Δ), Good d r →
    codeL d (rename r t) = codeL d t := by
  intro Γ Δ a t
  induction t generalizing Δ with
  | var v => intro d r h; simp only [rename, codeL, h v]
  | appL f x ihf ihx => intro d r h; simp only [rename, codeL, ihf d r h, ihx d r h]
  | lamL b ih => intro d r h; simp only [rename, codeL, ih (d + 1) _ (good_lift h)]
  | pos => intro _ _ _; rfl
  | wabs φ ih => intro d r h; simp only [rename, codeL, ih (d + 1) _ (good_lift h)]
  | holds p i ihp ihi => intro d r h; simp only [rename, codeL, ihp d r h, ihi d r h]
  | rel p i ihp ihi => intro d r h; simp only [rename, codeL, ihp d r h, ihi d r h]
  | act p i ihp ihi => intro d r h; simp only [rename, codeL, ihp d r h, ihi d r h]
  | bot => intro _ _ _; rfl
  | imp p i ihp ihi => intro d r h; simp only [rename, codeL, ihp d r h, ihi d r h]
  | and p i ihp ihi => intro d r h; simp only [rename, codeL, ihp d r h, ihi d r h]
  | or p i ihp ihi => intro d r h; simp only [rename, codeL, ihp d r h, ihi d r h]
  | all a p ih => intro d r h; simp only [rename, codeL, ih (d + 1) _ (good_lift h)]
  | ex a p ih => intro d r h; simp only [rename, codeL, ih (d + 1) _ (good_lift h)]
  | eq a s t ihs iht => intro d r h; simp only [rename, codeL, ihs d r h, iht d r h]

/-- Weakening does not change the code. -/
theorem codeL_wk (t : HTerm Γ a) : codeL 0 (wk (b := c) t) = codeL 0 t :=
  codeL_rename t 0 _ good_succ

/-- The formula over `Γ` with code `n`, if any (classical). -/
noncomputable def decL (Γ : List HTy) (a : HTy) (n : Nat) : Option (HTerm Γ a) :=
  open Classical in if h : ∃ t : HTerm Γ a, codeL 0 t = n then some (Classical.choose h) else none

theorem decL_codeL (t : HTerm Γ a) : decL Γ a (codeL 0 t) = some t := by
  have h : ∃ t' : HTerm Γ a, codeL 0 t' = codeL 0 t := ⟨t, rfl⟩
  unfold decL; rw [dif_pos h]; exact congrArg some (codeL_inj 0 _ _ (Classical.choose_spec h))

/-! ## Lindenbaum's construction with Henkin witnesses

Stage `k + 1` adds one variable to the context of stage `k`: for the formula processed at
stage `k` that is an `∃ a. χ` the variable is its witness, otherwise a dummy variable of type `o`.
Contexts never get variables that are not witnesses, which matters: a variable of type `L e` in
the context makes `∃ x : e. ⊤` derivable. -/

noncomputable def unpair (k : Nat) : Nat × Nat :=
  open Classical in
  if h : ∃ a b, pair a b = k then (Classical.choose h, Classical.choose (Classical.choose_spec h))
  else (0, 0)

theorem unpair_pair (a b : Nat) : unpair (pair a b) = (a, b) := by
  have h : ∃ a' b', pair a' b' = pair a b := ⟨a, b, rfl⟩
  unfold unpair; rw [dif_pos h]
  have e := pair_inj (Classical.choose_spec (Classical.choose_spec h))
  simp only [Prod.mk.injEq]; exact e

theorem le_pair (a b : Nat) : a ≤ pair a b := by
  have h1 : a < 2 ^ a := Nat.lt_two_pow_self
  have : 2 ^ a * 1 ≤ 2 ^ a * (2 * b + 1) := Nat.mul_le_mul_left _ (by omega)
  unfold pair; omega

section lind
variable (T : Tm [] .s → Prop)

def Cons (Γ : List HTy) (hs : List (HTerm Γ .o)) : Prop := ¬ DC T Γ hs .bot

def topH : HTerm Γ .o := .imp .bot .bot
def negH (φ : HTerm Γ .o) : HTerm Γ .o := .imp φ .bot

structure St where
  Γ : List HTy
  hs : List (HTerm Γ .o)

/-- Witness data: for `∃ a. χ` the type `a` and `χ`; otherwise a dummy `o`-variable. -/
def wit : HTerm Γ .o → (Σ b : HTy, HTerm (b :: Γ) .o)
  | .ex a χ => ⟨a, χ⟩
  | φ => ⟨.o, wk φ⟩

theorem wit_cases (ψ : HTerm Γ .o) :
    (∃ a χ, ψ = .ex a χ ∧ wit ψ = ⟨a, χ⟩) ∨ wit ψ = ⟨.o, wk ψ⟩ := by
  cases ψ <;> simp [wit]

/-- The formula decided at stage `k`: the formula over the current context with code
`(unpair k).2`, or its negation if it is inconsistent with the stage; `⊤` if there is none. -/
noncomputable def pick (k : Nat) (Γ : List HTy) (hs : List (HTerm Γ .o)) : HTerm Γ .o :=
  open Classical in
  match decL Γ .o (unpair k).2 with
  | some φ => if Cons T Γ (φ :: hs) then φ else negH φ
  | none => topH

noncomputable def step (k : Nat) (s : St) : St :=
  ⟨(wit (pick T k s.Γ s.hs)).1 :: s.Γ,
    (wit (pick T k s.Γ s.hs)).2 :: (pick T k s.Γ s.hs :: s.hs).map wk⟩

theorem pick_cons (k : Nat) {Γ : List HTy} {hs : List (HTerm Γ .o)} (h : Cons T Γ hs) :
    Cons T Γ (pick T k Γ hs :: hs) := by
  unfold pick
  split
  · rename_i φ _
    split
    · assumption
    · rename_i hn
      intro d
      apply h
      have d1 : DC T Γ hs (negH φ) := .impI (Classical.byContradiction hn)
      exact .impE (.impI d) d1
  · intro d
    exact h (.impE (.impI d) (.impI (.hyp (List.mem_cons_self ..))))

theorem wit_cons {Γ : List HTy} {ψ : HTerm Γ .o} {hs : List (HTerm Γ .o)} (h : Cons T Γ (ψ :: hs)) :
    Cons T ((wit ψ).1 :: Γ) ((wit ψ).2 :: (ψ :: hs).map wk) := by
  rcases wit_cases ψ with ⟨a, χ, rfl, e⟩ | e
  · rw [e]; intro d
    exact h (.exE a (.hyp (List.mem_cons_self ..)) d)
  · rw [e]; intro d
    apply h
    have e1 : DC T Γ (ψ :: hs) (.ex .o topH) := .exI .o .bot trivial (.impI (.hyp (List.mem_cons_self ..)))
    refine .exE .o e1 (d.weaken ?_)
    intro x m
    rcases List.mem_cons.1 m with rfl | m
    · exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_cons_self ..))
    · exact List.mem_cons_of_mem _ m

theorem step_cons (k : Nat) (s : St) (h : Cons T s.Γ s.hs) : Cons T (step T k s).Γ (step T k s).hs :=
  wit_cons T (pick_cons T k h)

variable (Γ0 : List HTy) (hs0 : List (HTerm Γ0 .o))

noncomputable def stage : Nat → St
  | 0 => ⟨Γ0, hs0⟩
  | k + 1 => step T k (stage k)

noncomputable abbrev Cx (n : Nat) : List HTy := (stage T Γ0 hs0 n).Γ
noncomputable abbrev Hs (n : Nat) : List (HTerm (Cx T Γ0 hs0 n) .o) := (stage T Γ0 hs0 n).hs

theorem stage_cons (h : Cons T Γ0 hs0) : ∀ n, Cons T (Cx T Γ0 hs0 n) (Hs T Γ0 hs0 n)
  | 0 => h
  | n + 1 => step_cons T n _ (stage_cons h n)

theorem mem_succ {n : Nat} {x : HTerm (Cx T Γ0 hs0 n) .o} (m : x ∈ Hs T Γ0 hs0 n) :
    wk x ∈ Hs T Γ0 hs0 (n + 1) :=
  List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_cons_of_mem _ m))

noncomputable def liftTo (m : Nat) : (N : Nat) → m ≤ N → HRen (Cx T Γ0 hs0 m) (Cx T Γ0 hs0 N)
  | 0, h => fun v => by have e : m = 0 := by omega
                        subst e; exact v
  | N + 1, h => fun v => if h' : m ≤ N then .succ (liftTo m N h' v) else
      by have e : m = N + 1 := by omega
         subst e; exact v

theorem liftTo_succ {m N : Nat} (h : m ≤ N) {a} (v : HVar (Cx T Γ0 hs0 m) a) :
    liftTo T Γ0 hs0 m (N + 1) (Nat.le_succ_of_le h) v = .succ (liftTo T Γ0 hs0 m N h v) := by
  rw [liftTo.eq_2]; exact dif_pos h

theorem liftTo_refl : ∀ (m : Nat) (h : m ≤ m) {a} (v : HVar (Cx T Γ0 hs0 m) a), liftTo T Γ0 hs0 m m h v = v
  | 0, _, _, _ => rfl
  | m + 1, _, _, v => by
      rw [liftTo.eq_2]; exact (dif_neg (Nat.not_succ_le_self m)).trans rfl

theorem liftTo_trans {m n : Nat} (h1 : m ≤ n) : ∀ (N : Nat) (h2 : n ≤ N) (h3 : m ≤ N) {a}
    (v : HVar (Cx T Γ0 hs0 m) a),
    liftTo T Γ0 hs0 n N h2 (liftTo T Γ0 hs0 m n h1 v) = liftTo T Γ0 hs0 m N h3 v
  | 0, h2, h3, a, v => by
      obtain rfl : n = 0 := by omega
      obtain rfl : m = 0 := by omega
      rw [liftTo_refl]
  | N + 1, h2, h3, a, v => by
      by_cases hn : n ≤ N
      · rw [liftTo_succ T Γ0 hs0 hn, liftTo_succ T Γ0 hs0 (Nat.le_trans h1 hn),
          liftTo_trans h1 N hn (Nat.le_trans h1 hn)]
      · obtain rfl : n = N + 1 := by omega
        rw [liftTo_refl]

theorem good_liftTo (m : Nat) : ∀ (N : Nat) (h : m ≤ N), Good 0 (liftTo T Γ0 hs0 m N h)
  | 0, h => by
      obtain rfl : m = 0 := by omega
      intro v; show vcode 0 (liftTo T Γ0 hs0 0 0 h v) = _; rw [liftTo_refl]
  | N + 1, h => by
      by_cases hm : m ≤ N
      · intro v
        show vcode 0 (liftTo T Γ0 hs0 m (N + 1) h v) = _
        rw [liftTo_succ T Γ0 hs0 hm]
        exact (good_succ (liftTo T Γ0 hs0 m N hm v)).trans (good_liftTo m N hm v)
      · obtain rfl : m = N + 1 := by omega
        intro v; show vcode 0 (liftTo T Γ0 hs0 _ _ h v) = _; rw [liftTo_refl]

theorem rename_id' (t : HTerm Γ a) (r : HRen Γ Γ) (h : ∀ {b} (v : HVar Γ b), r v = v) : rename r t = t := by
  have e := subst_rename t r (fun v => .var v) (fun v => .var v) (fun v => by rw [h])
  rw [subst_id _ _ (fun _ => rfl), subst_id _ _ (fun _ => rfl)] at e; exact e

theorem inst_lift_var0 (χ : HTerm (a :: Γ) b) :
    inst (rename (liftR (fun v => (HVar.succ v : HVar (a :: Γ) _))) χ) (.var .zero) = χ := by
  unfold inst
  rw [subst_rename χ _ (sub0 (.var .zero)) (fun v => .var v) (fun v => by cases v <;> rfl)]
  exact subst_id χ _ (fun _ => rfl)

theorem rename_liftTo_succ {m n : Nat} (h : m ≤ n) (φ : HTerm (Cx T Γ0 hs0 m) a) :
    rename (liftTo T Γ0 hs0 m (n + 1) (Nat.le_succ_of_le h)) φ = wk (rename (liftTo T Γ0 hs0 m n h) φ) := by
  unfold wk
  exact (rename_rename φ _ _ _ (fun v => (liftTo_succ T Γ0 hs0 h v).symm)).symm

theorem rename_liftTo_trans {m n N : Nat} (h1 : m ≤ n) (h2 : n ≤ N) (φ : HTerm (Cx T Γ0 hs0 m) a) :
    rename (liftTo T Γ0 hs0 n N h2) (rename (liftTo T Γ0 hs0 m n h1) φ) =
      rename (liftTo T Γ0 hs0 m N (Nat.le_trans h1 h2)) φ :=
  rename_rename φ _ _ _ (fun v => liftTo_trans T Γ0 hs0 h1 N h2 _ v)

/-- Membership in the limit of the stages. -/
def Mem (m : Nat) (φ : HTerm (Cx T Γ0 hs0 m) .o) : Prop :=
  ∃ N, ∃ h : m ≤ N, rename (liftTo T Γ0 hs0 m N h) φ ∈ Hs T Γ0 hs0 N

theorem mem_mono {m N : Nat} (h : m ≤ N) (φ : HTerm (Cx T Γ0 hs0 m) .o)
    (hm : rename (liftTo T Γ0 hs0 m N h) φ ∈ Hs T Γ0 hs0 N) :
    ∀ d, rename (liftTo T Γ0 hs0 m (N + d) (Nat.le_trans h (Nat.le_add_right N d))) φ ∈ Hs T Γ0 hs0 (N + d)
  | 0 => hm
  | d + 1 => by
      show rename (liftTo T Γ0 hs0 m (N + d + 1) _) φ ∈ Hs T Γ0 hs0 (N + d + 1)
      rw [rename_liftTo_succ T Γ0 hs0 (Nat.le_trans h (Nat.le_add_right N d))]
      exact mem_succ T Γ0 hs0 (mem_mono h φ hm d)

theorem mem_at {m N : Nat} (φ : HTerm (Cx T Γ0 hs0 m) .o) (hφ : Mem T Γ0 hs0 m φ) (hN : m ≤ N) :
    ∃ N', ∃ h : N ≤ N', rename (liftTo T Γ0 hs0 m N' (Nat.le_trans hN h)) φ ∈ Hs T Γ0 hs0 N' := by
  obtain ⟨N0, h0, hm⟩ := hφ
  refine ⟨N0 + N, Nat.le_add_left N N0, ?_⟩
  exact mem_mono T Γ0 hs0 h0 φ hm N

theorem mem_all {m : Nat} : ∀ (hs : List (HTerm (Cx T Γ0 hs0 m) .o)), (∀ x, x ∈ hs → Mem T Γ0 hs0 m x) →
    ∃ N, ∃ h : m ≤ N, ∀ x, x ∈ hs → rename (liftTo T Γ0 hs0 m N h) x ∈ Hs T Γ0 hs0 N
  | [], _ => ⟨m, Nat.le_refl m, fun _ m => nomatch m⟩
  | x :: hs, hm => by
      obtain ⟨N1, h1, k1⟩ := mem_all hs (fun y my => hm y (List.mem_cons_of_mem _ my))
      obtain ⟨N2, h2, k2⟩ := mem_at T Γ0 hs0 x (hm x (List.mem_cons_self ..)) h1
      refine ⟨N2, Nat.le_trans h1 h2, fun y my => ?_⟩
      rcases List.mem_cons.1 my with rfl | my
      · exact k2
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h2
        exact mem_mono T Γ0 hs0 h1 y (k1 y my) d

/-- The limit is consistent. -/
theorem mem_consistent (hc : Cons T Γ0 hs0) {m : Nat} (hs : List (HTerm (Cx T Γ0 hs0 m) .o))
    (hm : ∀ x, x ∈ hs → Mem T Γ0 hs0 m x) : ¬ DC T (Cx T Γ0 hs0 m) hs .bot := by
  intro d
  obtain ⟨N, h, k⟩ := mem_all T Γ0 hs0 hs hm
  apply stage_cons T Γ0 hs0 hc N
  refine (d.ren (liftTo T Γ0 hs0 m N h)).weaken ?_
  intro y my
  obtain ⟨x, mx, rfl⟩ := List.mem_map.1 my
  exact k x mx

theorem mem_lift {m k : Nat} (h : m ≤ k) {φ : HTerm (Cx T Γ0 hs0 m) .o} (hφ : Mem T Γ0 hs0 m φ) :
    Mem T Γ0 hs0 k (rename (liftTo T Γ0 hs0 m k h) φ) := by
  obtain ⟨N', h', hm⟩ := mem_at T Γ0 hs0 φ hφ h
  exact ⟨N', h', by rw [rename_liftTo_trans]; exact hm⟩

theorem mem_self {N : Nat} {φ : HTerm (Cx T Γ0 hs0 N) .o} (h : φ ∈ Hs T Γ0 hs0 N) : Mem T Γ0 hs0 N φ :=
  ⟨N, Nat.le_refl N, by rw [rename_id' φ _ (fun v => liftTo_refl T Γ0 hs0 N _ v)]; exact h⟩

/-- The stage at which `φ` is decided. -/
noncomputable def dstage (m : Nat) (φ : HTerm (Cx T Γ0 hs0 m) .o) : Nat := pair m (codeL 0 φ)

theorem pick_at (m : Nat) (φ : HTerm (Cx T Γ0 hs0 m) .o) :
    pick T (dstage T Γ0 hs0 m φ) (Cx T Γ0 hs0 (dstage T Γ0 hs0 m φ)) (Hs T Γ0 hs0 (dstage T Γ0 hs0 m φ)) =
      (open Classical in
      if Cons T _ (rename (liftTo T Γ0 hs0 m _ (le_pair _ _)) φ :: Hs T Γ0 hs0 (dstage T Γ0 hs0 m φ))
      then rename (liftTo T Γ0 hs0 m _ (le_pair _ _)) φ
      else negH (rename (liftTo T Γ0 hs0 m _ (le_pair _ _)) φ)) := by
  have hc : codeL 0 (rename (liftTo T Γ0 hs0 m _ (le_pair m (codeL 0 φ))) φ) = codeL 0 φ :=
    codeL_rename φ 0 _ (good_liftTo T Γ0 hs0 m _ _)
  have hd : decL (Cx T Γ0 hs0 (dstage T Γ0 hs0 m φ)) .o (unpair (dstage T Γ0 hs0 m φ)).2 =
      some (rename (liftTo T Γ0 hs0 m _ (le_pair _ _)) φ) := by
    unfold dstage; rw [unpair_pair]
    have := decL_codeL (rename (liftTo T Γ0 hs0 m _ (le_pair m (codeL 0 φ))) φ)
    rw [hc] at this; exact this
  unfold pick; rw [hd]; rfl

theorem pick_mem (k : Nat) (x : HTerm (Cx T Γ0 hs0 k) .o)
    (hx : x = pick T k (Cx T Γ0 hs0 k) (Hs T Γ0 hs0 k)) : wk x ∈ Hs T Γ0 hs0 (k + 1) := by
  subst hx
  exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_cons_self ..))

/-- The limit is maximal. -/
theorem mem_max (m : Nat) (φ : HTerm (Cx T Γ0 hs0 m) .o) :
    Mem T Γ0 hs0 m φ ∨ Mem T Γ0 hs0 m (negH φ) := by
  have hp := pick_at T Γ0 hs0 m φ
  have hk := le_pair m (codeL 0 φ)
  split at hp
  · left
    refine ⟨_, Nat.le_succ_of_le hk, ?_⟩
    rw [rename_liftTo_succ T Γ0 hs0 hk]
    exact pick_mem T Γ0 hs0 _ _ hp.symm
  · right
    refine ⟨_, Nat.le_succ_of_le hk, ?_⟩
    rw [rename_liftTo_succ T Γ0 hs0 hk]
    exact pick_mem T Γ0 hs0 _ _ hp.symm

theorem mem_not_both (hc : Cons T Γ0 hs0) {m : Nat} {φ : HTerm (Cx T Γ0 hs0 m) .o}
    (h1 : Mem T Γ0 hs0 m φ) (h2 : Mem T Γ0 hs0 m (negH φ)) : False := by
  refine mem_consistent T Γ0 hs0 hc [φ, negH φ] ?_ ?_
  · intro x mx; simp only [List.mem_cons, List.not_mem_nil, or_false] at mx
    rcases mx with rfl | rfl <;> assumption
  · exact .impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (.hyp (List.mem_cons_self ..))

theorem step_wit (k : Nat) (s : St) {a : HTy} (χ : HTerm (a :: s.Γ) .o)
    (hp : pick T k s.Γ s.hs = .ex a χ) :
    ∃ x : HVar (step T k s).Γ a, inst (rename (liftR (fun v => (HVar.succ v : HVar (step T k s).Γ _))) χ) (.var x) ∈
      (step T k s).hs := by
  unfold step
  generalize pick T k s.Γ s.hs = p at hp ⊢
  subst hp
  refine ⟨.zero, ?_⟩
  show inst (rename (liftR (fun v => (HVar.succ v : HVar (a :: s.Γ) _))) χ) (.var .zero) ∈
    (χ :: ((HTerm.ex a χ :: s.hs).map wk : List (HTerm (a :: s.Γ) .o)))
  rw [inst_lift_var0]; exact List.mem_cons_self ..

/-- The limit has Henkin witnesses. -/
theorem mem_henkin (hc : Cons T Γ0 hs0) {m : Nat} {a : HTy} {χ : HTerm (a :: Cx T Γ0 hs0 m) .o}
    (h : Mem T Γ0 hs0 m (.ex a χ)) :
    ∃ N, ∃ hN : m ≤ N, ∃ x : HVar (Cx T Γ0 hs0 N) a,
      Mem T Γ0 hs0 N (inst (rename (liftR (liftTo T Γ0 hs0 m N hN)) χ) (.var x)) := by
  have hk := le_pair m (codeL 0 (HTerm.ex a χ))
  have hp := pick_at T Γ0 hs0 m (.ex a χ)
  split at hp
  · obtain ⟨x, hx⟩ := step_wit T _ _ _ hp
    refine ⟨_ + 1, Nat.le_succ_of_le hk, x, mem_self T Γ0 hs0 ?_⟩
    have e : rename (liftR (fun v => (HVar.succ v : HVar (Cx T Γ0 hs0 (dstage T Γ0 hs0 m (.ex a χ) + 1)) _)))
        (rename (liftR (liftTo T Γ0 hs0 m _ hk)) χ) =
        rename (liftR (liftTo T Γ0 hs0 m _ (Nat.le_succ_of_le hk))) χ :=
      rename_rename χ _ _ _ (fun v => by
        cases v with
        | zero => rfl
        | succ v => exact congrArg HVar.succ (liftTo_succ T Γ0 hs0 hk v).symm)
    rw [← e]; exact hx
  · exfalso
    rename_i hn
    have m1 : Mem T Γ0 hs0 (dstage T Γ0 hs0 m (.ex a χ) + 1) (wk (negH (rename (liftTo T Γ0 hs0 m _ hk) (.ex a χ)))) :=
      mem_self T Γ0 hs0 (pick_mem T Γ0 hs0 _ _ hp.symm)
    have m2 := mem_lift T Γ0 hs0 (Nat.le_succ_of_le hk) h
    rw [rename_liftTo_succ T Γ0 hs0 hk] at m2
    exact mem_not_both T Γ0 hs0 hc m2 m1

/-- The limit is deductively closed. -/
theorem mem_deriv (hc : Cons T Γ0 hs0) {m : Nat} {hs : List (HTerm (Cx T Γ0 hs0 m) .o)}
    {φ : HTerm (Cx T Γ0 hs0 m) .o} (hm : ∀ x, x ∈ hs → Mem T Γ0 hs0 m x) (d : DC T (Cx T Γ0 hs0 m) hs φ) :
    Mem T Γ0 hs0 m φ := by
  rcases mem_max T Γ0 hs0 m φ with h | h
  · exact h
  · exfalso
    refine mem_consistent T Γ0 hs0 hc (negH φ :: hs) ?_ (.impE (.hyp (List.mem_cons_self ..)) (d.wk1 _))
    intro x mx
    rcases List.mem_cons.1 mx with rfl | mx
    · exact h
    · exact hm x mx

/-- The starting point of completeness: a non-derivable `⟦φ⟧` at a world variable. -/
theorem start_cons {φ : Tm [] .s} (h : ¬ DC T [.w] [] (.holds (emb nilR φ) var0)) :
    Cons T [.w] [negH (.holds (emb nilR φ) var0)] :=
  fun d => h (.byContra d)

end lind
end Programme.«20261022-1724-ontological».ThHenkin

/-! ## M3d: the canonical model -/

namespace Programme.«20261022-1724-ontological».ThCanon
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX Programme.«20261022-1724-ontological».ThHenkin
noncomputable section

/-! ### Normal form of certified terms -/

def Lpart : List HTy → List FTy
  | [] => []
  | .L t :: Γ => t :: Lpart Γ
  | .w :: Γ => Lpart Γ
  | .o :: Γ => Lpart Γ

def canonR : {Γ : List HTy} → {t : FTy} → Var (Lpart Γ) t → HVar Γ (.L t)
  | .L _ :: _, _, .zero => .zero
  | .L _ :: Γ, _, .succ v => .succ (canonR (Γ := Γ) v)
  | .w :: Γ, _, v => .succ (canonR (Γ := Γ) v)
  | .o :: Γ, _, v => .succ (canonR (Γ := Γ) v)

def lposG : {Γ : List HTy} → {a : HTy} → HVar Γ a → (t : FTy) → a = .L t → Var (Lpart Γ) t
  | _, _, @HVar.zero Γ a, t, h =>
      match a, h with
      | .L _, rfl => (Var.zero : Var (Lpart (.L t :: Γ)) t)
  | _, _, @HVar.succ Γ _ b v, t, h =>
      match b with
      | .L _ => .succ (lposG v t h)
      | .w => lposG v t h
      | .o => lposG v t h

def lpos {Γ : List HTy} {t : FTy} (v : HVar Γ (.L t)) : Var (Lpart Γ) t := lposG v t rfl

theorem canonR_lposG : ∀ {Γ : List HTy} {a : HTy} (v : HVar Γ a) (t : FTy) (h : a = .L t),
    canonR (lposG v t h) = h ▸ v
  | _, _, @HVar.zero Γ a, t, h => by cases h; rfl
  | _, _, @HVar.succ Γ _ b v, t, h => by
      cases h
      cases b <;> simp only [lposG, canonR, canonR_lposG v _ rfl]

theorem canonR_lpos {Γ : List HTy} {t : FTy} (v : HVar Γ (.L t)) : canonR (lpos v) = v :=
  canonR_lposG v t rfl

theorem lpos_canonR : ∀ {Γ : List HTy} {t : FTy} (v : Var (Lpart Γ) t), lpos (canonR v) = v
  | .L _ :: _, _, .zero => rfl
  | .L _ :: Γ, _, .succ v => congrArg Var.succ (lpos_canonR (Γ := Γ) v)
  | .w :: Γ, _, v => lpos_canonR (Γ := Γ) v
  | .o :: Γ, _, v => lpos_canonR (Γ := Γ) v

/-- Every embedded term is an embedding through the canonical renaming. -/
theorem emb_nf (r : LRen Γ' Γ) (s : Tm Γ' t) :
    emb r s = emb canonR (renameL (fun v => lpos (r v)) s) :=
  (emb_renameL s _ canonR r (fun v => canonR_lpos (r v))).symm

theorem cert_nf {x : HTerm Γ (.L t)} (h : Cert (.L t) x) : ∃ s : Tm (Lpart Γ) t, x = emb canonR s := by
  obtain ⟨_, s, r, rfl⟩ := h
  exact ⟨_, emb_nf r s⟩


/-! ### 𝓛-level substitution algebra -/

theorem substL_renameL : ∀ {Γ Δ Θ t} (tm : Tm Γ t) (q : RenL Γ Δ) (s : SubL Δ Θ) (s' : SubL Γ Θ),
    (∀ {u} (v : Var Γ u), s (q v) = s' v) → substL s (renameL q tm) = substL s' tm := by
  intro Γ Δ Θ t tm
  induction tm generalizing Δ Θ with
  | var i => intro q s s' h; simp only [renameL, substL, h]
  | app F x ihF ihx => intro q s s' h; simp only [renameL, substL, ihF q s s' h, ihx q s s' h]
  | lam b ih =>
      intro q s s' h; simp only [renameL, substL]
      rw [ih (liftRL q) (liftSL s) (liftSL s') (fun v => by cases v <;> simp [liftRL, liftSL, h])]
  | top => intros; rfl
  | bot => intros; rfl
  | neg x ih => intro q s s' h; simp only [renameL, substL, ih q s s' h]
  | and x y ihx ihy => intro q s s' h; simp only [renameL, substL, ihx q s s' h, ihy q s s' h]
  | or x y ihx ihy => intro q s s' h; simp only [renameL, substL, ihx q s s' h, ihy q s s' h]
  | imp x y ihx ihy => intro q s s' h; simp only [renameL, substL, ihx q s s' h, ihy q s s' h]
  | box x ih => intro q s s' h; simp only [renameL, substL, ih q s s' h]
  | all a b ih =>
      intro q s s' h; simp only [renameL, substL]
      rw [ih (liftRL q) (liftSL s) (liftSL s') (fun v => by cases v <;> simp [liftRL, liftSL, h])]
  | ex a b ih =>
      intro q s s' h; simp only [renameL, substL]
      rw [ih (liftRL q) (liftSL s) (liftSL s') (fun v => by cases v <;> simp [liftRL, liftSL, h])]
  | allE b ih =>
      intro q s s' h; simp only [renameL, substL]
      rw [ih (liftRL q) (liftSL s) (liftSL s') (fun v => by cases v <;> simp [liftRL, liftSL, h])]
  | exE b ih =>
      intro q s s' h; simp only [renameL, substL]
      rw [ih (liftRL q) (liftSL s) (liftSL s') (fun v => by cases v <;> simp [liftRL, liftSL, h])]
  | eq a x y ihx ihy => intro q s s' h; simp only [renameL, substL, ihx q s s' h, ihy q s s' h]
  | pos => intros; rfl

theorem renameL_renameL : ∀ {Γ Δ Θ t} (tm : Tm Γ t) (q : RenL Γ Δ) (q' : RenL Δ Θ) (q'' : RenL Γ Θ),
    (∀ {u} (v : Var Γ u), q' (q v) = q'' v) → renameL q' (renameL q tm) = renameL q'' tm := by
  intro Γ Δ Θ t tm
  induction tm generalizing Δ Θ with
  | var i => intro q s s' h; simp only [renameL, h]
  | app F x ihF ihx => intro q s s' h; simp only [renameL, ihF q s s' h, ihx q s s' h]
  | lam b ih =>
      intro q s s' h; simp only [renameL]
      rw [ih (liftRL q) (liftRL s) (liftRL s') (fun v => by cases v <;> simp [liftRL, h])]
  | top => intros; rfl
  | bot => intros; rfl
  | neg x ih => intro q s s' h; simp only [renameL, ih q s s' h]
  | and x y ihx ihy => intro q s s' h; simp only [renameL, ihx q s s' h, ihy q s s' h]
  | or x y ihx ihy => intro q s s' h; simp only [renameL, ihx q s s' h, ihy q s s' h]
  | imp x y ihx ihy => intro q s s' h; simp only [renameL, ihx q s s' h, ihy q s s' h]
  | box x ih => intro q s s' h; simp only [renameL, ih q s s' h]
  | all a b ih =>
      intro q s s' h; simp only [renameL]
      rw [ih (liftRL q) (liftRL s) (liftRL s') (fun v => by cases v <;> simp [liftRL, h])]
  | ex a b ih =>
      intro q s s' h; simp only [renameL]
      rw [ih (liftRL q) (liftRL s) (liftRL s') (fun v => by cases v <;> simp [liftRL, h])]
  | allE b ih =>
      intro q s s' h; simp only [renameL]
      rw [ih (liftRL q) (liftRL s) (liftRL s') (fun v => by cases v <;> simp [liftRL, h])]
  | exE b ih =>
      intro q s s' h; simp only [renameL]
      rw [ih (liftRL q) (liftRL s) (liftRL s') (fun v => by cases v <;> simp [liftRL, h])]
  | eq a x y ihx ihy => intro q s s' h; simp only [renameL, ihx q s s' h, ihy q s s' h]
  | pos => intros; rfl

theorem renameL_wkL (q : RenL Γ Δ) (t : Tm Γ u) :
    renameL (liftRL (a := a) q) (wkL t) = wkL (renameL q t) := by
  unfold wkL
  exact (renameL_renameL t (fun v => .succ v) (liftRL q) (fun v => .succ (q v)) (fun _ => rfl)).trans
    (renameL_renameL t q (fun v => .succ v) (fun v => .succ (q v)) (fun _ => rfl)).symm

theorem renameL_substL : ∀ {Γ Δ Θ t} (tm : Tm Γ t) (s : SubL Γ Δ) (q : RenL Δ Θ) (s' : SubL Γ Θ),
    (∀ {u} (v : Var Γ u), renameL q (s v) = s' v) → renameL q (substL s tm) = substL s' tm := by
  intro Γ Δ Θ t tm
  induction tm generalizing Δ Θ with
  | var i => intro s q s' h; simp only [substL, h]
  | app F x ihF ihx => intro s q s' h; simp only [renameL, substL, ihF s q s' h, ihx s q s' h]
  | lam b ih =>
      intro s q s' h; simp only [renameL, substL]
      rw [ih (liftSL s) (liftRL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [renameL_wkL, h])]
  | top => intros; rfl
  | bot => intros; rfl
  | neg x ih => intro s q s' h; simp only [renameL, substL, ih s q s' h]
  | and x y ihx ihy => intro s q s' h; simp only [renameL, substL, ihx s q s' h, ihy s q s' h]
  | or x y ihx ihy => intro s q s' h; simp only [renameL, substL, ihx s q s' h, ihy s q s' h]
  | imp x y ihx ihy => intro s q s' h; simp only [renameL, substL, ihx s q s' h, ihy s q s' h]
  | box x ih => intro s q s' h; simp only [renameL, substL, ih s q s' h]
  | all a b ih =>
      intro s q s' h; simp only [renameL, substL]
      rw [ih (liftSL s) (liftRL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [renameL_wkL, h])]
  | ex a b ih =>
      intro s q s' h; simp only [renameL, substL]
      rw [ih (liftSL s) (liftRL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [renameL_wkL, h])]
  | allE b ih =>
      intro s q s' h; simp only [renameL, substL]
      rw [ih (liftSL s) (liftRL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [renameL_wkL, h])]
  | exE b ih =>
      intro s q s' h; simp only [renameL, substL]
      rw [ih (liftSL s) (liftRL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [renameL_wkL, h])]
  | eq a x y ihx ihy => intro s q s' h; simp only [renameL, substL, ihx s q s' h, ihy s q s' h]
  | pos => intros; rfl

theorem substL_wkL (s : SubL Γ Δ) (t : Tm Γ u) :
    substL (liftSL (a := a) s) (wkL t) = wkL (substL s t) := by
  unfold wkL
  exact (substL_renameL t (fun v => .succ v) (liftSL s) (fun v => wkL (s v)) (fun _ => rfl)).trans
    (renameL_substL t s (fun v => .succ v) (fun v => wkL (s v)) (fun _ => rfl)).symm

theorem substL_substL : ∀ {Γ Δ Θ t} (tm : Tm Γ t) (s : SubL Γ Δ) (s' : SubL Δ Θ) (s'' : SubL Γ Θ),
    (∀ {u} (v : Var Γ u), substL s' (s v) = s'' v) → substL s' (substL s tm) = substL s'' tm := by
  intro Γ Δ Θ t tm
  induction tm generalizing Δ Θ with
  | var i => intro s q s' h; simp only [substL, h]
  | app F x ihF ihx => intro s q s' h; simp only [substL, ihF s q s' h, ihx s q s' h]
  | lam b ih =>
      intro s q s' h; simp only [substL]
      rw [ih (liftSL s) (liftSL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [substL_wkL, h])]
  | top => intros; rfl
  | bot => intros; rfl
  | neg x ih => intro s q s' h; simp only [substL, ih s q s' h]
  | and x y ihx ihy => intro s q s' h; simp only [substL, ihx s q s' h, ihy s q s' h]
  | or x y ihx ihy => intro s q s' h; simp only [substL, ihx s q s' h, ihy s q s' h]
  | imp x y ihx ihy => intro s q s' h; simp only [substL, ihx s q s' h, ihy s q s' h]
  | box x ih => intro s q s' h; simp only [substL, ih s q s' h]
  | all a b ih =>
      intro s q s' h; simp only [substL]
      rw [ih (liftSL s) (liftSL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [substL_wkL, h])]
  | ex a b ih =>
      intro s q s' h; simp only [substL]
      rw [ih (liftSL s) (liftSL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [substL_wkL, h])]
  | allE b ih =>
      intro s q s' h; simp only [substL]
      rw [ih (liftSL s) (liftSL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [substL_wkL, h])]
  | exE b ih =>
      intro s q s' h; simp only [substL]
      rw [ih (liftSL s) (liftSL q) (liftSL s') (fun v => by
        cases v with
        | zero => rfl
        | succ v => simp only [liftSL]; rw [substL_wkL, h])]
  | eq a x y ihx ihy => intro s q s' h; simp only [substL, ihx s q s' h, ihy s q s' h]
  | pos => intros; rfl

theorem sub0L_wkL (t : Tm Γ a) (x : Tm Γ b) : substL (sub0L x) (wkL t) = t := by
  rw [wkL, substL_renameL _ _ (sub0L x) (fun v => .var v) (fun _ => rfl), substL_id _ _ (fun _ => rfl)]

/-- Instantiating a lifted substitution: `(s↑ b)[x] = (x · s) b`. -/
def consL (x : Tm Δ a) (s : SubL Γ Δ) : SubL (a :: Γ) Δ
  | _, .zero => x
  | _, .succ v => s v

theorem instL_liftSL (b : Tm (a :: Γ) u) (s : SubL Γ Δ) (x : Tm Δ a) :
    instL (substL (liftSL s) b) x = substL (consL x s) b :=
  substL_substL b _ _ _ (fun v => by
    cases v with
    | zero => rfl
    | succ v => exact sub0L_wkL _ _)

theorem renameL_id' (tm : Tm Γ t) (q : RenL Γ Γ) (h : ∀ {u} (v : Var Γ u), q v = v) : renameL q tm = tm := by
  have := substL_renameL tm q (fun v => .var v) (fun v => .var v) (fun v => by simp only [h])
  rwa [substL_id _ _ (fun _ => rfl), substL_id _ _ (fun _ => rfl)] at this

/-! ### The seed and stage bookkeeping -/

/-- Data of the canonical construction: a consistent start with a world term. -/
structure Seed where
  T : Tm [] .s → Prop
  Γ0 : List HTy
  hs0 : List (HTerm Γ0 .o)
  hc : Cons T Γ0 hs0
  i0 : HTerm Γ0 .w

namespace Seed
variable (Z : Seed)

noncomputable abbrev X (n : Nat) : List HTy := Cx Z.T Z.Γ0 Z.hs0 n
noncomputable abbrev lt (m N : Nat) (h : m ≤ N) : HRen (Z.X m) (Z.X N) := liftTo Z.T Z.Γ0 Z.hs0 m N h
abbrev M (n : Nat) (φ : HTerm (Z.X n) .o) : Prop := Mem Z.T Z.Γ0 Z.hs0 n φ
abbrev D (n : Nat) (hs : List (HTerm (Z.X n) .o)) (φ : HTerm (Z.X n) .o) : Prop := DC Z.T (Z.X n) hs φ
noncomputable abbrev Lp (n : Nat) : List FTy := Lpart (Z.X n)

theorem lt_trans {m n N : Nat} (h1 : m ≤ n) (h2 : n ≤ N) (h3 : m ≤ N) {a} (v : HVar (Z.X m) a) :
    Z.lt n N h2 (Z.lt m n h1 v) = Z.lt m N h3 v := liftTo_trans Z.T Z.Γ0 Z.hs0 h1 N h2 h3 v

theorem lt_refl (m : Nat) (h : m ≤ m) {a} (v : HVar (Z.X m) a) : Z.lt m m h v = v :=
  liftTo_refl Z.T Z.Γ0 Z.hs0 m h v

theorem ren_trans {m n N : Nat} (h1 : m ≤ n) (h2 : n ≤ N) (h3 : m ≤ N) (φ : HTerm (Z.X m) a) :
    rename (Z.lt n N h2) (rename (Z.lt m n h1) φ) = rename (Z.lt m N h3) φ :=
  rename_rename φ _ _ _ (fun v => Z.lt_trans h1 h2 h3 v)

theorem ren_refl (m : Nat) (h : m ≤ m) (φ : HTerm (Z.X m) a) : rename (Z.lt m m h) φ = φ :=
  rename_id' φ _ (fun v => Z.lt_refl m h v)

theorem M_deriv {n : Nat} {hs : List (HTerm (Z.X n) .o)} {φ : HTerm (Z.X n) .o}
    (hm : ∀ x, x ∈ hs → Z.M n x) (d : Z.D n hs φ) : Z.M n φ :=
  mem_deriv Z.T Z.Γ0 Z.hs0 Z.hc hm d

theorem M_of {n : Nat} {φ : HTerm (Z.X n) .o} (d : Z.D n [] φ) : Z.M n φ :=
  Z.M_deriv (fun _ m => by simp at m) d

theorem M_mp {n : Nat} {φ ψ : HTerm (Z.X n) .o} (h : Z.M n φ) (d : Z.D n [φ] ψ) : Z.M n ψ :=
  Z.M_deriv (fun x m => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at m; subst m; exact h) d

theorem M_mp2 {n : Nat} {φ φ' ψ : HTerm (Z.X n) .o} (h : Z.M n φ) (h' : Z.M n φ') (d : Z.D n [φ, φ'] ψ) :
    Z.M n ψ :=
  Z.M_deriv (fun x m => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl <;> assumption) d

theorem M_max (n : Nat) (φ : HTerm (Z.X n) .o) : Z.M n φ ∨ Z.M n (negH φ) := mem_max Z.T Z.Γ0 Z.hs0 n φ

theorem M_not_both {n : Nat} {φ : HTerm (Z.X n) .o} (h1 : Z.M n φ) (h2 : Z.M n (negH φ)) : False :=
  mem_not_both Z.T Z.Γ0 Z.hs0 Z.hc h1 h2

theorem M_neg {n : Nat} {φ : HTerm (Z.X n) .o} : Z.M n (negH φ) ↔ ¬ Z.M n φ :=
  ⟨fun h h' => Z.M_not_both h' h, fun h => (Z.M_max n φ).resolve_left h⟩

theorem M_bot {n : Nat} : ¬ Z.M n .bot := fun h =>
  mem_consistent Z.T Z.Γ0 Z.hs0 Z.hc [.bot] (fun x m => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at m; subst m; exact h)
    (.hyp (List.mem_cons_self ..))

theorem M_lift {n K : Nat} (h : n ≤ K) (φ : HTerm (Z.X n) .o) :
    Z.M n φ ↔ Z.M K (rename (Z.lt n K h) φ) := by
  constructor
  · exact fun m => mem_lift Z.T Z.Γ0 Z.hs0 h m
  · intro m
    rcases Z.M_max n φ with h1 | h1
    · exact h1
    · exact (Z.M_not_both m (mem_lift Z.T Z.Γ0 Z.hs0 h h1)).elim

/-- Stage independence for natural families of formulas. -/
theorem transfer {m : Nat} (Φ : (K : Nat) → m ≤ K → HTerm (Z.X K) .o)
    (nat : ∀ K K' (hK : m ≤ K) (h : K ≤ K'), rename (Z.lt K K' h) (Φ K hK) = Φ K' (Nat.le_trans hK h))
    {K1 K2 : Nat} (h1 : m ≤ K1) (h2 : m ≤ K2) (m1 : Z.M K1 (Φ K1 h1)) : Z.M K2 (Φ K2 h2) := by
  have a := (Z.M_lift (Nat.le_max_left K1 K2) _).1 m1
  rw [nat] at a
  rw [Z.M_lift (Nat.le_max_right K1 K2), nat]
  exact a

/-! ### Global terms: an 𝓛-term over the 𝓛-part of some stage -/

abbrev G (t : FTy) : Type := Σ n, Tm (Z.Lp n) t

/-- Stage lifting on the 𝓛-part. -/
noncomputable def qL (m N : Nat) (h : m ≤ N) : RenL (Z.Lp m) (Z.Lp N) := fun v => lpos (Z.lt m N h (canonR v))

theorem emb_qL {m N : Nat} (h : m ≤ N) (s : Tm (Z.Lp m) t) :
    emb canonR (renameL (Z.qL m N h) s) = rename (Z.lt m N h) (emb canonR s) := by
  exact (emb_renameL s _ canonR (fun v => Z.lt m N h (canonR v)) (fun v => canonR_lpos _)).trans
    (rename_emb s _ canonR _ (fun _ => rfl)).symm

theorem qL_trans {m n N : Nat} (h1 : m ≤ n) (h2 : n ≤ N) (h3 : m ≤ N) {u} (v : Var (Z.Lp m) u) :
    Z.qL n N h2 (Z.qL m n h1 v) = Z.qL m N h3 v := by
  simp only [qL, canonR_lpos, Z.lt_trans h1 h2 h3]

theorem qL_refl (m : Nat) (h : m ≤ m) {u} (v : Var (Z.Lp m) u) : Z.qL m m h v = v := by
  simp only [qL, Z.lt_refl, lpos_canonR]

variable {Z}

noncomputable def liftG (x : Z.G t) (N : Nat) (h : x.1 ≤ N) : Tm (Z.Lp N) t := renameL (Z.qL x.1 N h) x.2

/-- The embedded image of a global term at a stage. -/
noncomputable def E (x : Z.G t) (N : Nat) (h : x.1 ≤ N) : HTerm (Z.X N) (.L t) := emb canonR (liftG x N h)

theorem E_ren (x : Z.G t) (N : Nat) (h : x.1 ≤ N) : E x N h = rename (Z.lt x.1 N h) (emb canonR x.2) :=
  Z.emb_qL h x.2

theorem liftG_trans (x : Z.G t) {N N' : Nat} (h : x.1 ≤ N) (h' : N ≤ N') :
    renameL (Z.qL N N' h') (liftG x N h) = liftG x N' (Nat.le_trans h h') :=
  renameL_renameL _ _ _ _ (fun v => Z.qL_trans _ _ _ v)

theorem E_nat (x : Z.G t) {N N' : Nat} (h : x.1 ≤ N) (h' : N ≤ N') :
    rename (Z.lt N N' h') (E x N h) = E x N' (Nat.le_trans h h') := by
  rw [E_ren, E_ren, Z.ren_trans]

theorem liftG_self (x : Z.G t) (h : x.1 ≤ x.1) : liftG x x.1 h = x.2 :=
  renameL_id' _ _ (fun v => Z.qL_refl x.1 h v)

/-- Worlds: a world term at some stage. -/
abbrev Wd (Z : Seed) : Type := Σ n, HTerm (Z.X n) .w

noncomputable def wl (w : Z.Wd) (N : Nat) (h : w.1 ≤ N) : HTerm (Z.X N) .w := rename (Z.lt w.1 N h) w.2

theorem wl_nat (w : Z.Wd) {N N' : Nat} (h : w.1 ≤ N) (h' : N ≤ N') :
    rename (Z.lt N N' h') (wl w N h) = wl w N' (Nat.le_trans h h') := Z.ren_trans _ _ _ _

end Seed

/-! ### Derivation helpers -/

section dh
variable {T : Tm [] .s → Prop} {Γ' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)} {r : LRen Γ' Γ}

def oneR (v : HVar Γ (.L t)) : LRen [t] Γ
  | _, .zero => v

theorem cert_var (v : HVar Γ (.L t)) : Cert (.L t) (.var v) := ⟨[t], .var .zero, oneR v, rfl⟩

theorem cert_var0 : ∀ (a : HTy), Cert a (var0 : HTerm (a :: Γ) a)
  | .L _ => cert_var _
  | .w => trivial
  | .o => trivial

theorem inst_ren_wk (ρ : HRen Γ Δ) (P : HTerm Γ c) (t : HTerm Δ a) :
    inst (rename (liftR ρ) (wk P)) t = rename ρ P := by rw [rename_liftR_wk, inst_wk]

/-- `¬∀ ⊢ ∃¬`. -/
theorem d_ex_not {φ : HTerm (a :: Γ) .o} : DC T Γ (negH (.all a φ) :: hs) (.ex a (negH φ)) := by
  refine .byContra (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (.allI a (.byContra ?_)))
  refine .impE (φ := .ex a (rename (liftR (fun v => (HVar.succ v : HVar (a :: Γ) _))) (negH φ))) (.hyp ?_) ?_
  · exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_cons_self ..))
  · refine .exI a var0 (cert_var0 a) ?_
    rw [inst_lift_var0]; exact .hyp (List.mem_cons_self ..)

theorem d_holds_rw {p q : HTerm Γ (.L .s)} {i : HTerm Γ .w} (e : DC T Γ hs (.eq (.L .s) p q))
    (d : DC T Γ hs (.holds p i)) : DC T Γ hs (.holds q i) := by
  have h := Deriv.subst (.L .s) (.holds var0 (wk i)) rfl e (by
    show DC T Γ hs (.holds p (inst (wk i) p)); rw [inst_wk]; exact d)
  show DC T Γ hs (.holds q i)
  have e2 : inst (HTerm.holds var0 (wk i)) q = .holds q i := by
    show HTerm.holds q (inst (wk i) q) = _; rw [inst_wk]
  rw [e2] at h; exact h

theorem d_act_rw {x y : HTerm Γ (.L .e)} {i : HTerm Γ .w} (e : DC T Γ hs (.eq (.L .e) x y))
    (d : DC T Γ hs (.act x i)) : DC T Γ hs (.act y i) := by
  have h := Deriv.subst (.L .e) (.act var0 (wk i)) rfl e (by
    show DC T Γ hs (.act x (inst (wk i) x)); rw [inst_wk]; exact d)
  have e2 : inst (HTerm.act var0 (wk i)) y = .act y i := by
    show HTerm.act y (inst (wk i) y) = _; rw [inst_wk]
  rw [e2] at h; exact h

/-- Congruence: an `𝓛`-context respects provable equality of `𝓛`-terms. -/
theorem d_cong (i : HTerm Γ .w) {x y : Tm Γ' a} (B : Tm (a :: Γ') b)
    (e : DC T Γ hs (.eq (.L a) (emb r x) (emb r y))) :
    DC T Γ hs (.eq (.L b) (emb r (instL B x)) (emb r (instL B y))) := by
  have hx : instL (Tm.eq b (wkL (instL B x)) B) x = .eq b (instL B x) (instL B x) := by
    show Tm.eq b (substL (sub0L x) (wkL (instL B x))) (instL B x) = _; rw [sub0L_wkL]
  have hy : instL (Tm.eq b (wkL (instL B x)) B) y = .eq b (instL B x) (instL B y) := by
    show Tm.eq b (substL (sub0L y) (wkL (instL B x))) (instL B y) = _; rw [sub0L_wkL]
  have d0 : DC T Γ hs (Lf r (instL (Tm.eq b (wkL (instL B x)) B) x) i) := by
    rw [hx]; exact L_eqI (Deriv.refl _ _)
  have d1 := L_leib _ e d0
  rw [hy] at d1
  exact L_eqE d1

theorem d_app (i : HTerm Γ .w) {f f' : Tm Γ' (.arr a b)} {x x' : Tm Γ' a}
    (ef : DC T Γ hs (.eq (.L (.arr a b)) (emb r f) (emb r f')))
    (ex : DC T Γ hs (.eq (.L a) (emb r x) (emb r x'))) :
    DC T Γ hs (.eq (.L b) (emb r (.app f x)) (emb r (.app f' x'))) := by
  have h1 := Deriv.allE (.L a) (emb r x) (Deriv.funApp ef) (cert_emb r x)
  have e1 : inst (HTerm.eq (.L b) (.appL (wk (emb r f)) var0) (.appL (wk (emb r f')) var0)) (emb r x) =
      .eq (.L b) (.appL (emb r f) (emb r x)) (.appL (emb r f') (emb r x)) := by
    show HTerm.eq _ (.appL (inst (wk (emb r f)) (emb r x)) (emb r x))
      (.appL (inst (wk (emb r f')) (emb r x)) (emb r x)) = _
    rw [inst_wk, inst_wk]
  rw [e1] at h1
  have h2 := d_cong i (Tm.app (wkL f') (.var .zero)) ex
  have e2 : ∀ z : Tm Γ' a, instL (Tm.app (wkL f') (.var .zero)) z = .app f' z := fun z => by
    show Tm.app (substL (sub0L z) (wkL f')) z = _; rw [sub0L_wkL]
  rw [e2, e2] at h2
  exact Deriv.trans _ h1 h2

end dh

/-! ### The canonical model -/

namespace Seed
variable {Z : Seed}

/-- A world term at every stage. -/
noncomputable def wK (Z : Seed) (K : Nat) : HTerm (Z.X K) .w := rename (Z.lt 0 K (Nat.zero_le K)) Z.i0

theorem E_mk (n : Nat) (s : Tm (Z.Lp n) t) (K : Nat) (h : n ≤ K) :
    E (⟨n, s⟩ : Z.G t) K h = rename (Z.lt n K h) (emb canonR s) := E_ren _ _ _

def Eqv (x y : Z.G t) : Prop :=
  ∀ K (hx : x.1 ≤ K) (hy : y.1 ≤ K), Z.M K (.eq (.L t) (E x K hx) (E y K hy))

theorem eqv_at {x y : Z.G t} {K : Nat} (hx : x.1 ≤ K) (hy : y.1 ≤ K)
    (m : Z.M K (.eq (.L t) (E x K hx) (E y K hy))) : Eqv x y := fun K' hx' hy' =>
  Z.transfer (m := max x.1 y.1)
    (fun K hK => .eq (.L t) (E x K (Nat.le_trans (Nat.le_max_left _ _) hK))
      (E y K (Nat.le_trans (Nat.le_max_right _ _) hK)))
    (fun K K' hK h => by
      show HTerm.eq _ (rename _ (E x K _)) (rename _ (E y K _)) = _
      rw [E_nat, E_nat])
    (Nat.max_le.2 ⟨hx, hy⟩) (Nat.max_le.2 ⟨hx', hy'⟩) m

theorem eqv_refl (x : Z.G t) : Eqv x x :=
  eqv_at (Nat.le_refl _) (Nat.le_refl _) (Z.M_of (.refl _ _))

theorem eqv_symm {x y : Z.G t} (h : Eqv x y) : Eqv y x :=
  eqv_at (K := max y.1 x.1) (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    (Z.M_mp (h _ (Nat.le_max_right _ _) (Nat.le_max_left _ _)) (.symm _ (.hyp (List.mem_cons_self ..))))

theorem eqv_trans {x y z : Z.G t} (h1 : Eqv x y) (h2 : Eqv y z) : Eqv x z := by
  have hx : x.1 ≤ max (max x.1 y.1) z.1 := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hy : y.1 ≤ max (max x.1 y.1) z.1 := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hz : z.1 ≤ max (max x.1 y.1) z.1 := Nat.le_max_right _ _
  exact eqv_at hx hz (Z.M_mp2 (h1 _ hx hy) (h2 _ hy hz)
    (.trans _ (.hyp (List.mem_cons_self ..)) (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))

instance setoidG (Z : Seed) (t : FTy) : Setoid (Z.G t) where
  r := Eqv
  iseqv := ⟨eqv_refl, eqv_symm, eqv_trans⟩

abbrev Car (Z : Seed) (t : FTy) : Type := Quotient (setoidG Z t)

abbrev cls (x : Z.G t) : Z.Car t := Quotient.mk (setoidG Z t) x

theorem cls_eq {x y : Z.G t} : cls x = cls y ↔ Eqv x y := ⟨Quotient.exact, fun h => Quotient.sound h⟩

/-- A global term and its lift to a later stage are equal. -/
theorem cls_lift (x : Z.G t) (N : Nat) (h : x.1 ≤ N) : cls (⟨N, liftG x N h⟩ : Z.G t) = cls x := by
  apply cls_eq.2
  refine eqv_at (K := N) (Nat.le_refl N) h ?_
  rw [E_mk, Z.ren_refl]
  exact Z.M_of (.refl _ _)

/-! #### Truth of propositions, actuality, accessibility -/

def prF (p : Z.G .s) (w : Z.Wd) : Prop :=
  Z.M (max p.1 w.1) (.holds (E p _ (Nat.le_max_left _ _)) (wl w _ (Nat.le_max_right _ _)))

theorem prF_iff (p : Z.G .s) (w : Z.Wd) (K : Nat) (hp : p.1 ≤ K) (hw : w.1 ≤ K) :
    prF p w ↔ Z.M K (.holds (E p K hp) (wl w K hw)) := by
  have nat : ∀ K K' (hK : max p.1 w.1 ≤ K) (h : K ≤ K'),
      rename (Z.lt K K' h) (HTerm.holds (E p K (Nat.le_trans (Nat.le_max_left _ _) hK))
        (wl w K (Nat.le_trans (Nat.le_max_right _ _) hK))) =
      .holds (E p K' (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans hK h)))
        (wl w K' (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans hK h))) := fun K K' hK h => by
    show HTerm.holds (rename _ (E p K _)) (rename _ (wl w K _)) = _
    rw [E_nat, wl_nat]
  exact ⟨Z.transfer _ nat (Nat.le_refl _) (Nat.max_le.2 ⟨hp, hw⟩),
    Z.transfer _ nat (Nat.max_le.2 ⟨hp, hw⟩) (Nat.le_refl _)⟩

theorem prF_resp {p q : Z.G .s} (h : Eqv p q) (w : Z.Wd) (hp : prF p w) : prF q w := by
  let K := max (max p.1 q.1) w.1
  have h1 : p.1 ≤ K := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have h2 : q.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have h3 : w.1 ≤ K := Nat.le_max_right _ _
  rw [prF_iff p w K h1 h3] at hp
  rw [prF_iff q w K h2 h3]
  exact Z.M_mp2 (h K h1 h2) hp (d_holds_rw (.hyp (List.mem_cons_self ..))
    (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

def actF (x : Z.G .e) (w : Z.Wd) : Prop :=
  Z.M (max x.1 w.1) (.act (E x _ (Nat.le_max_left _ _)) (wl w _ (Nat.le_max_right _ _)))

theorem actF_iff (x : Z.G .e) (w : Z.Wd) (K : Nat) (hx : x.1 ≤ K) (hw : w.1 ≤ K) :
    actF x w ↔ Z.M K (.act (E x K hx) (wl w K hw)) := by
  have nat : ∀ K K' (hK : max x.1 w.1 ≤ K) (h : K ≤ K'),
      rename (Z.lt K K' h) (HTerm.act (E x K (Nat.le_trans (Nat.le_max_left _ _) hK))
        (wl w K (Nat.le_trans (Nat.le_max_right _ _) hK))) =
      .act (E x K' (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans hK h)))
        (wl w K' (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans hK h))) := fun K K' hK h => by
    show HTerm.act (rename _ (E x K _)) (rename _ (wl w K _)) = _
    rw [E_nat, wl_nat]
  exact ⟨Z.transfer _ nat (Nat.le_refl _) (Nat.max_le.2 ⟨hx, hw⟩),
    Z.transfer _ nat (Nat.max_le.2 ⟨hx, hw⟩) (Nat.le_refl _)⟩

theorem actF_resp {x y : Z.G .e} (h : Eqv x y) (w : Z.Wd) (hp : actF x w) : actF y w := by
  let K := max (max x.1 y.1) w.1
  have h1 : x.1 ≤ K := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have h2 : y.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have h3 : w.1 ≤ K := Nat.le_max_right _ _
  rw [actF_iff x w K h1 h3] at hp
  rw [actF_iff y w K h2 h3]
  exact Z.M_mp2 (h K h1 h2) hp (d_act_rw (.hyp (List.mem_cons_self ..))
    (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

def RF (w v : Z.Wd) : Prop :=
  Z.M (max w.1 v.1) (.rel (wl w _ (Nat.le_max_left _ _)) (wl v _ (Nat.le_max_right _ _)))

theorem RF_iff (w v : Z.Wd) (K : Nat) (hw : w.1 ≤ K) (hv : v.1 ≤ K) :
    RF w v ↔ Z.M K (.rel (wl w K hw) (wl v K hv)) := by
  have nat : ∀ K K' (hK : max w.1 v.1 ≤ K) (h : K ≤ K'),
      rename (Z.lt K K' h) (HTerm.rel (wl w K (Nat.le_trans (Nat.le_max_left _ _) hK))
        (wl v K (Nat.le_trans (Nat.le_max_right _ _) hK))) =
      .rel (wl w K' (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans hK h)))
        (wl v K' (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans hK h))) := fun K K' hK h => by
    show HTerm.rel (rename _ (wl w K _)) (rename _ (wl v K _)) = _
    rw [wl_nat, wl_nat]
  exact ⟨Z.transfer _ nat (Nat.le_refl _) (Nat.max_le.2 ⟨hw, hv⟩),
    Z.transfer _ nat (Nat.max_le.2 ⟨hw, hv⟩) (Nat.le_refl _)⟩

/-! #### Application, extensionality, injectivity of truth -/

abbrev apF (f : Z.G (.arr a b)) (x : Z.G a) : Z.G b :=
  ⟨max f.1 x.1, .app (liftG f _ (Nat.le_max_left _ _)) (liftG x _ (Nat.le_max_right _ _))⟩

theorem E_apF (f : Z.G (.arr a b)) (x : Z.G a) (K : Nat) (h : max f.1 x.1 ≤ K) :
    E (apF f x) K h = emb canonR (.app (liftG f K (Nat.le_trans (Nat.le_max_left _ _) h))
      (liftG x K (Nat.le_trans (Nat.le_max_right _ _) h))) := by
  show emb canonR (Tm.app (renameL (Z.qL (max f.1 x.1) K h) (liftG f _ (Nat.le_max_left _ _)))
    (renameL (Z.qL (max f.1 x.1) K h) (liftG x _ (Nat.le_max_right _ _)))) = _
  rw [liftG_trans f (Nat.le_max_left f.1 x.1) h, liftG_trans x (Nat.le_max_right f.1 x.1) h]

theorem apF_resp {f f' : Z.G (.arr a b)} {x x' : Z.G a} (hf : Eqv f f') (hx : Eqv x x') :
    Eqv (apF f x) (apF f' x') := by
  let K := max (max f.1 x.1) (max f'.1 x'.1)
  have k1 : max f.1 x.1 ≤ K := Nat.le_max_left _ _
  have k2 : max f'.1 x'.1 ≤ K := Nat.le_max_right _ _
  have h1 : f.1 ≤ K := Nat.le_trans (Nat.le_max_left _ _) k1
  have h2 : f'.1 ≤ K := Nat.le_trans (Nat.le_max_left _ _) k2
  have h3 : x.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) k1
  have h4 : x'.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) k2
  refine eqv_at k1 k2 ?_
  rw [E_apF, E_apF]
  have d : Z.D K [.eq (.L (.arr a b)) (E f K h1) (E f' K h2), .eq (.L a) (E x K h3) (E x' K h4)]
      (.eq (.L b) (emb canonR (.app (liftG f K h1) (liftG x K h3)))
        (emb canonR (.app (liftG f' K h2) (liftG x' K h4)))) :=
    d_app (Z.wK K) (.hyp (List.mem_cons_self ..)) (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  exact Z.M_mp2 (hf K h1 h2) (hx K h3 h4) d

theorem M_eqo {N : Nat} {A B : HTerm (Z.X N) .o} (h : Z.M N A ↔ Z.M N B) : Z.M N (.eq .o A B) := by
  by_cases ha : Z.M N A
  · exact Z.M_mp2 ha (h.1 ha) (.propExt (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))) (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  · have hb : ¬ Z.M N B := fun hb => ha (h.2 hb)
    exact Z.M_mp2 (Z.M_neg.2 ha) (Z.M_neg.2 hb)
      (.propExt (.exFalso (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        (.hyp (List.mem_cons_self ..))))
        (.exFalso (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
        (.hyp (List.mem_cons_self ..)))))

theorem prInj (p q : Z.G .s) (h : ∀ w, prF p w ↔ prF q w) : Eqv p q := by
  let K := max p.1 q.1
  have hp : p.1 ≤ K := Nat.le_max_left _ _
  have hq : q.1 ≤ K := Nat.le_max_right _ _
  refine eqv_at hp hq ?_
  rcases Z.M_max K (.eq (.L .s) (E p K hp) (E q K hq)) with m | m
  · exact m
  exfalso
  have m1 : Z.M K (negH (.all .w (.eq .o (.holds (wk (E p K hp)) var0) (.holds (wk (E q K hq)) var0)))) :=
    Z.M_mp m (.impI (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (.wExt (.hyp (List.mem_cons_self ..)))))
  have m2 := Z.M_mp m1 d_ex_not
  obtain ⟨N, hN, x, mx⟩ := mem_henkin Z.T Z.Γ0 Z.hs0 Z.hc m2
  have e : inst (rename (liftR (Z.lt K N hN))
      (negH (.eq .o (.holds (wk (E p K hp)) var0) (.holds (wk (E q K hq)) var0)))) (.var x) =
      negH (.eq .o (.holds (E p N (Nat.le_trans hp hN)) (.var x)) (.holds (E q N (Nat.le_trans hq hN)) (.var x))) := by
    show HTerm.imp (.eq .o (.holds (inst (rename (liftR _) (wk (E p K hp))) (.var x)) (.var x))
      (.holds (inst (rename (liftR _) (wk (E q K hq))) (.var x)) (.var x))) .bot = _
    rw [inst_ren_wk, inst_ren_wk, E_nat, E_nat]; rfl
  have mx' : Z.M N _ := mx
  rw [e] at mx'
  let w : Z.Wd := ⟨N, .var x⟩
  have hw : wl w N (Nat.le_refl N) = .var x := Z.ren_refl _ _ _
  have h1 := prF_iff p w N (Nat.le_trans hp hN) (Nat.le_refl N)
  have h2 := prF_iff q w N (Nat.le_trans hq hN) (Nat.le_refl N)
  rw [hw] at h1 h2
  exact Z.M_not_both (M_eqo (h1.symm.trans ((h w).trans h2))) mx'

theorem apExt (f g : Z.G (.arr a b)) (h : ∀ x : Z.G a, Eqv (apF f x) (apF g x)) : Eqv f g := by
  let K := max f.1 g.1
  have hf : f.1 ≤ K := Nat.le_max_left _ _
  have hg : g.1 ≤ K := Nat.le_max_right _ _
  refine eqv_at hf hg ?_
  rcases Z.M_max K (.eq (.L (.arr a b)) (E f K hf) (E g K hg)) with m | m
  · exact m
  exfalso
  have m1 : Z.M K (negH (.all (.L a) (.eq (.L b) (.appL (wk (E f K hf)) var0) (.appL (wk (E g K hg)) var0)))) :=
    Z.M_mp m (.impI (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (.funExt (.hyp (List.mem_cons_self ..)))))
  have m2 := Z.M_mp m1 d_ex_not
  obtain ⟨N, hN, y, my⟩ := mem_henkin Z.T Z.Γ0 Z.hs0 Z.hc m2
  have e : inst (rename (liftR (Z.lt K N hN))
      (negH (.eq (.L b) (.appL (wk (E f K hf)) var0) (.appL (wk (E g K hg)) var0)))) (.var y) =
      negH (.eq (.L b) (.appL (E f N (Nat.le_trans hf hN)) (.var y)) (.appL (E g N (Nat.le_trans hg hN)) (.var y))) := by
    show HTerm.imp (.eq (.L b) (.appL (inst (rename (liftR _) (wk (E f K hf))) (.var y)) (.var y))
      (.appL (inst (rename (liftR _) (wk (E g K hg))) (.var y)) (.var y))) .bot = _
    rw [inst_ren_wk, inst_ren_wk, E_nat, E_nat]; rfl
  have my' : Z.M N _ := my
  rw [e] at my'
  let yv : Z.G a := ⟨N, .var (lpos y)⟩
  have ey : E yv N (Nat.le_refl N) = .var y := by
    rw [E_mk, Z.ren_refl]; show HTerm.var (canonR (lpos y)) = _; rw [canonR_lpos]
  have k := h yv N (Nat.max_le.2 ⟨Nat.le_trans hf hN, Nat.le_refl N⟩) (Nat.max_le.2 ⟨Nat.le_trans hg hN, Nat.le_refl N⟩)
  rw [E_apF, E_apF] at k
  have e2 : ∀ (u : Z.G (.arr a b)) (hu : u.1 ≤ N) (hu' : max u.1 yv.1 ≤ N),
      emb canonR (Tm.app (liftG u N (Nat.le_trans (Nat.le_max_left _ _) hu'))
        (liftG yv N (Nat.le_trans (Nat.le_max_right _ _) hu'))) = .appL (E u N hu) (.var y) := by
    intro u hu hu'
    show HTerm.appL (E u N _) (E yv N _) = _
    rw [ey]
  rw [e2 f (Nat.le_trans hf hN) (Nat.max_le.2 ⟨Nat.le_trans hf hN, Nat.le_refl N⟩),
    e2 g (Nat.le_trans hg hN) (Nat.max_le.2 ⟨Nat.le_trans hg hN, Nat.le_refl N⟩)] at k
  exact Z.M_not_both k my'

end Seed

/-- **The canonical v4 model.** -/
noncomputable def VMc (Z : Seed) : VM Z.Wd where
  R := Seed.RF
  C := Z.Car
  act := Quotient.lift (s := Seed.setoidG Z .e) (fun x w => Seed.actF x w)
    (fun _ _ h => funext fun w => propext ⟨Seed.actF_resp h w, Seed.actF_resp (Seed.eqv_symm h) w⟩)
  pr := Quotient.lift (s := Seed.setoidG Z .s) (fun p w => Seed.prF p w)
    (fun _ _ h => funext fun w => propext ⟨Seed.prF_resp h w, Seed.prF_resp (Seed.eqv_symm h) w⟩)
  pr_inj := fun p q => Quotient.inductionOn₂ (s₁ := Seed.setoidG Z .s) (s₂ := Seed.setoidG Z .s) p q
    fun p q h => Seed.cls_eq.2 (Seed.prInj p q (fun w => Iff.of_eq (congrFun h w)))
  ap := fun {a b} => Quotient.lift₂ (s₁ := Seed.setoidG Z (.arr a b)) (s₂ := Seed.setoidG Z a)
    (fun f x => Seed.cls (Seed.apF f x)) (fun _ _ _ _ hf hx => Seed.cls_eq.2 (Seed.apF_resp hf hx))
  ap_ext := fun {a b} f g => Quotient.inductionOn₂ (s₁ := Seed.setoidG Z (.arr a b))
    (s₂ := Seed.setoidG Z (.arr a b)) f g fun f g h => Seed.cls_eq.2 (Seed.apExt f g
      (fun x => Seed.cls_eq.1 (h (Seed.cls x))))
  P := Seed.cls (⟨0, .pos⟩ : Z.G th)

/-! ### The 𝓛-general structure of the canonical model -/

namespace Seed
variable {Z : Seed}

abbrev Tr (K : Nat) (φ : Tm (Z.Lp K) .s) (i : HTerm (Z.X K) .w) : Prop := Z.M K (Lf canonR φ i)

theorem tr_top {K : Nat} {i : HTerm (Z.X K) .w} : Tr K .top i := Z.M_of L_topI

theorem tr_bot {K : Nat} {i : HTerm (Z.X K) .w} : ¬ Tr K .bot i := fun h =>
  Z.M_bot (Z.M_mp h (L_botE (.hyp (List.mem_cons_self ..))))

theorem tr_neg {K : Nat} {x : Tm (Z.Lp K) .s} {i : HTerm (Z.X K) .w} : Tr K (.neg x) i ↔ ¬ Tr K x i :=
  ⟨fun h hx => Z.M_bot (Z.M_mp2 h hx (.impE (L_negE (.hyp (List.mem_cons_self ..)))
      (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))),
   fun h => Z.M_mp (Z.M_neg.2 h) (L_negI (.hyp (List.mem_cons_self ..)))⟩

theorem tr_and {K : Nat} {x y : Tm (Z.Lp K) .s} {i : HTerm (Z.X K) .w} :
    Tr K (.and x y) i ↔ Tr K x i ∧ Tr K y i :=
  ⟨fun h => ⟨Z.M_mp h (.andL (L_andE (.hyp (List.mem_cons_self ..)))),
      Z.M_mp h (.andR (L_andE (.hyp (List.mem_cons_self ..))))⟩,
   fun h => Z.M_mp2 h.1 h.2 (L_andI (.andI (.hyp (List.mem_cons_self ..))
      (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))⟩

theorem tr_or {K : Nat} {x y : Tm (Z.Lp K) .s} {i : HTerm (Z.X K) .w} :
    Tr K (.or x y) i ↔ Tr K x i ∨ Tr K y i := by
  constructor
  · intro h
    by_cases hx : Tr K x i
    · exact .inl hx
    by_cases hy : Tr K y i
    · exact .inr hy
    exfalso
    refine Z.M_bot (Z.M_deriv (hs := [Lf canonR (.or x y) i, negH (Lf canonR x i), negH (Lf canonR y i)])
      (fun z m => ?_) (.orE (L_orE (.hyp (List.mem_cons_self ..)))
        (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
          (.hyp (List.mem_cons_self ..)))
        (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_self ..))))) (.hyp (List.mem_cons_self ..)))))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl | rfl
    · exact h
    · exact Z.M_neg.2 hx
    · exact Z.M_neg.2 hy
  · rintro (h | h)
    · exact Z.M_mp h (L_orI (.orL (.hyp (List.mem_cons_self ..))))
    · exact Z.M_mp h (L_orI (.orR (.hyp (List.mem_cons_self ..))))

theorem tr_imp {K : Nat} {x y : Tm (Z.Lp K) .s} {i : HTerm (Z.X K) .w} :
    Tr K (.imp x y) i ↔ (Tr K x i → Tr K y i) := by
  constructor
  · intro h hx
    exact Z.M_mp2 h hx (.impE (L_impE (.hyp (List.mem_cons_self ..)))
      (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  · intro h
    by_cases hx : Tr K x i
    · exact Z.M_mp (h hx) (L_impI (.impI (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    · exact Z.M_mp (Z.M_neg.2 hx) (L_impI (.impI (.exFalso (.impE
        (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (.hyp (List.mem_cons_self ..))))))

/-! #### Environments -/

def stg : {Γ' : List FTy} → VEnv (VMc Z) Γ' → Nat
  | [], _ => 0
  | t :: _, ρ => max (qout (s := setoidG Z t) ρ.1).1 (stg ρ.2)

def subE : {Γ' : List FTy} → (ρ : VEnv (VMc Z) Γ') → (K : Nat) → stg ρ ≤ K → {t : FTy} →
    Var Γ' t → Tm (Z.Lp K) t
  | u :: _, ρ, K, h, _, .zero => liftG (qout (s := setoidG Z u) ρ.1) K (Nat.le_trans (Nat.le_max_left _ _) h)
  | _ :: _, ρ, K, h, _, .succ i => subE ρ.2 K (Nat.le_trans (Nat.le_max_right _ _) h) i

theorem sub_nat : ∀ {Γ' : List FTy} (ρ : VEnv (VMc Z) Γ') {K N : Nat} (hK : stg ρ ≤ K) (h : K ≤ N) {t : FTy}
    (i : Var Γ' t), renameL (Z.qL K N h) (subE ρ K hK i) = subE ρ N (Nat.le_trans hK h) i
  | _ :: _, _, _, _, _, _, _, .zero => liftG_trans _ _ _
  | _ :: _, ρ, _, _, _, h, _, .succ i => sub_nat ρ.2 _ h i

theorem ev_nat (ρ : VEnv (VMc Z) Γ') {K N : Nat} (hK : stg ρ ≤ K) (h : K ≤ N) (tm : Tm Γ' t) :
    renameL (Z.qL K N h) (substL (subE ρ K hK) tm) = substL (subE ρ N (Nat.le_trans hK h)) tm :=
  renameL_substL _ _ _ _ (fun v => sub_nat ρ hK h v)

abbrev evc (tm : Tm Γ' t) (ρ : VEnv (VMc Z) Γ') : Z.G t := ⟨stg ρ, substL (subE ρ (stg ρ) (Nat.le_refl _)) tm⟩

theorem E_ev (tm : Tm Γ' t) (ρ : VEnv (VMc Z) Γ') (K : Nat) (h : stg ρ ≤ K) :
    E (evc tm ρ) K h = emb canonR (substL (subE ρ K h) tm) :=
  congrArg (emb canonR) (ev_nat ρ (Nat.le_refl _) h tm)

theorem pr_ev (φ : Tm Γ' .s) (ρ : VEnv (VMc Z) Γ') (w : Z.Wd) (K : Nat) (hK : stg ρ ≤ K) (hw : w.1 ≤ K) :
    (VMc Z).pr (cls (evc φ ρ)) w ↔ Tr K (substL (subE ρ K hK) φ) (wl w K hw) := by
  have := prF_iff (evc φ ρ) w K hK hw
  rw [E_ev] at this
  exact this

theorem lift_tr {K N : Nat} (h : K ≤ N) (φ : Tm (Z.Lp K) .s) (i : HTerm (Z.X K) .w) :
    rename (Z.lt K N h) (Lf canonR φ i) = Lf canonR (renameL (Z.qL K N h) φ) (rename (Z.lt K N h) i) := by
  show HTerm.holds (rename _ (emb canonR φ)) (rename _ i) = _
  rw [← Z.emb_qL]; rfl

end Seed

theorem substL_congr (tm : Tm Γ t) {s s' : SubL Γ Δ} (h : ∀ {u} (v : Var Γ u), s v = s' v) :
    substL s tm = substL s' tm := by
  have := substL_renameL tm (fun v => v) s s' (fun v => h v)
  rwa [renameL_id' _ _ (fun _ => rfl)] at this

theorem substL_var (q : RenL Γ Δ) (tm : Tm Γ t) : substL (fun v => .var (q v)) tm = renameL q tm := by
  have := substL_renameL tm q (fun v => .var v) (fun v => .var (q v)) (fun _ => rfl)
  rw [substL_id _ _ (fun _ => rfl)] at this
  exact this.symm

namespace Seed
variable {Z : Seed}

theorem subE_cons (x : Z.Car u) (ρ : VEnv (VMc Z) Γ') (K : Nat) (h : stg (Γ' := u :: Γ') (x, ρ) ≤ K) (b : Tm (u :: Γ') t) :
    substL (subE (Γ' := u :: Γ') (x, ρ) K h) b =
      substL (consL (liftG (qout (s := setoidG Z u) x) K (Nat.le_trans (Nat.le_max_left _ _) h))
        (subE ρ K (Nat.le_trans (Nat.le_max_right _ _) h))) b :=
  substL_congr b (fun v => by cases v <;> rfl)

theorem cls_subE : ∀ {Γ' : List FTy} (ρ : VEnv (VMc Z) Γ') (K : Nat) (h : stg ρ ≤ K) {t : FTy} (i : Var Γ' t),
    cls (⟨K, subE ρ K h i⟩ : Z.G t) = i.vget (VMc Z) ρ
  | u :: _, ρ, K, h, _, .zero => (cls_lift _ _ _).trans (qout_eq (s := setoidG Z u) ρ.1)
  | _ :: _, ρ, K, h, _, .succ i => cls_subE ρ.2 K _ i

theorem ev_var (i : Var Γ' t) (ρ : VEnv (VMc Z) Γ') : cls (evc (.var i) ρ) = i.vget (VMc Z) ρ :=
  cls_subE ρ _ _ i

theorem ev_app (F : Tm Γ' (.arr a b)) (x : Tm Γ' a) (ρ : VEnv (VMc Z) Γ') :
    cls (evc (.app F x) ρ) = (VMc Z).ap (cls (evc F ρ)) (cls (evc x ρ)) := by
  show cls (evc (.app F x) ρ) = cls (apF (evc F ρ) (evc x ρ))
  apply cls_eq.2
  refine eqv_at (K := max (stg ρ) (stg ρ)) (Nat.le_max_left _ _) (Nat.le_refl _) ?_
  rw [E_ev, E_apF]
  show Z.M _ (.eq _ (emb canonR (Tm.app (substL _ F) (substL _ x))) (emb canonR (Tm.app
    (renameL (Z.qL (stg ρ) _ _) (substL _ F)) (renameL (Z.qL (stg ρ) _ _) (substL _ x)))))
  rw [ev_nat, ev_nat]
  exact Z.M_of (.refl _ _)

theorem ev_lam (t : Tm (a :: Γ') b) (ρ : VEnv (VMc Z) Γ') (x : Z.Car a) :
    (VMc Z).ap (cls (evc (.lam t) ρ)) x = cls (evc (Γ' := a :: Γ') t (x, ρ)) := by
  induction x using Quotient.inductionOn (s := setoidG Z a) with
  | h u =>
  show cls (apF (evc (.lam t) ρ) u) = _
  apply cls_eq.2
  let K := max (max (stg ρ) u.1) (stg (Γ' := a :: Γ') (cls u, ρ))
  have k1 : max (stg ρ) u.1 ≤ K := Nat.le_max_left _ _
  have k2 : stg (Γ' := a :: Γ') (cls u, ρ) ≤ K := Nat.le_max_right _ _
  have hS : stg ρ ≤ K := Nat.le_trans (Nat.le_max_left _ _) k1
  have hu : u.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) k1
  refine eqv_at k1 k2 ?_
  rw [E_apF, E_ev, subE_cons]
  show Z.M K (.eq _ (emb canonR (Tm.app (renameL (Z.qL (stg ρ) K _) (substL _ (Tm.lam t))) (liftG u K hu))) _)
  rw [ev_nat]
  -- β, then replace the representative
  have e1 := Deriv.betaL (T := Z.T) (ok := fun a t => Cert a t) (hs := [])
    (emb (liftL canonR) (substL (liftSL (subE ρ K hS)) t)) (emb canonR (liftG u K hu))
  rw [inst_emb, instL_liftSL] at e1
  have q := mk_qout (s := setoidG Z a) u
  have e2 : Z.M K (.eq (.L a) (E u K hu) (E (qout (s := setoidG Z a) (cls u)) K
      (Nat.le_trans (Nat.le_max_left _ _) k2))) := eqv_symm q K _ _
  have e3 := Z.M_mp e2 (d_cong (r := canonR) (Z.wK K) (substL (liftSL (subE ρ K hS)) t) (.hyp (List.mem_cons_self ..)))
  rw [instL_liftSL, instL_liftSL] at e3
  exact Z.M_mp e3 (.trans _ (e1.weaken (fun _ m => nomatch m)) (.hyp (List.mem_cons_self ..)))

theorem ev_pos (ρ : VEnv (VMc Z) Γ') : cls (evc .pos ρ) = (VMc Z).P :=
  cls_eq.2 (eqv_at (K := stg ρ) (Nat.le_refl _) (Nat.zero_le _) (Z.M_of (.refl _ _)))

theorem ev_eq (a : FTy) (x y : Tm Γ' a) (ρ : VEnv (VMc Z) Γ') (w : Z.Wd) :
    (VMc Z).pr (cls (evc (.eq a x y) ρ)) w ↔ cls (evc x ρ) = cls (evc y ρ) := by
  let K := max (stg ρ) w.1
  have hS : stg ρ ≤ K := Nat.le_max_left _ _
  rw [pr_ev _ ρ w K hS (Nat.le_max_right _ _), cls_eq]
  constructor
  · intro h
    refine eqv_at hS hS ?_
    rw [E_ev, E_ev]
    exact Z.M_mp h (L_eqE (.hyp (List.mem_cons_self ..)))
  · intro h
    have := h K hS hS
    rw [E_ev, E_ev] at this
    exact Z.M_mp this (L_eqI (.hyp (List.mem_cons_self ..)))

end Seed

/-! #### Quantifier and box clauses -/

section qh
variable {T : Tm [] .s → Prop} {Γ'' : List FTy} {Γ : List HTy} {hs : List (HTerm Γ .o)}
  {r : LRen Γ'' Γ} {i : HTerm Γ .w}

theorem L_all_hyp {b : Tm (a :: Γ'') .s} :
    DC T Γ (.all (.L a) (Lf (liftL r) b (wk i)) :: hs) (Lf r (.all a b) i) :=
  Deriv.betaWI _ _ (by rw [body_all]; exact .hyp (List.mem_cons_self ..))

theorem L_allE_hyp {b : Tm (.e :: Γ'') .s} :
    DC T Γ (.all (.L .e) (.imp (.act var0 (wk i)) (Lf (liftL r) b (wk i))) :: hs) (Lf r (.allE b) i) :=
  Deriv.betaWI _ _ (by rw [body_allE]; exact .hyp (List.mem_cons_self ..))

theorem L_box_hyp {x : Tm Γ'' .s} :
    DC T Γ (.all .w (.imp (.rel (wk i) var0) (Lf (shL r) x var0)) :: hs) (Lf r (.box x) i) :=
  Deriv.betaWI _ _ (by rw [body_box]; exact .hyp (List.mem_cons_self ..))

theorem L_ex_hyp {b : Tm (a :: Γ'') .s} :
    DC T Γ (Lf r (.ex a b) i :: hs) (.ex (.L a) (Lf (liftL r) b (wk i))) := by
  have h0 : DC T Γ (Lf r (.ex a b) i :: hs) (Lf r (.ex a b) i) := .hyp (List.mem_cons_self ..)
  have := Deriv.betaWE _ _ h0
  rwa [body_ex] at this

theorem L_exE_hyp {b : Tm (.e :: Γ'') .s} :
    DC T Γ (Lf r (.exE b) i :: hs) (.ex (.L .e) (.and (.act var0 (wk i)) (Lf (liftL r) b (wk i)))) := by
  have h0 : DC T Γ (Lf r (.exE b) i :: hs) (Lf r (.exE b) i) := .hyp (List.mem_cons_self ..)
  have := Deriv.betaWE _ _ h0
  rwa [body_exE] at this

/-- From `¬φ'`, where `φ'` implies `φ`, get `¬φ`... in the form used below. -/
theorem d_neg_of {φ ψ : HTerm Γ .o} (d : DC T Γ (ψ :: hs) φ) : DC T Γ (negH φ :: hs) (negH ψ) :=
  .impI (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    ((d.weaken (fun x m => by
      rcases List.mem_cons.1 m with rfl | m
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ m)))))

end qh

theorem inst_act (ρ : HRen Γ Δ) (j : HTerm Γ .w) (t : HTerm Δ (.L .e)) :
    inst (rename (liftR ρ) (HTerm.act var0 (wk j))) t = .act t (rename ρ j) := by
  show HTerm.act t (inst (rename (liftR ρ) (wk j)) t) = _; rw [inst_ren_wk]

theorem inst_rel (ρ : HRen Γ Δ) (j : HTerm Γ .w) (t : HTerm Δ .w) :
    inst (rename (liftR ρ) (HTerm.rel (wk j) var0)) t = .rel (rename ρ j) t := by
  show HTerm.rel (inst (rename (liftR ρ) (wk j)) t) t = _; rw [inst_ren_wk]

namespace Seed
variable {Z : Seed}

theorem M_negimp {N : Nat} {A B : HTerm (Z.X N) .o} (h : Z.M N (negH (.imp A B))) : Z.M N A ∧ ¬ Z.M N B := by
  refine ⟨Z.M_mp h (.byContra (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (.impI (.exFalso (.impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (.hyp (List.mem_cons_self ..))))))),
    fun hb => Z.M_not_both (Z.M_mp hb (.impI (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))) h⟩

theorem M_and {N : Nat} {A B : HTerm (Z.X N) .o} (h : Z.M N (.and A B)) : Z.M N A ∧ Z.M N B :=
  ⟨Z.M_mp h (.andL (.hyp (List.mem_cons_self ..))), Z.M_mp h (.andR (.hyp (List.mem_cons_self ..)))⟩

theorem tr_lift {K N : Nat} (h : K ≤ N) (φ : Tm (Z.Lp K) .s) (i : HTerm (Z.X K) .w) :
    Tr K φ i ↔ Tr N (renameL (Z.qL K N h) φ) (rename (Z.lt K N h) i) := by
  show Z.M K _ ↔ Z.M N _
  rw [Z.M_lift h, lift_tr]

theorem tr_cons {K : Nat} (B : Tm (a :: Γ') .s) (σ : SubL Γ' (Z.Lp K)) {U U' : Tm (Z.Lp K) a}
    (e : Z.M K (.eq (.L a) (emb canonR U) (emb canonR U'))) {i : HTerm (Z.X K) .w}
    (h : Tr K (substL (consL U σ) B) i) : Tr K (substL (consL U' σ) B) i := by
  have h' : Z.M K (Lf canonR (instL (substL (liftSL σ) B) U) i) := by rw [instL_liftSL]; exact h
  have := Z.M_mp2 e h' (L_leib _ (.hyp (List.mem_cons_self ..)) (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  rwa [instL_liftSL] at this

theorem henkin_inst {K N : Nat} (hN : K ≤ N) (B : Tm (a :: Z.Lp K) .s) (j : HTerm (Z.X K) .w)
    (y : HVar (Z.X N) (.L a)) :
    inst (rename (liftR (Z.lt K N hN)) (Lf (liftL canonR) B (wk j))) (.var y) =
      Lf canonR (substL (consL (.var (lpos y)) (fun v => .var (Z.qL K N hN v))) B) (rename (Z.lt K N hN) j) := by
  show HTerm.holds (inst (rename (liftR _) (emb (liftL canonR) B)) (.var y))
    (inst (rename (liftR _) (wk j)) (.var y)) = _
  rw [inst_ren_wk, rename_emb B _ (liftL canonR) (liftL (fun v => Z.lt K N hN (canonR v)))
    (fun v => by cases v <;> rfl)]
  unfold inst
  rw [subst_emb B _ (liftL _) canonR (consL (.var (lpos y)) (fun v => .var (Z.qL K N hN v))) (fun v => by
    cases v with
    | zero => show HTerm.var y = HTerm.var (canonR (lpos y)); rw [canonR_lpos]
    | succ v => show HTerm.var _ = HTerm.var (canonR (lpos _)); rw [canonR_lpos])]
  rfl

theorem cons_comp {Γ' : List FTy} (ρ : VEnv (VMc Z) Γ') {K N : Nat} (hK : stg ρ ≤ K) (hN : K ≤ N)
    (Y : Tm (Z.Lp N) a) (b : Tm (a :: Γ') .s) :
    substL (consL Y (fun v => .var (Z.qL K N hN v))) (substL (liftSL (subE ρ K hK)) b) =
      substL (consL Y (subE ρ N (Nat.le_trans hK hN))) b :=
  substL_substL _ _ _ _ (fun v => by
    cases v with
    | zero => rfl
    | succ v =>
        show substL _ (renameL _ (subE ρ K hK v)) = subE ρ N _ v
        rw [substL_renameL (subE ρ K hK v) (fun v => .succ v) _ (fun v => .var (Z.qL K N hN v)) (fun _ => rfl),
          substL_var, sub_nat])

theorem cons_lift {Γ' : List FTy} (ρ : VEnv (VMc Z) Γ') {K N : Nat} (hK : stg ρ ≤ K) (hN : K ≤ N)
    (Y : Tm (Z.Lp K) a) (b : Tm (a :: Γ') .s) :
    renameL (Z.qL K N hN) (substL (consL Y (subE ρ K hK)) b) =
      substL (consL (renameL (Z.qL K N hN) Y) (subE ρ N (Nat.le_trans hK hN))) b :=
  renameL_substL _ _ _ _ (fun v => by
    cases v with
    | zero => rfl
    | succ v => exact sub_nat ρ hK hN v)

theorem E_var (N : Nat) (y : HVar (Z.X N) (.L a)) (h : N ≤ N) :
    E (⟨N, .var (lpos y)⟩ : Z.G a) N h = .var y := by
  rw [E_mk, Z.ren_refl]; show HTerm.var (canonR (lpos y)) = _; rw [canonR_lpos]

/-- The Henkin step for an `𝓛`-quantifier: a witness variable, as a global term. -/
theorem ev_all (a : FTy) (b : Tm (a :: Γ') .s) (ρ : VEnv (VMc Z) Γ') (w : Z.Wd) :
    (VMc Z).pr (cls (evc (.all a b) ρ)) w ↔
      ∀ x : Z.Car a, (VMc Z).pr (cls (evc (Γ' := a :: Γ') b (x, ρ))) w := by
  constructor
  · intro h x
    induction x using Quotient.inductionOn (s := setoidG Z a) with
    | h u =>
    let K := max (max (stg ρ) w.1) (stg (Γ' := a :: Γ') (cls u, ρ))
    have hS : stg ρ ≤ K := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have hw : w.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    have k2 : stg (Γ' := a :: Γ') (cls u, ρ) ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ ρ w K hS hw] at h
    rw [pr_ev _ _ w K k2 hw, subE_cons]
    have := Z.M_mp h (L_allE (.hyp (List.mem_cons_self ..))
      (liftG (qout (s := setoidG Z a) (cls u)) K (Nat.le_trans (Nat.le_max_left _ _) k2)))
    rwa [instL_liftSL] at this
  · intro H
    let K := max (stg ρ) w.1
    have hS : stg ρ ≤ K := Nat.le_max_left _ _
    have hw : w.1 ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ ρ w K hS hw]
    rcases Z.M_max K (Lf canonR (substL (subE ρ K hS) (.all a b)) (wl w K hw)) with m | m
    · exact m
    exfalso
    have m2 := Z.M_mp (Z.M_mp m (d_neg_of L_all_hyp)) d_ex_not
    obtain ⟨N, hN, y, my⟩ := mem_henkin Z.T Z.Γ0 Z.hs0 Z.hc m2
    have e := henkin_inst hN (substL (liftSL (subE ρ K hS)) b) (wl w K hw) y
    rw [cons_comp, wl_nat] at e
    have my' : Z.M N (negH (Lf canonR (substL (consL (.var (lpos y)) (subE ρ N (Nat.le_trans hS hN))) b)
        (wl w N (Nat.le_trans hw hN)))) := by
      have : Z.M N (negH (inst (rename (liftR (Z.lt K N hN)) (Lf (liftL canonR) (substL (liftSL (subE ρ K hS)) b)
        (wk (wl w K hw)))) (.var y))) := my
      rwa [e] at this
    let yv : Z.G a := ⟨N, .var (lpos y)⟩
    have Hx := H (cls yv)
    let K' := max N (stg (Γ' := a :: Γ') (cls yv, ρ))
    have hNK : N ≤ K' := Nat.le_max_left _ _
    have k2 : stg (Γ' := a :: Γ') (cls yv, ρ) ≤ K' := Nat.le_max_right _ _
    have hw' : w.1 ≤ K' := Nat.le_trans (Nat.le_trans hw hN) hNK
    rw [pr_ev _ _ w K' k2 hw', subE_cons] at Hx
    have my2 := (Z.M_lift hNK _).1 my'
    have e2 : rename (Z.lt N K' hNK) (negH (Lf canonR (substL (consL (.var (lpos y))
        (subE ρ N (Nat.le_trans hS hN))) b) (wl w N (Nat.le_trans hw hN)))) =
        negH (Lf canonR (substL (consL (liftG yv K' hNK) (subE ρ K' (Nat.le_trans (Nat.le_trans hS hN) hNK))) b)
          (wl w K' hw')) := by
      show HTerm.imp (rename _ (Lf canonR _ _)) .bot = _
      rw [lift_tr, cons_lift, wl_nat]; rfl
    rw [e2] at my2
    have q := mk_qout (s := setoidG Z a) yv
    exact Z.M_not_both (tr_cons b _ (q K' _ hNK) Hx) my2

end Seed

namespace Seed
variable {Z : Seed}

theorem act_cls (u : Z.G .e) (w : Z.Wd) : (VMc Z).act (cls u) w ↔ actF u w := Iff.rfl

theorem ev_ex (a : FTy) (b : Tm (a :: Γ') .s) (ρ : VEnv (VMc Z) Γ') (w : Z.Wd) :
    (VMc Z).pr (cls (evc (.ex a b) ρ)) w ↔
      ∃ x : Z.Car a, (VMc Z).pr (cls (evc (Γ' := a :: Γ') b (x, ρ))) w := by
  constructor
  · intro h
    let K := max (stg ρ) w.1
    have hS : stg ρ ≤ K := Nat.le_max_left _ _
    have hw : w.1 ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ ρ w K hS hw] at h
    have m2 := Z.M_mp h L_ex_hyp
    obtain ⟨N, hN, y, my⟩ := mem_henkin Z.T Z.Γ0 Z.hs0 Z.hc m2
    have e := henkin_inst hN (substL (liftSL (subE ρ K hS)) b) (wl w K hw) y
    rw [cons_comp, wl_nat] at e
    have my' : Tr N (substL (consL (.var (lpos y)) (subE ρ N (Nat.le_trans hS hN))) b)
        (wl w N (Nat.le_trans hw hN)) := by
      have : Z.M N (inst (rename (liftR (Z.lt K N hN)) (Lf (liftL canonR) (substL (liftSL (subE ρ K hS)) b)
        (wk (wl w K hw)))) (.var y)) := my
      rwa [e] at this
    let yv : Z.G a := ⟨N, .var (lpos y)⟩
    refine ⟨cls yv, ?_⟩
    let K' := max N (stg (Γ' := a :: Γ') (cls yv, ρ))
    have hNK : N ≤ K' := Nat.le_max_left _ _
    have k2 : stg (Γ' := a :: Γ') (cls yv, ρ) ≤ K' := Nat.le_max_right _ _
    have hw' : w.1 ≤ K' := Nat.le_trans (Nat.le_trans hw hN) hNK
    rw [pr_ev _ _ w K' k2 hw', subE_cons]
    have my2 := (tr_lift hNK _ _).1 my'
    rw [cons_lift, wl_nat] at my2
    have q := mk_qout (s := setoidG Z a) yv
    exact tr_cons b _ (eqv_symm q K' hNK _) my2
  · rintro ⟨x, hx⟩
    induction x using Quotient.inductionOn (s := setoidG Z a) with
    | h u =>
    let K := max (max (stg ρ) w.1) (stg (Γ' := a :: Γ') (cls u, ρ))
    have hS : stg ρ ≤ K := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have hw : w.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    have k2 : stg (Γ' := a :: Γ') (cls u, ρ) ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ _ w K k2 hw, subE_cons] at hx
    rw [pr_ev _ ρ w K hS hw]
    have hx' : Tr K (instL (substL (liftSL (subE ρ K hS)) b)
        (liftG (qout (s := setoidG Z a) (cls u)) K (Nat.le_trans (Nat.le_max_left _ _) k2))) (wl w K hw) := by
      rw [instL_liftSL]; exact hx
    exact Z.M_mp hx' (L_exI _ (.hyp (List.mem_cons_self ..)))

theorem ev_allE (b : Tm (.e :: Γ') .s) (ρ : VEnv (VMc Z) Γ') (w : Z.Wd) :
    (VMc Z).pr (cls (evc (.allE b) ρ)) w ↔
      ∀ x : Z.Car .e, (VMc Z).act x w → (VMc Z).pr (cls (evc (Γ' := .e :: Γ') b (x, ρ))) w := by
  constructor
  · intro h x hxw
    induction x using Quotient.inductionOn (s := setoidG Z .e) with
    | h u =>
    let K := max (max (stg ρ) w.1) (stg (Γ' := .e :: Γ') (cls u, ρ))
    have hS : stg ρ ≤ K := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have hw : w.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    have k2 : stg (Γ' := .e :: Γ') (cls u, ρ) ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ ρ w K hS hw] at h
    rw [pr_ev _ _ w K k2 hw, subE_cons]
    have hq : actF (qout (s := setoidG Z .e) (cls u)) w :=
      actF_resp (eqv_symm (mk_qout (s := setoidG Z .e) u)) w hxw
    rw [actF_iff _ w K (Nat.le_trans (Nat.le_max_left _ _) k2) hw] at hq
    have := Z.M_mp2 h hq (L_allEE (.hyp (List.mem_cons_self ..))
      (liftG (qout (s := setoidG Z .e) (cls u)) K (Nat.le_trans (Nat.le_max_left _ _) k2))
      (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    rwa [instL_liftSL] at this
  · intro H
    let K := max (stg ρ) w.1
    have hS : stg ρ ≤ K := Nat.le_max_left _ _
    have hw : w.1 ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ ρ w K hS hw]
    rcases Z.M_max K (Lf canonR (substL (subE ρ K hS) (.allE b)) (wl w K hw)) with m | m
    · exact m
    exfalso
    have m2 := Z.M_mp (Z.M_mp m (d_neg_of L_allE_hyp)) d_ex_not
    obtain ⟨N, hN, y, my⟩ := mem_henkin Z.T Z.Γ0 Z.hs0 Z.hc m2
    have e := henkin_inst hN (substL (liftSL (subE ρ K hS)) b) (wl w K hw) y
    rw [cons_comp, wl_nat] at e
    have ea := inst_act (Z.lt K N hN) (wl w K hw) (.var y)
    rw [wl_nat] at ea
    have my' : Z.M N (negH (.imp (.act (.var y) (wl w N (Nat.le_trans hw hN)))
        (Lf canonR (substL (consL (.var (lpos y)) (subE ρ N (Nat.le_trans hS hN))) b)
        (wl w N (Nat.le_trans hw hN))))) := by
      have : Z.M N (negH (.imp (inst (rename (liftR (Z.lt K N hN)) (HTerm.act var0 (wk (wl w K hw)))) (.var y))
        (inst (rename (liftR (Z.lt K N hN)) (Lf (liftL canonR) (substL (liftSL (subE ρ K hS)) b)
        (wk (wl w K hw)))) (.var y)))) := my
      rwa [e, ea] at this
    obtain ⟨ma, mb⟩ := M_negimp my'
    let yv : Z.G .e := ⟨N, .var (lpos y)⟩
    have hact : (VMc Z).act (cls yv) w := by
      show actF yv w
      rw [actF_iff yv w N (Nat.le_refl N) (Nat.le_trans hw hN), E_var]
      exact ma
    have Hx := H (cls yv) hact
    let K' := max N (stg (Γ' := .e :: Γ') (cls yv, ρ))
    have hNK : N ≤ K' := Nat.le_max_left _ _
    have k2 : stg (Γ' := .e :: Γ') (cls yv, ρ) ≤ K' := Nat.le_max_right _ _
    have hw' : w.1 ≤ K' := Nat.le_trans (Nat.le_trans hw hN) hNK
    rw [pr_ev _ _ w K' k2 hw', subE_cons] at Hx
    have q := mk_qout (s := setoidG Z .e) yv
    have h3 := tr_cons b _ (q K' _ hNK) Hx
    apply mb
    refine (tr_lift hNK _ _).2 ?_
    rw [cons_lift, wl_nat]
    exact h3

theorem ev_exE (b : Tm (.e :: Γ') .s) (ρ : VEnv (VMc Z) Γ') (w : Z.Wd) :
    (VMc Z).pr (cls (evc (.exE b) ρ)) w ↔
      ∃ x : Z.Car .e, (VMc Z).act x w ∧ (VMc Z).pr (cls (evc (Γ' := .e :: Γ') b (x, ρ))) w := by
  constructor
  · intro h
    let K := max (stg ρ) w.1
    have hS : stg ρ ≤ K := Nat.le_max_left _ _
    have hw : w.1 ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ ρ w K hS hw] at h
    have m2 := Z.M_mp h L_exE_hyp
    obtain ⟨N, hN, y, my⟩ := mem_henkin Z.T Z.Γ0 Z.hs0 Z.hc m2
    have e := henkin_inst hN (substL (liftSL (subE ρ K hS)) b) (wl w K hw) y
    rw [cons_comp, wl_nat] at e
    have ea := inst_act (Z.lt K N hN) (wl w K hw) (.var y)
    rw [wl_nat] at ea
    have my' : Z.M N (.and (.act (.var y) (wl w N (Nat.le_trans hw hN)))
        (Lf canonR (substL (consL (.var (lpos y)) (subE ρ N (Nat.le_trans hS hN))) b)
        (wl w N (Nat.le_trans hw hN)))) := by
      have : Z.M N (.and (inst (rename (liftR (Z.lt K N hN)) (HTerm.act var0 (wk (wl w K hw)))) (.var y))
        (inst (rename (liftR (Z.lt K N hN)) (Lf (liftL canonR) (substL (liftSL (subE ρ K hS)) b)
        (wk (wl w K hw)))) (.var y))) := my
      rwa [e, ea] at this
    obtain ⟨ma, mb⟩ := M_and my'
    let yv : Z.G .e := ⟨N, .var (lpos y)⟩
    refine ⟨cls yv, ?_, ?_⟩
    · show actF yv w
      rw [actF_iff yv w N (Nat.le_refl N) (Nat.le_trans hw hN), E_var]
      exact ma
    let K' := max N (stg (Γ' := .e :: Γ') (cls yv, ρ))
    have hNK : N ≤ K' := Nat.le_max_left _ _
    have k2 : stg (Γ' := .e :: Γ') (cls yv, ρ) ≤ K' := Nat.le_max_right _ _
    have hw' : w.1 ≤ K' := Nat.le_trans (Nat.le_trans hw hN) hNK
    rw [pr_ev _ _ w K' k2 hw', subE_cons]
    have my2 := (tr_lift hNK _ _).1 mb
    rw [cons_lift, wl_nat] at my2
    have q := mk_qout (s := setoidG Z .e) yv
    exact tr_cons b _ (eqv_symm q K' hNK _) my2
  · rintro ⟨x, hxw, hx⟩
    induction x using Quotient.inductionOn (s := setoidG Z .e) with
    | h u =>
    let K := max (max (stg ρ) w.1) (stg (Γ' := .e :: Γ') (cls u, ρ))
    have hS : stg ρ ≤ K := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have hw : w.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    have k2 : stg (Γ' := .e :: Γ') (cls u, ρ) ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ _ w K k2 hw, subE_cons] at hx
    rw [pr_ev _ ρ w K hS hw]
    have hq : actF (qout (s := setoidG Z .e) (cls u)) w :=
      actF_resp (eqv_symm (mk_qout (s := setoidG Z .e) u)) w hxw
    rw [actF_iff _ w K (Nat.le_trans (Nat.le_max_left _ _) k2) hw] at hq
    have hx' : Tr K (instL (substL (liftSL (subE ρ K hS)) b)
        (liftG (qout (s := setoidG Z .e) (cls u)) K (Nat.le_trans (Nat.le_max_left _ _) k2))) (wl w K hw) := by
      rw [instL_liftSL]; exact hx
    exact Z.M_mp2 hq hx' (L_exEI _ (.hyp (List.mem_cons_self ..)) (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem ev_box (x : Tm Γ' .s) (ρ : VEnv (VMc Z) Γ') (w : Z.Wd) :
    (VMc Z).pr (cls (evc (.box x) ρ)) w ↔ ∀ v, (VMc Z).R w v → (VMc Z).pr (cls (evc x ρ)) v := by
  constructor
  · intro h v hv
    let K := max (max (stg ρ) w.1) v.1
    have hS : stg ρ ≤ K := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have hw : w.1 ≤ K := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    have hv' : v.1 ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ ρ w K hS hw] at h
    rw [pr_ev _ ρ v K hS hv']
    have hr : Z.M K (.rel (wl w K hw) (wl v K hv')) := (RF_iff w v K hw hv').1 hv
    exact Z.M_mp2 h hr (L_boxE (.hyp (List.mem_cons_self ..)) (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  · intro H
    let K := max (stg ρ) w.1
    have hS : stg ρ ≤ K := Nat.le_max_left _ _
    have hw : w.1 ≤ K := Nat.le_max_right _ _
    rw [pr_ev _ ρ w K hS hw]
    rcases Z.M_max K (Lf canonR (substL (subE ρ K hS) (.box x)) (wl w K hw)) with m | m
    · exact m
    exfalso
    have m2 := Z.M_mp (Z.M_mp m (d_neg_of L_box_hyp)) d_ex_not
    obtain ⟨N, hN, y, my⟩ := mem_henkin Z.T Z.Γ0 Z.hs0 Z.hc m2
    have er := inst_rel (Z.lt K N hN) (wl w K hw) (.var y)
    rw [wl_nat] at er
    have el : inst (rename (liftR (Z.lt K N hN)) (Lf (shL canonR) (substL (subE ρ K hS) x) var0)) (.var y) =
        Lf canonR (substL (subE ρ N (Nat.le_trans hS hN)) x) (.var y) := by
      show HTerm.holds (inst (rename (liftR _) (emb (shL canonR) (substL (subE ρ K hS) x))) (.var y)) (.var y) = _
      rw [rename_emb _ _ (shL canonR) (shL (fun v => Z.lt K N hN (canonR v))) (fun _ => rfl)]
      unfold inst
      rw [sub0_shL, ← ev_nat ρ hS hN x]
      show HTerm.holds (emb (fun v => Z.lt K N hN (canonR v)) _) _ =
        HTerm.holds (emb canonR (renameL (Z.qL K N hN) _)) _
      rw [Z.emb_qL, rename_emb _ _ canonR _ (fun _ => rfl)]
    have my' : Z.M N (negH (.imp (.rel (wl w N (Nat.le_trans hw hN)) (.var y))
        (Lf canonR (substL (subE ρ N (Nat.le_trans hS hN)) x) (.var y)))) := by
      have : Z.M N (negH (.imp (inst (rename (liftR (Z.lt K N hN)) (HTerm.rel (wk (wl w K hw)) var0)) (.var y))
        (inst (rename (liftR (Z.lt K N hN)) (Lf (shL canonR) (substL (subE ρ K hS) x) var0)) (.var y)))) := my
      rwa [er, el] at this
    obtain ⟨ma, mb⟩ := M_negimp my'
    let v : Z.Wd := ⟨N, .var y⟩
    have hwv : wl v N (Nat.le_refl N) = .var y := Z.ren_refl _ _ _
    have hR : (VMc Z).R w v := by
      show RF w v
      rw [RF_iff w v N (Nat.le_trans hw hN) (Nat.le_refl N), hwv]
      exact ma
    have Hv := H v hR
    rw [pr_ev _ ρ v N (Nat.le_trans hS hN) (Nat.le_refl N), hwv] at Hv
    exact mb Hv

end Seed

namespace Seed
variable {Z : Seed}

theorem pr_evK (φ : Tm Γ' .s) (ρ : VEnv (VMc Z) Γ') (w : Z.Wd) :
    (VMc Z).pr (cls (evc φ ρ)) w ↔
      Tr (max (stg ρ) w.1) (substL (subE ρ _ (Nat.le_max_left _ _)) φ) (wl w _ (Nat.le_max_right _ _)) :=
  pr_ev φ ρ w _ _ _

end Seed

/-- **The canonical model is 𝓛-general** (v4 def:lgeneral, as `LGen`). -/
noncomputable def LGc (Z : Seed) : LGen (VMc Z) where
  ev := fun tm ρ => Seed.cls (Seed.evc tm ρ)
  var := Seed.ev_var
  app := Seed.ev_app
  lam := Seed.ev_lam
  top := fun ρ w => ⟨fun _ => trivial, fun _ => (Seed.pr_evK _ ρ w).2 Seed.tr_top⟩
  bot := fun ρ w => ⟨fun h => Seed.tr_bot ((Seed.pr_evK _ ρ w).1 h), False.elim⟩
  neg := fun x ρ w => (Seed.pr_evK _ ρ w).trans (Seed.tr_neg.trans (not_congr (Seed.pr_evK x ρ w).symm))
  and := fun x y ρ w => (Seed.pr_evK _ ρ w).trans (Seed.tr_and.trans
    (and_congr (Seed.pr_evK x ρ w).symm (Seed.pr_evK y ρ w).symm))
  or := fun x y ρ w => (Seed.pr_evK _ ρ w).trans (Seed.tr_or.trans
    (or_congr (Seed.pr_evK x ρ w).symm (Seed.pr_evK y ρ w).symm))
  imp := fun x y ρ w => (Seed.pr_evK _ ρ w).trans (Seed.tr_imp.trans
    (imp_congr (Seed.pr_evK x ρ w).symm (Seed.pr_evK y ρ w).symm))
  box := Seed.ev_box
  all := Seed.ev_all
  ex := Seed.ev_ex
  allE := Seed.ev_allE
  exE := Seed.ev_exE
  eq := Seed.ev_eq
  pos := Seed.ev_pos

/-! ### Completeness -/

def nilRL : RenL [] Δ := fun v => nomatch v

theorem closed_tr {Z : Seed} {K : Nat} (ψ : Tm [] .s) (σ : SubL [] (Z.Lp K)) (i : HTerm (Z.X K) .w) :
    Lf canonR (substL σ ψ) i = Lf nilR ψ i := by
  rw [substL_congr ψ (s' := fun v => .var (nilRL v)) (fun v => nomatch v), substL_var]
  show HTerm.holds (emb canonR (renameL nilRL ψ)) i = HTerm.holds (emb nilR ψ) i
  rw [emb_renameL ψ nilRL canonR nilR (fun v => nomatch v)]

/-- **Completeness (M3).** If `∃x.⊤ ∈ T` and the `𝓛`-sentence `φ` holds in every v4 `𝓛`-general
model of `T` with nonempty individuals, then `⟦φ⟧` has a certified deep derivation from `T` at a
world variable. -/
theorem completeness {T : Tm [] .s → Prop} {φ : Tm [] .s} (hNE : T (.ex .e .top)) (H : ValidV4 T φ) :
    DC T [.w] [] (.holds (emb nilR φ) var0) := by
  refine Classical.byContradiction fun hd => ?_
  let Z : Seed := ⟨T, [.w], [negH (.holds (emb nilR φ) var0)], start_cons T hd, var0⟩
  have hT : ∀ ψ, T ψ → ∀ w, (VMc Z).pr ((LGc Z).ev ψ ()) w := fun ψ hψ w => by
    show (VMc Z).pr (Seed.cls (Seed.evc ψ ())) w
    rw [Seed.pr_evK]
    show Z.M _ _
    rw [closed_tr]
    exact Z.M_of (L_ax hψ nilR _)
  let w0 : Z.Wd := ⟨0, var0⟩
  have hne : Nonempty ((VMc Z).C .e) := by
    obtain ⟨x, _⟩ := ((LGc Z).ex (Γ := []) .e .top () w0).1 (hT _ hNE w0)
    exact ⟨x⟩
  have h0 := H Z.Wd (VMc Z) (LGc Z) hne hT w0
  have h1 : (VMc Z).pr (Seed.cls (Seed.evc φ ())) w0 := h0
  rw [Seed.pr_ev φ () w0 0 (Nat.le_refl 0) (Nat.le_refl 0)] at h1
  have h2 : Z.M 0 (Lf canonR (substL (Seed.subE (Z := Z) (Γ' := []) () 0 (Nat.le_refl 0)) φ)
      (Seed.wl w0 0 (Nat.le_refl 0))) := h1
  rw [closed_tr, Seed.wl, Z.ren_refl] at h2
  exact Z.M_not_both h2 (mem_self T [.w] _ (List.mem_cons_self ..))

/-- **Soundness and completeness over v4's 𝓛-general models**, for theories with `∃x.⊤`. -/
theorem sound_complete {T : Tm [] .s → Prop} {φ : Tm [] .s} (hNE : T (.ex .e .top)) :
    DC T [.w] [] (.holds (emb nilR φ) var0) ↔ ValidV4 T φ :=
  ⟨Programme.«20261022-1724-ontological».Run3.V4.sound_v4, completeness hNE⟩

/-- The same over closed `eqT`-respecting structures (K4's class), via the bridge. -/
theorem sound_complete_str {T : Tm [] .s → Prop} {φ : Tm [] .s} (hNE : T (.ex .e .top)) :
    DC T [.w] [] (.holds (emb nilR φ) var0) ↔ ValidStr T φ :=
  (sound_complete hNE).trans (valid_iff T φ)

/-- `T` with the sentence `∃x.⊤` (nonempty individuals) added. -/
def withNE (T : Tm [] .s → Prop) : Tm [] .s → Prop := fun ψ => T ψ ∨ ψ = .ex .e .top

theorem validV4_withNE {T : Tm [] .s → Prop} {φ : Tm [] .s} : ValidV4 (withNE T) φ ↔ ValidV4 T φ := by
  constructor
  · intro H W M L hne hT w
    refine H W M L hne (fun ψ hψ v => ?_) w
    rcases hψ with hψ | rfl
    · exact hT ψ hψ v
    · obtain ⟨x⟩ := hne
      exact (L.ex (Γ := []) .e .top () v).2 ⟨x, (L.top (Γ := [.e]) (x, ()) v).2 trivial⟩
  · intro H W M L hne hT w
    exact H W M L hne (fun ψ hψ v => hT ψ (.inl hψ) v) w

/-- **Soundness and completeness for every 𝓛-theory**: `φ` holds in every v4 𝓛-general model of `T`
with nonempty individuals iff `⟦φ⟧` has a certified deep derivation from `T ∪ {∃x.⊤}`. -/
theorem sound_complete_all {T : Tm [] .s → Prop} {φ : Tm [] .s} :
    DC (withNE T) [.w] [] (.holds (emb nilR φ) var0) ↔ ValidV4 T φ :=
  (sound_complete (.inr rfl)).trans validV4_withNE


/-! ## Downward Löwenheim–Skolem (th, round 8)
The canonical model `VMc Z` has countably many worlds and countable carriers at every type: worlds are
`Σ n, HTerm (Z.X n) .w` (coded by `pair n (codeT _)`), carriers are quotients of `Σ n, Tm (Z.Lp n) t`
(coded by an injective code of 𝓛-terms through a chosen representative). Hence every 𝓛-sentence that
fails in some v4 𝓛-general model of `T` (nonempty individuals) fails in a countable one. -/

/-- `α` injects into `Nat`. -/
def Ctbl (α : Type) : Prop := ∃ f : α → Nat, ∀ a b, f a = f b → a = b

def codeVar : {Γ : List FTy} → {t : FTy} → Var Γ t → Nat
  | _, _, .zero => 0
  | _, _, .succ v => codeVar v + 1

theorem codeVar_inj : ∀ {Γ t} (v v' : Var Γ t), codeVar v = codeVar v' → v = v'
  | _, _, .zero, .zero, _ => rfl
  | _, _, .zero, .succ _, h => by simp [codeVar] at h
  | _, _, .succ _, .zero, h => by simp [codeVar] at h
  | _, _, .succ v, .succ v', h => by
      simp only [codeVar, Nat.add_right_cancel_iff] at h; rw [codeVar_inj v v' h]

def codeTm : {Γ : List FTy} → {t : FTy} → Tm Γ t → Nat
  | _, _, .var v => pair 0 (codeVar v)
  | _, _, @Tm.app _ a _ f x => pair 1 (pair (codeF a) (pair (codeTm f) (codeTm x)))
  | _, _, .lam b => pair 2 (codeTm b)
  | _, _, .top => pair 3 0
  | _, _, .bot => pair 4 0
  | _, _, .neg p => pair 5 (codeTm p)
  | _, _, .and p q => pair 6 (pair (codeTm p) (codeTm q))
  | _, _, .or p q => pair 7 (pair (codeTm p) (codeTm q))
  | _, _, .imp p q => pair 8 (pair (codeTm p) (codeTm q))
  | _, _, .box p => pair 9 (codeTm p)
  | _, _, .all a p => pair 10 (pair (codeF a) (codeTm p))
  | _, _, .ex a p => pair 11 (pair (codeF a) (codeTm p))
  | _, _, .allE p => pair 12 (codeTm p)
  | _, _, .exE p => pair 13 (codeTm p)
  | _, _, .eq a s t => pair 14 (pair (codeF a) (pair (codeTm s) (codeTm t)))
  | _, _, .pos => pair 15 0

theorem codeTm_inj : ∀ {Γ t} (x y : Tm Γ t), codeTm x = codeTm y → x = y
  | _, _, .var v, y, h => by
      cases y <;> simp only [codeTm, pair_iff] at h <;> first | omega | rw [codeVar_inj _ _ h.2]
  | _, _, @Tm.app _ a _ f x, y, h => by
      cases y with
      | @app _ a' _ f' x' =>
          simp only [codeTm, pair_iff] at h
          obtain ⟨_, ha, hf, hx⟩ := h
          cases codeF_inj ha
          rw [codeTm_inj f f' hf, codeTm_inj x x' hx]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .lam b, y, h => by
      cases y with
      | lam b' => simp only [codeTm, pair_iff] at h; rw [codeTm_inj b b' h.2]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .top, y, h => by cases y <;> simp only [codeTm, pair_iff] at h <;> first | omega | rfl
  | _, _, .bot, y, h => by cases y <;> simp only [codeTm, pair_iff] at h <;> first | omega | rfl
  | _, _, .pos, y, h => by cases y <;> simp only [codeTm, pair_iff] at h <;> first | omega | rfl
  | _, _, .neg p, y, h => by
      cases y with
      | neg p' => simp only [codeTm, pair_iff] at h; rw [codeTm_inj p p' h.2]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .box p, y, h => by
      cases y with
      | box p' => simp only [codeTm, pair_iff] at h; rw [codeTm_inj p p' h.2]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .allE p, y, h => by
      cases y with
      | allE p' => simp only [codeTm, pair_iff] at h; rw [codeTm_inj p p' h.2]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .exE p, y, h => by
      cases y with
      | exE p' => simp only [codeTm, pair_iff] at h; rw [codeTm_inj p p' h.2]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .and p q, y, h => by
      cases y with
      | and p' q' => simp only [codeTm, pair_iff] at h; rw [codeTm_inj p p' h.2.1, codeTm_inj q q' h.2.2]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .or p q, y, h => by
      cases y with
      | or p' q' => simp only [codeTm, pair_iff] at h; rw [codeTm_inj p p' h.2.1, codeTm_inj q q' h.2.2]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .imp p q, y, h => by
      cases y with
      | imp p' q' => simp only [codeTm, pair_iff] at h; rw [codeTm_inj p p' h.2.1, codeTm_inj q q' h.2.2]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .all a p, y, h => by
      cases y with
      | all a' p' =>
          simp only [codeTm, pair_iff] at h
          obtain ⟨_, ha, hp⟩ := h
          cases codeF_inj ha
          rw [codeTm_inj p p' hp]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .ex a p, y, h => by
      cases y with
      | ex a' p' =>
          simp only [codeTm, pair_iff] at h
          obtain ⟨_, ha, hp⟩ := h
          cases codeF_inj ha
          rw [codeTm_inj p p' hp]
      | _ => simp only [codeTm, pair_iff] at h; omega
  | _, _, .eq a s t, y, h => by
      cases y with
      | eq a' s' t' =>
          simp only [codeTm, pair_iff] at h
          obtain ⟨_, ha, hs, ht⟩ := h
          cases codeF_inj ha
          rw [codeTm_inj s s' hs, codeTm_inj t t' ht]
      | _ => simp only [codeTm, pair_iff] at h; omega

theorem ctbl_sigma {F : Nat → Type} (c : ∀ n, F n → Nat) (hc : ∀ n (x y : F n), c n x = c n y → x = y) :
    Ctbl (Σ n, F n) := by
  refine ⟨fun x => pair x.1 (c x.1 x.2), ?_⟩
  rintro ⟨n, x⟩ ⟨m, y⟩ h
  obtain ⟨h1, h2⟩ := pair_inj h
  cases h1
  rw [hc n x y h2]

theorem ctbl_quot {α : Type} {s : Setoid α} (h : Ctbl α) : Ctbl (Quotient s) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun q => f (qout q), fun a b hab => ?_⟩
  rw [← qout_eq a, ← qout_eq b, hf _ _ hab]

theorem ctbl_worlds (Z : Seed) : Ctbl Z.Wd :=
  ctbl_sigma (fun _ t => codeT t) (fun _ x y h => codeT_inj x y h)

theorem ctbl_carriers (Z : Seed) (t : FTy) : Ctbl ((VMc Z).C t) :=
  ctbl_quot (ctbl_sigma (F := fun n => Tm (Z.Lp n) t) (fun _ x => codeTm x) (fun _ x y h => codeTm_inj x y h))

/-- **Downward Löwenheim–Skolem for v4's 𝓛-general models.** If `T ∋ ∃x.⊤` and an 𝓛-sentence `φ` fails
in some 𝓛-general model of `T` with nonempty individuals, it fails in one whose set of worlds and every
carrier `C t` inject into `Nat`. -/
theorem lowenheim_skolem {T : Tm [] .s → Prop} {φ : Tm [] .s} (hNE : T (.ex .e .top))
    (H : ¬ ValidV4 T φ) :
    ∃ (W : Type) (M : VM W) (L : LGen M), Ctbl W ∧ (∀ t, Ctbl (M.C t)) ∧ Nonempty (M.C .e) ∧
      (∀ ψ, T ψ → ∀ w, M.pr (L.ev ψ ()) w) ∧ ∃ w, ¬ M.pr (L.ev φ ()) w := by
  have hd : ¬ DC T [.w] [] (.holds (emb nilR φ) var0) := fun d => H (Programme.«20261022-1724-ontological».Run3.V4.sound_v4 d)
  let Z : Seed := ⟨T, [.w], [negH (.holds (emb nilR φ) var0)], start_cons T hd, var0⟩
  have hT : ∀ ψ, T ψ → ∀ w, (VMc Z).pr ((LGc Z).ev ψ ()) w := fun ψ hψ w => by
    show (VMc Z).pr (Seed.cls (Seed.evc ψ ())) w
    rw [Seed.pr_evK]
    show Z.M _ _
    rw [closed_tr]
    exact Z.M_of (L_ax hψ nilR _)
  let w0 : Z.Wd := ⟨0, var0⟩
  have hne : Nonempty ((VMc Z).C .e) := by
    obtain ⟨x, _⟩ := ((LGc Z).ex (Γ := []) .e .top () w0).1 (hT _ hNE w0)
    exact ⟨x⟩
  refine ⟨Z.Wd, VMc Z, LGc Z, ctbl_worlds Z, ctbl_carriers Z, hne, hT, w0, fun h0 => ?_⟩
  have h1 : (VMc Z).pr (Seed.cls (Seed.evc φ ())) w0 := h0
  rw [Seed.pr_ev φ () w0 0 (Nat.le_refl 0) (Nat.le_refl 0)] at h1
  have h2 : Z.M 0 (Lf canonR (substL (Seed.subE (Z := Z) (Γ' := []) () 0 (Nat.le_refl 0)) φ)
      (Seed.wl w0 0 (Nat.le_refl 0))) := h1
  rw [closed_tr, Seed.wl, Z.ren_refl] at h2
  exact Z.M_not_both h2 (mem_self T [.w] _ (List.mem_cons_self ..))

/-- Validity over countable 𝓛-general models. -/
def ValidCtbl (T : Tm [] .s → Prop) (φ : Tm [] .s) : Prop :=
  ∀ (W : Type) (M : VM W) (L : LGen M), Ctbl W → (∀ t, Ctbl (M.C t)) → Nonempty (M.C .e) →
    (∀ ψ, T ψ → ∀ w, M.pr (L.ev ψ ()) w) → ∀ w, M.pr (L.ev φ ()) w

/-- For theories with `∃x.⊤`, validity over all v4 𝓛-general models equals validity over countable ones. -/
theorem valid_iff_ctbl {T : Tm [] .s → Prop} {φ : Tm [] .s} (hNE : T (.ex .e .top)) :
    ValidV4 T φ ↔ ValidCtbl T φ := by
  constructor
  · intro H W M L _ _ hne hT w
    exact H W M L hne hT w
  · intro H
    refine Classical.byContradiction fun hn => ?_
    obtain ⟨W, M, L, hW, hC, hne, hT, w, hw⟩ := lowenheim_skolem hNE hn
    exact hw (H W M L hW hC hne hT w)

/-- Every 𝓛-theory: `⟦φ⟧` derivable from `T ∪ {∃x.⊤}` iff `φ` holds in all countable 𝓛-general models of `T`. -/
theorem sound_complete_ctbl {T : Tm [] .s → Prop} {φ : Tm [] .s} :
    DC (withNE T) [.w] [] (.holds (emb nilR φ) var0) ↔ ValidCtbl T φ := by
  rw [sound_complete (.inr rfl), valid_iff_ctbl (.inr rfl)]
  constructor
  · intro H W M L hW hC hne hT w
    exact H W M L hW hC hne (fun ψ hψ v => by
      rcases hψ with hψ | rfl
      · exact hT ψ hψ v
      · obtain ⟨x⟩ := hne
        exact (L.ex (Γ := []) .e .top () v).2 ⟨x, (L.top (Γ := [.e]) (x, ()) v).2 trivial⟩) w
  · intro H W M L hW hC hne hT w
    exact H W M L hW hC hne (fun ψ hψ v => hT ψ (.inl hψ) v) w

/-! ## Compactness (th, round 8): a derivation uses finitely many axioms of `T`. -/

theorem mem_app3 {α : Type} {x : α} {l1 l2 l3 : List α} (h : x ∈ l1 ++ l2 ++ l3) :
    x ∈ l1 ∨ x ∈ l2 ∨ x ∈ l3 := by
  simp only [List.mem_append] at h; rcases h with (h | h) | h <;> simp [h]

macro "fin_close" : tactic => `(tactic| first
  | assumption
  | (apply ‹∀ T' : Tm [] .s → Prop, (∀ ψ, ψ ∈ _ → T' ψ) → _›; intro ψ hψ; apply ‹∀ ψ, ψ ∈ _ → _›; simp [hψ]))

theorem Deriv.finite {T : Tm [] .s → Prop} {ok : ∀ {Γ : List HTy} (a : HTy), HTerm Γ a → Prop}
    {Γ : List HTy} {hs : List (HTerm Γ .o)} {φ : HTerm Γ .o} (d : Deriv T ok Γ hs φ) :
    ∃ l : List (Tm [] .s), (∀ ψ, ψ ∈ l → T ψ) ∧
      ∀ T' : Tm [] .s → Prop, (∀ ψ, ψ ∈ l → T' ψ) → Deriv T' ok Γ hs φ := by
  induction d with
  | ax φ i h => exact ⟨[φ], fun ψ hψ => by simp at hψ; subst hψ; exact h, fun T' h' => .ax φ i (h' φ (by simp))⟩
  | hyp _ =>
    refine ⟨[], fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp at hψ
    · skip
      apply Deriv.hyp <;> first | assumption
  | impI _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.impI <;> first | assumption
  | impE _ _ ih1 ih2 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    obtain ⟨l2, a2, k2⟩ := ih2
    refine ⟨l1 ++ l2, fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp only [List.mem_append] at hψ
      rcases hψ with h | h
      · exact a1 ψ h
      · exact a2 ψ h
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      have e2 := k2 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1 k2
      apply Deriv.impE <;> first | assumption
  | byContra _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.byContra <;> first | assumption
  | andI _ _ ih1 ih2 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    obtain ⟨l2, a2, k2⟩ := ih2
    refine ⟨l1 ++ l2, fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp only [List.mem_append] at hψ
      rcases hψ with h | h
      · exact a1 ψ h
      · exact a2 ψ h
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      have e2 := k2 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1 k2
      apply Deriv.andI <;> first | assumption
  | andL _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.andL <;> first | assumption
  | andR _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.andR <;> first | assumption
  | orL _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.orL <;> first | assumption
  | orR _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.orR <;> first | assumption
  | orE _ _ _ ih1 ih2 ih3 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    obtain ⟨l2, a2, k2⟩ := ih2
    obtain ⟨l3, a3, k3⟩ := ih3
    refine ⟨l1 ++ l2 ++ l3, fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp only [List.mem_append] at hψ
      rcases hψ with (h | h) | h
      · exact a1 ψ h
      · exact a2 ψ h
      · exact a3 ψ h
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      have e2 := k2 T' (fun ψ hψ => h ψ (by simp [hψ]))
      have e3 := k3 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1 k2 k3
      apply Deriv.orE <;> first | assumption
  | allI _ _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.allI <;> first | assumption
  | allE _ _ _ _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.allE <;> first | assumption
  | exI _ _ _ _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.exI <;> first | assumption
  | exE _ _ _ ih1 ih2 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    obtain ⟨l2, a2, k2⟩ := ih2
    refine ⟨l1 ++ l2, fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp only [List.mem_append] at hψ
      rcases hψ with h | h
      · exact a1 ψ h
      · exact a2 ψ h
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      have e2 := k2 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1 k2
      apply Deriv.exE <;> first | assumption
  | refl _ _ =>
    refine ⟨[], fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp at hψ
    · skip
      apply Deriv.refl <;> first | assumption
  | symm _ _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.symm <;> first | assumption
  | trans _ _ _ ih1 ih2 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    obtain ⟨l2, a2, k2⟩ := ih2
    refine ⟨l1 ++ l2, fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp only [List.mem_append] at hψ
      rcases hψ with h | h
      · exact a1 ψ h
      · exact a2 ψ h
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      have e2 := k2 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1 k2
      apply Deriv.trans <;> first | assumption
  | subst _ _ _ _ _ ih1 ih2 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    obtain ⟨l2, a2, k2⟩ := ih2
    refine ⟨l1 ++ l2, fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp only [List.mem_append] at hψ
      rcases hψ with h | h
      · exact a1 ψ h
      · exact a2 ψ h
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      have e2 := k2 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1 k2
      apply Deriv.subst <;> first | assumption
  | funExt _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.funExt <;> first | assumption
  | funApp _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.funApp <;> first | assumption
  | wExt _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.wExt <;> first | assumption
  | wApp _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.wApp <;> first | assumption
  | propExt _ _ ih1 ih2 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    obtain ⟨l2, a2, k2⟩ := ih2
    refine ⟨l1 ++ l2, fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp only [List.mem_append] at hψ
      rcases hψ with h | h
      · exact a1 ψ h
      · exact a2 ψ h
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      have e2 := k2 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1 k2
      apply Deriv.propExt <;> first | assumption
  | betaL _ _ =>
    refine ⟨[], fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp at hψ
    · skip
      apply Deriv.betaL <;> first | assumption
  | betaWI _ _ _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.betaWI <;> first | assumption
  | betaWE _ _ _ ih1 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    refine ⟨l1, fun ψ hψ => ?_, fun T' h => ?_⟩
    · exact a1 ψ hψ
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1
      apply Deriv.betaWE <;> first | assumption
  | leib a r M i h1 h2 _ _ ih1 ih2 =>
    obtain ⟨l1, a1, k1⟩ := ih1
    obtain ⟨l2, a2, k2⟩ := ih2
    refine ⟨l1 ++ l2, fun ψ hψ => ?_, fun T' h => ?_⟩
    · simp only [List.mem_append] at hψ
      rcases hψ with h | h
      · exact a1 ψ h
      · exact a2 ψ h
    · skip
      have e1 := k1 T' (fun ψ hψ => h ψ (by simp [hψ]))
      have e2 := k2 T' (fun ψ hψ => h ψ (by simp [hψ]))
      clear k1 k2
      exact Deriv.leib a r M i h1 h2 e1 e2

open Classical in
/-- **Compactness of K4's certified calculus**, hence (by completeness) of validity over v4's 𝓛-general
models: if `φ` holds in every 𝓛-general model of `T` with nonempty individuals, it holds in every such
model of some finite list of members of `T`. -/
theorem compactness {T : Tm [] .s → Prop} {φ : Tm [] .s} (H : ValidV4 T φ) :
    ∃ l : List (Tm [] .s), (∀ ψ, ψ ∈ l → T ψ) ∧ ValidV4 (fun ψ => ψ ∈ l) φ := by
  obtain ⟨l, hl, k⟩ := Deriv.finite (sound_complete_all.2 H)
  refine ⟨l.filter (fun ψ => decide (T ψ)), ?_, ?_⟩
  · intro ψ hψ
    simpa using (List.mem_filter.1 hψ).2
  · apply sound_complete_all.1
    apply k
    intro ψ hψ
    by_cases hT : T ψ
    · exact .inl (List.mem_filter.2 ⟨hψ, by simpa using hT⟩)
    · rcases hl ψ hψ with h | h
      · exact absurd h hT
      · exact .inr h

end
end Programme.«20261022-1724-ontological».ThCanon



/-! ## The separating sentence: countable but no finite countermodel (pr, round 9)
Composition of K8 (`sep_not_valid_v4`), K11 (`sep_finite`) and th's `lowenheim_skolem`. -/

namespace Programme.«20261022-1724-ontological».Run3.SepLS
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.SepV2.Sep Programme.«20261022-1724-ontological».ThCanon

/-- **Countably infinite is the threshold for `A ∃p.(Atom p ∧ p)` over variant 2.** There is a v4
𝓛-general model with nonempty individuals in which variant 2 (`Ax1Gen`, `Ax2a`, `Ax2b`, `Ax3`, `Ax4`)
holds at every world and `A ∃p.(Atom p ∧ p)` fails at some world, whose worlds and carriers at every
type inject into `Nat` and whose worlds are not a finite list; and every v4 𝓛-general model with
finitely many worlds satisfies the sentence at every world. -/
theorem sep_threshold :
    (∃ (W : Type) (M : VM W) (L : LGen M), Ctbl W ∧ (∀ t, Ctbl (M.C t)) ∧ Nonempty (M.C .e) ∧
      (∀ ψ, Programme.«20261022-1724-ontological».Run3.SepV2.V2.T2 ψ → ∀ w, M.pr (L.ev ψ ()) w) ∧
      (∃ w, ¬ M.pr (L.ev phiSep ()) w) ∧ ¬ ∃ l : List W, ∀ w, w ∈ l) ∧
    (∀ (W : Type) (M : VM W) (L : LGen M), (∃ l : List W, ∀ w, w ∈ l) →
      ∀ w, M.pr (L.ev phiSep ()) w) := by
  refine ⟨?_, fun W M L hfin w => Programme.«20261022-1724-ontological».Run3.SepR.sep_finite M L hfin w⟩
  have hn : ¬ ValidV4 (withNE Programme.«20261022-1724-ontological».Run3.SepV2.V2.T2) phiSep := fun H =>
    Programme.«20261022-1724-ontological».Run3.SepV2.V2.sep_not_valid_v4 (validV4_withNE.1 H)
  obtain ⟨W, M, L, hW, hC, hne, hT, w, hw⟩ := lowenheim_skolem (.inr rfl) hn
  exact ⟨W, M, L, hW, hC, hne, fun ψ hψ => hT ψ (.inl hψ), ⟨w, hw⟩,
    fun hfin => hw (Programme.«20261022-1724-ontological».Run3.SepR.sep_finite M L hfin w)⟩

end Programme.«20261022-1724-ontological».Run3.SepLS

#print axioms Programme.«20261022-1724-ontological».Run3.SepLS.sep_threshold
