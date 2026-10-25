import Programme.«20261022-0733-ontological».Run2.LGeneral
-- Copied from agents/th/lean/Programme/Th/RigidExit.lean (author: th, E12, P165); only the namespace changed.
/-! # The principality exit with rigidity kept, in a model closed under the fragment of `𝓛`

Thread D / arXiv 2608.07578's question (are the ways out of collapse distinct?).  K10 gives an
exit that keeps principality and drops rigidity (Ax2b).  Here is the other one: positivity is
rigid (Ax2b holds) and is a *free* ultrafilter, so no world has a God-like being; Ax2a, Ax3
(variant 2 and 3′), Ax4 hold and admitted modal collapse fails.  The model is closed under
pr's fragment `LGeneral.Tm` (fact (a) proved here by a permutation-model argument).

Model: worlds are the bit streams with infinitely many `true`s and `false`s; one individual;
`R` and actuality universal (S5).  The group is all permutations of `ℕ`, acting on streams by
precomposition; `Fix n` fixes `0, …, n-1`.  Admitted objects at every type are those fixed by
some `Fix n` (Fraenkel–Mostowski style).  `P φ` iff `φ` holds on all streams vanishing below
some `n`: the neighbourhood filter of the missing point `0^ω`.  It is invariant under every
permutation, so the model is `LGeneral`.  Every `Fix n`-orbit is a whole cylinder
(`transitive`), so admitted properties are cylinders and `P` decides them (Ax2a).  No admitted
property is an essence (cylinders are never singletons), so `E = E₃ = ⊤`.

Contrast: with full carriers on a symmetric frame, Ax2a, Ax3, Ax4 force `R ⊆ id` and collapse
(`StandardKB.kb_collapse`), and with Ax1Gen, Ax2a, Ax2b collapse follows in closed models (K55);
hence Ax1Gen fails here, and must. -/

namespace Programme.«20261022-0733-ontological».Run2.RigidExit

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.LGeneral

/-! ## Generic equivariance for world bijections (one individual) -/

structure WAut (W : Type) where
  f : W → W
  g : W → W
  fg : ∀ w, f (g w) = w
  gf : ∀ w, g (f w) = w

variable {W : Type}

def WAut.inv (a : WAut W) : WAut W := ⟨a.g, a.f, a.gf, a.fg⟩

/-- Pull-back along `a` at each type. -/
def fl (a : WAut W) : (t : Ty) → Den W Unit t → Den W Unit t
  | .e, x => x
  | .s, q => fun w => q (a.f w)
  | .p, φ => fun x w => φ x (a.f w)
  | .h, Φ => fun ψ w => Φ (fun x v => ψ x (a.g v)) (a.f w)

theorem fl_inv (a : WAut W) : ∀ (t : Ty) (x : Den W Unit t), fl a.inv t (fl a t x) = x
  | .e, _ => rfl
  | .s, q => by funext w; simp [fl, WAut.inv, a.fg]
  | .p, φ => by funext x w; simp [fl, WAut.inv, a.fg]
  | .h, Φ => by funext ψ w; simp [fl, WAut.inv, a.fg]

theorem fl_inv' (a : WAut W) : ∀ (t : Ty) (x : Den W Unit t), fl a t (fl a.inv t x) = x
  | .e, _ => rfl
  | .s, q => by funext w; simp [fl, WAut.inv, a.gf]
  | .p, φ => by funext x w; simp [fl, WAut.inv, a.gf]
  | .h, Φ => by funext ψ w; simp [fl, WAut.inv, a.gf]

theorem fl_inj (a : WAut W) (t : Ty) {x y : Den W Unit t} : fl a t x = fl a t y ↔ x = y :=
  ⟨fun h => by rw [← fl_inv a t x, h, fl_inv], fun h => h ▸ rfl⟩

def flEnv (a : WAut W) : (Γ : List Ty) → Env W Unit Γ → Env W Unit Γ
  | [], _ => ()
  | t :: Γ, ρ => (fl a t ρ.1, flEnv a Γ ρ.2)

theorem get_fl (a : WAut W) : ∀ {Γ t} (i : Var Γ t) (ρ : Env W Unit Γ),
    i.get (flEnv a Γ ρ) = fl a t (i.get ρ)
  | _, _, .zero, _ => rfl
  | _, _, .succ i, ρ => get_fl a i ρ.2

/-- `a` is an automorphism of the model. -/
structure Auto (M : Model W Unit) (a : WAut W) : Prop where
  hR : ∀ w v, M.R (a.f w) (a.f v) ↔ M.R w v
  hact : ∀ y w, M.act y (a.f w) ↔ M.act y w
  hP : ∀ ψ w, M.P (fun x v => ψ x (a.g v)) (a.f w) ↔ M.P ψ w
  hadm : ∀ t x, Adm M t x → Adm M t (fl a t x)
  hadm' : ∀ t x, Adm M t x → Adm M t (fl a.inv t x)

variable {M : Model W Unit}

theorem forall_fl {a : WAut W} (A : Auto M a) (t : Ty) (Q : Den W Unit t → Prop) :
    (∀ x, Adm M t x → Q (fl a t x)) ↔ (∀ x, Adm M t x → Q x) :=
  ⟨fun h x hx => fl_inv' a t x ▸ h _ (A.hadm' t x hx), fun h x hx => h _ (A.hadm t x hx)⟩

theorem exists_fl {a : WAut W} (A : Auto M a) (t : Ty) (Q : Den W Unit t → Prop) :
    (∃ x, Adm M t x ∧ Q (fl a t x)) ↔ (∃ x, Adm M t x ∧ Q x) :=
  ⟨fun ⟨x, hx, hq⟩ => ⟨_, A.hadm t x hx, hq⟩,
   fun ⟨x, hx, hq⟩ => ⟨fl a.inv t x, A.hadm' t x hx, by rw [fl_inv']; exact hq⟩⟩

/-- **Equivariance**: evaluation commutes with every automorphism. -/
theorem eval_act {a : WAut W} (A : Auto M a) :
    ∀ {Γ t} (tm : Tm Γ t) (ρ : Env W Unit Γ), eval M tm (flEnv a Γ ρ) = fl a t (eval M tm ρ)
  | _, _, .var i, ρ => get_fl a i ρ
  | _, _, .appP f x, ρ => by
      show eval M f _ (eval M x _) = _
      rw [eval_act A f ρ, eval_act A x ρ]; rfl
  | _, _, .appH F f, ρ => by
      show eval M F _ (eval M f _) = _
      rw [eval_act A F ρ, eval_act A f ρ]
      funext w; simp only [fl, a.fg]; rfl
  | _, _, .lamP b, ρ => by
      funext x w
      exact congrFun (eval_act A b (x, ρ)) w
  | _, _, .lamH b, ρ => by
      funext φ w
      have := congrFun (eval_act A b (fl a.inv .p φ, ρ)) w
      simp only [flEnv, fl_inv'] at this
      exact this
  | _, _, .top, _ => rfl
  | _, _, .bot, _ => rfl
  | _, _, .neg x, ρ => by
      funext w; show (¬ _) = _; rw [eval_act A x ρ]; rfl
  | _, _, .and x y, ρ => by
      funext w; show (_ ∧ _) = _; rw [eval_act A x ρ, eval_act A y ρ]; rfl
  | _, _, .or x y, ρ => by
      funext w; show (_ ∨ _) = _; rw [eval_act A x ρ, eval_act A y ρ]; rfl
  | _, _, .imp x y, ρ => by
      funext w; show (_ → _) = _; rw [eval_act A x ρ, eval_act A y ρ]; rfl
  | _, _, .box x, ρ => by
      funext w
      show (∀ v, M.R w v → eval M x (flEnv a _ ρ) v) = (∀ v, M.R (a.f w) v → eval M x ρ v)
      rw [eval_act A x ρ]
      apply propext
      constructor
      · intro h v hv
        have := h (a.g v) (by rw [← A.hR, a.fg]; exact hv)
        simpa [fl, a.fg] using this
      · intro h v hv
        exact h _ ((A.hR w v).2 hv)
  | _, _, .all t b, ρ => by
      funext w
      show (∀ x, Adm M t x → eval M b (x, flEnv a _ ρ) w) =
        (∀ x, Adm M t x → eval M b (x, ρ) (a.f w))
      apply propext
      rw [← forall_fl A t]
      refine forall_congr' fun x => imp_congr_right fun _ => ?_
      exact Iff.of_eq (congrFun (eval_act A b (x, ρ)) w)
  | _, _, .ex t b, ρ => by
      funext w
      show (∃ x, Adm M t x ∧ eval M b (x, flEnv a _ ρ) w) =
        (∃ x, Adm M t x ∧ eval M b (x, ρ) (a.f w))
      apply propext
      rw [← exists_fl A t]
      refine exists_congr fun x => and_congr_right fun _ => ?_
      exact Iff.of_eq (congrFun (eval_act A b (x, ρ)) w)
  | _, _, .allE b, ρ => by
      funext w
      show (∀ y, M.act y w → eval M b (y, flEnv a _ ρ) w) =
        (∀ y, M.act y (a.f w) → eval M b (y, ρ) (a.f w))
      apply propext
      refine forall_congr' fun y => ?_
      rw [A.hact]
      have := congrFun (eval_act A b (y, ρ)) w
      rw [show ((y, flEnv a _ ρ) : Env W Unit (.e :: _)) = flEnv a (.e :: _) (y, ρ) from rfl, this]
      rfl
  | _, _, .exE b, ρ => by
      funext w
      show (∃ y, M.act y w ∧ eval M b (y, flEnv a _ ρ) w) =
        (∃ y, M.act y (a.f w) ∧ eval M b (y, ρ) (a.f w))
      apply propext
      refine exists_congr fun y => ?_
      rw [A.hact]
      have := congrFun (eval_act A b (y, ρ)) w
      rw [show ((y, flEnv a _ ρ) : Env W Unit (.e :: _)) = flEnv a (.e :: _) (y, ρ) from rfl, this]
      rfl
  | _, _, .eqE x y, ρ => by
      funext w; show (_ = _) = _; rw [eval_act A x ρ, eval_act A y ρ]; rfl
  | _, _, .eqP x y, ρ => by
      funext w; show (_ = _) = _; rw [eval_act A x ρ, eval_act A y ρ, fl_inj]; rfl
  | _, _, .pos, _ => by
      funext ψ w
      exact propext (A.hP ψ w).symm

/-- A symmetric model: a filtration `Fx n` of automorphism sets; admitted = fixed by some `Fx n`. -/
structure SymM (M : Model W Unit) where
  Fx : Nat → WAut W → Prop
  mono : ∀ {n m a}, n ≤ m → Fx m a → Fx n a
  adm : ∀ t x, Adm M t x ↔ ∃ n, ∀ a, Fx n a → fl a t x = x
  auto : ∀ a, Fx 0 a → Auto M a

theorem env_sup (S : SymM M) :
    ∀ (Γ : List Ty) (ρ : Env W Unit Γ), EnvAdm M Γ ρ → ∃ N, ∀ a, S.Fx N a → flEnv a Γ ρ = ρ
  | [], _, _ => ⟨0, fun _ _ => rfl⟩
  | t :: Γ, (x, r), ⟨h1, h2⟩ => by
      obtain ⟨n, hn⟩ := (S.adm t x).1 h1
      obtain ⟨m, hm⟩ := env_sup S Γ r h2
      refine ⟨max n m, fun a ha => ?_⟩
      show (fl a t x, flEnv a Γ r) = (x, r)
      rw [hn a (S.mono (Nat.le_max_left n m) ha), hm a (S.mono (Nat.le_max_right n m) ha)]

/-- **Fact (a)** for symmetric models. -/
theorem lgeneral (S : SymM M) : LGeneral M := by
  intro Γ t tm ρ hρ
  obtain ⟨N, hN⟩ := env_sup S Γ ρ hρ
  refine (S.adm t _).2 ⟨N, fun a ha => ?_⟩
  rw [← eval_act (S.auto a (S.mono (Nat.zero_le N) ha)) tm ρ, hN a ha]

/-! ## Streams, permutations, transitivity -/

def InfB (w : Nat → Bool) (b : Bool) : Prop := ∀ N, ∃ i, N ≤ i ∧ w i = b

/-- Worlds: streams with infinitely many `true`s and infinitely many `false`s. -/
def Wd : Type := {w : Nat → Bool // InfB w true ∧ InfB w false}

structure Pm where
  p : Nat → Nat
  q : Nat → Nat
  pq : ∀ i, p (q i) = i
  qp : ∀ i, q (p i) = i

def Pm.inv (π : Pm) : Pm := ⟨π.q, π.p, π.qp, π.pq⟩

/-- A bound for `f` on `[0,n)`. -/
def bnd (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => max (bnd f n) (f n + 1)

theorem lt_bnd (f : Nat → Nat) : ∀ {n i}, i < n → f i < bnd f n
  | n + 1, i, h => by
      simp only [bnd]
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
      · exact Nat.lt_of_lt_of_le (lt_bnd f h) (Nat.le_max_left _ _)
      · subst h; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)

theorem infB_comp (π : Pm) {w : Nat → Bool} {b : Bool} (h : InfB w b) : InfB (w ∘ π.p) b := by
  intro N
  obtain ⟨j, hj, hw⟩ := h (bnd π.p N)
  refine ⟨π.q j, ?_, by simp [Function.comp, π.pq, hw]⟩
  apply Nat.le_of_not_lt
  intro hlt
  have := lt_bnd π.p hlt
  rw [π.pq] at this
  omega

def wact (π : Pm) (w : Wd) : Wd :=
  ⟨w.1 ∘ π.p, infB_comp π w.2.1, infB_comp π w.2.2⟩

theorem wact_inv (π : Pm) (w : Wd) : wact π (wact π.inv w) = w := by
  apply Subtype.ext; funext i; simp [wact, Pm.inv, Function.comp, π.qp]

theorem wact_inv' (π : Pm) (w : Wd) : wact π.inv (wact π w) = w := by
  apply Subtype.ext; funext i; simp [wact, Pm.inv, Function.comp, π.pq]

def toAut (π : Pm) : WAut Wd := ⟨wact π, wact π.inv, wact_inv π, wact_inv' π⟩

def Fixes (n : Nat) (π : Pm) : Prop := ∀ i, i < n → π.p i = i

/-- Counting the positions `j ∈ [n,i)` with `w j = b`. -/
def cnt (w : Nat → Bool) (b : Bool) (n : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => cnt w b n i + (if n ≤ i ∧ w i = b then 1 else 0)

theorem cnt_mono (w b n) : ∀ {i j}, i ≤ j → cnt w b n i ≤ cnt w b n j
  | _, 0, h => by rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | i, j + 1, h => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with h' | h'
      · have := cnt_mono w b n (Nat.le_of_lt_succ h')
        simp only [cnt]; omega
      · rw [h']; exact Nat.le_refl _

theorem cnt_step (w b n i) : cnt w b n (i + 1) ≤ cnt w b n i + 1 := by
  simp only [cnt]; split <;> omega

theorem cnt_hit (w b n i) (h : n ≤ i) (hw : w i = b) : cnt w b n (i + 1) = cnt w b n i + 1 := by
  simp [cnt, h, hw]

theorem cnt_lt (w b n) {i j} (h : n ≤ i) (hw : w i = b) (hij : i < j) :
    cnt w b n i < cnt w b n j := by
  have := cnt_mono w b n (Nat.succ_le_of_lt hij)
  rw [cnt_hit w b n i h hw] at this; omega

theorem cnt_below (w b n) : ∀ i, i ≤ n → cnt w b n i = 0
  | 0, _ => rfl
  | i + 1, h => by simp only [cnt]; rw [cnt_below w b n i (by omega)]; split <;> omega

theorem cnt_unbounded {w b} (h : InfB w b) (n : Nat) : ∀ m, ∃ N, m ≤ cnt w b n N
  | 0 => ⟨0, Nat.zero_le _⟩
  | m + 1 => by
      obtain ⟨N, hN⟩ := cnt_unbounded h n m
      obtain ⟨i, hi, hw⟩ := h (max N n)
      refine ⟨i + 1, ?_⟩
      rw [cnt_hit w b n i (by omega) hw]
      have := cnt_mono w b n (show N ≤ i by omega)
      omega

/-- Discrete intermediate value: below a count `> m`, value `m` is attained at a `b`-position. -/
theorem cnt_ivt (w b n m) : ∀ N, m < cnt w b n N → ∃ i, n ≤ i ∧ w i = b ∧ cnt w b n i = m
  | 0, h => by simp [cnt] at h
  | N + 1, h => by
      by_cases hN : m < cnt w b n N
      · exact cnt_ivt w b n m N hN
      · refine ⟨N, ?_⟩
        simp only [cnt] at h
        by_cases hc : n ≤ N ∧ w N = b
        · exact ⟨hc.1, hc.2, by simp [hc] at h; omega⟩
        · simp [hc] at h; omega

/-- The canonical stream with prefix `w|n` and tail `1010…`. -/
def can (w : Nat → Bool) (n : Nat) (i : Nat) : Bool :=
  if i < n then w i else decide ((i - n) % 2 = 0)

/-- The position map sending `w` to its canonical form. -/
def cq (w : Nat → Bool) (n i : Nat) : Nat :=
  if i < n then i else if w i = true then n + 2 * cnt w true n i else n + 2 * cnt w false n i + 1

theorem can_cq (w : Nat → Bool) (n i : Nat) : can w n (cq w n i) = w i := by
  unfold cq can
  by_cases hi : i < n
  · simp [hi]
  · by_cases hw : w i = true
    · simp [hi, hw]
    · have hf : w i = false := by cases h : w i <;> simp_all
      have hlt : ¬ (n + 2 * cnt w false n i + 1 < n) := by omega
      simp [hi, hw, hlt]; omega

theorem cq_inj (w : Nat → Bool) (n : Nat) {i j : Nat} (h : cq w n i = cq w n j) : i = j := by
  have key : ∀ {i j}, i < j → cq w n i ≠ cq w n j := by
    intro i j hij
    unfold cq
    by_cases hi : i < n
    · by_cases hj : j < n
      · simp [hi, hj]; omega
      · simp only [hi, hj, ite_true, ite_false]; split <;> omega
    · have hj : ¬ j < n := by omega
      simp only [hi, hj, ite_false]
      by_cases wi : w i = true <;> by_cases wj : w j = true
      · have := cnt_lt w true n (by omega) wi hij
        simp [wi, wj]; omega
      · simp [wi, wj]; omega
      · simp [wi, wj]; omega
      · have wi' : w i = false := by cases h : w i <;> simp_all
        have := cnt_lt w false n (by omega) wi' hij
        simp [wi, wj]; omega
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exact absurd h (key hij)
  · exact hij
  · exact absurd h.symm (key hij)

theorem cq_surj (w : Wd) (n j : Nat) : ∃ i, cq w.1 n i = j := by
  by_cases hj : j < n
  · exact ⟨j, by simp [cq, hj]⟩
  · obtain ⟨m, hm⟩ : ∃ m, j = n + 2 * m ∨ j = n + 2 * m + 1 :=
      ⟨(j - n) / 2, by omega⟩
    rcases hm with hm | hm
    · obtain ⟨N, hN⟩ := cnt_unbounded w.2.1 n (m + 1)
      obtain ⟨i, hi, hw, hc⟩ := cnt_ivt w.1 true n m N (by omega)
      exact ⟨i, by simp [cq, hw, hc, show ¬ i < n by omega, hm]⟩
    · obtain ⟨N, hN⟩ := cnt_unbounded w.2.2 n (m + 1)
      obtain ⟨i, hi, hw, hc⟩ := cnt_ivt w.1 false n m N (by omega)
      exact ⟨i, by simp [cq, hw, hc, show ¬ i < n by omega, hm]⟩

/-- The canonicalising permutation of `w` above `n`: `q = cq`, `p` its inverse. -/
noncomputable def canPm (w : Wd) (n : Nat) : Pm where
  p := fun j => Classical.choose (cq_surj w n j)
  q := cq w.1 n
  pq := fun i => cq_inj w.1 n (Classical.choose_spec (cq_surj w n (cq w.1 n i)))
  qp := fun j => Classical.choose_spec (cq_surj w n j)

theorem canPm_fix (w : Wd) (n : Nat) : Fixes n (canPm w n) := by
  intro i hi
  apply cq_inj w.1 n
  exact ((canPm w n).qp i).trans (by simp [cq, hi] : cq w.1 n i = i).symm

theorem pm_fix_q {π : Pm} {n} (h : Fixes n π) : ∀ i, i < n → π.q i = i :=
  fun i hi => by have := congrArg π.q (h i hi); rw [π.qp] at this; exact this.symm

/-- **Transitivity**: `Fix n` acts transitively on streams with a given prefix of length `n`. -/
theorem transitive (w w' : Wd) (n : Nat) (h : ∀ i, i < n → w.1 i = w'.1 i) :
    ∃ π, Fixes n π ∧ wact π w = w' := by
  let a := canPm w n
  let b := canPm w' n
  refine ⟨⟨fun i => a.p (b.q i), fun i => b.p (a.q i),
    fun i => by simp only [b.qp, a.pq], fun i => by simp only [a.qp, b.pq]⟩, ?_, ?_⟩
  · intro i hi
    show a.p (b.q i) = i
    rw [pm_fix_q (canPm_fix w' n) i hi, canPm_fix w n i hi]
  · apply Subtype.ext; funext i
    show w.1 (a.p (cq w'.1 n i)) = w'.1 i
    have hcan : can w.1 n = can w'.1 n := by
      funext j; unfold can; split
      · exact h j (by assumption)
      · rfl
    rw [← can_cq w.1 n (a.p _)]
    show can w.1 n (a.q (a.p _)) = _
    rw [a.qp, hcan, can_cq]

/-! ## The model -/

def Fx (n : Nat) (a : WAut Wd) : Prop := ∃ π, Fixes n π ∧ a = toAut π

def AdmF (t : Ty) (x : Den Wd Unit t) : Prop := ∃ n, ∀ a, Fx n a → fl a t x = x

/-- Vanishing below `n`. -/
def Zb (n : Nat) (w : Wd) : Prop := ∀ i, i < n → w.1 i = false

/-- The free ultrafilter at the missing point `0^ω`. -/
def Pz (φ : Unit → Wd → Prop) : Prop := ∃ n, ∀ w, Zb n w → φ () w

def rx : Model Wd Unit where
  R := fun _ _ => True
  act := fun _ _ => True
  AS := AdmF .s
  AT := AdmF .p
  AH := AdmF .h
  P := fun φ _ => Pz φ

theorem fx_mono {n m a} (h : n ≤ m) (ha : Fx m a) : Fx n a := by
  obtain ⟨π, hπ, rfl⟩ := ha
  exact ⟨π, fun i hi => hπ i (by omega), rfl⟩

theorem adm_iff : ∀ t x, Adm rx t x ↔ AdmF t x
  | .e, _ => ⟨fun _ => ⟨0, fun _ _ => rfl⟩, fun _ => trivial⟩
  | .s, _ => Iff.rfl
  | .p, _ => Iff.rfl
  | .h, _ => Iff.rfl

theorem toAut_inv (π : Pm) : (toAut π).inv = toAut π.inv := rfl

/-- `τ := π⁻¹ σ π`. -/
def cj (π σ : Pm) : Pm := ⟨fun i => π.q (σ.p (π.p i)), fun i => π.q (σ.q (π.p i)),
    fun i => by simp [π.pq, σ.pq, π.qp], fun i => by simp [π.pq, σ.qp, π.qp]⟩

theorem wact_cj (π σ : Pm) (w : Wd) : wact π (wact σ w) = wact (cj π σ) (wact π w) := by
  apply Subtype.ext; funext i; simp [wact, cj, Function.comp, π.pq]

theorem wact_cj' (π σ : Pm) (v : Wd) :
    wact σ.inv (wact π.inv v) = wact π.inv (wact (cj π σ).inv v) := by
  apply Subtype.ext; funext i; simp [wact, cj, Pm.inv, Function.comp, π.pq]

theorem fl_cj (π σ : Pm) : ∀ t x, fl (toAut σ) t (fl (toAut π) t x) =
    fl (toAut π) t (fl (toAut (cj π σ)) t x)
  | .e, _ => rfl
  | .s, q => by funext w; simp only [fl, toAut]; rw [wact_cj]
  | .p, φ => by funext x w; simp only [fl, toAut]; rw [wact_cj]
  | .h, Φ => by
      funext ψ w
      have e : (fun (x : Unit) v => ψ x (wact σ.inv (wact π.inv v))) =
          (fun x v => ψ x (wact π.inv (wact (cj π σ).inv v))) := by
        funext x v; rw [wact_cj']
      simp only [fl, toAut]; rw [wact_cj, e]

/-- Conjugation: if `x` is fixed by `Fix n`, then `π · x` is fixed by `Fix (bnd π.p n)`. -/
theorem admF_act (π : Pm) (t : Ty) (x : Den Wd Unit t) (hx : AdmF t x) :
    AdmF t (fl (toAut π) t x) := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨bnd π.p n, ?_⟩
  rintro _ ⟨σ, hσ, rfl⟩
  have hτ : Fixes n (cj π σ) := by
    intro i hi
    show π.q (σ.p (π.p i)) = i
    rw [hσ (π.p i) (lt_bnd π.p hi), π.qp]
  rw [fl_cj, hn _ ⟨_, hτ, rfl⟩]

theorem auto_rx (π : Pm) : Auto rx (toAut π) where
  hR := fun _ _ => Iff.rfl
  hact := fun _ _ => Iff.rfl
  hP := fun ψ _ => by
    show Pz (fun x v => ψ x (wact π.inv v)) ↔ Pz ψ
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨bnd π.p n, fun w hw => ?_⟩
      have := hn (wact π w) (fun i hi => hw _ (lt_bnd π.p hi))
      simp only [wact_inv'] at this; exact this
    · rintro ⟨n, hn⟩
      exact ⟨bnd π.q n, fun w hw => hn _ (fun i hi => hw _ (lt_bnd π.q hi))⟩
  hadm := fun t x hx => (adm_iff t _).2 (admF_act π t x ((adm_iff t x).1 hx))
  hadm' := fun t x hx => by
    rw [toAut_inv]; exact (adm_iff t _).2 (admF_act π.inv t x ((adm_iff t x).1 hx))

def symRx : SymM rx where
  Fx := Fx
  mono := fx_mono
  adm := adm_iff
  auto := by rintro _ ⟨π, _, rfl⟩; exact auto_rx π

/-- **Fact (a)**: the model is closed under the fragment of `𝓛`. -/
theorem rx_lgeneral : LGeneral rx := lgeneral symRx

/-! ## The axioms -/

/-- `0^k (10)^ω`. -/
def zw (k : Nat) : Wd :=
  ⟨fun i => decide (k ≤ i ∧ (i - k) % 2 = 0),
   fun N => ⟨k + 2 * N, by omega, by simp⟩,
   fun N => ⟨k + 2 * N + 1, by omega, by simp; omega⟩⟩

theorem zb_zw {n k : Nat} (h : n ≤ k) : Zb n (zw k) := by
  intro i hi; simp [zw]; omega

theorem adm_inv {φ : Unit → Wd → Prop} (h : AdmF .p φ) :
    ∃ n, ∀ π, Fixes n π → ∀ w, (φ () (wact π w) ↔ φ () w) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun π hπ w => Iff.of_eq (congrFun (congrFun (hn _ ⟨π, hπ, rfl⟩) ()) w)⟩

theorem cyl {φ : Unit → Wd → Prop} {n : Nat}
    (hn : ∀ π, Fixes n π → ∀ w, (φ () (wact π w) ↔ φ () w)) {w w' : Wd}
    (h : ∀ i, i < n → w.1 i = w'.1 i) : φ () w ↔ φ () w' := by
  obtain ⟨π, hπ, rfl⟩ := transitive w w' n h
  exact (hn π hπ w).symm

theorem ax2a : Ax2a rx := by
  intro φ hφ _
  obtain ⟨n, hn⟩ := adm_inv hφ
  refine ⟨?_, ?_⟩
  · by_cases h : φ () (zw n)
    · exact Or.inl ⟨n, fun w hw => (cyl hn (fun i hi => by rw [zb_zw (Nat.le_refl n) i hi, hw i hi])).1 h⟩
    · exact Or.inr ⟨n, fun w hw => fun hw' =>
        h ((cyl hn (fun i hi => by rw [zb_zw (Nat.le_refl n) i hi, hw i hi])).2 hw')⟩
  · rintro ⟨⟨n1, h1⟩, ⟨n2, h2⟩⟩
    exact h2 _ (zb_zw (Nat.le_max_right n1 n2)) (h1 _ (zb_zw (Nat.le_max_left n1 n2)))

theorem ax2b : Ax2b rx := fun _ _ _ h _ _ => h

theorem ax4 : Ax4 rx := by
  rintro φ ψ - - w ⟨n, hn⟩ hinc
  exact ⟨n, fun v hv => hinc v trivial () trivial (hn v hv)⟩

/-- The bit at `i` is admitted (supported by `Fix (i+1)`). -/
theorem bit_adm (i : Nat) (c : Bool) : rx.AT (fun _ v => v.1 i = c) := by
  refine ⟨i + 1, ?_⟩
  rintro _ ⟨π, hπ, rfl⟩
  funext x v
  show ((v.1 (π.p i)) = c) = (v.1 i = c)
  rw [hπ i (Nat.lt_succ_self i)]

def swp (i j k : Nat) : Nat := if k = i then j else if k = j then i else k

theorem swp_swp (i j k : Nat) : swp i j (swp i j k) = k := by
  unfold swp; split <;> split <;> (try split) <;> (try split) <;> omega

def tr (i j : Nat) : Pm := ⟨swp i j, swp i j, swp_swp i j, swp_swp i j⟩

/-- Every stream can be moved by `Fix n` at some coordinate. -/
theorem split (u : Wd) (n : Nat) : ∃ π i, Fixes n π ∧ (wact π u).1 i ≠ u.1 i := by
  obtain ⟨i, hi, hu⟩ := u.2.1 n
  obtain ⟨j, hj, hv⟩ := u.2.2 n
  have hij : i ≠ j := fun h => by subst h; rw [hu] at hv; exact Bool.noConfusion hv
  refine ⟨tr i j, i, fun k hk => ?_, ?_⟩
  · show swp i j k = k
    unfold swp; split <;> (try split) <;> omega
  · show u.1 (swp i j i) ≠ u.1 i
    simp [swp, hu, hv]

theorem top_adm : rx.AT top := ⟨0, by rintro _ ⟨π, -, rfl⟩; rfl⟩

/-- No admitted property is a (variant-2) essence. -/
theorem no_ess (φ : Unit → Wd → Prop) (hφ : rx.AT φ) (w : Wd) : ¬ Ess rx φ () w := by
  rintro ⟨hw, hall⟩
  obtain ⟨n, hn⟩ := adm_inv hφ
  obtain ⟨π, i, hπ, hne⟩ := split w n
  have hu : φ () (wact π w) := (hn π hπ w).2 hw
  exact hne (hall _ (bit_adm i (w.1 i)) rfl (wact π w) trivial () trivial hu)

/-- No admitted property is a (variant-3′) essence. -/
theorem no_ess3 (φ : Unit → Wd → Prop) (hφ : rx.AT φ) (w : Wd) : ¬ Ess3 rx φ () w := by
  intro h
  have hne : φ ≠ bot := (h top top_adm trivial w trivial).1
  have : ∃ u, φ () u := Classical.byContradiction fun hn =>
    hne (funext fun x => funext fun u => propext ⟨fun hu => hn ⟨u, by cases x; exact hu⟩,
      False.elim⟩)
  obtain ⟨u0, hu0⟩ := this
  obtain ⟨n, hn⟩ := adm_inv hφ
  obtain ⟨π, i, hπ, hdiff⟩ := split u0 n
  have hu1 : φ () (wact π u0) := (hn π hπ u0).2 hu0
  have key : ∀ u, φ () u → u.1 i = w.1 i := fun u hu =>
    (h _ (bit_adm i (w.1 i)) rfl u trivial).2 () trivial hu
  exact hdiff ((key _ hu1).trans (key _ hu0).symm)

theorem E_top (x : Unit) (w : Wd) : E rx x w := by
  cases x; exact fun φ hφ he => absurd he (no_ess φ hφ w)

theorem E3_top (x : Unit) (w : Wd) : E3 rx x w := by
  cases x; exact fun φ hφ he => absurd he (no_ess3 φ hφ w)

theorem ax3 : Ax3 rx := fun _ => ⟨0, fun w _ => E_top () w⟩

theorem ax3v3 : Ax3v3 rx := fun _ => ⟨0, fun w _ => E3_top () w⟩

/-- No world has a God-like being: positivity is not principal anywhere. -/
theorem godless (w : Wd) : ¬ ExG rx w := by
  rintro ⟨y, -, hG⟩
  obtain ⟨i, -, hi⟩ := w.2.1 0
  have := hG _ (bit_adm i false) ⟨i + 1, fun v hv => hv i (Nat.lt_succ_self i)⟩
  cases y; rw [hi] at this; exact Bool.noConfusion this

theorem not_mc : ¬ MC rx := by
  intro h
  have := h (fun v => v.1 0 = true) ⟨1, by
      rintro _ ⟨π, hπ, rfl⟩; funext v
      show (v.1 (π.p 0) = true) = (v.1 0 = true); rw [hπ 0 (by omega)]⟩
    (zw 0) (by simp [zw]) (zw 1) trivial
  simp [zw] at this

theorem not_ax1GenTwo : ¬ Ax1GenTwo rx := fun h =>
  not_mc (mc_v2 (closed_of_lgeneral rx_lgeneral) (E_adm rx_lgeneral) ax2a ax2b ax3 ax4 h)

theorem not_ax1Gen : ¬ Ax1Gen rx := fun h =>
  not_ax1GenTwo fun Φ φ hΦ hφ w _ => h Φ φ hΦ hφ w

/-- **The rigid, non-principal exit.**  A model closed under the fragment of `𝓛` (S5, one
individual, all actual) in which positivity is rigid (Ax2b) and satisfies Ax2a, Ax3 (variants 2
and 3′) and Ax4, yet admitted modal collapse fails and no world has a God-like being.
Ax1Gen and Ax1GenTwo fail, as they must (K1/K55). -/
theorem rigid_exit :
    LGeneral rx ∧ (∀ w v, rx.R w v) ∧ (∀ y w, rx.act y w) ∧
    Ax2a rx ∧ Ax2b rx ∧ Ax3 rx ∧ Ax3v3 rx ∧ Ax4 rx ∧
    ¬ MC rx ∧ (∀ w, ¬ ExG rx w) ∧ ¬ Ax1Gen rx ∧ ¬ Ax1GenTwo rx :=
  ⟨rx_lgeneral, fun _ _ => trivial, fun _ _ => trivial, ax2a, ax2b, ax3, ax3v3, ax4,
    not_mc, godless, not_ax1Gen, not_ax1GenTwo⟩

end Programme.«20261022-0733-ontological».Run2.RigidExit

#print axioms Programme.«20261022-0733-ontological».Run2.RigidExit.rx_lgeneral
#print axioms Programme.«20261022-0733-ontological».Run2.RigidExit.rigid_exit
