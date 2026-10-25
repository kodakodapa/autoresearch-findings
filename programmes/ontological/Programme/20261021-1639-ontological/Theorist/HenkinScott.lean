/- D13: K22 (Scott, KB: A1a + A2 + A5 ⇒ collapse) under general (Henkin-style) semantics.
Properties range over admitted `adm`, propositions over admitted `admP`; Ess, NE and G quantify
over admitted properties only.
(1) `mcAdm_of_types`: if every world's type (meet of the admitted propositions true there) is
    admitted, the K22 argument survives with object-level collapse `MCadm`.
(2) `cantor_*`: worlds `ℕ → Bool`, admitted = finitely based sets. No type is admitted, no entity
    has an essence, NE holds vacuously, and A1a, A2, A3, A4, A5 hold on an S5 frame while an
    admitted proposition violates collapse. A1b fails. -/
namespace Programme.«20261021-1639-ontological».Theorist.HenkinScott

structure GModel (W E : Type) where
  rel : W → W → Prop
  actual : E → W → Prop
  adm : (E → W → Prop) → Prop
  admP : (W → Prop) → Prop
  positive : (E → W → Prop) → W → Prop

variable {W E : Type} (m : GModel W E) (a : Bool)
def guard (x : E) (w : W) : Prop := a = true → m.actual x w

def EssH (p : E → W → Prop) (x : E) (w : W) : Prop :=
  p x w ∧ ∀ q, m.adm q → q x w → ∀ v, m.rel w v → ∀ y, guard m a y v → p y v → q y v
def NEH (x : E) (w : W) : Prop :=
  ∀ p, m.adm p → EssH m a p x w → ∀ v, m.rel w v → ∃ y, guard m a y v ∧ p y v
def GH (x : E) (w : W) : Prop := ∀ p, m.adm p → m.positive p w → p x w

def A1a : Prop := ∀ p w, m.adm p → m.positive (fun x v => ¬ p x v) w → ¬ m.positive p w
def A1b : Prop := ∀ p w, m.adm p → ¬ m.positive p w → m.positive (fun x v => ¬ p x v) w
def A2 : Prop := ∀ p q w, m.adm p → m.adm q → m.positive p w →
  (∀ v, m.rel w v → ∀ y, guard m a y v → p y v → q y v) → m.positive q w
def A3 : Prop := ∀ w, m.positive (GH m) w
def A4 : Prop := ∀ p w, m.adm p → m.positive p w → ∀ v, m.rel w v → m.positive p v
def A5 : Prop := ∀ w, m.positive (NEH m a) w
def MCadm : Prop := ∀ p, m.admP p → ∀ w, p w → ∀ v, m.rel w v → p v
/-- The type of `t`, the meet of all admitted propositions true at `t`, is itself admitted. -/
def TypesAdmitted : Prop :=
  ∀ t, ∃ c, m.admP c ∧ c t ∧ ∀ q, m.admP q → q t → ∀ v, c v → q v
/-- Closure facts used by (1); all are instances of definable-term closure. -/
structure Clo : Prop where
  neg : ∀ p, m.adm p → m.adm (fun x v => ¬ p x v)
  slice : ∀ p x, m.adm p → m.admP (fun v => p x v)
  sing : ∀ x c, m.admP c → m.adm (fun y v => y = x ∧ c v)
  ne : m.adm (NEH m a)

theorem positive_possible (hc : Clo m a) (h1 : A1a m) (h2 : A2 m a)
    (p : E → W → Prop) (hp : m.adm p) (w : W) (hpos : m.positive p w) :
    ∃ v, m.rel w v ∧ ∃ x, guard m a x v ∧ p x v := by
  apply Classical.byContradiction
  intro hn
  apply h1 p w hp (h2 p _ w hp (hc.neg p hp) hpos ?_) hpos
  intro v hv x hx hpx
  exact fun hnp => hn ⟨v, hv, x, hx, hnp⟩

/-- An admitted type gives a singleton-type essence. -/
theorem type_essence (hc : Clo m a) (x : E) (t : W) (c : W → Prop) (hct : c t)
    (hcq : ∀ q, m.admP q → q t → ∀ v, c v → q v) :
    EssH m a (fun y v => y = x ∧ c v) x t := by
  refine ⟨⟨rfl, hct⟩, ?_⟩
  intro q hq hqx v _ y _ hy
  obtain ⟨rfl, hcv⟩ := hy
  exact hcq _ (hc.slice q y hq) hqx v hcv

/-- (1) K22 survives when types are admitted (e.g. every finite Henkin model). -/
theorem mcAdm_of_types (hc : Clo m a) (hT : TypesAdmitted m)
    (symm : ∀ w v, m.rel w v → m.rel v w)
    (h1 : A1a m) (h2 : A2 m a) (h5 : A5 m a) : MCadm m := by
  intro p hp w hw v hwv
  obtain ⟨t, hwt, x, _, hx⟩ := positive_possible m a hc h1 h2 _ hc.ne w (h5 w)
  obtain ⟨ct, hctA, hct, hctq⟩ := hT t
  -- NE at t confines successors of t to the type of t
  have hsucc : ∀ u, m.rel t u → ct u := by
    intro u htu
    obtain ⟨y, _, hy⟩ := hx _ (hc.sing x ct hctA) (type_essence m a hc x t ct hct hctq) u htu
    exact hy.2
  -- so w has the type of t, and NE x (an admitted proposition) transfers to w
  have hxw : NEH m a x w :=
    hctq _ (hc.slice _ x hc.ne) hx w (hsucc w (symm w t hwt))
  obtain ⟨cw, hcwA, hcw, hcwq⟩ := hT w
  obtain ⟨y, _, hy⟩ := hxw _ (hc.sing x cw hcwA) (type_essence m a hc x w cw hcw hcwq) v hwv
  exact hcwq p hp hw v hy.2

/-! (2) The Cantor-space model. -/

abbrev Wc := Nat → Bool

def Based (n : Nat) (s : Wc → Prop) : Prop :=
  ∀ v v', (∀ k, k < n → v k = v' k) → (s v ↔ s v')

def cantor : GModel Wc Unit where
  rel _ _ := True
  actual _ _ := True
  adm p := ∃ n, Based n (p ())
  admP s := ∃ n, Based n s
  positive p _ := ∀ v, p () v

def flip (t : Wc) (n : Nat) : Wc := fun k => if k = n then !t n else t k

theorem flip_agree (t : Wc) (n : Nat) : ∀ k, k < n → t k = flip t n k := by
  intro k hk
  simp [flip, Nat.ne_of_lt hk]

/-- No admitted property is an essence of anything, at any world. -/
theorem cantor_no_essence (p : Unit → Wc → Prop) (hp : cantor.adm p) (x : Unit) (t : Wc) :
    ¬ EssH cantor a p x t := by
  intro ⟨hpt, hq⟩
  obtain ⟨n, hn⟩ := hp
  have hflip : p () (flip t n) := (hn t (flip t n) (flip_agree t n)).1 hpt
  have hadm : cantor.adm (fun _ v => v n = t n) := by
    refine ⟨n + 1, ?_⟩
    intro v v' hvv
    show v n = t n ↔ v' n = t n
    rw [hvv n (Nat.lt_succ_self n)]
  have := hq (fun _ v => v n = t n) hadm rfl (flip t n) trivial () (fun _ => trivial) hflip
  simp [flip] at this

theorem cantor_NE : ∀ x w, NEH cantor a x w := by
  intro x w p hp he
  exact (cantor_no_essence a p hp x w he).elim

theorem cantor_G : ∀ x w, GH cantor x w := by
  intro x w p _ hp
  exact hp w

theorem cantor_S5 : (∀ w, cantor.rel w w) ∧ (∀ w v, cantor.rel w v → cantor.rel v w) ∧
    (∀ w v u, cantor.rel w v → cantor.rel v u → cantor.rel w u) :=
  ⟨fun _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩

theorem cantor_A1a : A1a cantor := by
  intro p w _ hn hp
  exact hn (fun _ => false) (hp _)

theorem cantor_A2 : A2 cantor a := by
  intro p q w _ _ hp hpq v
  exact hpq v trivial () (fun _ => trivial) (hp v)

theorem cantor_A3 : A3 cantor := fun _ v => cantor_G () v

theorem cantor_A4 : A4 cantor := fun _ _ _ hp _ _ => hp

theorem cantor_A5 : A5 cantor a := fun _ v => cantor_NE a () v

theorem cantor_not_A1b : ¬ A1b cantor := by
  intro h
  have hadm : cantor.adm (fun _ v => v 0 = true) := by
    refine ⟨1, ?_⟩
    intro v v' hvv
    show v 0 = true ↔ v' 0 = true
    rw [hvv 0 (Nat.zero_lt_one)]
  have hn : ¬ cantor.positive (fun _ v => v 0 = true) (fun _ => true) :=
    fun hp => by simpa using hp (fun _ => false)
  have := h _ (fun _ => true) hadm hn (fun _ => true)
  simp at this

theorem cantor_not_MCadm : ¬ MCadm cantor := by
  intro h
  have := h (fun v => v 0 = true) ⟨1, fun v v' hvv => by show v 0 = true ↔ v' 0 = true; rw [hvv 0 Nat.zero_lt_one]⟩
    (fun _ => true) rfl (fun _ => false) trivial
  simp at this

theorem cantor_not_types : ¬ TypesAdmitted cantor := by
  intro h
  obtain ⟨c, ⟨n, hn⟩, hct, hcq⟩ := h (fun _ => false)
  have hcf : c (flip (fun _ => false) n) := (hn _ _ (flip_agree _ n)).1 hct
  have := hcq (fun v => v n = false) ⟨n + 1, fun v v' hvv => by show v n = false ↔ v' n = false; rw [hvv n (Nat.lt_succ_self n)]⟩
    rfl _ hcf
  simp [flip] at this

/-- Closure facts of (1) that hold in the Cantor model (only `sing` fails, as it must). -/
theorem cantor_clo_partial :
    (∀ p, cantor.adm p → cantor.adm (fun x v => ¬ p x v)) ∧
    (∀ p x, cantor.adm p → cantor.admP (fun v => p x v)) ∧
    cantor.adm (NEH cantor a) ∧ cantor.adm (GH cantor) ∧
    cantor.adm (fun _ _ => True) ∧ cantor.adm (fun _ _ => False) ∧
    (∀ s, cantor.admP s → cantor.adm (fun _ v => s v)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p ⟨n, hn⟩
    exact ⟨n, fun v v' h => not_congr (hn v v' h)⟩
  · intro p x ⟨n, hn⟩
    cases x
    exact ⟨n, hn⟩
  · exact ⟨0, fun v v' _ => iff_of_true (cantor_NE a () v) (cantor_NE a () v')⟩
  · exact ⟨0, fun v v' _ => iff_of_true (cantor_G () v) (cantor_G () v')⟩
  · exact ⟨0, fun _ _ _ => Iff.rfl⟩
  · exact ⟨0, fun _ _ _ => Iff.rfl⟩
  · intro s hs
    exact hs

/-! (3) Full Scott A1a, A1b, A2, A3, A4, A5 force object-level collapse on symmetric frames,
with no world naming: only negation, constant lifts, and admitted G and NE are used. -/

structure Clo3 : Prop where
  neg : ∀ p, m.adm p → m.adm (fun x v => ¬ p x v)
  lift : ∀ s, m.admP s → m.adm (fun _ v => s v)
  ne : m.adm (NEH m a)
  g : m.adm (GH m)

/-- A1b: every admitted property of a God is positive. -/
theorem god_positive (hc : Clo3 m a) (h1b : A1b m) (p : E → W → Prop) (hp : m.adm p)
    (x : E) (w : W) (hg : GH m x w) (hpx : p x w) : m.positive p w :=
  Classical.byContradiction fun hn => hg _ (hc.neg p hp) (h1b p w hp hn) hpx

/-- G is an essence of every God (A1b, A4). -/
theorem god_essence (hc : Clo3 m a) (h1b : A1b m) (h4 : A4 m) (x : E) (w : W)
    (hg : GH m x w) : EssH m a (GH m) x w := by
  refine ⟨hg, ?_⟩
  intro q hq hqx v hv y _ hgy
  exact hgy q hq (h4 q w hq (god_positive m a hc h1b q hq x w hg hqx) v hv)

/-- On symmetric frames every world has a guarded God. -/
theorem god_everywhere (hc : Clo3 m a) (symm : ∀ w v, m.rel w v → m.rel v w)
    (h1a : A1a m) (h1b : A1b m) (h2 : A2 m a) (h3 : A3 m) (h4 : A4 m) (h5 : A5 m a) :
    ∀ w, ∃ y, guard m a y w ∧ GH m y w := by
  intro w
  have hneg : ∀ p, m.adm p → m.adm (fun x v => ¬ p x v) := hc.neg
  obtain ⟨t, hwt, x, _, hx⟩ : ∃ v, m.rel w v ∧ ∃ x, guard m a x v ∧ GH m x v := by
    apply Classical.byContradiction
    intro hn
    apply h1a _ w hc.g (h2 _ _ w hc.g (hneg _ hc.g) (h3 w) ?_) (h3 w)
    exact fun v hv x hx hgx => hn ⟨v, hv, x, hx, hgx⟩ |>.elim
  have hne : NEH m a x t := hx _ hc.ne (h5 t)
  exact hne _ hc.g (god_essence m a hc h1b h4 x t hx) w (symm w t hwt)

theorem mcAdm_scott (hc : Clo3 m a) (symm : ∀ w v, m.rel w v → m.rel v w)
    (h1a : A1a m) (h1b : A1b m) (h2 : A2 m a) (h3 : A3 m) (h4 : A4 m) (h5 : A5 m a) :
    MCadm m := by
  intro p hp w hw v hwv
  obtain ⟨y, _, hy⟩ := god_everywhere m a hc symm h1a h1b h2 h3 h4 h5 w
  obtain ⟨y', _, hy'⟩ := god_everywhere m a hc symm h1a h1b h2 h3 h4 h5 v
  have hpos := god_positive m a hc h1b (fun _ u => p u) (hc.lift p hp) y w hy hw
  exact hy' _ (hc.lift p hp) (h4 _ w (hc.lift p hp) hpos v hwv)

#print axioms mcAdm_scott
#print axioms mcAdm_of_types
#print axioms cantor_no_essence
#print axioms cantor_A1a
#print axioms cantor_A2
#print axioms cantor_A3
#print axioms cantor_A4
#print axioms cantor_A5
#print axioms cantor_not_A1b
#print axioms cantor_not_MCadm
#print axioms cantor_not_types
#print axioms cantor_clo_partial
end Programme.«20261021-1639-ontological».Theorist.HenkinScott
