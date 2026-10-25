import Programme.«20261021-1639-ontological».Theorist.ScottTable
import Programme.«20261021-1639-ontological».Theorist.HenkinScott
/- D14: Henkin minimality of Scott's A1a, A1b, A2, A3, A4, A5 for object-level collapse.
`mcAdm_scott` (HenkinScott) derives MCadm on symmetric frames from all six axioms under `Clo3`.
Here: for each of the six there is an S5 GModel satisfying `Clo3` and the other five, refuting
MCadm. Drops of A1a, A2, A5 are the full-intension D7 models (adm = everything); A1b is the binary
Cantor model; A4 is the Cantor model with current-world positivity; A3 is a ternary Cantor model
with recursive-majority positivity (no God anywhere). -/
namespace Programme.«20261021-1639-ontological».Theorist.HenkinMinimal
open Programme.«20261021-1639-ontological».Theorist.HenkinScott

variable {W E : Type} (a : Bool)

def Symm {W E} (m : GModel W E) : Prop := ∀ w v, m.rel w v → m.rel v w

/-! ### Full-intension models as GModels. -/
def full (m : ScottTable.Model W E) : GModel W E :=
  ⟨m.rel, m.actual, fun _ => True, fun _ => True, m.positive⟩

theorem essH_full (m : ScottTable.Model W E) (p : E → W → Prop) (x : E) (w : W) :
    EssH (full m) a p x w ↔ ScottTable.Ess m a p x w :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1, fun q hq => h2 q trivial hq⟩,
   fun ⟨h1, h2⟩ => ⟨h1, fun q _ hq => h2 q hq⟩⟩

theorem gh_full (m : ScottTable.Model W E) : GH (full m) = ScottTable.G m := by
  funext x w; apply propext
  exact ⟨fun h p hp => h p trivial hp, fun h p _ hp => h p hp⟩

theorem neh_full (m : ScottTable.Model W E) : NEH (full m) a = ScottTable.NE m a := by
  funext x w; apply propext
  constructor
  · intro h p hp; exact h p trivial ((essH_full a m p x w).2 hp)
  · intro h p _ hp; exact h p ((essH_full a m p x w).1 hp)

theorem full_clo3 (m : ScottTable.Model W E) : Clo3 (full m) a :=
  ⟨fun _ _ => trivial, fun _ _ => trivial, trivial, trivial⟩

theorem full_A1a (m : ScottTable.Model W E) : A1a (full m) ↔ ScottTable.A1a m :=
  ⟨fun h p w => h p w trivial, fun h p w _ => h p w⟩
theorem full_A1b (m : ScottTable.Model W E) : A1b (full m) ↔ ScottTable.A1b m :=
  ⟨fun h p w => h p w trivial, fun h p w _ => h p w⟩
theorem full_A2 (m : ScottTable.Model W E) : A2 (full m) a ↔ ScottTable.A2 m a :=
  ⟨fun h p q w => h p q w trivial trivial, fun h p q w _ _ => h p q w⟩
theorem full_A3 (m : ScottTable.Model W E) : A3 (full m) ↔ ScottTable.A3 m := by
  unfold A3 ScottTable.A3; rw [gh_full]; exact Iff.rfl
theorem full_A4 (m : ScottTable.Model W E) : A4 (full m) ↔ ScottTable.A4 m :=
  ⟨fun h p w => h p w trivial, fun h p w _ => h p w⟩
theorem full_A5 (m : ScottTable.Model W E) : A5 (full m) a ↔ ScottTable.A5 m a := by
  unfold A5 ScottTable.A5; rw [neh_full]; exact Iff.rfl
theorem full_MC (m : ScottTable.Model W E) : MCadm (full m) ↔ ScottTable.MC m :=
  ⟨fun h p => h p trivial, fun h p _ => h p⟩

theorem henkin_drop_A1a :
    Clo3 (full ScottTable.allPos) a ∧ Symm (full ScottTable.allPos) ∧
    ¬ A1a (full ScottTable.allPos) ∧ A1b (full ScottTable.allPos) ∧
    A2 (full ScottTable.allPos) a ∧ A3 (full ScottTable.allPos) ∧ A4 (full ScottTable.allPos) ∧
    A5 (full ScottTable.allPos) a ∧ ¬ MCadm (full ScottTable.allPos) := by
  obtain ⟨s5, n1a, h1b, h2, h3, h4, h5, _, nmc, _⟩ := ScottTable.drop_A1a a
  exact ⟨full_clo3 a _, s5.2, fun h => n1a ((full_A1a _).1 h), (full_A1b _).2 h1b,
    (full_A2 a _).2 h2, (full_A3 _).2 h3, (full_A4 _).2 h4, (full_A5 a _).2 h5,
    fun h => nmc ((full_MC _).1 h)⟩

theorem henkin_drop_A2 :
    Clo3 (full ScottTable.twoPos) a ∧ Symm (full ScottTable.twoPos) ∧
    A1a (full ScottTable.twoPos) ∧ A1b (full ScottTable.twoPos) ∧
    ¬ A2 (full ScottTable.twoPos) a ∧ A3 (full ScottTable.twoPos) ∧ A4 (full ScottTable.twoPos) ∧
    A5 (full ScottTable.twoPos) a ∧ ¬ MCadm (full ScottTable.twoPos) := by
  obtain ⟨s5, h1a, h1b, n2, h3, h4, h5, _, nmc, _⟩ := ScottTable.drop_A2 a
  exact ⟨full_clo3 a _, s5.2, (full_A1a _).2 h1a, (full_A1b _).2 h1b,
    fun h => n2 ((full_A2 a _).1 h), (full_A3 _).2 h3, (full_A4 _).2 h4, (full_A5 a _).2 h5,
    fun h => nmc ((full_MC _).1 h)⟩

theorem henkin_drop_A5 :
    Clo3 (full ScottTable.princ) a ∧ Symm (full ScottTable.princ) ∧
    A1a (full ScottTable.princ) ∧ A1b (full ScottTable.princ) ∧
    A2 (full ScottTable.princ) a ∧ A3 (full ScottTable.princ) ∧ A4 (full ScottTable.princ) ∧
    ¬ A5 (full ScottTable.princ) a ∧ ¬ MCadm (full ScottTable.princ) := by
  obtain ⟨s5, h1a, h1b, h2, h3, h4, n5, _, nmc⟩ := ScottTable.drop_A5 a
  exact ⟨full_clo3 a _, s5.2, (full_A1a _).2 h1a, (full_A1b _).2 h1b,
    (full_A2 a _).2 h2, (full_A3 _).2 h3, (full_A4 _).2 h4, fun h => n5 ((full_A5 a _).1 h),
    fun h => nmc ((full_MC _).1 h)⟩

/-! ### Drop A1b: the binary Cantor model of HenkinScott. -/
theorem cantor_clo3 : Clo3 cantor a := by
  obtain ⟨hn, _, hne, hg, _, _, hl⟩ := cantor_clo_partial a
  exact ⟨hn, hl, hne, hg⟩

theorem henkin_drop_A1b :
    Clo3 cantor a ∧ Symm cantor ∧ A1a cantor ∧ ¬ A1b cantor ∧ A2 cantor a ∧ A3 cantor ∧
    A4 cantor ∧ A5 cantor a ∧ ¬ MCadm cantor :=
  ⟨cantor_clo3 a, fun _ _ _ => trivial, cantor_A1a, cantor_not_A1b, cantor_A2 a, cantor_A3,
    cantor_A4, cantor_A5 a, cantor_not_MCadm⟩

/-! ### Drop A4: binary Cantor worlds, positivity = truth at the current world. -/
def cantorCW : GModel Wc Unit := { cantor with positive := fun p w => p () w }

theorem cantorCW_NE (x : Unit) (w : Wc) : NEH cantorCW a x w := by
  intro p hp he
  exact (cantor_no_essence a p hp x w he).elim

theorem cantorCW_G (x : Unit) (w : Wc) : GH cantorCW x w := by
  intro p _ hp; cases x; exact hp

theorem henkin_drop_A4 :
    Clo3 cantorCW a ∧ Symm cantorCW ∧ A1a cantorCW ∧ A1b cantorCW ∧ A2 cantorCW a ∧
    A3 cantorCW ∧ ¬ A4 cantorCW ∧ A5 cantorCW a ∧ ¬ MCadm cantorCW := by
  obtain ⟨hn, _, _, _, _, _, hl⟩ := cantor_clo_partial a
  refine ⟨⟨hn, hl, ⟨0, fun v v' _ => iff_of_true (cantorCW_NE a () v) (cantorCW_NE a () v')⟩,
      ⟨0, fun v v' _ => iff_of_true (cantorCW_G () v) (cantorCW_G () v')⟩⟩,
    fun _ _ _ => trivial, fun _ _ _ hn hp => hn hp, fun _ _ _ h => h,
    fun _ _ w _ _ hp h => h w trivial () (fun _ => trivial) hp,
    fun w => cantorCW_G () w, ?_, fun w => cantorCW_NE a () w, ?_⟩
  · intro h
    have hadm : cantorCW.adm (fun _ v => v 0 = true) :=
      ⟨1, fun v v' hvv => by show v 0 = true ↔ v' 0 = true; rw [hvv 0 Nat.zero_lt_one]⟩
    have := h _ (fun _ => true) hadm rfl (fun _ => false) trivial
    exact Bool.false_ne_true this
  · intro h
    have := h (fun v => v 0 = true)
      ⟨1, fun v v' hvv => by show v 0 = true ↔ v' 0 = true; rw [hvv 0 Nat.zero_lt_one]⟩
      (fun _ => true) rfl (fun _ => false) trivial
    exact Bool.false_ne_true this

/-! ### Drop A3: ternary Cantor worlds, positivity = recursive ternary majority. -/
abbrev W3 := Nat → Fin 3

def Based3 (n : Nat) (s : W3 → Prop) : Prop :=
  ∀ v v', (∀ k, k < n → v k = v' k) → (s v ↔ s v')

def upd (v : W3) (d : Nat) (i : Fin 3) : W3 := fun j => if j = d then i else v j

def maj3 (P Q R : Prop) : Prop := (P ∧ Q) ∨ (P ∧ R) ∨ (Q ∧ R)

/-- Majority value of the depth-`k` ternary subtree below the depth-`d` node of `v`. -/
def rm : Nat → Nat → (W3 → Prop) → W3 → Prop
  | 0, _, s, v => s v
  | k + 1, d, s, v =>
    maj3 (rm k (d + 1) s (upd v d 0)) (rm k (d + 1) s (upd v d 1)) (rm k (d + 1) s (upd v d 2))

theorem upd_agree (v : W3) (d : Nat) (i : Fin 3) : ∀ k, k < d → upd v d i k = v k := by
  intro k hk; simp [upd, Nat.ne_of_lt hk]

theorem based_mono {n m : Nat} {s : W3 → Prop} (h : Based3 n s) (hnm : n ≤ m) : Based3 m s :=
  fun v v' hv => h v v' fun k hk => hv k (Nat.lt_of_lt_of_le hk hnm)

theorem maj3_same (P : Prop) : maj3 P P P ↔ P := by
  unfold maj3
  exact ⟨fun h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact h,
    fun h => Or.inl ⟨h, h⟩⟩

theorem maj3_congr {P P' Q Q' R R' : Prop} (h1 : P ↔ P') (h2 : Q ↔ Q') (h3 : R ↔ R') :
    maj3 P Q R ↔ maj3 P' Q' R' := by
  unfold maj3; rw [h1, h2, h3]

theorem rm_based (s : W3 → Prop) : ∀ j d v, Based3 d s → (rm j d s v ↔ s v) := by
  intro j
  induction j with
  | zero => intro d v _; exact Iff.rfl
  | succ j ih =>
    intro d v hb
    have hb' : Based3 (d + 1) s := based_mono hb (Nat.le_succ d)
    have hc : ∀ i, rm j (d + 1) s (upd v d i) ↔ s v := fun i =>
      (ih (d + 1) _ hb').trans (hb _ _ (upd_agree v d i))
    show maj3 _ _ _ ↔ _
    rw [maj3_congr (hc 0) (hc 1) (hc 2)]
    exact maj3_same _

theorem rm_stable (s : W3 → Prop) (j : Nat) :
    ∀ k d v, Based3 (d + k) s → (rm (k + j) d s v ↔ rm k d s v) := by
  intro k
  induction k with
  | zero =>
    intro d v hb
    rw [Nat.zero_add]
    exact rm_based s j d v hb
  | succ k ih =>
    intro d v hb
    have he : k + 1 + j = (k + j) + 1 := by omega
    have hb' : Based3 (d + 1 + k) s := by
      have : d + 1 + k = d + (k + 1) := by omega
      rw [this]; exact hb
    rw [he]
    exact maj3_congr (ih _ _ hb') (ih _ _ hb') (ih _ _ hb')

theorem rm_neg (s : W3 → Prop) : ∀ k d v, rm k d (fun u => ¬ s u) v ↔ ¬ rm k d s v := by
  intro k
  induction k with
  | zero => intro d v; exact Iff.rfl
  | succ k ih =>
    intro d v
    show maj3 _ _ _ ↔ ¬ maj3 _ _ _
    rw [maj3_congr (ih _ _) (ih _ _) (ih _ _)]
    unfold maj3
    generalize rm k (d + 1) s (upd v d 0) = A
    generalize rm k (d + 1) s (upd v d 1) = B
    generalize rm k (d + 1) s (upd v d 2) = C
    by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp [hA, hB, hC]

theorem rm_mono {s q : W3 → Prop} (h : ∀ u, s u → q u) :
    ∀ k d v, rm k d s v → rm k d q v := by
  intro k
  induction k with
  | zero => intro d v hs; exact h v hs
  | succ k ih =>
    intro d v hs
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨ih _ _ h1, ih _ _ h2⟩
    · exact Or.inr (Or.inl ⟨ih _ _ h1, ih _ _ h2⟩)
    · exact Or.inr (Or.inr ⟨ih _ _ h1, ih _ _ h2⟩)

theorem rm_false {s : W3 → Prop} (h : ∀ u, ¬ s u) : ∀ k d v, ¬ rm k d s v := by
  intro k
  induction k with
  | zero => intro d v hs; exact h v hs
  | succ k ih =>
    intro d v hs
    rcases hs with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact ih _ _ h1

def z0 : W3 := fun _ => 0

def pos3 (s : W3 → Prop) : Prop := ∃ n, Based3 n s ∧ rm n 0 s z0

theorem pos3_iff {s : W3 → Prop} {m : Nat} (hm : Based3 m s) : pos3 s ↔ rm m 0 s z0 := by
  constructor
  · intro ⟨n, hn, hr⟩
    have e1 := rm_stable s m n 0 z0 (by rw [Nat.zero_add]; exact hn)
    have e2 := rm_stable s n m 0 z0 (by rw [Nat.zero_add]; exact hm)
    rw [Nat.add_comm] at e2
    exact e2.1 (e1.2 hr)
  · intro h; exact ⟨m, hm, h⟩

def tern : GModel W3 Unit where
  rel _ _ := True
  actual _ _ := True
  adm p := ∃ n, Based3 n (p ())
  admP s := ∃ n, Based3 n s
  positive p _ := pos3 (p ())

theorem fin3_succ_ne (x : Fin 3) : x + 1 ≠ x := by
  rcases ScottTable.fin3_cases x with rfl | rfl | rfl <;> decide

theorem tern_no_essence (p : Unit → W3 → Prop) (hp : tern.adm p) (x : Unit) (t : W3) :
    ¬ EssH tern a p x t := by
  intro ⟨hpt, hq⟩
  obtain ⟨n, hn⟩ := hp
  cases x
  have hflip : p () (upd t n (t n + 1)) :=
    (hn t _ fun k hk => (upd_agree t n _ k hk).symm).1 hpt
  have hadm : tern.adm (fun _ v => v n = t n) := by
    refine ⟨n + 1, ?_⟩
    intro v v' hvv
    show v n = t n ↔ v' n = t n
    rw [hvv n (Nat.lt_succ_self n)]
  have := hq (fun _ v => v n = t n) hadm rfl _ trivial () (fun _ => trivial) hflip
  simp only [upd] at this
  exact fin3_succ_ne _ this

theorem tern_NE (x : Unit) (w : W3) : NEH tern a x w := by
  intro p hp he
  exact (tern_no_essence a p hp x w he).elim

theorem tern_noG (x : Unit) (w : W3) : ¬ GH tern x w := by
  intro h
  cases x
  have hb : Based3 1 (fun v => v 0 ≠ w 0) := by
    intro v v' hvv
    show v 0 ≠ w 0 ↔ v' 0 ≠ w 0
    rw [hvv 0 Nat.zero_lt_one]
  have hpos : tern.positive (fun _ v => v 0 ≠ w 0) w := by
    refine ⟨1, hb, ?_⟩
    show maj3 (upd z0 0 0 0 ≠ w 0) (upd z0 0 1 0 ≠ w 0) (upd z0 0 2 0 ≠ w 0)
    simp only [upd]
    unfold maj3
    rcases ScottTable.fin3_cases (w 0) with h0 | h0 | h0 <;> rw [h0] <;> decide
  exact h _ ⟨1, hb⟩ hpos rfl

theorem henkin_drop_A3 :
    Clo3 tern a ∧ Symm tern ∧ A1a tern ∧ A1b tern ∧ A2 tern a ∧ ¬ A3 tern ∧ A4 tern ∧
    A5 tern a ∧ ¬ MCadm tern := by
  have hnegb : ∀ n (s : W3 → Prop), Based3 n s → Based3 n (fun u => ¬ s u) :=
    fun n s hb v v' h => not_congr (hb v v' h)
  refine ⟨⟨?_, fun s hs => hs, ⟨0, fun v v' _ => iff_of_true (tern_NE a () v) (tern_NE a () v')⟩,
      ⟨0, fun v v' _ => iff_of_false (tern_noG () v) (tern_noG () v')⟩⟩,
    fun _ _ _ => trivial, ?_, ?_, ?_, ?_, fun _ _ _ h _ _ => h, ?_, ?_⟩
  · intro p ⟨n, hn⟩; exact ⟨n, hnegb n _ hn⟩
  · intro p w ⟨n, hn⟩ hneg hpos
    have h1 := (pos3_iff (hnegb n _ hn)).1 hneg
    have h2 := (pos3_iff hn).1 hpos
    exact (rm_neg (p ()) n 0 z0).1 h1 h2
  · intro p w ⟨n, hn⟩ hnot
    have : ¬ rm n 0 (p ()) z0 := fun h => hnot ⟨n, hn, h⟩
    exact ⟨n, hnegb n _ hn, (rm_neg (p ()) n 0 z0).2 this⟩
  · intro p q w ⟨n, hn⟩ ⟨m, hm⟩ hpos hinc
    have hN : Based3 (n + m) (p ()) := based_mono hn (Nat.le_add_right n m)
    have hNq : Based3 (n + m) (q ()) := based_mono hm (Nat.le_add_left m n)
    have hr := (pos3_iff hN).1 hpos
    exact ⟨n + m, hNq, rm_mono (fun u hu => hinc u trivial () (fun _ => trivial) hu) _ _ _ hr⟩
  · intro h
    obtain ⟨n, _, hr⟩ := h z0
    exact rm_false (fun u => tern_noG () u) n 0 z0 hr
  · intro w
    exact ⟨0, fun v v' _ => iff_of_true (tern_NE a () v) (tern_NE a () v'), tern_NE a () z0⟩
  · intro h
    have := h (fun v => v 0 = 0)
      ⟨1, fun v v' hvv => by show v 0 = 0 ↔ v' 0 = 0; rw [hvv 0 Nat.zero_lt_one]⟩
      z0 rfl (fun _ => 1) trivial
    exact absurd this (by decide)

#print axioms henkin_drop_A1a
#print axioms henkin_drop_A2
#print axioms henkin_drop_A5
#print axioms henkin_drop_A1b
#print axioms henkin_drop_A4
#print axioms henkin_drop_A3
end Programme.«20261021-1639-ontological».Theorist.HenkinMinimal
