import Programme.«20261021-1639-ontological».Atlas.PrincipalAxis
/- D11, last cell: current-world inclusion, no A4, non-principal *ultra*filter, ¬MC.
A free ultrafilter on ℕ needs the ultrafilter lemma; the library has no Mathlib, so we prove it
here from `Classical.choice` by a Bourbaki–Witt tower on the powerset lattice (Zorn-free, but
not choice-free: the axioms are [propext, Classical.choice, Quot.sound]). -/
-- Rebased from th P180; proof reuse, not independent verification.
namespace Programme.«20261021-1639-ontological».Atlas.FreeUltra
open Programme.«20261021-1639-ontological».Countermodels.Tests Programme.«20261021-1639-ontological».Countermodels.Scott Programme.«20261021-1639-ontological».Atlas.Scott
open Programme.«20261021-1639-ontological».Atlas.ScottTable Programme.«20261021-1639-ontological».Atlas.FilterAxis Programme.«20261021-1639-ontological».Atlas.PrincipalAxis

/-- Families of sets of naturals. -/
abbrev Fam := (Nat → Prop) → Prop

def Sub (F G : Fam) : Prop := ∀ A, F A → G A
def IsChain (S : Fam → Prop) : Prop := ∀ F G, S F → S G → Sub F G ∨ Sub G F
def Sup (S : Fam → Prop) : Fam := fun A => ∃ F, S F ∧ F A

section Tower
variable (F0 : Fam) (g : Fam → Fam)

inductive Tower : Fam → Prop
  | base : Tower F0
  | succ {F} : Tower F → Tower (g F)
  | sup (S : Fam → Prop) : (∀ F, S F → Tower F) → IsChain S → (∃ F, S F) → Tower (Sup S)

variable {F0 g} (hg : ∀ F, Sub F (g F))
include hg

theorem base_le {x} (hx : Tower F0 g x) : Sub F0 x := by
  induction hx with
  | base => exact fun _ h => h
  | succ _ ih => exact fun A h => hg _ A (ih A h)
  | sup S _ _ hne ih =>
    obtain ⟨F, hF⟩ := hne
    exact fun A h => ⟨F, hF, ih F hF A h⟩

/-- `c` is extreme: every tower element strictly below `c` is mapped by `g` into `c`. -/
def Extreme (c : Fam) : Prop :=
  ∀ x, Tower F0 g x → Sub x c → ¬ Sub c x → Sub (g x) c

theorem lemma1 {c} (hcT : Tower F0 g c) (hc : Extreme (F0 := F0) (g := g) c) {x}
    (hx : Tower F0 g x) : Sub x c ∨ Sub (g c) x := by
  induction hx with
  | base => exact Or.inl (base_le hg hcT)
  | @succ x hxT ih =>
    rcases ih with h | h
    · by_cases hcx : Sub c x
      · exact Or.inr fun A hA => by
          -- x = c extensionally, so g c ⊆ g x via monotonicity on equal arguments
          have : x = c := funext fun B => propext ⟨h B, hcx B⟩
          subst this; exact hA
      · exact Or.inl (hc x hxT h hcx)
    · exact Or.inr fun A hA => hg x A (h A hA)
  | sup S _ _ _ ih =>
    by_cases hall : ∀ F, S F → Sub F c
    · exact Or.inl fun A ⟨F, hF, hA⟩ => hall F hF A hA
    · have : ∃ F, S F ∧ ¬ Sub F c := Classical.byContradiction fun hn =>
        hall fun F hF => Classical.byContradiction fun h => hn ⟨F, hF, h⟩
      obtain ⟨F, hF, hnF⟩ := this
      rcases ih F hF with h | h
      · exact absurd h hnF
      · exact Or.inr fun A hA => ⟨F, hF, h A hA⟩

theorem all_extreme {c} (hc : Tower F0 g c) : Extreme (F0 := F0) (g := g) c := by
  induction hc with
  | base => exact fun x hx _ hn => absurd (base_le hg hx) hn
  | @succ c hcT ih =>
    intro x hx hxc hn
    rcases lemma1 hg hcT ih hx with h | h
    · by_cases hcx : Sub c x
      · have : x = c := funext fun B => propext ⟨h B, hcx B⟩
        subst this; exact fun A hA => hA
      · exact fun A hA => hg c A (ih x hx h hcx A hA)
    · exact absurd h hn
  | sup S hST _ _ ih =>
    intro x hx hxc hn
    have : ∃ s, S s ∧ ¬ Sub s x := Classical.byContradiction fun hno =>
      hn fun A ⟨s, hs, hA⟩ => Classical.byContradiction fun h =>
        hno ⟨s, hs, fun hsx => h (hsx A hA)⟩
    obtain ⟨s, hs, hsx⟩ := this
    rcases lemma1 hg (hST s hs) (ih s hs) hx with h | h
    · exact fun A hA => ⟨s, hs, ih s hs x hx h hsx A hA⟩
    · exact absurd (fun A hA => h A (hg s A hA)) hsx

theorem tower_chain : IsChain (Tower F0 g) := by
  intro x y hx hy
  rcases lemma1 hg hy (all_extreme hg hy) hx with h | h
  · exact Or.inl h
  · exact Or.inr fun A hA => h A (hg y A hA)

/-- The top of the tower is a fixed point of `g`. -/
theorem top_fixed : Tower F0 g (Sup (Tower F0 g)) ∧ Sub (g (Sup (Tower F0 g))) (Sup (Tower F0 g)) := by
  have hT : Tower F0 g (Sup (Tower F0 g)) :=
    Tower.sup _ (fun _ h => h) (tower_chain hg) ⟨F0, Tower.base⟩
  exact ⟨hT, fun A hA => ⟨_, Tower.succ hT, hA⟩⟩
end Tower

/-- Proper filter on ℕ. -/
def Good (F : Fam) : Prop :=
  F (fun _ => True) ∧ ¬ F (fun _ => False) ∧
  (∀ A B, F A → (∀ n, A n → B n) → F B) ∧ (∀ A B, F A → F B → F (fun n => A n ∧ B n))

/-- Fréchet filter. -/
def frechet : Fam := fun A => cof A

theorem frechet_good : Good frechet :=
  ⟨⟨0, fun _ _ => trivial⟩, fun ⟨N, h⟩ => h N (Nat.le_refl _),
   fun _ _ ⟨N, h⟩ hAB => ⟨N, fun n hn => hAB n (h n hn)⟩,
   fun _ _ ⟨N, h⟩ ⟨M, k⟩ => ⟨N + M, fun n hn => ⟨h n (by omega), k n (by omega)⟩⟩⟩

open Classical in
/-- Strict good extension if one exists, else stay. -/
noncomputable def step (F : Fam) : Fam :=
  if h : ∃ G, Good G ∧ Sub F G ∧ ∃ A, G A ∧ ¬ F A then Classical.choose h else F

theorem step_infl (F : Fam) : Sub F (step F) := by
  unfold step; split
  · next h => exact (Classical.choose_spec h).2.1
  · exact fun _ h => h

theorem tower_good {x} (hx : Tower frechet step x) : Good x := by
  induction hx with
  | base => exact frechet_good
  | @succ F _ ih =>
    unfold step; split
    · next h => exact (Classical.choose_spec h).1
    · exact ih
  | sup S _ hch hne ih =>
    obtain ⟨F0, hF0⟩ := hne
    refine ⟨⟨F0, hF0, (ih F0 hF0).1⟩, fun ⟨F, hF, h⟩ => (ih F hF).2.1 h,
      fun A B ⟨F, hF, hA⟩ hAB => ⟨F, hF, (ih F hF).2.2.1 A B hA hAB⟩, ?_⟩
    intro A B ⟨F, hF, hA⟩ ⟨G, hG, hB⟩
    rcases hch F G hF hG with h | h
    · exact ⟨G, hG, (ih G hG).2.2.2 A B (h A hA) hB⟩
    · exact ⟨F, hF, (ih F hF).2.2.2 A B hA (h B hB)⟩

/-- The free ultrafilter. -/
def U : Fam := Sup (Tower frechet step)

theorem U_good : Good U := tower_good (top_fixed (F0 := frechet) step_infl).1

theorem U_frechet : Sub frechet U := base_le (F0 := frechet) step_infl (top_fixed (F0 := frechet) step_infl).1

theorem U_maximal : ¬ ∃ G, Good G ∧ Sub U G ∧ ∃ A, G A ∧ ¬ U A := by
  intro h
  have hfix := (top_fixed (F0 := frechet) step_infl).2
  have hs : step U = Classical.choose h := by unfold step; rw [dif_pos h]
  obtain ⟨_, _, A, hGA, hUA⟩ := Classical.choose_spec h
  exact hUA (hfix A (by show step U A; rw [hs]; exact hGA))

theorem U_ultra (A : Nat → Prop) : U A ∨ U (fun n => ¬ A n) := by
  refine Classical.byContradiction fun hn => ?_
  have hA : ¬ U A := fun h => hn (Or.inl h)
  have hAc : ¬ U (fun n => ¬ A n) := fun h => hn (Or.inr h)
  have ⟨hT, h0, hup, hint⟩ := U_good
  let G : Fam := fun B => ∃ C, U C ∧ ∀ n, C n → A n → B n
  have gT : G (fun _ => True) := ⟨_, hT, fun _ _ _ => trivial⟩
  have g0 : ¬ G (fun _ => False) := fun ⟨C, hC, h⟩ =>
    hAc (hup C _ hC fun n hc ha => h n hc ha)
  have gup : ∀ B B', G B → (∀ n, B n → B' n) → G B' :=
    fun _ _ ⟨C, hC, h⟩ hBB => ⟨C, hC, fun n hc ha => hBB n (h n hc ha)⟩
  have gint : ∀ B B', G B → G B' → G (fun n => B n ∧ B' n) :=
    fun _ _ ⟨C, hC, h⟩ ⟨C', hC', h'⟩ =>
      ⟨_, hint C C' hC hC', fun n hcc ha => ⟨h n hcc.1 ha, h' n hcc.2 ha⟩⟩
  have gA : G A := ⟨_, hT, fun _ _ h => h⟩
  exact U_maximal ⟨G, ⟨gT, g0, gup, gint⟩, fun B hB => ⟨B, hB, fun _ h _ => h⟩, A, gA, hA⟩

/-- No set generates `U` (non-principality in the F1 sense). -/
theorem U_free : ¬ ∃ B, U B ∧ ∀ A, U A ↔ ∀ n, B n → A n := by
  rintro ⟨B, hB, hgen⟩
  refine U_good.2.1 (U_good.2.2.1 B _ hB fun n hn => ?_)
  exact (hgen (fun m => m ≠ n)).1 (U_frechet _ (cof_ne n)) n hn rfl

/-! The cell model: universal two-world frame, entities ℕ all actual, positivity = U on the
current slice. -/
def ultraLocal : Model Bool Nat := univN Bool fun p w => U (fun n => p n w)

def Ultra {W E} (m : Model W E) : Prop :=
  ∀ p w, m.positive p w ∨ m.positive (fun x v => ¬ p x v) w

theorem ultraLocal_props (a : Bool) :
    S5 ultraLocal ∧ FilterCW ultraLocal a ∧ Ultra ultraLocal ∧ A1a ultraLocal ∧ A1b ultraLocal ∧
    A2 ultraLocal a ∧ ¬ F1cw ultraLocal a ∧ ¬ F1box ultraLocal a ∧ ¬ A4 ultraLocal ∧
    ¬ MC ultraLocal := by
  have ⟨hT, h0, hup, hint⟩ := U_good
  refine ⟨⟨⟨fun _ => trivial, fun _ _ _ _ _ => trivial⟩, fun _ _ _ => trivial⟩,
    ⟨fun _ => hT, fun _ => h0, fun p q w hp hpq => hup _ _ hp fun n h => hpq n (fun _ => trivial) h,
      fun p q w hp hq => hint _ _ hp hq⟩,
    fun p w => U_ultra _, ?_, ?_, ?_, ?_, ?_, ?_, not_MC_univN _⟩
  · intro p w hn hp
    exact h0 (hup _ _ (hint _ _ hp hn) fun n ⟨h, h'⟩ => h' h)
  · intro p w hn
    exact (U_ultra (fun n => p n w)).resolve_left hn
  · intro p q w hp hpq
    exact hup _ _ hp fun n h => hpq w trivial n (fun _ => trivial) h
  · intro h
    obtain ⟨g, hg⟩ := h false
    exact U_free ⟨fun n => g n false, (hg g).2 fun _ _ h => h,
      fun A => (hg (fun n _ => A n)).trans ⟨fun h n => h n (fun _ => trivial),
        fun h n _ => h n⟩⟩
  · intro h
    obtain ⟨g, hg⟩ := h false
    have hG : U (fun n => g n false) := (hg g).2 fun _ _ _ _ h => h
    refine U_free ⟨fun n => g n false, hG, fun A => ⟨fun hA n hn => ?_, fun h => hup _ _ hG h⟩⟩
    exact (hg (fun m _ => A m)).1 hA false trivial n (fun _ => trivial) hn
  · intro h
    have hp : U (fun _ => True) := hT
    have := h (fun _ w => w = false) false (hup _ _ hp fun _ _ => rfl) true trivial
    exact h0 (hup _ _ this fun _ e => Bool.noConfusion e)

/-- As sk (P149) notes for Scott-style systems: a free positivity filter refutes A3 (no God). -/
theorem ultraLocal_not_A3 : ¬ A3 ultraLocal := by
  intro h
  refine U_good.2.1 (U_good.2.2.1 _ _ (h false) fun n hn => ?_)
  exact hn (fun m _ => m ≠ n) (U_frechet _ (cof_ne n)) rfl

#print axioms ultraLocal_not_A3
#print axioms U_ultra
#print axioms U_free
#print axioms ultraLocal_props
end Programme.«20261021-1639-ontological».Atlas.FreeUltra
