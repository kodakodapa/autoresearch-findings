import Programme.«20261022-0733-ontological».Run2.V3Row
import Programme.«20261022-0733-ontological».Run2.LGeneralFullInst
import Programme.«20261022-0733-ontological».Run2.Binary

-- Copied from th's Programme/Th/BinaryDeadEnd.lean (author th); namespace and imports changed.

/-! # Binary A1 at dead ends: no finite 3' separator, an infinite one with God nowhere

* `gen_at_deadEnd`: all properties admitted, finitely many entities, `Ax4`, `P ⊤` (or `Ax2a`),
  binary A1: at a world `w` with `R w v → v = w`, every admitted collection of positive
  properties has positive conjunction.  (Choose for each actual counterexample `z` a member
  `ψ_z` of `Φ` failing at `z`; the binary conjunction of the finitely many `ψ_z` is positive and
  `PInc`-below the conjunction.)
* `v3_finite_gen`: full carriers, finite `D`, variant 3' (`Ax2a`, `Ax3v3`, `Ax4`) and binary A1
  give `Ax1Gen`.  So no finite full 3' model separates binary A1 from `Ax1Gen`/`Ax1GenTwo`
  (K41's separator refutes `Ax3v3`).  Variant 2 analogue: `Ax1Gen` holds at every reflexive
  dead end (`v2_finite_gen_deadEnd`), so a finite full separator must fail at a non-dead end.
* `uf1_gap`: one world, entities `ℕ`, full carriers, positivity a free ultrafilter `U`.  `LGenF`,
  `Closed`, binary A1, `Ax2a`, `Ax2b`, `Ax3`, `Ax3v3`, `Ax4`, `MC`; no God-like entity, and
  `Ax1Gen`, `Ax1GenTwo` fail.  The ultrafilter construction is copied from the library's
  `Programme.Atlas.FreeUltra` (prev-K43; that module is not importable from this package). -/

namespace Programme.«20261022-0733-ontological».Run2.BinaryDeadEnd

open Programme.«20261022-0733-ontological».Run2 Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.Binary
open Programme.«20261022-0733-ontological».Run2.LGeneralFull (LGenF)

section DeadEnd
variable {W D : Type} {M : Model W D}

/-- Binary conjunction of the chosen witnesses along a list. -/
def bigConj (f : D → D → W → Prop) : List D → D → W → Prop
  | [] => top
  | z :: l => conj (f z) (bigConj f l)

theorem bigConj_pos (hT : ∀ φ, M.AT φ) (hb : Ax1Bin M) {w} {f : D → D → W → Prop}
    (hf : ∀ z, M.P (f z) w) (htop : M.P top w) : ∀ l, M.P (bigConj f l) w
  | [] => htop
  | z :: l => hb _ _ (hT _) (hT _) w (hf z) (bigConj_pos hT hb hf htop l)

theorem bigConj_mem {f : D → D → W → Prop} {y v} :
    ∀ l, bigConj f l y v → ∀ z, z ∈ l → f z y v
  | [], _, _, hz => nomatch hz
  | _ :: l, ⟨h1, h2⟩, z, hz => by
    cases hz with
    | head => exact h1
    | tail _ hz => exact bigConj_mem l h2 z hz

theorem pTop (hT : ∀ φ, M.AT φ) (h2a : Ax2a M) (h4 : Ax4 M) (w : W) : M.P top w := by
  rcases (h2a top (hT _) w).1 with h | h
  · exact h
  · exact h4 _ _ (hT _) (hT _) w h fun _ _ _ _ _ => trivial

open Classical in
theorem gen_at_deadEnd (hT : ∀ φ, M.AT φ) (l : List D) (hl : ∀ x, x ∈ l)
    (h4 : Ax4 M) (hb : Ax1Bin M) {w : W} (htop : M.P top w) (hw : ∀ v, M.R w v → v = w)
    (Φ : (D → W → Prop) → W → Prop) (φ : D → W → Prop)
    (hpos : PosProps M Φ w) (hc : ConjOf M φ Φ w) : M.P φ w := by
  let f : D → D → W → Prop := fun z =>
    if h : ∃ ψ, Φ ψ w ∧ ¬ ψ z w then h.choose else top
  have hf : ∀ z, M.P (f z) w := fun z => by
    simp only [f]; split
    · next h => exact hpos _ (hT _) h.choose_spec.1
    · exact htop
  refine h4 _ _ (hT _) (hT _) w (bigConj_pos hT hb hf htop l) ?_
  intro v hv y hy hχ
  have e := hw v hv; subst e
  refine Classical.byContradiction fun hn => ?_
  have hex : ∃ ψ, Φ ψ v ∧ ¬ ψ y v := by
    refine Classical.byContradiction fun hno => hn ((hc v hv y hy).2 fun ψ _ hψ => ?_)
    exact Classical.byContradiction fun h => hno ⟨ψ, hψ, h⟩
  have := bigConj_mem l hχ y (hl y)
  simp only [f, dif_pos hex] at this
  exact hex.choose_spec.2 this

end DeadEnd

section Rows
variable {W D : Type}

/-- **Variant 3', finite entities, full carriers: binary A1 gives `Ax1Gen`.** -/
theorem v3_finite_gen {R : W → W → Prop} {act : D → W → Prop} {P}
    (l : List D) (hl : ∀ x, x ∈ l)
    (h2a : Ax2a (KRow.full R act P)) (h3 : Ax3v3 (KRow.full R act P))
    (h4 : Ax4 (KRow.full R act P)) (hb : Ax1Bin (KRow.full R act P)) :
    Ax1Gen (KRow.full R act P) := by
  have one := V3Row.nec h2a h3 h4
  intro Φ φ _ _ w hpos hc
  exact gen_at_deadEnd (fun _ => trivial) l hl h4 hb (pTop (fun _ => trivial) h2a h4 w)
    (fun v _ => one.1 v w) Φ φ hpos hc

/-- With finitely many entities, every full 3' model with binary A1 also has `Ax1GenTwo`. -/
theorem v3_finite_two {R : W → W → Prop} {act : D → W → Prop} {P}
    (l : List D) (hl : ∀ x, x ∈ l)
    (h2a : Ax2a (KRow.full R act P)) (h3 : Ax3v3 (KRow.full R act P))
    (h4 : Ax4 (KRow.full R act P)) (hb : Ax1Bin (KRow.full R act P)) :
    Ax1GenTwo (KRow.full R act P) :=
  fun Φ φ hH hT w _ hpos hc => v3_finite_gen l hl h2a h3 h4 hb Φ φ hH hT w hpos hc

/-- **Variant 2, finite entities, full carriers:** at every dead end, the general conjunction
axiom holds (for any `Φ`), given binary A1, `Ax2a` and `Ax4`. -/
theorem v2_finite_gen_deadEnd {R : W → W → Prop} {act : D → W → Prop} {P}
    (l : List D) (hl : ∀ x, x ∈ l)
    (h2a : Ax2a (KRow.full R act P)) (h4 : Ax4 (KRow.full R act P))
    (hb : Ax1Bin (KRow.full R act P)) {w : W} (hw : ∀ v, R w v → v = w)
    (Φ : (D → W → Prop) → W → Prop) (φ : D → W → Prop)
    (hpos : PosProps (KRow.full R act P) Φ w) (hc : ConjOf (KRow.full R act P) φ Φ w) :
    P φ w :=
  gen_at_deadEnd (M := KRow.full R act P) (fun _ => trivial) l hl h4 hb
    (pTop (fun _ => trivial) h2a h4 w) hw Φ φ hpos hc

end Rows

/-! ## The free ultrafilter (copied verbatim from `Programme.Atlas.FreeUltra`, prev-K43) -/

def cof (s : Nat → Prop) : Prop := ∃ N, ∀ n, N ≤ n → s n

theorem cof_ne (k : Nat) : cof (fun n => n ≠ k) := ⟨k + 1, fun n hn h => by omega⟩

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

/-! ## The one-world free-ultrafilter model -/

def uf1 : Model Unit Nat := KRow.full (fun _ _ => True) (fun _ _ => True)
  (fun φ _ => U (fun n => φ n ()))

theorem lgenF_uf1 : LGenF uf1 :=
  LGeneralFullInst.lgenF_full uf1 (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)

theorem closed_uf1 : Closed uf1 where
  top := trivial
  bot := trivial
  neg := fun _ _ => trivial
  conj := fun _ _ _ _ => trivial
  lift := fun _ _ => trivial
  negS := fun _ _ => trivial
  god := trivial
  exG := trivial
  pos := trivial
  single := fun _ _ => trivial
  union := fun _ _ _ _ => trivial
  guard := fun _ _ _ _ => trivial
  atMost := fun _ _ _ _ => trivial

theorem not_both {A : Nat → Prop} (h1 : U A) (h2 : U (fun n => ¬ A n)) : False :=
  U_good.2.1 (U_good.2.2.1 _ _ (U_good.2.2.2 _ _ h1 h2) fun _ h => h.2 h.1)

theorem bin_uf1 : Ax1Bin uf1 := fun _ _ _ _ _ h1 h2 => U_good.2.2.2 _ _ h1 h2

theorem ax2a_uf1 : Ax2a uf1 := fun φ _ _ => ⟨U_ultra _, fun ⟨a, b⟩ => not_both a b⟩

theorem ax2b_uf1 : Ax2b uf1 := fun _ _ _ h _ _ => h

theorem ax4_uf1 : Ax4 uf1 := fun _ _ _ _ _ hφ hinc =>
  U_good.2.2.1 _ _ hφ fun n hn => hinc () trivial n trivial hn

theorem ax3_uf1 : Ax3 uf1 := fun _ =>
  U_good.2.2.1 _ _ U_good.1 fun x _ _ _ hess _ _ => ⟨x, trivial, hess.1⟩

theorem ax3v3_uf1 : Ax3v3 uf1 := fun _ => by
  refine U_good.2.2.1 _ _ U_good.1 fun x _ _ _ hess v hv => ?_
  have hne := (hess (fun _ _ => True) trivial trivial v hv).1
  refine Classical.byContradiction fun hn => hne (funext fun d => funext fun u => ?_)
  exact propext ⟨fun hd => hn ⟨d, trivial, by cases u; cases v; exact hd⟩, False.elim⟩

theorem mc_uf1 : MC uf1 := fun _ _ _ h v _ => by cases v; exact h

/-- Cofinite family `{λn. n ≠ k}`. -/
def coΦ : (Nat → Unit → Prop) → Unit → Prop := fun ψ _ => ∃ k, ψ = fun n _ => n ≠ k

theorem not_two_uf1 : ¬ Ax1GenTwo uf1 := fun h => by
  have := h coΦ bot trivial trivial ()
    ⟨fun n _ => n ≠ 0, fun n _ => n ≠ 1, trivial, trivial, ⟨0, rfl⟩, ⟨1, rfl⟩, fun e => by
      have := congrFun (congrFun e 0) (); simp at this⟩
    (fun ψ _ ⟨k, hk⟩ => by subst hk; exact U_frechet _ (cof_ne k))
    (fun v _ z _ => ⟨False.elim, fun hz => hz _ trivial ⟨z, rfl⟩ rfl⟩)
  exact U_good.2.1 this

theorem not_gen_uf1 : ¬ Ax1Gen uf1 := fun h =>
  not_two_uf1 fun Φ φ hH hT w _ hp hc => h Φ φ hH hT w hp hc

theorem no_god_uf1 : ¬ ExG uf1 () := fun ⟨y, _, hy⟩ =>
  hy (fun n _ => n ≠ y) trivial (U_frechet _ (cof_ne y)) rfl

/-- **Infinite separator, God at no world.** -/
theorem uf1_gap :
    LGenF uf1 ∧ Closed uf1 ∧ Ax1Bin uf1 ∧ Ax2a uf1 ∧ Ax2b uf1 ∧ Ax3 uf1 ∧ Ax3v3 uf1 ∧
    Ax4 uf1 ∧ MC uf1 ∧ (∀ w, ¬ ExG uf1 w) ∧ ¬ Ax1Gen uf1 ∧ ¬ Ax1GenTwo uf1 :=
  ⟨lgenF_uf1, closed_uf1, bin_uf1, ax2a_uf1, ax2b_uf1, ax3_uf1, ax3v3_uf1, ax4_uf1, mc_uf1,
   fun w => by cases w; exact no_god_uf1, not_gen_uf1, not_two_uf1⟩

end Programme.«20261022-0733-ontological».Run2.BinaryDeadEnd

#print axioms Programme.«20261022-0733-ontological».Run2.BinaryDeadEnd.gen_at_deadEnd
#print axioms Programme.«20261022-0733-ontological».Run2.BinaryDeadEnd.v3_finite_gen
#print axioms Programme.«20261022-0733-ontological».Run2.BinaryDeadEnd.v3_finite_two
#print axioms Programme.«20261022-0733-ontological».Run2.BinaryDeadEnd.v2_finite_gen_deadEnd
#print axioms Programme.«20261022-0733-ontological».Run2.BinaryDeadEnd.uf1_gap
