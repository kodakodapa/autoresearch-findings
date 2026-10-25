/-! # Thread F: the omitted-type lemma for `L_R` (th, P57)

Abstract Henkin reading of `OpenQuestions.Ax1GenRigidVariant2`: worlds `W`, entities `D`,
accessibility `R`, actuality `act` (arbitrary, may vary between worlds), admitted properties `A`
(containing `⊥`, closed under negation), admitted rigid families `F` (sets of properties
simpliciter), positivity `P`.  The module's axioms are read with property quantifiers over `A`
and `Ax1GenR` with `Φ` over `F`.  `G` is God-likeness over admitted properties.

* `realised`: every `Φ ∈ F` whose members are positive at `w` is jointly exemplified by an
  actual entity at some successor of `w` (no assumption on `P G`).
* `no_god_succ`: if `¬ P G w` (and `G ∈ A`), no successor of `w` has a God-like entity.
* `pos_type_omitted`: if `¬ P G w`, no `Φ ∈ F` has the same admitted members as `P_w`.
* `pos_type_omitted_of_pred`: in particular not `{ψ ∈ A | ∀ u, p u → P ψ u}` for a nonempty
  `p` on which positivity agrees with `P_w`.

Self-contained: no imports. -/

namespace Programme.«20261022-1314-ontological».F.RigidLemma

structure HV2 where
  W : Type
  D : Type
  R : W → W → Prop
  act : D → W → Prop
  A : (D → W → Prop) → Prop
  F : ((D → W → Prop) → Prop) → Prop
  P : (D → W → Prop) → W → Prop
  bot_A : A (fun _ _ => False)
  neg_A : ∀ φ, A φ → A (fun x w => ¬ φ x w)
  /-- `Ax2a` (exclusive disjunction). -/
  ax2a : ∀ φ, A φ → ∀ w, (P φ w ∨ P (fun x w => ¬ φ x w) w) ∧
    ¬ (P φ w ∧ P (fun x w => ¬ φ x w) w)
  /-- `Ax2b`. -/
  ax2b : ∀ φ, A φ → ∀ w, P φ w → ∀ v, R w v → P φ v
  /-- `Ax4` with the module's inclusion `⊃ᴺ`. -/
  ax4 : ∀ φ ψ, A φ → A ψ → ∀ w, P φ w →
    (∀ v, R w v → ∀ y, act y v → φ y v → ψ y v) → P ψ w
  /-- `Ax1GenR`: `PosPropsR Φ ∧ ConjR φ Φ → P φ`, `Φ` an admitted rigid family. -/
  ax1genR : ∀ Φ, F Φ → ∀ φ, A φ → ∀ w, (∀ ψ, Φ ψ → P ψ w) →
    (∀ v, R w v → ∀ z, act z v → (φ z v ↔ ∀ ψ, Φ ψ → ψ z v)) → P φ w

variable (M : HV2)

/-- God-like, over admitted properties. -/
def HV2.G (x : M.D) (w : M.W) : Prop := ∀ φ, M.A φ → M.P φ w → φ x w

/-- `P_succ` of the module. -/
theorem P_succ {w v : M.W} (hv : M.R w v) (ψ : M.D → M.W → Prop) (hA : M.A ψ) :
    M.P ψ v → M.P ψ w := fun hPv =>
  Classical.byContradiction fun hn =>
    (M.ax2a ψ hA v).2 ⟨hPv, M.ax2b _ (M.neg_A ψ hA) w
      (((M.ax2a ψ hA w).1).resolve_left hn) v hv⟩

/-- (ii) Every admitted rigid family of properties positive at `w` is realised by one actual
entity at a successor of `w`; otherwise `ConjR ⊥ Φ` gives `P ⊥`, `Ax4` gives `P ¬⊥`. -/
theorem realised (Φ : (M.D → M.W → Prop) → Prop) (hF : M.F Φ) (w : M.W)
    (hpos : ∀ ψ, Φ ψ → M.P ψ w) :
    ∃ v, M.R w v ∧ ∃ z, M.act z v ∧ ∀ ψ, Φ ψ → ψ z v := by
  refine Classical.byContradiction fun hno => ?_
  have hbot : M.P (fun _ _ => False) w :=
    M.ax1genR Φ hF _ M.bot_A w hpos fun v hv z hz =>
      ⟨False.elim, fun hall => hno ⟨v, hv, z, hz, hall⟩⟩
  have htop : M.P (fun x w => ¬ (fun (_ : M.D) (_ : M.W) => False) x w) w :=
    M.ax4 _ _ M.bot_A (M.neg_A _ M.bot_A) w hbot fun _ _ _ _ h => h.elim
  exact (M.ax2a _ M.bot_A w).2 ⟨hbot, htop⟩

/-- (i) If `G` is admitted and not positive at `w`, no successor of `w` has a God-like
entity (actual or not). -/
theorem no_god_succ (hG : M.A M.G) {w : M.W} (hn : ¬ M.P M.G w) :
    ∀ v, M.R w v → ∀ z, ¬ M.G z v := fun v hv _z hz =>
  have hneg : M.P (fun x w => ¬ M.G x w) w := ((M.ax2a _ hG w).1).resolve_left hn
  hz _ (M.neg_A _ hG) (M.ax2b _ (M.neg_A _ hG) w hneg v hv) hz

/-- (iii) `P_w` is an omitted type: if `¬ P G w`, no admitted rigid family has exactly the
admitted properties positive at `w` (its members positive at `w`, every admitted positive one
in it). Contrapositively, such a family gives `P G w`, as in `L_R`. -/
theorem pos_type_omitted (hG : M.A M.G) {w : M.W} (hn : ¬ M.P M.G w)
    (Φ : (M.D → M.W → Prop) → Prop) (hF : M.F Φ)
    (hsub : ∀ ψ, Φ ψ → M.P ψ w) (hsup : ∀ ψ, M.A ψ → M.P ψ w → Φ ψ) : False := by
  obtain ⟨v, hv, z, _, hall⟩ := realised M Φ hF w hsub
  exact no_god_succ M hG hn v hv z fun φ hA hPv => hall φ (hsup φ hA (P_succ M hv φ hA hPv))

/-- The same with the family `{ψ ∈ A | ∀ u, p u → P ψ u}` for a nonempty `p` on which
admitted positivity agrees with `P_w`. -/
theorem pos_type_omitted_of_pred (hG : M.A M.G) {w : M.W} (hn : ¬ M.P M.G w)
    (p : M.W → Prop) (u₀ : M.W) (hu₀ : p u₀)
    (hagree : ∀ u, p u → ∀ ψ, M.A ψ → (M.P ψ u ↔ M.P ψ w))
    (hF : M.F fun ψ => M.A ψ ∧ ∀ u, p u → M.P ψ u) : False :=
  pos_type_omitted M hG hn _ hF
    (fun ψ ⟨hA, h⟩ => (hagree u₀ hu₀ ψ hA).1 (h u₀ hu₀))
    (fun ψ hA hP => ⟨hA, fun u hu => (hagree u hu ψ hA).2 hP⟩)

/-- The hypotheses are satisfiable: one world, one entity, `P φ w := φ () w`, `F` empty. -/
def triv : HV2 where
  W := Unit
  D := Unit
  R _ _ := True
  act _ _ := True
  A _ := True
  F _ := False
  P φ w := φ () w
  bot_A := trivial
  neg_A _ _ := trivial
  ax2a _ _ _ := ⟨Classical.em _, fun ⟨h, hn⟩ => hn h⟩
  ax2b _ _ _ h _ _ := h
  ax4 _ _ _ _ w h hinc := hinc w trivial () trivial h
  ax1genR _ hF := hF.elim

end Programme.«20261022-1314-ontological».F.RigidLemma

#print axioms Programme.«20261022-1314-ontological».F.RigidLemma.realised
#print axioms Programme.«20261022-1314-ontological».F.RigidLemma.no_god_succ
#print axioms Programme.«20261022-1314-ontological».F.RigidLemma.pos_type_omitted
#print axioms Programme.«20261022-1314-ontological».F.RigidLemma.pos_type_omitted_of_pred
