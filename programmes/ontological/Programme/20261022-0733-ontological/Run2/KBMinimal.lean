import Programme.«20261022-0733-ontological».Run2.StandardKB

/-! # Minimality of `kb_collapse` (thread D)

`StandardKB.kb_collapse`: full property carrier (`FullT`), symmetric `R`, `Ax2a`, `Ax4` and
`Ax3` (or `Ax3v3`) give `∀ w v, R w v → v = w`.  Each hypothesis is needed:

* `FullT`: `FM.fm` (`StandardKB.separating_kb`, fragment-closed S5);
* symmetry: `StandardKB.s4model` (`s4_props`, reflexive transitive);
* `Ax4`, `Ax3`/`Ax3v3`, `Ax2a`: the three two-world full S5 models below (`noAx4`, `noAx3`,
  `noAx2a`).  `noAx4` is sk's control (c1) of P153: positivity is falsity at `false`, so
  the nominal essence `λz u. u = false` makes `E = ⊥` positive.

Side result (sk P153): `Ax2a` and `Ax4` force seriality on every frame (`serial`). -/
namespace Programme.«20261022-0733-ontological».Run2.KBMinimal

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.LGeneral Programme.«20261022-0733-ontological».Run2.StandardKB

variable {W D : Type} {M : Model W D}

/-- `Ax2a` and `Ax4` with `⊤`, `⊥` admitted: every world has a successor. -/
theorem serial (hT : M.AT top) (hB : M.AT bot) (h2a : Ax2a M) (h4 : Ax4 M) (w : W) :
    ∃ v, M.R w v := by
  have hp : M.P top w := by
    rcases (h2a top hT w).1 with h | h
    · exact h
    · exact absurd (neg_top ▸ h) (not_pBot hT hB h2a h4 w)
  obtain ⟨v, _, hv, _⟩ := somewhere hT hB h2a h4 hT hp
  exact ⟨v, hv⟩

/-- Two worlds, total accessibility, one always-actual entity, all carriers full. -/
def two (P : (Unit → Bool → Prop) → Bool → Prop) : Model Bool Unit where
  R := fun _ _ => True
  act := fun _ _ => True
  AS := fun _ => True
  AT := fun _ => True
  AH := fun _ => True
  P := P

theorem two_lgeneral (P) : LGeneral (two P) :=
  lgeneral_full (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)

theorem two_fullT (P) : FullT (two P) := fun _ => trivial

theorem two_not_id (P) : ¬ ∀ w v, (two P).R w v → v = w :=
  fun h => Bool.noConfusion (h false true trivial)

theorem two_not_mc (P) : ¬ MC (two P) :=
  fun h => Bool.noConfusion (h (fun w => w = false) trivial false rfl true trivial)

/-- The nominal essence `λz u. u = false`. -/
def nom : Unit → Bool → Prop := fun _ u => u = false

theorem not_E (P) : ¬ E (two P) () false := by
  intro hE
  have ess : Ess (two P) nom () false := by
    refine ⟨rfl, fun ψ _ hψ v _ y _ hv => ?_⟩
    cases y; exact (show v = false from hv) ▸ hψ
  obtain ⟨_, _, h⟩ := hE nom trivial ess true trivial
  exact Bool.noConfusion h

theorem not_E3 (P) : ¬ E3 (two P) () false := by
  intro hE
  have ess : Ess3 (two P) nom () false := by
    intro ψ _ hψ v _
    refine ⟨fun e => ?_, fun y _ hv => ?_⟩
    · have : nom () false := rfl
      rw [e] at this; exact this
    · cases y; exact (show v = false from hv) ▸ hψ
  obtain ⟨_, _, h⟩ := hE nom trivial ess true trivial
  exact Bool.noConfusion h

/-! ## `Ax4` needed: positivity is falsity at `false` -/

def noAx4 : Model Bool Unit := two fun φ _ => ¬ φ () false

theorem noAx4_props :
    Ax2a noAx4 ∧ Ax3 noAx4 ∧ Ax3v3 noAx4 ∧ ¬ Ax4 noAx4 := by
  refine ⟨?_, fun _ => not_E _, fun _ => not_E3 _, ?_⟩
  · intro φ _ _
    show (¬ φ () false ∨ ¬ ¬ φ () false) ∧ ¬ (¬ φ () false ∧ ¬ ¬ φ () false)
    exact ⟨(Classical.em (φ () false)).elim (fun h => Or.inr fun hn => hn h) Or.inl,
      fun ⟨a, b⟩ => b a⟩
  · intro h4
    -- `⊥` is positive and included in everything, so `⊤` would be positive
    have := h4 bot top trivial trivial false (fun h => h) (fun _ _ _ _ h => h.elim)
    exact this trivial

/-! ## `Ax3` needed: positivity is truth at `false` -/

def noAx3 : Model Bool Unit := two fun φ _ => φ () false

theorem noAx3_props :
    Ax2a noAx3 ∧ Ax4 noAx3 ∧ ¬ Ax3 noAx3 ∧ ¬ Ax3v3 noAx3 := by
  refine ⟨?_, ?_, fun h => not_E _ (h false), fun h => not_E3 _ (h false)⟩
  · intro φ _ _
    show (φ () false ∨ ¬ φ () false) ∧ ¬ (φ () false ∧ ¬ φ () false)
    exact ⟨Classical.em _, fun ⟨a, b⟩ => b a⟩
  · intro φ ψ _ _ w hφ hinc
    exact hinc false trivial () trivial hφ

/-! ## `Ax2a` needed: everything positive -/

def noAx2a : Model Bool Unit := two fun _ _ => True

theorem noAx2a_props :
    Ax3 noAx2a ∧ Ax3v3 noAx2a ∧ Ax4 noAx2a ∧ ¬ Ax2a noAx2a :=
  ⟨fun _ => trivial, fun _ => trivial, fun _ _ _ _ _ _ _ => trivial,
    fun h => (h top trivial false).2 ⟨trivial, trivial⟩⟩

/-- **Minimality of `kb_collapse`.** Each of `FullT`, symmetry, `Ax2a`, `Ax3`(`v3`), `Ax4` is
needed: dropping one leaves a fragment-closed model (`LGeneral`) of the others with an edge
`R w v`, `v ≠ w`, and admitted MC failing. -/
theorem kb_minimal :
    -- no `FullT`
    (LGeneral FM.fm ∧ (∀ w v, FM.fm.R w v) ∧ Ax2a FM.fm ∧ Ax3 FM.fm ∧ Ax3v3 FM.fm ∧
      Ax4 FM.fm ∧ ¬ MC FM.fm) ∧
    -- no symmetry
    (LGeneral s4model ∧ FullT s4model ∧ Ax2a s4model ∧ Ax3 s4model ∧ Ax4 s4model ∧
      s4model.R false true ∧ ¬ MC s4model) ∧
    -- no `Ax4`
    (LGeneral noAx4 ∧ FullT noAx4 ∧ (∀ w v, noAx4.R w v) ∧ Ax2a noAx4 ∧ Ax3 noAx4 ∧
      Ax3v3 noAx4 ∧ ¬ Ax4 noAx4 ∧ ¬ (∀ w v, noAx4.R w v → v = w) ∧ ¬ MC noAx4) ∧
    -- no `Ax3`, no `Ax3v3`
    (LGeneral noAx3 ∧ FullT noAx3 ∧ (∀ w v, noAx3.R w v) ∧ Ax2a noAx3 ∧ Ax4 noAx3 ∧
      ¬ Ax3 noAx3 ∧ ¬ Ax3v3 noAx3 ∧ ¬ (∀ w v, noAx3.R w v → v = w) ∧ ¬ MC noAx3) ∧
    -- no `Ax2a`
    (LGeneral noAx2a ∧ FullT noAx2a ∧ (∀ w v, noAx2a.R w v) ∧ Ax3 noAx2a ∧ Ax3v3 noAx2a ∧
      Ax4 noAx2a ∧ ¬ Ax2a noAx2a ∧ ¬ (∀ w v, noAx2a.R w v → v = w) ∧ ¬ MC noAx2a) := by
  obtain ⟨hLf, hRf, h2af, h3f, h3vf, h4f, _, _, hmf, _⟩ := separating_kb.2
  obtain ⟨hLs, _, _, h2as, _, h3s, h4s, hms, _, _⟩ := s4_props
  obtain ⟨a1, a2, a3, a4⟩ := noAx4_props
  obtain ⟨b1, b2, b3, b4⟩ := noAx3_props
  obtain ⟨c1, c2, c3, c4⟩ := noAx2a_props
  exact ⟨⟨hLf, hRf, h2af, h3f, h3vf, h4f, hmf⟩,
    ⟨hLs, fun _ => trivial, h2as, h3s, h4s, Or.inr rfl, hms⟩,
    ⟨two_lgeneral _, two_fullT _, fun _ _ => trivial, a1, a2, a3, a4, two_not_id _,
      two_not_mc _⟩,
    ⟨two_lgeneral _, two_fullT _, fun _ _ => trivial, b1, b2, b3, b4, two_not_id _,
      two_not_mc _⟩,
    ⟨two_lgeneral _, two_fullT _, fun _ _ => trivial, c1, c2, c3, c4, two_not_id _,
      two_not_mc _⟩⟩

end Programme.«20261022-0733-ontological».Run2.KBMinimal

#print axioms Programme.«20261022-0733-ontological».Run2.KBMinimal.kb_minimal
#print axioms Programme.«20261022-0733-ontological».Run2.KBMinimal.serial
