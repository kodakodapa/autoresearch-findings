import Programme.«20261021-1639-ontological».Deep.ConjunctionRecovery
import Programme.«20261021-1639-ontological».Deep.V2FullNotes

/-! Conditional closed-Henkin Two recovery, following th P422 and sk P419.
Only negated family applications are substituted into modal collapse. -/
namespace Programme.«20261021-1639-ontological».Deep.TwoRecovery
open Programme.«20261021-1639-ontological».Deep Programme.«20261021-1639-ontological».Deep.Henkin Programme.«20261021-1639-ontological».Theorist.HenkinScott
open Programme.«20261021-1639-ontological».Theorist.SymmetricModels Programme.«20261021-1639-ontological».Theorist.ScottBridge
open Programme.«20261021-1639-ontological».Theorist.ScottDeep Programme.«20261021-1639-ontological».Theorist.V2Deep

variable {W : Type} {m : Henkin.Model OntConst W}
  {gm : GModel W (m.frame.D .entity)}

def ex (t : T (a :: Γ) .prop) : T Γ .prop := neg (.all (neg t))
theorem sem_ex (ρ : Assignment m.frame Γ) (t : T (a :: Γ) .prop) (w : W) :
    sem m ρ (ex t) w ↔ ∃ x, sem m (push ρ x) t w := by
  simp only [ex, sem_neg, sem_all]
  exact Classical.not_forall_not

def tTwo : T [Property, HP] .prop :=
  ex (ex (conj (.app v3 v1) (conj (.app v3 v0) (neg (.equal v1 v0)))))
def tAx1GenTwo (a : Bool) : T [] .prop :=
  .all (a := HP) (.all (a := Property) (.imp tTwo (.imp
    (.all (a := Property) (.imp (.app v2 v0) (pos v0)))
    (.imp (.box (.all (a := .entity) (gimp a v0 (iff' (.app v1 v0)
      (.all (a := Property) (.imp (.app v3 v0) (.app v0 v1))))))) (pos v0)))))

theorem recover (hp : Presents m gm) (a : Bool) (ρ : Assignment m.frame [])
    (mc : DeepValid m ρ tMC) (ax4 : DeepValid m ρ (V2FullNotes.tAx4 a))
    (ptop : ∀ w, gm.positive (fun _ _ => True) w)
    (two : DeepValid m ρ (tAx1GenTwo a)) : DeepValid m ρ (tAx1Gen a) := by
  have back (S : m.frame.D HP) (Q : m.frame.D Property) (w v : W)
      (rv : m.frame.rel w v) (hv : m.frame.truth (m.frame.app S Q) v) :
      m.frame.truth (m.frame.app S Q) w := by
    have hmc := (deepValid_iff m ρ tMC).1 mc
    simp only [tMC, sem_all, sem_imp, sem_box, tr_v0] at hmc
    let n := Henkin.translate m.frame m.interp
      (neg (.app v1 v0) : T [Property, HP] .prop) (push (push ρ S) Q)
    have hn (u) : m.frame.truth n u ↔ ¬ m.frame.truth (m.frame.app S Q) u := by
      change sem m (push (push ρ S) Q) (neg (.app v1 v0)) u ↔ _
      simp only [sem_neg, sem_app, tr_v0, tr_v1]
    exact Classical.byContradiction fun h => (hn v).1 (hmc w n ((hn w).2 h) v rv) hv
  have h4 := (V2FullNotes.bridge_Ax4 hp a ρ).1 ax4
  rw [deepValid_iff] at two ⊢
  simp only [tAx1GenTwo, tTwo, sem_all, sem_imp, sem_ex, sem_conj, sem_neg,
    sem_equal, sem_box, sem_pos hp, sem_gimp hp, sem_iff, sem_app,
    tr_v0, tr_v1, tr_v2, tr_v3] at two
  simp only [tAx1Gen, sem_all, sem_imp, sem_box, sem_pos hp, sem_gimp hp,
    sem_iff, sem_app, tr_v0, tr_v1, tr_v2, tr_v3]
  intro w S P hpos hconj
  by_cases ht : ∃ Q₁ Q₂, m.frame.truth (m.frame.app S Q₁) w ∧
      m.frame.truth (m.frame.app S Q₂) w ∧ Q₁ ≠ Q₂
  · exact two w S P ht hpos hconj
  by_cases he : ∃ Q, m.frame.truth (m.frame.app S Q) w
  · obtain ⟨Q, hQ⟩ := he
    apply h4 (img m Q) (img m P) w ((adm_iff hp _).2 ⟨Q, rfl⟩)
      ((adm_iff hp _).2 ⟨P, rfl⟩) (hpos Q hQ)
    intro v rv y hy hqy
    have rv' := (hp.2.2.1 w v).2 rv
    apply (hconj v rv' y hy).2
    intro Q' hQ'
    have eq : Q' = Q := Classical.byContradiction fun ne =>
      ht ⟨Q', Q, back S Q' w v rv' hQ', hQ, ne⟩
    exact eq ▸ hqy
  · have topadm : gm.adm (fun _ _ => True) := by
      have hc := cloV2_of_presents hp a ρ
      have eq : Programme.«20261021-1639-ontological».Theorist.HenkinVariant2.negP
          (Programme.«20261021-1639-ontological».Theorist.HenkinVariant2.botP : m.frame.D .entity → W → Prop) =
          (fun _ _ => True) := by
        funext x u
        exact propext ⟨fun _ => True.intro, fun _ h => h⟩
      rw [← eq]
      exact hc.neg _ hc.bot
    apply h4 _ (img m P) w topadm ((adm_iff hp _).2 ⟨P, rfl⟩) (ptop w)
    intro v rv y hy _
    have rv' := (hp.2.2.1 w v).2 rv
    apply (hconj v rv' y hy).2
    intro Q hQ
    exact False.elim (he ⟨Q, back S Q w v rv' hQ⟩)

def tPosTop : T [] .prop := pos (.lam (neg .falsum))

theorem two_of_gen (a : Bool) (ρ : Assignment m.frame [])
    (h : DeepValid m ρ (tAx1Gen a)) : DeepValid m ρ (tAx1GenTwo a) := by
  rw [deepValid_iff] at h ⊢
  simp only [tAx1Gen, sem_all, sem_imp] at h
  simp only [tAx1GenTwo, sem_all, sem_imp]
  exact fun w S P _ => h w S P

theorem equivalence (hp : Presents m gm) (a : Bool) (ρ : Assignment m.frame [])
    (mc : DeepValid m ρ tMC) (ax4 : DeepValid m ρ (V2FullNotes.tAx4 a))
    (ptop : DeepValid m ρ tPosTop) :
    DeepValid m ρ (tAx1GenTwo a) ↔ DeepValid m ρ (tAx1Gen a) := by
  have ht : ∀ w, gm.positive (fun _ _ => True) w := by
    rw [deepValid_iff] at ptop
    simpa only [tPosTop, sem_pos hp, img_lam, sem_neg, sem_falsum, not_false_eq_true] using ptop
  exact ⟨recover hp a ρ mc ax4 ht, two_of_gen a ρ⟩

#print axioms equivalence
#print axioms two_of_gen
#print axioms recover
end Programme.«20261021-1639-ontological».Deep.TwoRecovery
