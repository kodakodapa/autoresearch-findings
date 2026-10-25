/- D12 sketch: the cw-filter + A4 collapse row in general (Henkin-style) semantics.
Properties and propositions range over admitted sub-collections `adm`, `admP`; the only closure
used is that ⊤, ⊥ and the constant lift `fun _ v => p v` of an admitted proposition are admitted.
Conclusion: modal collapse for every admitted proposition (not `R ⊆ id`, which K37 refutes). -/
namespace Programme.«20261021-1639-ontological».Theorist.HenkinCollapse

structure GModel (W E : Type) where
  rel : W → W → Prop
  actual : E → W → Prop
  adm : (E → W → Prop) → Prop
  admP : (W → Prop) → Prop
  positive : (E → W → Prop) → W → Prop

variable {W E : Type} (m : GModel W E) (a : Bool)
def guard (x : E) (w : W) : Prop := a = true → m.actual x w
def Closed : Prop := m.adm (fun _ _ => True) ∧ m.adm (fun _ _ => False) ∧
  ∀ p, m.admP p → m.adm (fun _ v => p v)
def HasU : Prop := ∀ w, m.positive (fun _ _ => True) w
def NoEmpty : Prop := ∀ w, ¬ m.positive (fun _ _ => False) w
/-- Current-world upward closure, quantifying over admitted properties only. -/
def UpCW : Prop := ∀ p q w, m.adm p → m.adm q → m.positive p w →
  (∀ x, guard m a x w → p x w → q x w) → m.positive q w
/-- A4 over admitted properties. -/
def A4 : Prop := ∀ p w, m.adm p → m.positive p w → ∀ v, m.rel w v → m.positive p v
/-- Object-level modal collapse: every admitted proposition true at `w` is true at successors. -/
def MCadm : Prop := ∀ p, m.admP p → ∀ w, p w → ∀ v, m.rel w v → p v

theorem mc_of_cw_A4 (hc : Closed m) (hU : HasU m) (h0 : NoEmpty m) (hup : UpCW m a)
    (h4 : A4 m) : MCadm m := by
  intro p hp w hw v hv
  obtain ⟨hT, hB, hL⟩ := hc
  have h1 : m.positive (fun _ v => p v) w := hup _ _ w hT (hL p hp) (hU w) fun _ _ _ => hw
  have h2 := h4 _ w (hL p hp) h1 v hv
  exact Classical.byContradiction fun hn => h0 v (hup _ _ v (hL p hp) hB h2 fun _ _ h => hn h)

#print axioms mc_of_cw_A4
end Programme.«20261021-1639-ontological».Theorist.HenkinCollapse
