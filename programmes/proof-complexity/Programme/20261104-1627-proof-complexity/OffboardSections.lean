import Programme.«20261025-0459-proof-complexity».OntoSubst
import Programme.«20261025-1627-proof-complexity».NoDrop

namespace Programme.«20261104-1627-proof-complexity».OffboardSections
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoSubst
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261025-1627-proof-complexity».NoDrop

theorem nsIn_pull {p D : Nat} {A : List (Poly Nat)} (σ : Nat → Lit)
    (hgood : ∀ a, Good A a → Good A (pull σ a))
    (hax : ∀ P ∈ A, ∀ a, P.eval (pull σ a) = P.eval a)
    {f : (Nat → Bool) → Int} (hf : NSIn p A D f) :
    NSIn p A D (fun a => f (pull σ a)) := by
  obtain ⟨L, hL, he⟩ := hf
  refine ⟨L.map (fun e => (Poly.subst σ e.1, e.2)), ?_, ?_⟩
  · intro e he
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
    exact ⟨(hL b hb).1, Nat.le_trans
      (Nat.add_le_add_right (subst_deg σ b.1) _) (hL b hb).2⟩
  · intro a ha
    have eq : ((L.map fun e => (Poly.subst σ e.1, e.2)).map
        fun e => e.1.eval a * e.2.eval a).sum =
        (L.map fun e => e.1.eval (pull σ a) * e.2.eval (pull σ a)).sum := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro e he
      simp only [Function.comp_def, subst_eval]
      rw [hax e.2 (hL e he).1 a]
    rw [eq]
    exact he (pull σ a) (hgood a ha)

def sectionSubst (B : Nat → Bool) (b : Nat → Bool) (x : Nat) : Lit :=
  if B x then .var x else .const (b x)

theorem pull_section (B b a : Nat → Bool) (x : Nat) :
    pull (sectionSubst B b) a x = if B x then a x else b x := by
  simp only [pull, sectionSubst]
  split <;> rfl

theorem section_degree (B b : Nat → Bool) (Q : Poly Nat) :
    (Poly.subst (sectionSubst B b) Q).deg ≤ Q.deg := subst_deg _ _

end Programme.«20261104-1627-proof-complexity».OffboardSections
#print axioms Programme.«20261104-1627-proof-complexity».OffboardSections.nsIn_pull
#print axioms Programme.«20261104-1627-proof-complexity».OffboardSections.section_degree
