import Programme.«20261104-1627-proof-complexity».SupportedCertificates
namespace Programme.«20261104-1627-proof-complexity».CoefficientSections
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261104-1627-proof-complexity».SupportedCertificates

def inside (B : Nat → Bool) (m : List Nat) := m.filter B
def outside (B : Nat → Bool) (m : List Nat) := m.filter (fun x => !(B x))
def coeffSection (B : Nat → Bool) (s : List Nat) (P : Poly Nat) : Poly Nat :=
  ⟨(P.terms.filter (fun t => outside B t.2 == s)).map
    (fun t => (t.1, inside B t.2))⟩
theorem lengths (B : Nat → Bool) (m : List Nat) :
    (inside B m).length + (outside B m).length = m.length := by
  induction m with
  | nil => simp [inside, outside]
  | cons x m ih =>
    cases h : B x <;> simp [inside, outside, h] at * <;> omega

theorem section_supported (B : Nat → Bool) (s : List Nat) (P : Poly Nat) :
    Supported B (coeffSection B s P) := by
  intro t ht x hx
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact (List.mem_filter.mp hx).2

theorem section_budget (B : Nat → Bool) (s : List Nat) (P : Poly Nat)
    (D : Nat) (hP : P.deg ≤ D) (hs : s.length ≤ D) :
    (coeffSection B s P).deg + s.length ≤ D := by
  have h : (coeffSection B s P).deg ≤ D - s.length := by
    apply (deg_le_iff _ _).mpr
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hu, he⟩ := List.mem_filter.mp hu
    have heq : outside B u.2 = s := by simpa using he
    have hd := (deg_le_iff P D).mp hP u hu
    have hl := lengths B u.2
    rw [heq] at hl
    dsimp
    omega
  omega

theorem multiplier_budget (B : Nat → Bool) (s : List Nat) (g A : Poly Nat)
    (D : Nat) (h : g.deg + A.deg ≤ D) (hs : s.length + A.deg ≤ D) :
    (coeffSection B s g).deg + A.deg + s.length ≤ D := by
  have hh := section_budget B s g (D - A.deg) (by omega) (by omega)
  omega

theorem mono_split (B a : Nat → Bool) (m : List Nat) :
    monoEval a m = monoEval a (inside B m) * monoEval a (outside B m) := by
  induction m with
  | nil => simp [monoEval, inside, outside]
  | cons x m ih =>
    cases hb : B x <;> cases ha : a x <;>
      simp [inside, outside, monoEval, hb, ha] at * <;> omega

theorem reconstruction (B a : Nat → Bool) (P : Poly Nat) :
    P.eval a = (P.terms.map (fun t =>
      (t.1 * monoEval a (inside B t.2)) * monoEval a (outside B t.2))).sum := by
  unfold Poly.eval
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [mono_split B a t.2, Int.mul_assoc]
end Programme.«20261104-1627-proof-complexity».CoefficientSections
#print axioms Programme.«20261104-1627-proof-complexity».CoefficientSections.section_budget
#print axioms Programme.«20261104-1627-proof-complexity».CoefficientSections.reconstruction

#print axioms Programme.«20261104-1627-proof-complexity».CoefficientSections.multiplier_budget
