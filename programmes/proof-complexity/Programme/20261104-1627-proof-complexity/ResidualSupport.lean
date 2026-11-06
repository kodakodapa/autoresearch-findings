import Programme.«20261104-1627-proof-complexity».SpanningResidualStep
import Programme.«20261104-1627-proof-complexity».LprimeAggregation

namespace Programme.«20261104-1627-proof-complexity».ResidualSupport
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261104-1627-proof-complexity».LprimeStages Programme.«20261104-1627-proof-complexity».SpanningResidualStep

private theorem sum_dvd (p : Int) (L : List Label) (f : Label → Int)
    (h : ∀ g ∈ L, p ∣ f g) : p ∣ (L.map f).sum := by
  induction L with
  | nil => simp
  | cons g gs ih =>
    exact Int.dvd_add (h g (by simp)) (ih (fun x hx => h x (by simp [hx])))

private theorem aggregate_coeff (a : Vector) (g : Label) : aggregate a g = vectorCoeff a g := by
  induction a with
  | nil => rfl
  | cons t ts ih =>
    by_cases h : t.2 = g <;> simp [aggregate, vectorCoeff, h] at ih ⊢ <;> exact ih

/-- Coordinatewise congruence transfers the actual polynomial kernel condition. -/
theorem kernel_of_congruent {p m n d : Nat} {v w : Vector}
    (hv : Kernel p m n d v) (hw : valid m n d w)
    (he : ∀ g, (p : Int) ∣ vectorCoeff v g - vectorCoeff w g) :
    Kernel p m n d w := by
  refine ⟨hw, ?_⟩
  intro u
  have H (a : Vector) (ha : valid m n d a) :
      coeff (top m n a) u =
      ((labels m n d).map fun g => vectorCoeff a g * coeff (topLabel m n g) u).sum := by
    rw [top_coeff_sum]
    have hh := grouped_sum (labels m n d) (labels_nodup m n d) a ha
      (fun g => coeff (topLabel m n g) u)
    simpa only [aggregate_coeff] using hh
  have hs := sum_dvd (p : Int) (labels m n d)
    (fun g => (vectorCoeff v g - vectorCoeff w g) * coeff (topLabel m n g) u)
    (fun g _ => by
      obtain ⟨z,hz⟩ := he g
      exact ⟨z * coeff (topLabel m n g) u, by rw [hz]; simp [Int.mul_assoc]⟩)
  have hsum (L : List Label) :
      (L.map fun g => (vectorCoeff v g - vectorCoeff w g) * coeff (topLabel m n g) u).sum =
      (L.map fun g => vectorCoeff v g * coeff (topLabel m n g) u).sum -
      (L.map fun g => vectorCoeff w g * coeff (topLabel m n g) u).sum := by
    induction L with
    | nil => simp
    | cons g gs ih => simp only [List.map_cons, List.sum_cons]; rw [ih, Int.sub_mul]; omega
  rw [hsum, ← H v hv.1, ← H w hw] at hs
  have hk : (p : Int) ∣ coeff (top m n v) u := by simpa [coeff, cf] using hv.2 u
  have hd := Int.dvd_sub hk hs
  have heq : coeff (top m n v) u - (coeff (top m n v) u - coeff (top m n w) u) =
      coeff (top m n w) u := by omega
  rw [heq] at hd
  simpa [coeff, cf] using hd

/-- Delete block one literally, rather than only making its coefficients zero. -/
def tailBlocks (m : Nat) (v : Vector) : Vector :=
  splitPigeon m 2 v ++ splitPigeon m 3 v

theorem tail_congruent {p m : Nat} {v : Vector}
    (hz : ∀ g, (p : Int) ∣ vectorCoeff (splitPigeon m 1 v) g) :
    ∀ g, (p : Int) ∣ vectorCoeff v g - vectorCoeff (tailBlocks m v) g := by
  intro g
  have he := vectorCoeff_splitPigeon m v g
  rw [tailBlocks, vectorCoeff_append]
  have hh : vectorCoeff v g -
      (vectorCoeff (splitPigeon m 2 v) g + vectorCoeff (splitPigeon m 3 v) g) =
      vectorCoeff (splitPigeon m 1 v) g := by omega
  rw [hh]
  exact hz g

theorem tail_kernel {p m n d : Nat} {v : Vector}
    (hv : Kernel p (m+1) n d v)
    (hz : ∀ g, (p : Int) ∣ vectorCoeff (splitPigeon m 1 v) g) :
    Kernel p (m+1) n d (tailBlocks m v) := by
  apply kernel_of_congruent hv _ (tail_congruent hz)
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact splitPigeon_valid m 2 hv.1 t h
  · exact splitPigeon_valid m 3 hv.1 t h

theorem tail_support (m : Nat) (v : Vector) :
    ∀ t ∈ tailBlocks m v, pigeonBlock m t.2 ≠ 1 := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · have hh := (List.mem_filter.mp h).2
    have : pigeonBlock m t.2 = 2 := by simpa using hh
    omega
  · have hh := (List.mem_filter.mp h).2
    have : pigeonBlock m t.2 = 3 := by simpa using hh
    omega

/-- The remaining mathematical obligation may be restricted to literal tail support. -/
def TailSpanning (p m n d : Nat) : Prop :=
  ∀ v, Kernel p (m+1) n d v →
    (∀ t ∈ v, pigeonBlock m t.2 ≠ 1) →
    ∃ c : List (Int × Vector),
      (∀ t ∈ c, t.2 ∈ syzygies (m+1) n d) ∧
      ∀ g, (p : Int) ∣ vectorCoeff v g - vectorCoeff (combine c) g

theorem residual_of_tail {p m n d : Nat} (h : TailSpanning p m n d) :
    ResidualSpanning p m n d := by
  intro v hv hz
  obtain ⟨c,hc,he⟩ := h (tailBlocks m v) (tail_kernel hv hz) (tail_support m v)
  refine ⟨c,hc,fun g => ?_⟩
  have hh := Int.dvd_add (tail_congruent hz g) (he g)
  have heq : vectorCoeff v g - vectorCoeff (tailBlocks m v) g +
      (vectorCoeff (tailBlocks m v) g - vectorCoeff (combine c) g) =
      vectorCoeff v g - vectorCoeff (combine c) g := by omega
  rwa [heq] at hh

theorem tail_of_residual {p m n d : Nat} (h : ResidualSpanning p m n d) :
    TailSpanning p m n d := by
  intro v hv hs
  apply h v hv
  have hz : splitPigeon m 1 v = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro t ht
    have hh := List.mem_filter.mp ht
    exact hs t hh.1 (by simpa using hh.2)
  intro g
  simp [hz, vectorCoeff]

theorem residual_iff_tail (p m n d : Nat) :
    ResidualSpanning p m n d ↔ TailSpanning p m n d :=
  ⟨tail_of_residual, residual_of_tail⟩

end Programme.«20261104-1627-proof-complexity».ResidualSupport
#print axioms Programme.«20261104-1627-proof-complexity».ResidualSupport.kernel_of_congruent
#print axioms Programme.«20261104-1627-proof-complexity».ResidualSupport.tail_kernel
#print axioms Programme.«20261104-1627-proof-complexity».ResidualSupport.residual_of_tail
#print axioms Programme.«20261104-1627-proof-complexity».ResidualSupport.residual_iff_tail
