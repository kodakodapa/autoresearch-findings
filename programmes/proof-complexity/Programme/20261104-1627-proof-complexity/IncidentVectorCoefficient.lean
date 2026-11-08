import Programme.«20261104-1627-proof-complexity».NonincidentCoefficient
import Programme.«20261104-1627-proof-complexity».TailMatchingCoordinates
import Programme.«20261104-1627-proof-complexity».KernelLinear
namespace Programme.«20261104-1627-proof-complexity».IncidentSection
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261104-1627-proof-complexity».TailMatchingCoordinates
private theorem scaled_cf (a : Int) (L : List (Int × List Nat)) (u : List Nat) :
    cf (L.map fun t => (a*t.1,t.2)) u = a * cf L u := by
  induction L with
  | nil => simp [cf]
  | cons t L ih =>
    by_cases h : t.2.Perm u <;> simp [cf,h,Int.mul_add] at ih ⊢ <;> exact ih
private theorem top_cons (m n : Nat) (t : Int × Label) (v : Vector) (u : List Nat) :
    coeff (top m n (t::v)) u = t.1 * coeff (topLabel m n t.2) u + coeff (top m n v) u := by
  simp only [top,List.flatMap_cons,coeff,cf_append,scaled_cf]

theorem incident_coeff {m n d h : Nat} (hn : 0 < n) (hh : h < n+1)
    (hd : 1 < d) {v : Vector} (hv : valid (m+1) (n+1) d v)
    (ht : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1)
    {E : Matching} (hE : E ∈ matchings m n (d-1)) :
    coeff (top (m+1) (n+1) v) ((m*(n+1)+h)::mono (n+1) (pushMatching h E)) =
      tailCoordinates m v (pushMatching h E) +
        coeff (top m n (sectionVector m h v)) (mono n E) := by
  induction v with
  | nil => simp [top,coeff,cf,tailCoordinates,vectorCoeff,sectionVector]
  | cons t v ih =>
    have hg := hv t (by simp)
    have hv' : valid (m+1) (n+1) d v := by
      intro a ha; exact hv a (by simp [ha])
    have ht' : ∀ a ∈ v, pigeonBlock m a.2 ≠ 1 := by
      intro a ha; exact ht a (by simp [ha])
    have hi := ih hv' ht'
    rw [top_cons,hi]
    by_cases hx : (m,h) ∈ t.2.base
    · have hc := incident_label_coeff hn hh hd hg hx hE
      have he : t.2 ≠ (⟨pushMatching h E,true,m⟩ : Label) := by
        intro he
        rw [he] at hx
        obtain ⟨a,ha,he⟩ := List.mem_map.mp hx
        have hh' := congrArg Prod.snd he
        exact omitHole_ne h a.2 hh'
      simp only [sectionVector,List.filter_cons,decide_eq_true hx,↓reduceIte,List.map_cons]
      rw [top_cons,hc]
      simp only [tailCoordinates,vectorCoeff,List.filter_cons,beq_iff_eq,he,↓reduceIte,List.map_cons,
        List.sum_cons] at *
      omega
    · have he : d = (d-1)+1 := by omega
      have hc := nonincident_label_coeff hh (he ▸ hg) hx (ht t (by simp)) hE
      simp only [sectionVector,List.filter_cons,decide_eq_false_iff_not.mpr hx,
        Bool.false_eq_true,↓reduceIte,List.map_cons]
      rw [hc]
      by_cases he : t.2 = (⟨pushMatching h E,true,m⟩ : Label)
      · simp [tailCoordinates,vectorCoeff,he,Int.mul_one] at * <;> omega
      · simp [tailCoordinates,vectorCoeff,he] at * <;> omega
/-- The negative incident section realizes the omitted-hole restriction of a Kernel tail. -/
theorem tail_restriction_topImage {p m n d h : Nat} (hn : 0 < n)
    (hh : h < n+1) (hd : 1 < d) {v : Vector}
    (hv : Kernel p (m+1) (n+1) d v)
    (ht : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1) :
    TopImage p m n (d-1) (restrictCoordinates h (tailCoordinates m v)) := by
  let w := (sectionVector m h v).map fun t => ((-1 : Int)*t.1,t.2)
  refine ⟨w, ?_, ?_⟩
  · intro t ht
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
    have hs := section_valid hh hd hv.1 a ha
    simpa only [Nat.add_sub_cancel] using hs
  · intro E hE
    have hc := incident_coeff hn hh hd hv.1 ht hE
    have hk := hv.2 ((m*(n+1)+h)::mono (n+1) (pushMatching h E))
    have hw := top_scale_coeff m n (-1) (sectionVector m h v) (mono n E)
    change (p : Int) ∣ tailCoordinates m v (pushMatching h E) - coeff (top m n w) (mono n E)
    change coeff (top m n w) (mono n E) = _ at hw
    rw [hw]
    have hz : coeff (⟨[]⟩ : Programme.«20261024-1633-proof-complexity».NS.Poly Nat)
        ((m*(n+1)+h)::mono (n+1) (pushMatching h E)) = 0 := rfl
    rw [hz, Int.sub_zero, hc] at hk
    simpa only [Int.neg_mul, Int.one_mul, Int.sub_neg] using hk

end Programme.«20261104-1627-proof-complexity».IncidentSection
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.incident_coeff

#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.tail_restriction_topImage
