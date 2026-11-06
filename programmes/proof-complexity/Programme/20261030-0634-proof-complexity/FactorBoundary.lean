import Programme.«20261026-1402-proof-complexity».SymDesign
import Programme.«20261030-0634-proof-complexity».TopSplice

namespace Programme.«20261030-0634-proof-complexity».FactorBoundary
open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum var)
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr)
open Programme.«20261025-1627-proof-complexity».MomGen (canon)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt)
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».SymDesign

def lower (n d : Nat) (g : List Nat) : Int := -cv n d g.length

theorem line_lower (n k d : Nat) (g : List Nat) (hg : CM n k g)
    (v : Nat → Nat) (M : Nat) (hv : ∀ t < M, v t < (n+k)*n)
    (hf : ∀ t < M, v t ∉ g) :
    lineS n k (lower n d) g v M =
      lineS n k (fun _ => -cv n d (g.length+1)) g v M := by
  unfold lineS
  apply rsum_congr
  intro t ht
  have hl := canon_len_eq (List.nodup_cons.mpr ⟨hf t ht, CM_nodup hg⟩)
    (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hv t ht
      · exact CM_lt hg hx)
  simp only [List.length_cons] at hl
  simp only [lower, hl]

theorem lower_bal {p n k d e : Nat} (hn : 0 < n) (hk : p ∣ k) (he : e < d) :
    Bal p n k (lower n d) (lower n d) e := by
  intro g hg hge
  have hs := cv_step n d e he
  constructor
  · intro i hi hf
    unfold rowS
    rw [line_lower n k d g hg (fun j => var n i j) n
      (fun j hj => var_lt n k i j hi hj) (notin_of_pfree hf)]
    change (p : Int) ∣ rowS n k (fun _ => -cv n d (g.length+1)) g i - lower n d g
    rw [rowS_const hn _ hg hf]
    simp only [lower, hge]
    rw [hs]
    exact ⟨0, by simp [Int.mul_neg]⟩
  · intro j hj hf
    unfold colS
    rw [line_lower n k d g hg (fun i => var n i j) (n+k)
      (fun i hi => var_lt n k i j hi hj) (fun i _ => notin_of_hfree hf i hj)]
    change (p : Int) ∣ colS n k (fun _ => -cv n d (g.length+1)) g j - lower n d g
    rw [colS_const hn _ hg hj hf]
    simp only [lower, hge]
    rw [hs]
    have H : (p : Int) ∣ (k : Int) := Int.natCast_dvd_natCast.mpr hk
    have HH : (p : Int) ∣ (k : Int) * (-cv n d (e+1)) :=
      Int.dvd_trans H ⟨-cv n d (e+1), rfl⟩
    have eqn : ((n+k : Nat) - (e : Int)) * -cv n d (e+1) -
        -(((n : Int) - e) * cv n d (e+1)) = (k : Int) * -cv n d (e+1) := by
      have hh : ((n+k : Nat) : Int) - e = ((n : Int) - e) + k := by omega
      rw [hh, Int.add_mul]
      simp only [Int.mul_neg]
      omega
    rw [eqn]
    exact HH

theorem lower_top (n d : Nat) (g : List Nat) (h : g.length = d) :
    lower n d g = -1 := by simp [lower, cv, h, ff]

/-- The symmetric factorial boundary and a single top extension give all balance levels. -/
theorem design_of_top {p n k d : Nat} (hn : 0 < n) (hk : p ∣ k)
    (U : List Nat → Int) (ht : Bal p n k U (fun _ => -1) d) :
    ∃ T : List Nat → Int, T [] = -ff n d ∧
      ∀ e ≤ d, Bal p n k T T e := by
  refine ⟨Programme.«20261030-0634-proof-complexity».TopSplice.splice d (lower n d) U, ?_, ?_⟩
  · simp [Programme.«20261030-0634-proof-complexity».TopSplice.splice, lower, cv]
  · exact Programme.«20261030-0634-proof-complexity».TopSplice.splice_bal p n k d (lower n d) U (fun _ => -1)
      (fun e he => lower_bal hn hk he)
      (fun g _ hl => (lower_top n d g hl).symm) ht

#print axioms lower_bal
#print axioms design_of_top
end Programme.«20261030-0634-proof-complexity».FactorBoundary
