import Programme.«20261026-1402-proof-complexity».ExtLemma

namespace Programme.«20261030-0634-proof-complexity».TopSplice
open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum var)
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr)
open Programme.«20261025-1627-proof-complexity».MomGen (canon)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt)
open Programme.«20261026-1402-proof-complexity».ExtLemma

def splice (d : Nat) (L U : List Nat → Int) (g : List Nat) : Int :=
  if g.length ≤ d then L g else U g

theorem line_splice (d n k : Nat) (L U : List Nat → Int)
    (g : List Nat) (hg : CM n k g) (v : Nat → Nat) (M : Nat)
    (hv : ∀ t < M, v t < (n+k)*n) (hf : ∀ t < M, v t ∉ g) :
    lineS n k (splice d L U) g v M =
      if g.length < d then lineS n k L g v M else lineS n k U g v M := by
  unfold lineS
  by_cases h : g.length < d
  · rw [if_pos h]
    apply rsum_congr
    intro t ht
    have hl := canon_len_eq (List.nodup_cons.mpr ⟨hf t ht, CM_nodup hg⟩)
      (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hv t ht
        · exact CM_lt hg hx)
    simp only [List.length_cons] at hl
    simp [splice, hl, show g.length + 1 ≤ d by omega]
  · rw [if_neg h]
    apply rsum_congr
    intro t ht
    have hl := canon_len_eq (List.nodup_cons.mpr ⟨hf t ht, CM_nodup hg⟩)
      (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hv t ht
        · exact CM_lt hg hx)
    simp only [List.length_cons] at hl
    simp [splice, hl, show ¬ g.length + 1 ≤ d by omega]

/-- Joining a balanced lower boundary to a single top extension. -/
theorem splice_bal (p n k d : Nat) (L U C : List Nat → Int)
    (low : ∀ e < d, Bal p n k L L e)
    (boundary : ∀ g, CM n k g → g.length = d → C g = L g)
    (top : Bal p n k U C d) :
    ∀ e ≤ d, Bal p n k (splice d L U) (splice d L U) e := by
  intro e he g hg hge
  have hbase : splice d L U g = L g := by simp [splice, hge, he]
  have hr (i : Nat) (hi : i < n+k) (hf : pfree n g i) :=
    line_splice d n k L U g hg (fun j => var n i j) n
      (fun j hj => var_lt n k i j hi hj) (notin_of_pfree hf)
  have hc (j : Nat) (hj : j < n) (hf : hfree n g j) :=
    line_splice d n k L U g hg (fun i => var n i j) (n+k)
      (fun i hi => var_lt n k i j hi hj) (fun i _ => notin_of_hfree hf i hj)
  by_cases h : e < d
  · have H := low e h g hg hge
    constructor
    · intro i hi hf
      simpa only [rowS, hr i hi hf, hge, if_pos h, hbase] using H.1 i hi hf
    · intro j hj hf
      simpa only [colS, hc j hj hf, hge, if_pos h, hbase] using H.2 j hj hf
  · have hed : e = d := by omega
    have hgd : g.length = d := hge.trans hed
    have H := top g hg hgd
    have hb := boundary g hg hgd
    constructor
    · intro i hi hf
      simpa only [rowS, hr i hi hf, hgd, Nat.lt_irrefl, ↓reduceIte, hbase, hb] using H.1 i hi hf
    · intro j hj hf
      simpa only [colS, hc j hj hf, hgd, Nat.lt_irrefl, ↓reduceIte, hbase, hb] using H.2 j hj hf

#print axioms splice_bal
end Programme.«20261030-0634-proof-complexity».TopSplice
