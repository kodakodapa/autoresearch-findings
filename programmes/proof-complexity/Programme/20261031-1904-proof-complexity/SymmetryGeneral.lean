import Programme.«20261026-1402-proof-complexity».SymDesign
import Programme.«20261027-1434-proof-complexity».RowColG

namespace Programme.«20261031-1904-proof-complexity».SymmetryGeneral
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».SymDesign
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt rsum_dvd)
open Programme.«20261027-1434-proof-complexity».RowColG (exists_free_hole fp_free)

def LengthInvariant (p n k : Nat) (T : List Nat → Int) : Prop :=
  ∀ g h, CM n k g → CM n k h → g.length = h.length → g.length ≤ p →
    T g % (p : Int) = T h % (p : Int)

private theorem ext_cm {n k : Nat} {g : List Nat} (hg : CM n k g)
    {i j : Nat} (hi : i < n+k) (hj : j < n) (hf : pfree n g i)
    (hm : isMatch n (var n i j :: g) = true) :
    CM n k (canon ((n+k)*n) (var n i j :: g)) ∧
    (canon ((n+k)*n) (var n i j :: g)).length = g.length + 1 := by
  have hall : ∀ x ∈ var n i j :: g, x < (n+k)*n := by
    intro x hx; rcases List.mem_cons.mp hx with rfl | hx
    · exact var_lt n k i j hi hj
    · exact CM_lt hg hx
  refine ⟨⟨canon_idem _, ?_⟩, ?_⟩
  · rw [isMatch_congr n _ _ (mem_canon' hall)]; exact hm
  · rw [canon_len_eq (List.nodup_cons.mpr ⟨notin_of_pfree hf j hj, CM_nodup hg⟩) hall]
    simp

private theorem free_match {n : Nat} {g : List Nat} (hg : isMatch n g = true)
    {i j : Nat} (hj : j < n) (hi : pfree n g i) (hh : hfree n g j) :
    isMatch n (var n i j :: g) = true := by
  apply (isMatch_cons n _ g).mpr
  refine ⟨hg, fun w hw => ?_⟩
  have h1 := hi w hw
  have h2 := hh w hw
  simp only [cfl, Bool.and_eq_false_iff, bne_eq_false_iff_eq,
    Bool.or_eq_false_iff, beq_eq_false_iff_ne, var_div n i j hj, var_mod n i j hj]
  exact Or.inr ⟨Ne.symm h1, Ne.symm h2⟩

private theorem row_congr {p n k : Nat} (hn : 0 < n) (T : List Nat → Int)
    (hs : LengthInvariant p n k T) {g h : List Nat} (hg : CM n k g)
    (hh : CM n k h) (hl : h.length = g.length+1) (hp : h.length ≤ p)
    {i : Nat} (hi : i < n+k) (hf : pfree n g i) :
    (p : Int) ∣ rowS n k T g i - ((n : Int) - g.length) * T h := by
  rw [← rowS_const hn (T h) hg hf]
  unfold rowS lineS
  rw [← Programme.«20261025-1627-proof-complexity».OntoExt3.rsum_sub']
  apply rsum_dvd
  intro j hj
  cases hm : isMatch n (var n i j :: g)
  · simp [hm]
  · simp only [hm, ite_true]
    have hc := ext_cm hg hi hj hf hm
    exact Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp
      (hs _ _ hc.1 hh (by omega) (by omega)))

/-- Full length symmetry cannot support a unit balanced tower, for any positive modulus. -/
theorem no_unit_length_invariant {p n k : Nat} (hp : 0 < p) (hn : p ≤ n)
    (T : List Nat → Int) (hu : ¬ (p : Int) ∣ T [])
    (hb : ∀ e < p, Bal p n k T T e) (hs : LengthInvariant p n k T) : False := by
  let r := n % p
  have hr : r < p := Nat.mod_lt n hp
  have hzero : (p : Int) ∣ (n : Int) - r := by
    apply Int.dvd_of_emod_eq_zero
    rw [Int.sub_emod]
    have he : (n : Int) % (p : Int) = (r : Int) := by
      exact_mod_cast (rfl : n % p = r)
    have er : (r : Int) % (p : Int) = r := Int.emod_eq_of_lt (by omega) (by exact_mod_cast hr)
    rw [he, er, Int.sub_self, Int.zero_emod]
  have kill : ∀ d, ∀ g, CM n k g → g.length + d = r → (p : Int) ∣ T g := by
    intro d
    induction d with
    | zero =>
      intro g hg hlen
      have hgn : g.length < n := by omega
      obtain ⟨j, hj, hjf⟩ := exists_free_hole hgn
      obtain ⟨hi, hif⟩ := fp_free (k := k) hgn
      let i := Programme.«20261027-1434-proof-complexity».RowColG.fp n k g
      have hm := free_match hg.2 hj hif hjf
      have hc := ext_cm hg hi hj hif hm
      have rc := row_congr (by omega) T hs hg hc.1 hc.2 (by omega) hi hif
      have hd : (p : Int) ∣ ((n : Int) - g.length) * T (canon ((n+k)*n) (var n i j :: g)) := by
        obtain ⟨q, hq⟩ := hzero
        refine ⟨q * T (canon ((n+k)*n) (var n i j :: g)), ?_⟩
        rw [show g.length = r by omega, hq, Int.mul_assoc]
      have br := (hb g.length (by omega) g hg rfl).1 _ hi hif
      have hh := Int.dvd_sub (Int.dvd_add hd rc) br
      dsimp [i] at hh
      have ee : ∀ a b c : Int, a + (b-a) - (b-c) = c := by intros; omega
      rwa [ee] at hh
    | succ d ih =>
      intro g hg hlen
      have hgn : g.length < n := by omega
      obtain ⟨hi, hif⟩ := fp_free (k := k) hgn
      have hd : (p : Int) ∣ rowS n k T g (Programme.«20261027-1434-proof-complexity».RowColG.fp n k g) := by
        unfold rowS lineS
        apply rsum_dvd
        intro j hj
        cases hm : isMatch n (var n _ j :: g)
        · simp [hm]
        · simp only [hm, ite_true]
          have hc := ext_cm hg hi hj hif hm
          exact ih _ hc.1 (by omega)
      have br := (hb g.length (by omega) g hg rfl).1 _ hi hif
      have := Int.dvd_sub hd br
      have ee : ∀ a b : Int, a - (a-b) = b := by intros; omega
      rwa [ee] at this
  have ce : CM n k [] := ⟨List.eq_nil_iff_forall_not_mem.mpr (fun x h => by simp [mem_canon] at h), by simp [isMatch]⟩
  exact hu (kill r [] ce (by simp))
end Programme.«20261031-1904-proof-complexity».SymmetryGeneral
#print axioms Programme.«20261031-1904-proof-complexity».SymmetryGeneral.no_unit_length_invariant
