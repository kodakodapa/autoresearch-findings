import Programme.«20261102-1249-proof-complexity».UniformC3.Pad

namespace Programme.«20261102-1249-proof-complexity».UniformC3
open Programme.«20261026-1402-proof-complexity».Relabel
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261025-1627-proof-complexity».MomGen (canon mem_canon)

structure Selection (m n : Nat) where
  rows : List Nat
  nodup : rows.Nodup
  length : rows.length = n
  bound : ∀ v ∈ rows, v < m

def Selection.full {m n : Nat} (A : Selection m n) : List Nat :=
  A.rows ++ (List.range m).filter (fun i => i ∉ A.rows)

theorem Selection.full_nodup {m n : Nat} (A : Selection m n) : A.full.Nodup := by
  apply List.nodup_append.mpr
  refine ⟨A.nodup, List.Pairwise.filter _ List.nodup_range, ?_⟩
  intro a ha b hb hab
  have h := List.mem_filter.mp hb
  have hnot : b ∉ A.rows := by simpa using h.2
  exact hnot (hab ▸ ha)

theorem Selection.mem_full {m n : Nat} (A : Selection m n) (v : Nat) :
    v ∈ A.full ↔ v < m := by
  simp only [Selection.full, List.mem_append, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · exact A.bound v h
    · exact h.1
  · intro h
    by_cases ha : v ∈ A.rows
    · exact Or.inl ha
    · exact Or.inr ⟨h,ha⟩

theorem Selection.full_perm {m n : Nat} (A : Selection m n) :
    A.full.Perm (List.range m) := by
  apply (List.perm_ext_iff_of_nodup A.full_nodup List.nodup_range).mpr
  intro v
  simp only [A.mem_full, List.mem_range]

theorem Selection.full_length {m n : Nat} (A : Selection m n) : A.full.length = m := by
  simpa using A.full_perm.length_eq

def Selection.perm {m n : Nat} (A : Selection m n) : Perm m where
  f := fun i => A.full.idxOf i
  g := fun i => A.full[i]?.getD 0
  f_lt := by
    intro i hi
    have h := List.idxOf_lt_length_of_mem ((A.mem_full i).mpr hi)
    simpa [A.full_length] using h
  g_lt := by
    intro i hi
    have hi' : i < A.full.length := by simpa [A.full_length] using hi
    rw [List.getElem?_eq_getElem hi']
    exact (A.mem_full _).mp (List.getElem_mem hi')
  gf := by
    intro i hi
    have hi' := List.idxOf_lt_length_of_mem ((A.mem_full i).mpr hi)
    rw [List.getElem?_eq_getElem hi']
    exact List.getElem_idxOf hi'
  fg := by
    intro i hi
    have hi' : i < A.full.length := by simpa [A.full_length] using hi
    rw [List.getElem?_eq_getElem hi']
    exact A.full_nodup.idxOf_getElem i hi'

theorem Selection.perm_selected {m n : Nat} (A : Selection m n) (i : Nat) :
    A.perm.f i < n ↔ i ∈ A.rows := by
  change (A.rows ++ _).idxOf i < n ↔ _
  rw [List.idxOf_append]
  by_cases hi : i ∈ A.rows
  · rw [if_pos hi]
    have h := List.idxOf_lt_length_of_mem hi
    rw [A.length] at h
    exact ⟨fun _ => hi, fun _ => h⟩
  · rw [if_neg hi, A.length]
    constructor
    · intro h; omega
    · intro h; exact False.elim (hi h)

def Selection.contains {m n : Nat} (A : Selection m n) (g : List Nat) : Prop :=
  ∀ v ∈ g, v / n ∈ A.rows

instance {m n : Nat} (A : Selection m n) (g : List Nat) : Decidable (A.contains g) :=
  inferInstanceAs (Decidable (∀ v ∈ g, v/n ∈ A.rows))

theorem Selection.image_small {n k : Nat} (hn : 0 < n) (A : Selection (n+k) n)
    {g : List Nat} (hg : CM n k g) :
    (∀ w ∈ canon ((n+k)*n) (g.map (phi A.perm (idPerm n))), w < n*n) ↔
      A.contains g := by
  constructor
  · intro hs v hv
    have hb := phi_lt A.perm (idPerm n) (CM_lt hg hv)
    have hm : phi A.perm (idPerm n) v ∈ canon ((n+k)*n) (g.map (phi A.perm (idPerm n))) :=
      (mem_canon _ _ _).mpr ⟨List.mem_map.mpr ⟨v,hv,rfl⟩,hb⟩
    have hsmall := hs _ hm
    have hd : phi A.perm (idPerm n) v / n < n := (Nat.div_lt_iff_lt_mul hn).mpr hsmall
    rw [phi_div A.perm (idPerm n) (CM_lt hg hv)] at hd
    exact (A.perm_selected _).mp hd
  · intro hs w hw
    obtain ⟨hm,_⟩ := (mem_canon _ _ _).mp hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hm
    apply (Nat.div_lt_iff_lt_mul hn).mp
    rw [phi_div A.perm (idPerm n) (CM_lt hg hv)]
    exact (A.perm_selected _).mpr (hs v hv)

def embed {p k : Nat} (H : IntegralLift p) (A : Selection (2*p-1+k) (2*p-1)) :
    List Nat → Int := relab A.perm (idPerm (2*p-1)) (pad (2*p-1) H.coeff)

theorem embed_unit {p k : Nat} (hp : 1 < p) (H : IntegralLift p)
    (A : Selection (2*p-1+k) (2*p-1)) {g : List Nat}
    (hg : CM (2*p-1) k g) (hl : g.length = p) :
    (p : Int) ∣ embed H A g - (if A.contains g then 1 else 0) := by
  have hn : 0 < 2*p-1 := by omega
  obtain ⟨him, hlen⟩ := CM_image A.perm (idPerm (2*p-1)) hg
  have hs := A.image_small hn hg
  unfold embed relab pad
  by_cases hc : A.contains g
  · rw [if_pos hc, if_pos (hs.mpr hc)]
    exact H.unit _ (small_cm him (hs.mpr hc)) (hlen.trans hl)
  · rw [if_neg hc, if_neg (fun h => hc (hs.mp h))]
    exact Int.dvd_zero _

theorem embed_harmonic {p k : Nat} (hp : 1 < p) (H : IntegralLift p)
    (A : Selection (2*p-1+k) (2*p-1)) :
    Bal 0 (2*p-1) k (embed H A) (fun _ => 0) (p-1) := by
  apply embedded_bal (by omega) H.coeff
  intro g hg hl
  obtain ⟨hr,hc⟩ := H.harmonic g hg hl
  constructor
  · intro i hi hf
    simp only [Nat.add_zero] at hi
    rw [hr i hi hf]
    exact Int.dvd_zero _
  · intro j hj hf
    rw [hc j hj hf]
    exact Int.dvd_zero _

#print axioms embed_unit
#print axioms embed_harmonic
end Programme.«20261102-1249-proof-complexity».UniformC3
