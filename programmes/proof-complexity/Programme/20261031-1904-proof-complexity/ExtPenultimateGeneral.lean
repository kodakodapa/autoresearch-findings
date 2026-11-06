import Programme.«20261031-1904-proof-complexity».ExtPenultimate

namespace Programme.«20261031-1904-proof-complexity».ExtPenultimateGeneral
open Programme.«20261031-1904-proof-complexity».ExtPenultimate
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».SymDesign
open Programme.«20261027-1434-proof-complexity».RowColG
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoSubst (var_div var_mod rsum_congr)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt rsum_pick)

private theorem inside_exists (n k : Nat) : ∀ d ≤ n, ∃ g,
    CM n k g ∧ g.length = d ∧ (∀ v ∈ g, v / n < n) := by
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨[], ⟨?_, ?_⟩, rfl, by simp⟩
    · exact List.eq_nil_iff_forall_not_mem.mpr (fun x h => by simp [mem_canon] at h)
    · simp [isMatch]
  | succ d ih =>
    intro hd
    obtain ⟨g,hg,hl,hs⟩ := ih (by omega)
    obtain ⟨hi,hfi⟩ := fp_free (n := n) (k := 0) (g := g) (by omega)
    let i := fp n 0 g
    obtain ⟨j,hj,hfj⟩ := exists_free_hole (n := n) (g := g) (by omega)
    have hi' : i < n+k := by dsimp [i]; omega
    obtain ⟨hc,hcl,-,-⟩ := CM_add hg hi' hj hfi hfj
    refine ⟨_,hc,by omega,?_⟩
    intro v hv
    rw [mem_canon] at hv
    rcases List.mem_cons.mp hv.1 with rfl | hv
    · rw [var_div n i j hj]; dsimp [i]; omega
    · exact hs v hv

private theorem unique_hole {n k : Nat} {g : List Nat} (hg : CM n k g)
    (hl : g.length = n-1) {j t : Nat} (hj : j < n) (ht : t < n)
    (hjf : hfree n g j) (htf : hfree n g t) : t = j := by
  apply Classical.byContradiction; intro hne
  have hnd : (t :: j :: g.map (· % n)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, match_nodup_mod hg⟩⟩
    · simp only [List.mem_cons, List.mem_map]
      rintro (h | ⟨v,hv,he⟩)
      · exact hne h
      · exact htf v hv he
    · intro h
      obtain ⟨v,hv,he⟩ := List.mem_map.mp h
      exact hjf v hv he
  have hsub : t :: j :: g.map (· % n) ⊆ List.range n := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_range.mpr ht
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_range.mpr hj
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr (Nat.mod_lt _ (by omega))
  have hb := nodup_len _ _ hnd hsub
  simp only [List.length_cons, List.length_map, List.length_range] at hb
  omega

private theorem singleton_row {n k : Nat} {g : List Nat} (hg : CM n k g)
    (hl : g.length = n-1) {i j : Nat} (hj : j < n)
    (hpi : pfree n g i) (hhj : hfree n g j) (y : List Nat → Int) :
    rowS n k y g i = y (canon ((n+k)*n) (var n i j :: g)) := by
  unfold rowS lineS
  calc
    _ = rsum n (fun t => if t = j then y (canon ((n+k)*n) (var n i t :: g)) else 0) := by
      apply rsum_congr
      intro t ht
      rw [match_cons hg.2 ht (notin_of_pfree hpi t ht), pfB_iff.mpr hpi, Bool.true_and]
      by_cases he : t = j
      · subst t; simp [hfB_iff.mpr hhj]
      · have hn : hfB n g t = false := by
          cases hb : hfB n g t
          · rfl
          · exact False.elim (he (unique_hole hg hl hj ht hhj (hfB_iff.mp hb)))
        simp [hn,he]
    _ = _ := by rw [rsum_pick]; simp [hj]

theorem opposite_faces {n k : Nat} (hn : 2 ≤ n) (hk : 0 < k) :
    OppositeFaces n k := by
  classical
  obtain ⟨g,hg,hl,hs⟩ := inside_exists n k (n-2) (by omega)
  obtain ⟨hi,hfi⟩ := fp_free (n := n) (k := 0) (g := g) (by omega)
  let i := fp n 0 g
  have hin : i < n := by dsimp [i]; omega
  have hi' : i < n+k := by omega
  obtain ⟨j,hj,hfj⟩ := exists_free_hole (n := n) (g := g) (by omega)
  let a := canon ((n+k)*n) (var n i j :: g)
  obtain ⟨ha,hal,-,-⟩ := CM_add hg hi' hj hfi hfj
  have hal' : a.length = n-1 := by dsimp [a]; omega
  have hlt : ∀ x ∈ var n i j :: g, x < (n+k)*n := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact var_lt n k i j hi' hj
    · exact CM_lt hg hx
  have hsa : ∀ v ∈ a, v / n < n := by
    intro v hv
    rw [mem_canon' hlt] at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · rw [var_div n i j hj]; exact hin
    · exact hs v hv
  obtain ⟨t,ht,hft⟩ := exists_free_hole (n := n) (g := a) (by omega)
  have hftg : hfree n g t := by
    intro v hv
    apply hft v
    exact (mem_canon' hlt _).mpr (List.mem_cons_of_mem _ hv)
  have htj : t ≠ j := by
    intro he
    have hh := hft (var n i j) ((mem_canon' hlt _).mpr (List.mem_cons_self ..))
    exact hh (by rw [var_mod n i j hj]; exact he.symm)
  have hfn : pfree n g n := by
    intro v hv he
    have := hs v hv
    omega
  have hfn_a : pfree n a n := by
    intro v hv he
    have := hsa v hv
    omega
  have hn' : n < n+k := by omega
  let b := canon ((n+k)*n) (var n n t :: g)
  obtain ⟨hb,hbl,-,-⟩ := CM_add hg hn' ht hfn hftg
  have hbl' : b.length = n-1 := by dsimp [b]; omega
  have hltb : ∀ x ∈ var n n t :: g, x < (n+k)*n := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact var_lt n k n t hn' ht
    · exact CM_lt hg hx
  have hfib : pfree n b i := pfree_add ht hfi (by omega) hltb
  have hfjb : hfree n b j := hfree_add ht hfj htj hltb
  have hfa : F n a = 1 := by
    simp only [F, List.all_eq_true, decide_eq_true_eq]
    exact ite_eq_left hsa
  have hfb : F n b = 0 := by
    have hbad : ¬ (∀ v ∈ b, v / n < n) := by
      intro hh
      have hh' := hh (var n n t) ((mem_canon' hltb _).mpr (List.mem_cons_self ..))
      rw [var_div n n t ht] at hh'
      omega
    simp only [F, List.all_eq_true, decide_eq_true_eq]
    exact ite_eq_right hbad
  refine ⟨a,b,canon ((n+k)*n) (var n n t :: a),n,i,
    ha,hb,hal',hbl',hn',hi',hfn_a,hfib,hfa,hfb,?_,?_⟩
  · intro y
    exact singleton_row ha hal' ht hfn_a hft y
  · intro y
    rw [singleton_row hb hbl' hj hfib hfjb y]
    dsimp [a,b]
    rw [canon_cons_canon,canon_cons_canon,canon_swap2]

/-- The canonical universal extension property fails one level below a full board. -/
theorem not_ext_penultimate {n k : Nat} (hn : 2 ≤ n) (hk : 0 < k) :
    ¬ EXT 2 n k (n-1) :=
  not_ext_of_faces hn (opposite_faces hn hk)

end Programme.«20261031-1904-proof-complexity».ExtPenultimateGeneral
#print axioms Programme.«20261031-1904-proof-complexity».ExtPenultimateGeneral.opposite_faces
#print axioms Programme.«20261031-1904-proof-complexity».ExtPenultimateGeneral.not_ext_penultimate
