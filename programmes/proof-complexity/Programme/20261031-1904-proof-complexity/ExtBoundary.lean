import Programme.«20261026-1402-proof-complexity».SymDesign
import Programme.«20261027-1434-proof-complexity».RowColG

namespace Programme.«20261031-1904-proof-complexity».ExtBoundary
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».SymDesign
open Programme.«20261027-1434-proof-complexity».RowColG
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero)

private theorem free_pigeon {n k : Nat} {g : List Nat} (hl : g.length < n+k) :
    ∃ i < n+k, pfree n g i := by
  apply Classical.byContradiction; intro H
  have hall : ∀ i < n+k, ∃ v ∈ g, v / n = i := by
    intro i hi
    apply Classical.byContradiction; intro h
    exact H ⟨i, hi, fun v hv e => h ⟨v,hv,e⟩⟩
  have hs : List.range (n+k) ⊆ g.map (· / n) := by
    intro i hi
    obtain ⟨v,hv,e⟩ := hall i (List.mem_range.mp hi)
    exact List.mem_map.mpr ⟨v,hv,e⟩
  have := nodup_len _ _ List.nodup_range hs
  simp at this
  omega

private theorem matching_exists (n k : Nat) : ∀ d ≤ n, ∃ g, CM n k g ∧ g.length = d := by
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨[], ⟨?_, ?_⟩, rfl⟩
    · exact List.eq_nil_iff_forall_not_mem.mpr (fun x h => by simp [mem_canon] at h)
    · simp [isMatch]
  | succ d ih =>
    intro hd
    obtain ⟨g,hg,hl⟩ := ih (by omega)
    obtain ⟨i,hi,hfi⟩ := free_pigeon (n := n) (k := k) (g := g) (by omega)
    obtain ⟨j,hj,hfj⟩ := exists_free_hole (n := n) (g := g) (by omega)
    have hc := CM_add hg hi hj hfi hfj
    exact ⟨_,hc.1,by omega⟩

/-- Universal extension fails at the full-board boundary. -/
theorem not_ext_boundary {p n k : Nat} (hp : 1 < p) (hn : 0 < n)
    (hk : 0 < k) (hpk : p ∣ k) : ¬ EXT p n k n := by
  intro hext
  have hb : ∀ e, e+1=n → Bal p n k (fun _ => 1) (fun _ => 1) e := by
    intro e he g hg hl
    refine ⟨?_, ?_⟩
    · intro i hi hf
      rw [rowS_const hn 1 hg hf, hl]
      have hcast : (e : Int) + 1 = n := by exact_mod_cast he
      have hz : ((n : Int) - e) * 1 - 1 = 0 := by omega
      rw [hz]; exact ⟨0, by simp⟩
    · intro j hj hf
      rw [colS_const hn 1 hg hj hf, hl]
      have hcast : (e : Int) + 1 = n := by exact_mod_cast he
      have hz : ((n+k : Nat) - (e : Int)) * 1 - 1 = k := by omega
      rw [hz]
      exact_mod_cast hpk
  obtain ⟨y,hy⟩ := hext (fun _ => 1) (fun _ => 1) hb
  obtain ⟨g,hg,hl⟩ := matching_exists n k n (Nat.le_refl n)
  obtain ⟨i,hi,hfi⟩ := free_pigeon (n := n) (k := k) (g := g) (by omega)
  have hz : rowS n k y g i = 0 := by
    unfold rowS lineS
    have hnone : ∀ j < n, isMatch n (var n i j :: g) = false := by
      intro j hj
      cases hm : isMatch n (var n i j :: g)
      · rfl
      · have hf := match_cons hg.2 hj (notin_of_pfree hfi j hj)
        rw [hm] at hf
        have hh : hfB n g j = true := by
          cases hb : hfB n g j
          · simp only [hb, Bool.and_false] at hf
            cases hf
          · rfl
        have hadd := CM_add hg hi hj hfi (hfB_iff.mp hh)
        have hlen := match_nodup_mod hadd.1
        have hsub : (canon ((n+k)*n) (var n i j :: g)).map (· % n) ⊆ List.range n := by
          intro x hx
          obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
          exact List.mem_range.mpr (Nat.mod_lt _ hn)
        have hbound := nodup_len _ _ hlen hsub
        simp only [List.length_map, List.length_range] at hbound
        omega
    calc
      _ = rsum n (fun _ => (0 : Int)) := rsum_congr n _ _ (fun j hj => by simp [hnone j hj])
      _ = 0 := rsum_zero n _ (by intros; rfl)
  have hbad := (hy g hg hl).1 i hi hfi
  rw [hz] at hbad
  have hone : (p : Int) ∣ 1 := by
    have := Int.dvd_neg.mpr hbad
    simpa using this
  exact Programme.«20261025-1627-proof-complexity».OntoExt2.not_dvd_one hp hone
end Programme.«20261031-1904-proof-complexity».ExtBoundary
#print axioms Programme.«20261031-1904-proof-complexity».ExtBoundary.not_ext_boundary
