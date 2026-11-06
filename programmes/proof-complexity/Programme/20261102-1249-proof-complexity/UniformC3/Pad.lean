import Programme.«20261102-1249-proof-complexity».UniformC3.Boundary

namespace Programme.«20261102-1249-proof-complexity».UniformC3
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».Relabel
open Programme.«20261025-1627-proof-complexity».MomGen (canon mem_canon)
open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum var)
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero var_div)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt)

theorem canon_bound {N M : Nat} (h : N ≤ M) (g : List Nat)
    (hb : ∀ v ∈ g, v < N) : canon M g = canon N g := by
  obtain ⟨r,rfl⟩ : ∃ r, M = N+r := ⟨M-N, by omega⟩
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.add_succ, canon, if_neg (by intro hv; have := hb (N+r) hv; omega)]
    exact ih (by omega)

theorem small_cm {n k : Nat} {g : List Nat} (hg : CM n k g)
    (hb : ∀ v ∈ g, v < n*n) : CM n 0 g := by
  refine ⟨?_, hg.2⟩
  simpa using (canon_bound (by exact Nat.mul_le_mul_right n (Nat.le_add_right n k)) g hb).symm.trans hg.1

def pad (n : Nat) (H : List Nat → Int) (g : List Nat) : Int :=
  if ∀ v ∈ g, v < n*n then H g else 0

theorem pad_term_bad {n k : Nat} (H : List Nat → Int) {g : List Nat}
    (hg : CM n k g) (hb : ¬ ∀ v ∈ g, v < n*n) {v : Nat}
    (hv : v < (n+k)*n) : pad n H (canon ((n+k)*n) (v::g)) = 0 := by
  apply if_neg
  intro h
  apply hb
  intro w hw
  exact h w ((mem_canon _ _ _).mpr ⟨List.mem_cons_of_mem _ hw, CM_lt hg hw⟩)

theorem pad_line_bad {n k : Nat} (H : List Nat → Int) {g : List Nat}
    (hg : CM n k g) (hb : ¬ ∀ v ∈ g, v < n*n)
    (v : Nat → Nat) (M : Nat) (hv : ∀ t < M, v t < (n+k)*n) :
    lineS n k (pad n H) g v M = 0 := by
  apply rsum_zero
  intro t ht
  rw [pad_term_bad H hg hb (hv t ht)]
  split <;> rfl

theorem pad_term_small {n k : Nat} (H : List Nat → Int) {g : List Nat}
    (hb : ∀ v ∈ g, v < n*n) {v : Nat} (hv : v < n*n) :
    pad n H (canon ((n+k)*n) (v::g)) = H (canon (n*n) (v::g)) := by
  have hsmall : ∀ w ∈ v::g, w < n*n := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hv
    · exact hb w hw
  rw [canon_bound (Nat.mul_le_mul_right n (Nat.le_add_right n k)) _ hsmall]
  apply if_pos
  intro w hw
  exact ((mem_canon _ _ _).mp hw).2

theorem pad_term_outside {n k : Nat} (H : List Nat → Int) (g : List Nat)
    {v : Nat} (hv : v < (n+k)*n) (ho : n*n ≤ v) :
    pad n H (canon ((n+k)*n) (v::g)) = 0 := by
  apply if_neg
  intro h
  have := h v ((mem_canon _ _ _).mpr ⟨List.mem_cons_self,hv⟩)
  omega

theorem rsum_cut (N K : Nat) (f : Nat → Int) (hz : ∀ i, N ≤ i → i < N+K → f i = 0) :
    rsum (N+K) f = rsum N f := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.add_succ, rsum, hz (N+K) (by omega) (by omega), Int.add_zero]
    exact ih (fun i h1 h2 => hz i h1 (by omega))

theorem pad_bal {n k d : Nat} (hn : 0 < n) (H : List Nat → Int)
    (hH : Bal 0 n 0 H (fun _ => 0) d) :
    Bal 0 n k (pad n H) (fun _ => 0) d := by
  intro g hg hl
  by_cases hb : ∀ v ∈ g, v < n*n
  · have hs := hH g (small_cm hg hb) hl
    constructor
    · intro i hi hf
      by_cases hin : i < n
      · have he : rowS n k (pad n H) g i = rowS n 0 H g i := by
          unfold rowS lineS
          apply rsum_congr
          intro j hj
          rw [pad_term_small H hb (by simpa using var_lt n 0 i j (by simpa using hin) hj)]
          simp
        rw [he]
        exact hs.1 i (by simpa using hin) hf
      · have he : rowS n k (pad n H) g i = 0 := by
          apply rsum_zero
          intro j hj
          rw [pad_term_outside H g (var_lt n k i j hi hj) (by
            unfold var
            exact Nat.le_trans (Nat.mul_le_mul_right n (by omega)) (Nat.le_add_right _ _))]
          split <;> rfl
        simp [he]
    · intro j hj hf
      have he : colS n k (pad n H) g j = colS n 0 H g j := by
        unfold colS lineS
        rw [rsum_cut n k _ (by
          intro i hi hi'
          rw [pad_term_outside H g (var_lt n k i j hi' hj) (by
            unfold var
            exact Nat.le_trans (Nat.mul_le_mul_right n hi) (Nat.le_add_right _ _))]
          split <;> rfl)]
        simp only [Nat.add_zero]
        apply rsum_congr
        intro i hi
        rw [pad_term_small H hb (by simpa using var_lt n 0 i j (by simpa using hi) hj)]
      rw [he]
      exact hs.2 j hj hf
  · constructor
    · intro i hi _
      rw [rowS, pad_line_bad H hg hb _ _ (fun j hj => var_lt n k i j hi hj)]
      simp
    · intro j hj _
      rw [colS, pad_line_bad H hg hb _ _ (fun i hi => var_lt n k i j hi hj)]
      simp

def idPerm (m : Nat) : Perm m where
  f := id
  g := id
  f_lt := fun _ h => h
  g_lt := fun _ h => h
  gf := fun _ _ => rfl
  fg := fun _ _ => rfl

/-- One padded and row-relabelled square harmonic lift is harmonic exactly. -/
theorem embedded_bal {n k d : Nat} (hn : 0 < n) (H : List Nat → Int)
    (hH : Bal 0 n 0 H (fun _ => 0) d) (σ : Perm (n+k)) :
    Bal 0 n k (relab σ (idPerm n) (pad n H)) (fun _ => 0) d := by
  exact bal_relab σ (idPerm n) (pad_bal hn H hH)

#print axioms pad_bal
#print axioms embedded_bal
end Programme.«20261102-1249-proof-complexity».UniformC3
