import Programme.«20261025-0459-proof-complexity».OntoSubst

/-!
# Blow-up: `(c n, c k) → (n, k)`

Pigeon `P` of `onto-FPHP^{c(n+k)}_{cn}` is the pair `(P / c, P % c)`, hole `J` is `(J / c, J % c)`.
The substitution `y_{P J} := [P % c = J % c] · x_{P/c, J/c}` maps every axiom at `(c n, c k)` to
an axiom at `(n, k)` or to `0`. So a degree-`D` refutation at `(c n, c k)` gives one at `(n, k)`:
lower bounds for `k` transfer to `c k` (with `c = p`, from `p^l` to `p^{l+1}`).
-/

namespace Programme.«20261025-0459-proof-complexity».OntoBlowup

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst

theorem rsum_append (m l : Nat) (f : Nat → Int) :
    rsum (m + l) f = rsum m f + rsum l (fun t => f (m + t)) := by
  induction l with
  | zero => simp [rsum]
  | succ l ih => rw [← Nat.add_assoc]; simp only [rsum]; rw [ih]; omega

theorem rsum_single (c a : Nat) (v : Int) (ha : a < c) :
    rsum c (fun t => if a = t then v else 0) = v := by
  induction c with
  | zero => omega
  | succ c ih =>
    simp only [rsum]
    by_cases hac : a = c
    · rw [rsum_zero c _ (fun t ht => by rw [if_neg (by omega)]), if_pos hac]; omega
    · rw [ih (by omega), if_neg hac]; omega

theorem rsum_block (c a : Nat) (ha : a < c) (f : Nat → Int) :
    ∀ n, rsum (c * n) (fun J => if a = J % c then f (J / c) else 0) = rsum n f
  | 0 => by simp [rsum]
  | n + 1 => by
    rw [Nat.mul_succ, rsum_append, rsum_block c a ha f n]
    simp only [rsum]
    congr 1
    rw [rsum_congr c _ (fun t => if a = t then f n else 0) (fun t ht => by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht,
        Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt ht, Nat.zero_add])]
    exact rsum_single c a _ ha

theorem div_lt_of_mod_eq {c P P' : Nat} (h : P < P') (hm : P % c = P' % c) : P / c < P' / c := by
  have e1 := Nat.div_add_mod P c
  have e2 := Nat.div_add_mod P' c
  apply Nat.lt_of_not_le
  intro hle
  have := Nat.mul_le_mul_left c hle
  omega

theorem div_lt {c x y : Nat} (hc : 0 < c) (h : x < c * y) : x / c < y := by
  rw [Nat.div_lt_iff_lt_mul hc, Nat.mul_comm]; exact h

/-- The blow-up substitution. -/
def σB (c n : Nat) (x : Nat) : Lit :=
  if x / (c * n) % c = x % (c * n) % c then .var (var n (x / (c * n) / c) (x % (c * n) / c))
  else .const false

theorem xv_B (c n P J : Nat) (hJ : J < c * n) (a : Nat → Bool) :
    xv (var (c * n) P J) (pull (σB c n) a) =
      if P % c = J % c then xv (var n (P / c) (J / c)) a else 0 := by
  simp only [xv, pull, σB, var_div _ _ _ hJ, var_mod _ _ _ hJ]
  by_cases h : P % c = J % c <;> simp [h, Lit.val]

/-- Blow-up: for `c > 0`, a degree-`D` refutation of `onto-FPHP^{c(n+k)}_{cn}` gives one of
`onto-FPHP^{n+k}_n`. -/
theorem ontoFPHP_blowup (p c n k D : Nat) (hc : 0 < c) (hD : 1 ≤ D) (hnk : 0 < n + k)
    (h : PPCRefutation p (ontoFPHP (c * n) (c * k)) D) : PPCRefutation p (ontoFPHP n k) D := by
  have hz := zero_der p n k D hD hnk
  have em : c * n + c * k = c * (n + k) := (Nat.mul_add c n k).symm
  refine PPCDerivable.subst (σB c n) hz ?_ h
  intro P hP hPD
  rcases mem_ontoFPHP hP with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ | hcl | hf
  · -- pigeon axiom
    have hi' : i / c < n + k := div_lt hc (by omega)
    have hB := PPCDerivable.ax (p := p) _ (mem_pig (n := n) (k := k) hi')
      (Nat.le_trans (sumOne_deg _ _) hD)
    refine of_eq hB (fun a => ?_)
    rw [sumOne_eval, sumOne_eval]
    rw [rsum_congr (c * n) _ (fun J => if i % c = J % c then xv (var n (i / c) (J / c)) a else 0)
      (fun t ht => xv_B c n i t ht a)]
    rw [rsum_block c (i % c) (Nat.mod_lt _ hc) (fun j => xv (var n (i / c) j) a) n]
  · -- hole axiom
    have hj' : j / c < n := div_lt hc hj
    have hB := PPCDerivable.ax (p := p) _ (mem_hole (n := n) (k := k) hj')
      (Nat.le_trans (sumOne_deg _ _) hD)
    refine of_eq hB (fun a => ?_)
    rw [sumOne_eval, sumOne_eval, em]
    rw [rsum_congr (c * (n + k)) _
      (fun P => if j % c = P % c then xv (var n (P / c) (j / c)) a else 0)
      (fun t _ => by rw [xv_B c n t j hj a]; by_cases h : t % c = j % c <;> simp [h, Ne.symm])]
    rw [rsum_block c (j % c) (Nat.mod_lt _ hc) (fun i => xv (var n i (j / c)) a) (n + k)]
  · -- collision axiom
    obtain ⟨j, i, i', hj, hi, hi', hii, rfl⟩ := mem_collAx.mp hcl
    by_cases h0 : i % c = j % c ∧ i' % c = j % c
    · have hlt := div_lt_of_mod_eq hii (h0.1.trans h0.2.symm)
      have hm : prod2 (var n (i / c) (j / c)) (var n (i' / c) (j / c)) ∈ ontoFPHP n k :=
        mem_coll (mem_collAx.mpr ⟨j / c, i / c, i' / c, div_lt hc hj, div_lt hc (by omega),
          div_lt hc (by omega), hlt, rfl⟩)
      have hB := PPCDerivable.ax (p := p) _ hm (by rw [prod2_deg]; rw [prod2_deg] at hPD; exact hPD)
      refine of_eq hB (fun a => ?_)
      rw [prod2_eval, prod2_eval, xv_B _ _ _ _ hj, xv_B _ _ _ _ hj, if_pos h0.1, if_pos h0.2]
    · refine of_eq hz (fun a => ?_)
      rw [prod2_eval, xv_B _ _ _ _ hj, xv_B _ _ _ _ hj]
      by_cases h1 : i % c = j % c
      · rw [if_neg (fun h2 => h0 ⟨h1, h2⟩)]; simp
      · rw [if_neg h1]; simp
  · -- functional axiom
    obtain ⟨i, j, j', hi, hj, hj', hjj, rfl⟩ := mem_funcAx.mp hf
    by_cases h0 : i % c = j % c ∧ i % c = j' % c
    · have hlt := div_lt_of_mod_eq hjj (h0.1.symm.trans h0.2)
      have hm : prod2 (var n (i / c) (j / c)) (var n (i / c) (j' / c)) ∈ ontoFPHP n k :=
        mem_func (mem_funcAx.mpr ⟨i / c, j / c, j' / c, div_lt hc (by omega), div_lt hc hj,
          div_lt hc hj', hlt, rfl⟩)
      have hB := PPCDerivable.ax (p := p) _ hm (by rw [prod2_deg]; rw [prod2_deg] at hPD; exact hPD)
      refine of_eq hB (fun a => ?_)
      rw [prod2_eval, prod2_eval, xv_B _ _ _ _ hj, xv_B _ _ _ _ hj', if_pos h0.1, if_pos h0.2]
    · refine of_eq hz (fun a => ?_)
      rw [prod2_eval, xv_B _ _ _ _ hj, xv_B _ _ _ _ hj']
      by_cases h1 : i % c = j % c
      · rw [if_neg (fun h2 => h0 ⟨h1, h2⟩)]; simp
      · rw [if_neg h1]; simp


/-- Iterated restriction: `(n + m, k) → (n, k)`. -/
theorem ontoFPHP_restrict_iter (p n k D : Nat) (hD : 1 ≤ D) (hk : 0 < k) :
    ∀ m, PPCRefutation p (ontoFPHP (n + m) k) D → PPCRefutation p (ontoFPHP n k) D
  | 0, h => h
  | m + 1, h => ontoFPHP_restrict_iter p n k D hD hk m
      (ontoFPHP_restrict p (n + m) k D hD (by omega) (by rw [← Nat.add_assoc] at h; exact h))

/-- Lower bounds lift: if `onto-FPHP^{n+k}_n` has no degree-`D` refutation over `Z/p` (`D ≥ 1`,
`k, c > 0`), then for every `n' ≥ c n`, `onto-FPHP^{n'+ck}_{n'}` has none either. -/
theorem ontoFPHP_lift (p c n k D : Nat) (hc : 0 < c) (hk : 0 < k) (hD : 1 ≤ D)
    (hlow : ¬ PPCRefutation p (ontoFPHP n k) D) (n' : Nat) (hn' : c * n ≤ n') :
    ¬ PPCRefutation p (ontoFPHP n' (c * k)) D := by
  intro h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn'
  have hck : 0 < c * k := Nat.mul_pos hc hk
  exact hlow (ontoFPHP_blowup p c n k D hc hD (by omega)
    (ontoFPHP_restrict_iter p (c * n) (c * k) D hD hck m h))

end Programme.«20261025-0459-proof-complexity».OntoBlowup

#print axioms Programme.«20261025-0459-proof-complexity».OntoBlowup.ontoFPHP_blowup
#print axioms Programme.«20261025-0459-proof-complexity».OntoSubst.ontoFPHP_restrict
#print axioms Programme.«20261025-0459-proof-complexity».OntoBlowup.ontoFPHP_lift
