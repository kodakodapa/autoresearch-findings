import Programme.«20261025-0805-proof-complexity».HallM6
import Programme.«20261025-0459b-proof-complexity».HallEnd
import Programme.«20261025-0459b-proof-complexity».Hall

namespace Programme.«20261025-0805-proof-complexity».HallCP

open Programme.«20261024-1633-proof-complexity».CP (val)
open Programme.«20261024-1633-proof-complexity».CPInterp (shared)
open Programme.«20261025-0805-proof-complexity».MApprox Programme.«20261025-0805-proof-complexity».MPluck Programme.«20261025-0805-proof-complexity».MCircuit Programme.«20261025-0805-proof-complexity».HallM6
open Programme.«20261025-0805-proof-complexity».PermCount (arr fact mem_arr arr_length)
open Programme.«20261025-0459b-proof-complexity».Indep Programme.«20261025-0459b-proof-complexity».HallRise Programme.«20261025-0459b-proof-complexity».HallEnd Programme.«20261025-0459b-proof-complexity».Hall

/-! ## th's circuits as pr's circuits -/

theorem mc_rev {V : Type} {P : V → Bool} : ∀ {fs : List ((V → Bool) → Int)},
    Programme.«20261025-0459b-proof-complexity».CPDagInterp.MC P fs → Programme.«20261025-0459b-proof-complexity».CPDagPr.MC P fs.reverse
  | _, .nil => .nil
  | _, .cons hfs hg => by
    have ih := mc_rev hfs
    rw [List.reverse_cons]
    cases hg with
    | const k => exact .const k ih
    | inp u hu => exact .inp u hu ih
    | gate1 g hg hf => exact .gate1 g hg ih (List.mem_reverse.2 hf)
    | gate2 g hg hf hh => exact .gate2 g hg ih (List.mem_reverse.2 hf) (List.mem_reverse.2 hh)

/-! ## Embedding graphs, input approximators -/

def emb (n : Nat) (H : Nat → Nat → Bool) : V → Bool
  | .x i j => H i j && decide (i < n) && decide (j < n)
  | _ => false

def inA (n : Nat) : V → MA
  | .x i j => if i < n ∧ j < n then inpA i j else constA 0
  | _ => constA 0

theorem thr_pos (p ℓ : Nat) (hp : 1 ≤ p) : 1 ≤ thr p ℓ := by
  unfold thr
  exact Nat.mul_pos (Programme.«20261024-1633-proof-complexity».Sunflower.fact_pos _)
    (Nat.pow_pos (Nat.mul_pos hp (Nat.pow_pos (by omega))))

theorem hin (p ℓ n : Nat) (hp : 1 ≤ p) (hℓ : 1 ≤ ℓ) : ∀ u, shared isA isB u = true →
    MInv n ℓ (inA n u) ∧ (inA n u).ents.length ≤ thr p ℓ ∧
      (∀ σ : List Nat, σ.Nodup → val (emb n (pmG σ)) u ≤ eval (inA n u) (pmG σ)) ∧
      (∀ H, eval (inA n u) H ≤ val (emb n H) u) := by
  intro u hu
  cases u with
  | x i j =>
    by_cases hij : i < n ∧ j < n
    · simp only [inA, if_pos hij]
      refine ⟨?_, ?_, fun σ _ => ?_, fun H => ?_⟩
      · intro e he
        simp [inpA] at he; subst he
        simp [isM, hij.1, hij.2]; exact hℓ
      · simp [inpA]; exact thr_pos p ℓ hp
      · rw [inp_eval]; simp [val, emb, hij.1, hij.2]
      · rw [inp_eval]; simp [val, emb, hij.1, hij.2]
    · simp only [inA, if_neg hij]
      refine ⟨fun e he => by simp [constA] at he, by simp [constA], fun σ _ => ?_, fun H => ?_⟩
      · rw [const_eval]
        have : (H : Nat → Nat → Bool) → (H i j && decide (i < n) && decide (j < n)) = false := by
          intro H; by_cases h1 : i < n <;> by_cases h2 : j < n <;> simp_all
        simp [val, emb, this]
      · rw [const_eval]; simp only [val]; split <;> omega
  | _ => simp [shared, isA, isB] at hu

/-! ## The two test distributions -/

theorem pm_ok (n : Nat) (σ : List Nat) (hσ : σ ∈ arr n (List.range n)) : HasPM n (emb n (pmG σ)) := by
  have hl := arr_length hσ
  have hnd := arr_nodup List.nodup_range hσ
  refine ⟨fun i => σ.getD i 0, fun i hi => ?_, fun i i' hi hi' hne h => ?_⟩
  · have hm : σ[i]'(by omega) ∈ σ := List.getElem_mem _
    have := List.mem_range.1 (mem_arr hσ _ hm)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < σ.length),
      Option.getD_some]
    refine ⟨this, ?_⟩
    simp [emb, pmG, hi, this, List.getElem?_eq_getElem (by omega : i < σ.length)]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < σ.length),
      List.getElem?_eq_getElem (by omega : i' < σ.length), Option.getD_some] at h
    exact hne ((List.Nodup.getElem_inj hnd).1 h)

theorem viol_ok (n : Nat) (α : Nat → Bool) (h : viol n α) : HasViolator n (emb n (negG α)) := by
  refine ⟨fun i => α (2 * i), fun j => α (2 * j + 1), fun i j hi hj hS hx => ?_, h⟩
  simp [emb, negG, hi, hj, hS] at hx; exact hx

/-! ## M3 and M5 in the shape of `m6_core` -/

theorem asg_len (n : Nat) : (asg (List.range (2 * n))).length = 2 ^ (2 * n) := by
  simp [asg, ext_length]

theorem g_rise (p ℓ n : Nat) (ev : EvT) (h : MEv p ℓ n ev) :
    ((asg (List.range (2 * n))).filter fun α =>
        decide (Programme.«20261025-0805-proof-complexity».MApprox.pres (negG α) ev.2.1 ∧ ∀ P ∈ ev.2.2, ¬ Programme.«20261025-0805-proof-complexity».MApprox.pres (negG α) P)).length *
      2 ^ (ℓ * p) ≤ (asg (List.range (2 * n))).length * (2 ^ ℓ - 1) ^ p := by
  obtain ⟨C, I, Ps⟩ := ev
  obtain ⟨hnd, hmem, hok⟩ := ev_petals p ℓ n C I Ps h
  have hp : Ps.length = p := h.1
  let Pets : List Petal := Ps.map fun P => ⟨Qp I P, Rp C P⟩
  have hR : Pets.flatMap Petal.R = Ps.flatMap (Rp C) := by simp [Pets, List.flatMap_map]
  have hk := hall_rise_on ℓ (List.range (2 * n)) (baseP n C Ps) Pets List.nodup_range
    (by rw [hR]; exact hnd) (by intro y; rw [hR, List.mem_range]; exact hmem y)
    (by
      intro Pt hPt
      obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hPt
      exact hok P hP)
  have hlen : Pets.length = p := by simp [Pets, hp]
  rw [hlen, List.length_range] at hk
  rw [asg_len]
  refine Nat.le_trans (Nat.mul_le_mul_right _ ?_) hk
  apply cnt_mono
  intro α _ hα Pt hPt
  obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hPt
  exact rise_Q hα.1 (hα.2 P hP)

theorem sub_len : ∀ {L M : List Nat}, L.Nodup → (∀ x ∈ L, x ∈ M) → L.length ≤ M.length
  | [], _, _, _ => by simp
  | a :: L, M, hL, h => by
    obtain ⟨ha, hL'⟩ := List.nodup_cons.1 hL
    have hm : a ∈ M := h a (List.mem_cons_self ..)
    have ih := sub_len (M := M.erase a) hL' fun x hx =>
      (List.mem_erase_of_ne (fun e => ha (by subst e; exact hx))).2 (h x (List.mem_cons_of_mem _ hx))
    rw [List.length_erase_of_mem hm] at ih
    have : 0 < M.length := List.length_pos_of_mem hm
    simp only [List.length_cons]; omega

theorem g_end (ℓ n : Nat) (hℓn : ℓ < n) (P : List (Nat × Nat)) (hnd : P.Nodup) (hM : isM P = true)
    (hl : P.length ≤ ℓ) (hb : ∀ x ∈ P, x.1 < n ∧ x.2 < n) :
    (asg (List.range (2 * n))).length ≤ 2 ^ (4 * ℓ + 3) *
      ((asg (List.range (2 * n))).filter fun α =>
        decide (Programme.«20261025-0805-proof-complexity».MApprox.pres (negG α) P) && decide (viol n α)).length := by
  -- a free left index `u` that is no right endpoint of `P`
  obtain ⟨u, hun, hu⟩ : ∃ u, u < n ∧ u ∉ P.map (·.2) := by
    apply Classical.byContradiction
    intro hc
    have : (List.range n).length ≤ (P.map (·.2)).length :=
      sub_len List.nodup_range fun x hx => by
        apply Classical.byContradiction; intro hx'
        exact hc ⟨x, List.mem_range.1 hx, hx'⟩
    simp at this; omega
  let F := (List.range n).filter fun i => decide (i ∈ P.map (·.1) ∨ i ∈ P.map (·.2) ∨ i = u)
  have hFn : F.Nodup := List.Sublist.nodup List.filter_sublist List.nodup_range
  have mF : ∀ i, i ∈ F ↔ i < n ∧ (i ∈ P.map (·.1) ∨ i ∈ P.map (·.2) ∨ i = u) := by
    intro i; simp [F, List.mem_filter]
  have hFl : F.length ≤ 2 * ℓ + 1 := by
    have := sub_len hFn (M := P.map (·.1) ++ P.map (·.2) ++ [u]) (fun i hi => by
      have := ((mF i).1 hi).2; simp only [List.mem_append, List.mem_singleton]
      rcases this with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h)
    simp at this; omega
  have hk := hall_end n (List.range (2 * n)) List.nodup_range (fun y => List.mem_range) P F u hFn
    (fun i hi => ((mF i).1 hi).1) ((mF u).2 ⟨hun, Or.inr (Or.inr rfl)⟩) (by
      intro e he
      refine ⟨(mF _).2 ⟨(hb e he).1, Or.inl (List.mem_map.2 ⟨e, he, rfl⟩)⟩,
        (mF _).2 ⟨(hb e he).2, Or.inr (Or.inl (List.mem_map.2 ⟨e, he, rfl⟩))⟩, ?_⟩
      intro h; exact hu (h ▸ List.mem_map.2 ⟨e, he, rfl⟩))
  have hc : cnt (asg (List.range (2 * n))) (fun α => Programme.«20261025-0459b-proof-complexity».HallRise.pres (negG α) P ∧ viol n α) =
      ((asg (List.range (2 * n))).filter fun α =>
        decide (Programme.«20261025-0805-proof-complexity».MApprox.pres (negG α) P) && decide (viol n α)).length := by
    unfold cnt; congr 1
  rw [hc] at hk
  rw [List.length_range] at hk
  rw [asg_len]
  refine Nat.le_trans hk (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega)))

/-! ## The assembly -/

/-- **Hall split formula, DAG-like cutting planes.** For `1 ≤ ℓ < n`, `p ≥ 1`, every refutation
`Programme.«20261025-0459b-proof-complexity».CPDag.DRefutation (Hall n)` with `s` lines satisfies, with `E = s(2n+7) ℓ (thr p ℓ + 1)^2`,
`n! ≤ E (n-ℓ-1)!` or `2^{ℓp} ≤ 2^{4ℓ+3} E (2^ℓ-1)^p`. -/
theorem hall_cp (n p ℓ : Nat) (hp : 1 ≤ p) (hℓ : 1 ≤ ℓ) (hℓn : ℓ < n)
    (Rf : Programme.«20261025-0459b-proof-complexity».CPDag.DRefutation (Hall n)) :
    fact n ≤ Rf.size * (2 * n + 7) * (ℓ * (thr p ℓ + 1) ^ 2) * fact (n - (ℓ + 1)) ∨
      2 ^ (ℓ * p) ≤ 2 ^ (4 * ℓ + 3) * (Rf.size * (2 * n + 7) * (ℓ * (thr p ℓ + 1) ^ 2)) *
        (2 ^ ℓ - 1) ^ p := by
  obtain ⟨fs, hfs, hlen, f, hf, hsep⟩ := hall_interp_dag n Rf
  have h := m6_core (shared isA isB) p ℓ n hp hℓ (emb n) (inA n) (hin p ℓ n hp hℓ) (mc_rev hfs) f
    (List.mem_reverse.2 hf) (fun σ hσ => (hsep _).1 (pm_ok n σ hσ))
    (asg (List.range (2 * n))) negG (fun α => decide (viol n α))
    (by rw [asg_len]; exact Nat.pow_pos (by omega))
    (fun α _ hv => (hsep _).2 (viol_ok n α (by simpa using hv)))
    (fun ev hev => g_rise p ℓ n ev hev)
    (fun P h1 h2 h3 h4 => g_end ℓ n hℓn P h1 h2 h3 h4)
  rw [List.length_reverse] at h
  have hE : fs.length * (ℓ * (thr p ℓ + 1) ^ 2) ≤ Rf.size * (2 * n + 7) * (ℓ * (thr p ℓ + 1) ^ 2) :=
    Nat.mul_le_mul_right _ hlen
  rcases h with h | h
  · exact Or.inl (Nat.le_trans h (Nat.mul_le_mul_right _ hE))
  · exact Or.inr (Nat.le_trans h (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hE)))

end Programme.«20261025-0805-proof-complexity».HallCP

#print axioms Programme.«20261025-0805-proof-complexity».HallCP.hall_cp
