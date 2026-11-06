import Programme.«20261025-0805-proof-complexity».MCircuit
import Programme.«20261025-0805-proof-complexity».PermCount

/-!
# The output-gate step for the Hall plan (M6 of P88)

`m6_core`: for a monotone real circuit `fs` and a gate `f` that is `≥ 1` on every perfect matching
`pmG σ` (`σ ∈ arr n (range n)`) and `≤ 0` on the negative test graphs `G α` (`α ∈ A`, `viol α`),
the approximation `Work.MCircuit.mapproxC` forces, with `E = |fs| ℓ (B+1)^2`, `B = thr p ℓ`,

* `n! ≤ E (n-ℓ-1)!` (positive errors cover all perfect matchings, by M4 `pm_count`), or
* `2^{ℓp} ≤ 2^{4ℓ+3} E (2^ℓ-1)^p` (the pluck events cover the many negatives on which a short
  matching is present).

The two probabilistic facts about the negatives are hypotheses in the shape of th's M3
(`Programme.«20261025-0459b-proof-complexity».HallEnd.hall_rise_on`, rise bound for one event) and M5 (`Programme.«20261025-0459b-proof-complexity».HallEnd.hall_end`). The
assignment list `A`, the graph map `G` and `viol` are abstract here; for the Hall plan they are
`asg U`, `negG` and `viol n`.

`ev_petals`: the residual petals `(P_j \ I, vs P_j \ C)` of an event `MEv p ℓ n (C, I, Ps)`, with
base `{y < 2n} \ ⋃ R_j`, satisfy the hypotheses of `hall_rise_on` (written out, th's `Ok`), and
a rise (inner edges present, no petal present) leaves every residual matching absent.
-/

namespace Programme.«20261025-0805-proof-complexity».HallM6

open Programme.«20261025-0805-proof-complexity».MApprox
open Programme.«20261025-0805-proof-complexity».MPluck
open Programme.«20261025-0805-proof-complexity».MCircuit
open Programme.«20261025-0805-proof-complexity».PermCount (fitsP arr fact pm_count arr_full mem_arr)
open Programme.«20261025-0459b-proof-complexity».CPDagPr (MC)
open Programme.«20261024-1633-proof-complexity».CP (val)

/-! ## Counting helpers -/

theorem filter_split {X : Type} (q r : X → Bool) : ∀ L : List X,
    (L.filter q).length ≤ (L.filter r).length + (L.filter fun x => q x && !r x).length
  | [] => by simp
  | x :: L => by
    have ih := filter_split q r L
    simp only [List.filter_cons]
    cases hq : q x <;> cases hr : r x <;> simp <;> omega

/-- A union bound: if every `q`-element satisfies `r y` for some `y ∈ Ys`. -/
theorem union_bound {X Y : Type} (r : Y → X → Bool) (L : List X) :
    ∀ (Ys : List Y) (q : X → Bool), (∀ x ∈ L, q x = true → ∃ y ∈ Ys, r y x = true) →
    (L.filter q).length ≤ (Ys.map fun y => (L.filter (r y)).length).sum
  | [], q, h => by
    have : L.filter q = [] := List.filter_eq_nil_iff.2 fun x hx hq => by
      obtain ⟨y, hy, _⟩ := h x hx (by simpa using hq); simp at hy
    simp [this]
  | y :: Ys, q, h => by
    have ih := union_bound r L Ys (fun x => q x && !r y x) (by
      intro x hx hq
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hq
      obtain ⟨z, hz, hrz⟩ := h x hx hq.1
      rcases List.mem_cons.1 hz with rfl | hz
      · rw [hq.2] at hrz; cases hrz
      · exact ⟨z, hz, hrz⟩)
    have := filter_split q (r y) L
    simp only [List.map_cons, List.sum_cons]; omega

theorem sum_le_mul {Y : Type} (g : Y → Nat) (K C : Nat) :
    ∀ Ys : List Y, (∀ y ∈ Ys, g y * K ≤ C) → (Ys.map g).sum * K ≤ Ys.length * C
  | [], _ => by simp
  | y :: Ys, h => by
    have ih := sum_le_mul g K C Ys fun z hz => h z (List.mem_cons_of_mem _ hz)
    have hy := h y (List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.succ_mul]; omega

theorem fact_pos : ∀ n, 0 < fact n
  | 0 => by simp [fact]
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

theorem fact_mono : ∀ {a b : Nat}, a ≤ b → fact a ≤ fact b
  | a, 0, h => by rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | a, b + 1, h => by
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · have := fact_mono (Nat.le_of_lt_succ h)
      have : fact b ≤ (b + 1) * fact b := Nat.le_mul_of_pos_left _ (Nat.succ_pos b)
      simp only [fact]; omega
    · exact Nat.le_refl _

theorem arr_nodup : ∀ {k : Nat} {L σ : List Nat}, L.Nodup → σ ∈ arr k L → σ.Nodup
  | 0, L, σ, _, h => by simp [arr] at h; subst h; simp
  | k + 1, L, σ, hL, h => by
    simp only [arr, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a, -, τ, hτ, rfl⟩ := h
    refine List.nodup_cons.2 ⟨fun ha => ?_, arr_nodup (hL.erase a) hτ⟩
    exact (List.Nodup.not_mem_erase hL) (mem_arr hτ a ha)

/-! ## M6 -/

/-- **M6 (output gate).** With `E = |fs| ℓ (B+1)^2`, `B = thr p ℓ`: a gate `≥ 1` on all perfect
matchings and `≤ 0` on the violators of `A` forces `n! ≤ E (n-ℓ-1)!` or
`2^{ℓp} ≤ 2^{4ℓ+3} E (2^ℓ-1)^p`, given the rise bound `hrise` (M3 shape) and the endgame count
`hend` (M5 shape). -/
theorem m6_core {V X : Type} (Q : V → Bool) (p ℓ n : Nat) (hp : 1 ≤ p) (hℓ : 1 ≤ ℓ)
    (emb : (Nat → Nat → Bool) → V → Bool) (inA : V → MA)
    (hin : ∀ u, Q u = true → MInv n ℓ (inA u) ∧ (inA u).ents.length ≤ thr p ℓ ∧
      (∀ σ : List Nat, σ.Nodup → val (emb (pmG σ)) u ≤ eval (inA u) (pmG σ)) ∧
      (∀ H, eval (inA u) H ≤ val (emb H) u))
    {fs : List ((V → Bool) → Int)} (hfs : MC Q fs) (f : (V → Bool) → Int) (hf : f ∈ fs)
    (hpos : ∀ σ ∈ arr n (List.range n), 1 ≤ f (emb (pmG σ)))
    (A : List X) (G : X → Nat → Nat → Bool) (viol : X → Bool) (hA : 0 < A.length)
    (hneg : ∀ α ∈ A, viol α = true → f (emb (G α)) ≤ 0)
    (hrise : ∀ ev, MEv p ℓ n ev →
      (A.filter fun α => decide (pres (G α) ev.2.1 ∧ ∀ P ∈ ev.2.2, ¬ pres (G α) P)).length *
        2 ^ (ℓ * p) ≤ A.length * (2 ^ ℓ - 1) ^ p)
    (hend : ∀ P : List (Nat × Nat), P.Nodup → isM P = true → P.length ≤ ℓ →
      (∀ x ∈ P, x.1 < n ∧ x.2 < n) →
      A.length ≤ 2 ^ (4 * ℓ + 3) * (A.filter fun α => decide (pres (G α) P) && viol α).length) :
    fact n ≤ fs.length * (ℓ * (thr p ℓ + 1) ^ 2) * fact (n - (ℓ + 1)) ∨
      2 ^ (ℓ * p) ≤ 2 ^ (4 * ℓ + 3) * (fs.length * (ℓ * (thr p ℓ + 1) ^ 2)) * (2 ^ ℓ - 1) ^ p := by
  obtain ⟨pe, ne, hpe, hne, hpeM, hneM, hgood⟩ := mapproxC Q p ℓ n hp hℓ emb inA hin hfs
  obtain ⟨a, haI, -, hapos, haneg⟩ := hgood f hf
  generalize fs.length * (ℓ * (thr p ℓ + 1) ^ 2) = E at hpe hne ⊢
  -- positive side
  by_cases hall : ∀ σ ∈ arr n (List.range n), ∃ P ∈ pe, fitsP P σ = true
  · left
    have hu := union_bound (fun P σ => fitsP P σ) (arr n (List.range n)) pe (fun _ => true)
      (fun σ hσ _ => hall σ hσ)
    rw [List.filter_eq_self.2 (fun _ _ => rfl), arr_full] at hu
    have hs := sum_le_mul (fun P => ((arr n (List.range n)).filter (fitsP P)).length) 1
      (fact (n - (ℓ + 1))) pe (by
        intro P hP
        obtain ⟨hM, hlen, hb⟩ := hpeM P hP
        simp only [isM, decide_eq_true_eq] at hM
        rw [Nat.mul_one, pm_count n P hM.1 hM.2 hb]
        exact fact_mono (by omega))
    rw [Nat.mul_one] at hs
    exact Nat.le_trans hu (Nat.le_trans hs (Nat.mul_le_mul_right _ hpe))
  right
  obtain ⟨σ, hσ, hfit⟩ : ∃ σ ∈ arr n (List.range n), ∀ P ∈ pe, fitsP P σ = false := by
    apply Classical.byContradiction; intro hc; apply hall; intro σ hσ
    apply Classical.byContradiction; intro hc2; apply hc
    refine ⟨σ, hσ, fun P hP => ?_⟩
    cases h : fitsP P σ
    · rfl
    · exact absurd ⟨P, hP, h⟩ hc2
  have hσn : σ.Nodup := arr_nodup List.nodup_range hσ
  have h1 : 1 ≤ eval a (pmG σ) := by
    rcases hapos σ hσn with h | ⟨P, hP, hfP⟩
    · exact Int.le_trans (hpos σ hσ) h
    · rw [hfit P hP] at hfP; cases hfP
  obtain ⟨e, he, hpe1, hev⟩ := eval_attain a (pmG σ)
  rw [hev] at h1
  have heok : e.1.Nodup ∧ isM e.1 = true ∧ e.1.length ≤ ℓ ∧ ∀ x ∈ e.1, x.1 < n ∧ x.2 < n := by
    rcases List.mem_cons.1 he with rfl | he
    · simp [isM]
    · exact haI e he
  have hE := hend e.1 heok.1 heok.2.1 heok.2.2.1 heok.2.2.2
  -- negative side: every good assignment is in a rise event
  have hu := union_bound
    (fun ev α => decide (pres (G α) ev.2.1 ∧ ∀ P ∈ ev.2.2, ¬ pres (G α) P)) A ne
    (fun α => decide (pres (G α) e.1) && viol α) (by
      intro α hα hq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
      have hge : (1 : Int) ≤ eval a (G α) := Int.le_trans h1 (eval_ent he hq.1)
      have hle := hneg α hα hq.2
      rcases haneg (G α) with h | ⟨ev, hev, hE⟩
      · omega
      · exact ⟨ev, hev, by simpa using hE⟩)
  have hs := sum_le_mul
    (fun ev => (A.filter fun α => decide (pres (G α) ev.2.1 ∧ ∀ P ∈ ev.2.2, ¬ pres (G α) P)).length)
    (2 ^ (ℓ * p)) (A.length * (2 ^ ℓ - 1) ^ p) ne (fun ev hev => hrise ev (hneM ev hev))
  have k1 : A.length * 2 ^ (ℓ * p) ≤ A.length * (2 ^ (4 * ℓ + 3) * E * (2 ^ ℓ - 1) ^ p) := by
    calc A.length * 2 ^ (ℓ * p)
        ≤ 2 ^ (4 * ℓ + 3) * (A.filter fun α => decide (pres (G α) e.1) && viol α).length *
            2 ^ (ℓ * p) := Nat.mul_le_mul_right _ hE
      _ ≤ 2 ^ (4 * ℓ + 3) * ((ne.map fun ev => (A.filter fun α =>
            decide (pres (G α) ev.2.1 ∧ ∀ P ∈ ev.2.2, ¬ pres (G α) P)).length).sum * 2 ^ (ℓ * p)) := by
          rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hu)
      _ ≤ 2 ^ (4 * ℓ + 3) * (ne.length * (A.length * (2 ^ ℓ - 1) ^ p)) :=
          Nat.mul_le_mul_left _ hs
      _ ≤ 2 ^ (4 * ℓ + 3) * (E * (A.length * (2 ^ ℓ - 1) ^ p)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hne)
      _ = A.length * (2 ^ (4 * ℓ + 3) * E * (2 ^ ℓ - 1) ^ p) := by
          simp only [Nat.mul_assoc, Nat.mul_left_comm]
  exact Nat.le_of_mul_le_mul_left k1 hA

/-! ## Events as th's petals (input of `Programme.«20261025-0459b-proof-complexity».HallEnd.hall_rise_on`) -/

/-- Residual matching of a petal: the edges outside the inner matching `I`. -/
def Qp (I P : List (Nat × Nat)) : List (Nat × Nat) := P.filter fun e => decide (e ∉ I)

/-- Residue of a petal: its vertex coordinates outside the core `C`. -/
def Rp (C : List Nat) (P : List (Nat × Nat)) : List Nat := (vs P).filter fun y => decide (y ∉ C)

/-- The base: all coordinates `< 2n` in no residue. -/
def baseP (n : Nat) (C : List Nat) (Ps : List (List (Nat × Nat))) : List Nat :=
  (List.range (2 * n)).filter fun y => decide (∀ P ∈ Ps, y ∉ Rp C P)

theorem nodup_flatMap' {X Y : Type} (f : X → List Y) : ∀ l : List X, (∀ x ∈ l, (f x).Nodup) →
    l.Pairwise (fun a b => ∀ y, y ∈ f a → y ∉ f b) → (l.flatMap f).Nodup
  | [], _, _ => by simp
  | a :: l, h1, h2 => by
    rw [List.flatMap_cons]
    obtain ⟨h2a, h2l⟩ := List.pairwise_cons.1 h2
    refine List.nodup_append.2 ⟨h1 a (List.mem_cons_self ..),
      nodup_flatMap' f l (fun x hx => h1 x (List.mem_cons_of_mem _ hx)) h2l, ?_⟩
    intro y hy z hz hyz
    subst hyz
    obtain ⟨b, hb, hzb⟩ := List.mem_flatMap.1 hz
    exact h2a b hb y hy hzb

theorem vs_nodup : ∀ {P : List (Nat × Nat)}, isM P = true → (vs P).Nodup
  | [], _ => by simp [vs]
  | e :: P, h => by
    simp only [isM, decide_eq_true_eq, List.map_cons, List.nodup_cons] at h
    obtain ⟨⟨h1, h1'⟩, h2, h2'⟩ := h
    have hP : isM P = true := by simp [isM, h1', h2']
    have ih := vs_nodup hP
    have hv : vs (e :: P) = (2 * e.1) :: (2 * e.2 + 1) :: vs P := by simp [vs]
    rw [hv]
    refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, ih⟩⟩
    · intro hm
      rcases List.mem_cons.1 hm with h | h
      · omega
      obtain ⟨e', he', hx | hx⟩ := mem_vs.1 h
      · exact h1 (List.mem_map.2 ⟨e', he', by omega⟩)
      · omega
    · intro hm
      obtain ⟨e', he', hx | hx⟩ := mem_vs.1 hm
      · omega
      · exact h2 (List.mem_map.2 ⟨e', he', by omega⟩)

/-- **Events as petals.** For an event `MEv p ℓ n (C, I, Ps)`, the petals `(Qp I P, Rp C P)`,
`P ∈ Ps`, with base `baseP n C Ps`: residues and base are duplicate-free and pairwise disjoint,
together they list exactly the coordinates `< 2n`, and every petal satisfies th's
`Programme.«20261025-0459b-proof-complexity».HallRise.Ok ℓ base` (spelled out). -/
theorem ev_petals (p ℓ n : Nat) (C : List Nat) (I : List (Nat × Nat)) (Ps : List (List (Nat × Nat)))
    (h : MEv p ℓ n (C, I, Ps)) :
    (baseP n C Ps ++ Ps.flatMap (Rp C)).Nodup ∧
    (∀ y, y < 2 * n ↔ y ∈ baseP n C Ps ++ Ps.flatMap (Rp C)) ∧
    ∀ P ∈ Ps, let Q := Qp I P; let R := Rp C P; let base := baseP n C Ps;
      Q.Nodup ∧ R.Nodup ∧ Q.length ≤ ℓ ∧
      (∀ e ∈ Q, ∀ e' ∈ Q, e.1 = e'.1 → e = e') ∧ (∀ e ∈ Q, ∀ e' ∈ Q, e.2 = e'.2 → e = e') ∧
      (∀ e ∈ Q, (2 * e.1 ∈ base ∨ 2 * e.1 ∈ R) ∧ (2 * e.2 + 1 ∈ base ∨ 2 * e.2 + 1 ∈ R)) ∧
      (∀ e ∈ Q, 2 * e.1 ∈ R ∨ 2 * e.2 + 1 ∈ R) := by
  obtain ⟨-, -, -, hP, hpw⟩ := h
  have mR : ∀ {P y}, y ∈ Rp C P ↔ y ∈ vs P ∧ y ∉ C := by
    intro P y; simp [Rp, List.mem_filter]
  have mB : ∀ {y}, y ∈ baseP n C Ps ↔ y < 2 * n ∧ ∀ P ∈ Ps, y ∉ Rp C P := by
    intro y; simp [baseP, List.mem_filter]
  have mQ : ∀ {P e}, e ∈ Qp I P ↔ e ∈ P ∧ e ∉ I := by
    intro P e; simp [Qp, List.mem_filter]
  have vlt : ∀ P ∈ Ps, ∀ y ∈ vs P, y < 2 * n := by
    intro P hPm y hy
    obtain ⟨e, he, hx | hx⟩ := mem_vs.1 hy
    · have := ((hP P hPm).2.2.2.1 e he).1; omega
    · have := ((hP P hPm).2.2.2.1 e he).2; omega
  refine ⟨List.nodup_append.2 ⟨List.Sublist.nodup List.filter_sublist List.nodup_range,
      nodup_flatMap' _ Ps (fun P hPm => List.Sublist.nodup List.filter_sublist
        (vs_nodup (hP P hPm).2.1)) (hpw.imp fun {P P'} hc y hy hy' =>
          (mR.1 hy).2 (hc y (mR.1 hy).1 (mR.1 hy').1)), ?_⟩, fun y => ⟨fun hy => ?_, fun hy => ?_⟩,
      fun P hPm => ?_⟩
  · intro y hy z hz hyz
    subst hyz
    obtain ⟨P, hPm, hzP⟩ := List.mem_flatMap.1 hz
    exact (mB.1 hy).2 P hPm hzP
  · by_cases hr : ∃ P ∈ Ps, y ∈ Rp C P
    · obtain ⟨P, hPm, hyP⟩ := hr
      exact List.mem_append_right _ (List.mem_flatMap.2 ⟨P, hPm, hyP⟩)
    · exact List.mem_append_left _ (mB.2 ⟨hy, fun P hPm hyP => hr ⟨P, hPm, hyP⟩⟩)
  · rcases List.mem_append.1 hy with hy | hy
    · exact (mB.1 hy).1
    · obtain ⟨P, hPm, hyP⟩ := List.mem_flatMap.1 hy
      exact vlt P hPm y (mR.1 hyP).1
  · obtain ⟨hnd, hM, hlen, hb, -, -, hout⟩ := hP P hPm
    simp only [isM, decide_eq_true_eq] at hM
    have side : ∀ y ∈ vs P, y ∈ baseP n C Ps ∨ y ∈ Rp C P := by
      intro y hy
      by_cases hC : y ∈ C
      · exact Or.inl (mB.2 ⟨vlt P hPm y hy, fun P' _ hy' => (mR.1 hy').2 hC⟩)
      · exact Or.inr (mR.2 ⟨hy, hC⟩)
    refine ⟨List.Sublist.nodup List.filter_sublist hnd,
      List.Sublist.nodup List.filter_sublist (vs_nodup (by simp [isM, hM.1, hM.2])),
      Nat.le_trans (List.Sublist.length_le List.filter_sublist) hlen,
      fun e he e' he' h12 => Programme.«20261025-0805-proof-complexity».PermCount.nodup_map_inj (·.1) P hM.1 (mQ.1 he).1 (mQ.1 he').1 h12,
      fun e he e' he' h12 => Programme.«20261025-0805-proof-complexity».PermCount.nodup_map_inj (·.2) P hM.2 (mQ.1 he).1 (mQ.1 he').1 h12,
      fun e he => ⟨side _ (mem_vs.2 ⟨e, (mQ.1 he).1, Or.inl rfl⟩),
        side _ (mem_vs.2 ⟨e, (mQ.1 he).1, Or.inr rfl⟩)⟩, fun e he => ?_⟩
    rcases hout e (mQ.1 he).1 (mQ.1 he).2 with h | h
    · exact Or.inl (mR.2 ⟨mem_vs.2 ⟨e, (mQ.1 he).1, Or.inl rfl⟩, h⟩)
    · exact Or.inr (mR.2 ⟨mem_vs.2 ⟨e, (mQ.1 he).1, Or.inr rfl⟩, h⟩)

/-- A rise (inner edges present, the petal absent) leaves the residual matching absent. -/
theorem rise_Q {H : Nat → Nat → Bool} {I P : List (Nat × Nat)} (hI : pres H I) (hP : ¬ pres H P) :
    ¬ pres H (Qp I P) := by
  intro hQ
  apply hP
  intro e he
  by_cases hi : e ∈ I
  · exact hI e hi
  · exact hQ e (by simp [Qp, List.mem_filter, he, hi])

end Programme.«20261025-0805-proof-complexity».HallM6

#print axioms Programme.«20261025-0805-proof-complexity».HallM6.m6_core
#print axioms Programme.«20261025-0805-proof-complexity».HallM6.ev_petals
#print axioms Programme.«20261025-0805-proof-complexity».HallM6.rise_Q
