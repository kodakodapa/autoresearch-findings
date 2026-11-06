import Programme.«20261024-1633-proof-complexity».ApproxRCR
import Programme.«20261024-1633-proof-complexity».CCRange

/-!
# The approximation method for clique–colouring

K19 (`cc_range`) turns a tree-like CP refutation of `CC m k` with `s` nodes and line weights `≤ W`
into a monotone real formula with `≤ s (2k+6)` gates, every subformula of range `≤ 2W`. `approx`
then gives an approximator of the output with error lists. The final case analysis of the
approximation method yields `cc_approx`: there are a list `pe` of sets of size `> ℓ` and a list `ne`
of pluck events, each of length at most `s (2k+6) (2WB + 1)^2`, such that
* either every `k`-set of vertices `< m` contains a set of `pe`,
* or for some set `S` (duplicate-free, `≤ ℓ` vertices `< m`) every `(k-1)`-colouring making `S`
  rainbow is hit by an event of `ne` (core rainbow, no petal rainbow).

Counting (pr's `pos_count` for the first case; `petal_count` for the second) turns this into the
known exponential lower bound for tree-like CP with bounded coefficients (Bonet–Pitassi–Raz 1997).
-/

namespace Programme.«20261024-1633-proof-complexity».CCApprox

open Programme.«20261024-1110-proof-complexity».Haken (Lit Clause CNF Lit.eval Clause.eval)
open Programme.«20261024-1633-proof-complexity».RealApprox Programme.«20261024-1633-proof-complexity».Pluck Programme.«20261024-1633-proof-complexity».CP Programme.«20261024-1633-proof-complexity».CPInterp Programme.«20261024-1633-proof-complexity».CPRange Programme.«20261024-1633-proof-complexity».CliqueColour Programme.«20261024-1633-proof-complexity».ApproxRCR Programme.«20261024-1633-proof-complexity».CCRange

/-- Graph `G` read as an assignment of the edge variables `p i j`, `i < j < m`. -/
def emb (m : Nat) (G : Nat → Nat → Bool) : V → Bool
  | .p i j => decide (i < j) && decide (j < m) && G i j
  | _ => false

/-- Input approximators. -/
def inA (m : Nat) : V → Approx
  | .p i j => if i < j ∧ j < m then inpA i j else constA 0
  | _ => constA 0

theorem nodup_inj : ∀ {K : List Nat}, K.Nodup → ∀ {i j : Nat} (hi : i < K.length)
    (hj : j < K.length), K[i] = K[j] → i = j
  | [], _, _, _, hi, _, _ => by simp at hi
  | x :: l, h, i, j, hi, hj, e => by
    have ⟨hx, hl⟩ := List.nodup_cons.1 h
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at e
        exact absurd (e ▸ List.getElem_mem _) hx
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at e
        exact absurd (e.symm ▸ List.getElem_mem _) hx
      | succ j =>
        simp only [List.getElem_cons_succ] at e
        simp only [List.length_cons] at hi hj
        exact congrArg (· + 1) (nodup_inj hl (by omega) (by omega) e)

theorem posG_symm (K : List Nat) (i j : Nat) : posG K i j = posG K j i := by
  simp only [posG, Bool.and_comm]

theorem negG_symm (c : Nat → Nat) (i j : Nat) : negG c i j = negG c j i := by
  simp only [negG, ne_comm]

theorem adj_emb (m : Nat) (G : Nat → Nat → Bool) (hs : ∀ i j, G i j = G j i) (i j : Nat)
    (hij : i ≠ j) (hi : i < m) (hj : j < m) : adj (emb m G) i j = G i j := by
  unfold adj
  by_cases h : i < j
  · simp [emb, h, hj]
  · have : j < i := by omega
    simp [emb, h, this, hi, hs j i]

theorem clique_pos (m k : Nat) (K : List Nat) (hK : K.Nodup) (hl : K.length = k)
    (hm : ∀ x ∈ K, x < m) : HasClique m k (emb m (posG K)) := by
  refine ⟨fun l => if h : l < K.length then K[l] else 0, fun l hl' => ?_, fun l l' hl1 hl2 hne => ?_⟩
  · have h : l < K.length := by omega
    simp only [h, dite_true]; exact hm _ (List.getElem_mem _)
  · have h1 : l < K.length := by omega
    have h2 : l' < K.length := by omega
    simp only [h1, h2, dite_true]
    have hd : K[l] ≠ K[l'] := fun e => hne (nodup_inj hK h1 h2 e)
    refine ⟨hd, ?_⟩
    rw [adj_emb m _ (posG_symm K) _ _ hd (hm _ (List.getElem_mem _)) (hm _ (List.getElem_mem _))]
    simp [posG, List.getElem_mem]

theorem colour_neg (m k : Nat) (c : Nat → Nat) (hc : ∀ i, i < m → c i < k - 1) :
    Colourable m k (emb m (negG c)) := by
  refine ⟨c, hc, fun i j hij hj ha => ?_⟩
  rw [adj_emb m _ (negG_symm c) _ _ (by omega) (by omega) hj] at ha
  simpa [negG] using ha

theorem val_emb (m i j : Nat) (G : Nat → Nat → Bool) :
    val (emb m G) (.p i j) = if i < j ∧ j < m ∧ G i j = true then 1 else 0 := by
  unfold val emb
  by_cases h1 : i < j <;> by_cases h2 : j < m <;> simp [h1, h2]

theorem hin (m ℓ RB : Nat) (hℓ : 2 ≤ ℓ) (hRB : 1 ≤ RB) : ∀ u, shared isR isQ u = true →
    Inv ℓ m (inA m u) ∧ (inA m u).base = val (fun _ => false) u ∧
      (∀ e ∈ (inA m u).ents, e.2 ≤ val (fun _ => true) u) ∧ (inA m u).ents.length ≤ RB ∧
      (∀ K, val (emb m (posG K)) u ≤ eval (inA m u) (posG K)) ∧
      (∀ c, eval (inA m u) (negG c) ≤ val (emb m (negG c)) u) := by
  intro u hu
  cases u with
  | q _ _ => simp [shared, isR, isQ] at hu
  | r _ _ => simp [shared, isR, isQ] at hu
  | p i j =>
    by_cases h : i < j ∧ j < m
    · have hij : i ≠ j := by omega
      have e : inA m (.p i j) = inpA i j := by simp [inA, h]
      rw [e]
      refine ⟨?_, by simp [inpA, val], ?_, by simp [inpA]; omega, fun K => ?_, fun c => ?_⟩
      · intro x hx
        simp only [inpA, List.mem_singleton] at hx; subst hx
        refine ⟨by simp [hij], by simp; omega, ?_, ns_pair hij⟩
        intro x hx; simp at hx; omega
      · intro x hx; simp only [inpA, List.mem_singleton] at hx; subst hx; simp [val]
      · rw [inp_eval i j _ hij (posG_symm K i j), val_emb]
        by_cases g : posG K i j = true <;> simp [g, h]
      · rw [inp_eval i j _ hij (negG_symm c i j), val_emb]
        by_cases g : negG c i j = true <;> simp [g, h]
    · have e : inA m (.p i j) = constA 0 := by simp [inA, h]
      rw [e]
      refine ⟨fun x hx => by simp [constA] at hx, by simp [constA, val],
        fun x hx => by simp [constA] at hx, by simp [constA], fun K => ?_, fun c => ?_⟩
      · rw [val_emb, const_eval]
        have : ¬ (i < j ∧ j < m ∧ posG K i j = true) := fun h' => h ⟨h'.1, h'.2.1⟩
        simp only [this, ite_false]; exact Int.le_refl 0
      · rw [val_emb, const_eval]; split <;> omega

/-- **Clique–colouring, approximation step.** For every tree-like CP refutation of `CC m k` with
`s` nodes and line weights `≤ W`, and the sunflower lemma `SF p ℓ B` (`p ≥ 2`, `ℓ ≥ 2`, `B ≥ 1`):
there are sets `pe` (duplicate-free, `> ℓ` vertices `< m`) and pluck events `ne` (`Ev p ℓ m`), each
list of length `≤ s (2k+6) (2WB+1)^2`, such that either every duplicate-free `k`-list of vertices
`< m` contains a set of `pe`, or some duplicate-free `S` of `≤ ℓ` vertices `< m` has every
colouring `c` (colours `< k-1` on vertices `< m`) making `S` rainbow hit by an event of `ne`: its
core is rainbow under `c` and none of its petals is. -/
theorem cc_approx (m k p ℓ B : Nat) (hp : 2 ≤ p) (hℓ : 2 ≤ ℓ) (hB : 1 ≤ B) (hSF : SF p ℓ B)
    (Rf : BRefutation (CC m k)) :
    ∃ pe : List (List Nat), ∃ ne : List (List Nat × List (List Nat)),
      pe.length ≤ Rf.size * (2 * k + 6) * (2 * Rf.W.toNat * B + 1) ^ 2 ∧
      ne.length ≤ Rf.size * (2 * k + 6) * (2 * Rf.W.toNat * B + 1) ^ 2 ∧
      (∀ T ∈ pe, T.Nodup ∧ ℓ + 1 ≤ T.length ∧ ∀ x ∈ T, x < m) ∧ (∀ ev ∈ ne, Ev p ℓ m ev) ∧
      ((∀ K : List Nat, K.Nodup → K.length = k → (∀ x ∈ K, x < m) →
          ∃ T ∈ pe, ∀ i ∈ T, i ∈ K) ∨
       ∃ S : List Nat, S.Nodup ∧ S.length ≤ ℓ ∧ (∀ x ∈ S, x < m) ∧
          ∀ c : Nat → Nat, (∀ i, i < m → c i < k - 1) → clq (negG c) S →
            ∃ ev ∈ ne, clq (negG c) ev.1 ∧ ∀ S' ∈ ev.2, ¬ clq (negG c) S') := by
  obtain ⟨f, t, r, ht, _, hsep⟩ := cc_range m k Rf
  have hW := one_le_W Rf
  have e : 2 * Rf.W = ((2 * Rf.W.toNat : Nat) : Int) := by omega
  rw [e] at r
  have hRB : 1 ≤ 2 * Rf.W.toNat * B := by
    have : 1 ≤ Rf.W.toNat := by omega
    exact Nat.le_trans (by omega : 1 ≤ 2 * Rf.W.toNat) (Nat.le_mul_of_pos_right _ hB)
  obtain ⟨a, pe, ne, _, ha2, _, _, ha5, ha6, ha7, ha8, ha9, ha10⟩ :=
    approx (shared isR isQ) p ℓ m B (2 * Rf.W.toNat) hp hSF (emb m) (inA m)
      (hin m ℓ _ hℓ hRB) r
  have hmul : t * (2 * Rf.W.toNat * B + 1) ^ 2 ≤
      Rf.size * (2 * k + 6) * (2 * Rf.W.toNat * B + 1) ^ 2 := Nat.mul_le_mul_right _ ht
  refine ⟨pe, ne, Nat.le_trans ha5 hmul, Nat.le_trans ha6 hmul, ha7, ha8, ?_⟩
  -- a negative test graph on which `a` is at least `1` is an error
  have neg_err : ∀ c : Nat → Nat, (∀ i, i < m → c i < k - 1) → 1 ≤ eval a (negG c) →
      ∃ ev ∈ ne, clq (negG c) ev.1 ∧ ∀ S' ∈ ev.2, ¬ clq (negG c) S' := by
    intro c hc h1
    rcases ha10 c with h | h
    · have := (hsep (emb m (negG c))).2 (colour_neg m k c hc); omega
    · exact h
  by_cases hb : 1 ≤ a.base
  · refine Or.inr ⟨[], List.nodup_nil, by simp, by simp, fun c hc _ => neg_err c hc ?_⟩
    exact Int.le_trans hb (evalL_base _ _ _)
  · by_cases he : ∃ e ∈ a.ents, 1 ≤ e.2
    · obtain ⟨e, he, h1⟩ := he
      obtain ⟨hn, hl, hv, _⟩ := ha2 e he
      exact Or.inr ⟨e.1, hn, hl, hv, fun c hc hS =>
        neg_err c hc (Int.le_trans h1 (evalL_ent _ _ _ e he hS))⟩
    · left
      intro K hK hl hm
      rcases ha9 K with h | h
      · have h1 := (hsep (emb m (posG K))).1 (clique_pos m k K hK hl hm)
        have h2 : eval a (posG K) ≤ 0 := by
          apply eval_le_of_cover
          intro x hx _
          rcases List.mem_cons.1 hx with h' | h'
          · subst h'; show a.base ≤ 0; omega
          · have : ¬ 1 ≤ x.2 := fun h'' => he ⟨x, h', h''⟩
            omega
        omega
      · exact h

end Programme.«20261024-1633-proof-complexity».CCApprox
