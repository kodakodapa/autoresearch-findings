import Programme.«20261024-1110-proof-complexity».Haken
/-!
# A matching upper bound: `PHP n` has resolution refutations of size `2^n · poly(n)`

For every `n` we construct a `Refutation (PHP n)` (the type of the lower bound `Work.Haken.haken`)
with at most `(n+1) * (2^n * (2*n*n + n + 1))` clauses. With `haken` this pins the resolution
size of `PHP n` between `(72/71)^(4⌊n/12⌋)` and `2^n · poly(n)`: exponential, and the exponent
is `Θ(n)`.

Construction (the standard one, cf. Buss–Pitassi): for a set `H` of holes write
`E k H = ⋁_{p<k, h∈H} x_{p,h}` ("one of the first `k` pigeons sits in `H`"). It is implied by
the axioms once `|H| + k ≥ n + 1`. Level `k+1` is derived from level `k`: for `h ∉ H` resolve
`E k (H ∪ {h})` with the hole axioms `¬x_{p,h} ∨ ¬x_{k,h}` (`p < k`) to get `¬x_{k,h} ∨ E k H`,
then cut the literals `x_{k,h}`, `h ∉ H`, out of pigeon `k`'s axiom. At `k = n+1`, `H = ∅`
gives the empty clause. Clauses are tracked up to subsumption (`CoversP`), which is harmless
because the resolution rule of `Refutation` allows weakening.
-/

namespace Programme.«20261024-1110-proof-complexity».Haken

open Classical

/-! ## Building refutations by appending clauses -/

/-- Every clause of `L` is an axiom of `F` or a resolvent of two clauses occurring earlier. -/
def Valid {V} (F : CNF V) (L : List (Clause V)) : Prop :=
  ∀ k (hk : k < L.length), L[k] ∈ F ∨ ∃ A ∈ L.take k, ∃ B ∈ L.take k, IsResolvent A B L[k]

theorem valid_nil {V} (F : CNF V) : Valid F [] := fun _ hk => absurd hk (Nat.not_lt_zero _)

theorem valid_snoc {V} {F : CNF V} {L : List (Clause V)} {C : Clause V} (hL : Valid F L)
    (hC : C ∈ F ∨ ∃ A ∈ L, ∃ B ∈ L, IsResolvent A B C) : Valid F (L ++ [C]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  by_cases hkl : k < L.length
  · rw [List.getElem_append_left hkl, List.take_append_of_le_length (Nat.le_of_lt hkl)]
    exact hL k hkl
  · have hk' : k = L.length := by omega
    subst hk'
    rw [List.getElem_append_right (Nat.le_refl _), List.take_left' rfl]
    simpa using hC

def Refutation.ofValid {V} {F : CNF V} (L : List (Clause V)) (hL : Valid F L)
    (he : ([] : Clause V) ∈ L) : Refutation F where
  steps := L
  derived := by
    intro k hk
    rcases hL k hk with h | ⟨A, hA, B, hB, hR⟩
    · exact Or.inl h
    · right
      obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hA
      obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hB
      simp only [List.length_take] at ha hb
      refine ⟨a, b, by omega, by omega, ?_⟩
      simpa [List.getElem_take] using hR
  empty_mem := he

/-- Some clause of `L` has all its literals in `S` (subsumes the clause `S`). -/
def CoversP {V} (L : List (Clause V)) (S : Lit V → Prop) : Prop := ∃ D ∈ L, ∀ l ∈ D, S l

theorem CoversP.mono {V} {L : List (Clause V)} {S : Lit V → Prop} (h : CoversP L S)
    (M : List (Clause V)) : CoversP (L ++ M) S := by
  obtain ⟨D, hD, hS⟩ := h
  exact ⟨D, List.mem_append_left _ hD, hS⟩

theorem CoversP.weaken {V} {L : List (Clause V)} {S T : Lit V → Prop} (h : CoversP L S)
    (hST : ∀ l, S l → T l) : CoversP L T := by
  obtain ⟨D, hD, hS⟩ := h
  exact ⟨D, hD, fun l hl => hST l (hS l hl)⟩

/-- From `L`, at most `c` further clauses reach a valid list satisfying `P`. -/
def Reach {V} (F : CNF V) (L : List (Clause V)) (c : Nat) (P : List (Clause V) → Prop) : Prop :=
  ∃ M : List (Clause V), Valid F (L ++ M) ∧ M.length ≤ c ∧ P (L ++ M)

theorem reach_zero {V} {F : CNF V} {L : List (Clause V)} {P : List (Clause V) → Prop} (c : Nat)
    (hL : Valid F L) (hP : P L) : Reach F L c P :=
  ⟨[], by simpa using hL, by simp, by simpa using hP⟩

theorem reach_trans {V} {F : CNF V} {L : List (Clause V)} {c d : Nat}
    {P Q : List (Clause V) → Prop} (h : Reach F L c P)
    (h2 : ∀ M, Valid F (L ++ M) → P (L ++ M) → Reach F (L ++ M) d Q) : Reach F L (c + d) Q := by
  obtain ⟨M, hv, hl, hp⟩ := h
  obtain ⟨M', hv', hl', hq⟩ := h2 M hv hp
  refine ⟨M ++ M', ?_, ?_, ?_⟩
  · simpa using hv'
  · simp; omega
  · simpa using hq

theorem reach_le {V} {F : CNF V} {L : List (Clause V)} {c d : Nat} {P : List (Clause V) → Prop}
    (h : Reach F L c P) (hcd : c ≤ d) : Reach F L d P := by
  obtain ⟨M, hv, hl, hp⟩ := h
  exact ⟨M, hv, by omega, hp⟩

theorem reach_imp {V} {F : CNF V} {L : List (Clause V)} {c : Nat} {P Q : List (Clause V) → Prop}
    (h : Reach F L c P) (hPQ : ∀ M, P (L ++ M) → Q (L ++ M)) : Reach F L c Q := by
  obtain ⟨M, hv, hl, hp⟩ := h
  exact ⟨M, hv, hl, hPQ M hp⟩

theorem reach_ax {V} {F : CNF V} {L : List (Clause V)} {C : Clause V} {S : Lit V → Prop}
    (hL : Valid F L) (hC : C ∈ F) (hS : ∀ l ∈ C, S l) : Reach F L 1 (CoversP · S) :=
  ⟨[C], valid_snoc hL (Or.inl hC), by simp, ⟨C, by simp, hS⟩⟩

/-- Resolution up to subsumption: resolving (clauses covering) `SA` and `SB` on `x`. -/
theorem reach_res {V} {F : CNF V} {L : List (Clause V)} {SA SB S : Lit V → Prop} (x : V)
    (hL : Valid F L) (hA : CoversP L SA) (hB : CoversP L SB)
    (hAS : ∀ l, SA l → l ≠ ⟨x, true⟩ → S l) (hBS : ∀ l, SB l → l ≠ ⟨x, false⟩ → S l) :
    Reach F L 1 (CoversP · S) := by
  obtain ⟨D1, hD1, h1⟩ := hA
  obtain ⟨D2, hD2, h2⟩ := hB
  by_cases e1 : (⟨x, true⟩ : Lit V) ∈ D1
  · by_cases e2 : (⟨x, false⟩ : Lit V) ∈ D2
    · let C := D1.filter (fun l => l ≠ ⟨x, true⟩) ++ D2.filter (fun l => l ≠ ⟨x, false⟩)
      have hR : IsResolvent D1 D2 C :=
        ⟨x, e1, e2, fun l hl hne => by simp [C, hl, hne],
          fun l hl hne => by simp [C, hl, hne]⟩
      refine ⟨[C], valid_snoc hL (Or.inr ⟨D1, hD1, D2, hD2, hR⟩), by simp, C, by simp, ?_⟩
      intro l hl
      simp only [C, List.mem_append, List.mem_filter, decide_eq_true_eq] at hl
      rcases hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
      · exact hAS l (h1 l hl) hne
      · exact hBS l (h2 l hl) hne
    · exact reach_zero 1 hL ⟨D2, hD2, fun l hl => hBS l (h2 l hl) (fun h => e2 (h ▸ hl))⟩
  · exact reach_zero 1 hL ⟨D1, hD1, fun l hl => hAS l (h1 l hl) (fun h => e1 (h ▸ hl))⟩

/-- Doing a step for every item of a list, keeping a monotone base invariant `I`. -/
theorem reach_forall {V} {F : CNF V} {α} (I : List (Clause V) → Prop) (Q : α → List (Clause V) → Prop)
    (c : Nat) (hI : ∀ L M, I L → I (L ++ M)) (hQ : ∀ x L M, Q x L → Q x (L ++ M))
    (step : ∀ x L, Valid F L → I L → Reach F L c (Q x)) :
    ∀ (xs : List α) (L : List (Clause V)), Valid F L → I L →
      Reach F L (xs.length * c) (fun L' => I L' ∧ ∀ x ∈ xs, Q x L') := by
  intro xs
  induction xs with
  | nil => intro L hL hIL; exact reach_zero _ hL ⟨hIL, by simp⟩
  | cons a xs ih =>
    intro L hL hIL
    have h := reach_trans (Q := fun L' => I L' ∧ Q a L' ∧ ∀ x ∈ xs, Q x L')
      (step a L hL hIL) (fun M hv hq =>
      reach_imp (ih (L ++ M) hv (hI L M hIL))
        (fun M' h' => (⟨h'.1, hQ a _ M' hq, h'.2⟩ : I _ ∧ Q a _ ∧ ∀ x ∈ xs, Q x _)))
    refine reach_le (reach_imp h ?_) (by simp [Nat.succ_mul, Nat.add_comm])
    intro M ⟨hIM, hqM, hall⟩
    refine ⟨hIM, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hqM
    · exact hall x hx

/-! ## Hole sets as sublists -/

/-- All sublists of a list (`2^length` of them). -/
def subs {α} : List α → List (List α)
  | [] => [[]]
  | a :: l => subs l ++ (subs l).map (a :: ·)

theorem length_subs {α} (l : List α) : (subs l).length = 2 ^ l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [subs, ih, Nat.pow_succ, Nat.mul_two]

theorem nil_mem_subs {α} (l : List α) : [] ∈ subs l := by
  induction l with
  | nil => simp [subs]
  | cons a l ih => simp [subs, ih]

theorem subs_props {α} {l H : List α} (hH : H ∈ subs l) : H.length ≤ l.length ∧ ∀ y ∈ H, y ∈ l := by
  induction l generalizing H with
  | nil => simp [subs] at hH; subst hH; simp
  | cons a l ih =>
    simp only [subs, List.mem_append, List.mem_map] at hH
    rcases hH with hH | ⟨H0, hH0, rfl⟩
    · obtain ⟨h1, h2⟩ := ih hH
      exact ⟨by simp; omega, fun y hy => List.mem_cons_of_mem _ (h2 y hy)⟩
    · obtain ⟨h1, h2⟩ := ih hH0
      refine ⟨by simp; omega, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h2 y hy)

theorem subs_insert {α} {l H : List α} {h : α} (hH : H ∈ subs l) (hl : h ∈ l) (hn : h ∉ H) :
    ∃ H' ∈ subs l, H'.length = H.length + 1 ∧ ∀ y, y ∈ H' ↔ y = h ∨ y ∈ H := by
  induction l generalizing H with
  | nil => simp at hl
  | cons a l ih =>
    simp only [subs, List.mem_append, List.mem_map] at hH
    by_cases e : h = a
    · subst e
      rcases hH with hH | ⟨H0, _, rfl⟩
      · exact ⟨h :: H, by simp [subs, hH], by simp, by simp⟩
      · simp at hn
    · have hl' : h ∈ l := (List.mem_cons.mp hl).resolve_left e
      rcases hH with hH | ⟨H0, hH0, rfl⟩
      · obtain ⟨H', h1, h2, h3⟩ := ih hH hl' hn
        exact ⟨H', by simp [subs, h1], h2, h3⟩
      · have hn0 : h ∉ H0 := fun hh => hn (List.mem_cons_of_mem _ hh)
        obtain ⟨H', h1, h2, h3⟩ := ih hH0 hl' hn0
        refine ⟨a :: H', by simp [subs, h1], by simp [h2], ?_⟩
        intro y; simp only [List.mem_cons, h3]; exact or_left_comm

/-! ## The construction for `PHP n` -/

def pos (p h : Nat) : Lit (Nat × Nat) := ⟨(p, h), true⟩
def neg (p h : Nat) : Lit (Nat × Nat) := ⟨(p, h), false⟩

/-- `E k H` : one of the pigeons `0..k-1` sits in a hole of `H`. -/
def EP (k : Nat) (H : List Nat) (l : Lit (Nat × Nat)) : Prop := ∃ p h, p < k ∧ h ∈ H ∧ l = pos p h

theorem pigeonAx_mem {n p : Nat} (hp : p ≤ n) : pigeonAx n p ∈ PHP n := by
  unfold PHP
  exact List.mem_append_left _ (List.mem_map.mpr ⟨p, by simp; omega, rfl⟩)

theorem holeAx_mem {n p q h : Nat} (hpq : p < q) (hq : q ≤ n) (hh : h < n) :
    holeAx p q h ∈ PHP n := by
  unfold PHP
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨h, by simp; omega, ?_⟩)
  refine List.mem_flatMap.mpr ⟨p, by simp; omega, ?_⟩
  exact List.mem_map.mpr ⟨q, by simp; omega, rfl⟩

/-- From `E k (H ∪ {h})`, derive `¬x_{k,h} ∨ E k H` with `2k` clauses (resolving out the
literals `x_{p,h}`, `p < k`, against hole axioms). Invariant: the literals `x_{p,h}` with
`j ≤ p < k` remain. -/
theorem reach_G {n k h : Nat} {H : List Nat} (hk : k ≤ n) (hh : h < n) :
    ∀ j, j ≤ k → ∀ L, Valid (PHP n) L →
      CoversP L (fun l => l = neg k h ∨ EP k H l ∨ ∃ p, p < k ∧ l = pos p h) →
      Reach (PHP n) L (2 * j)
        (CoversP · (fun l => l = neg k h ∨ EP k H l ∨ ∃ p, j ≤ p ∧ p < k ∧ l = pos p h)) := by
  intro j
  induction j with
  | zero =>
    intro _ L hL hc
    exact reach_zero _ hL (hc.weaken fun l hl => by
      rcases hl with hl | hl | ⟨p, hp, rfl⟩
      · exact Or.inl hl
      · exact Or.inr (Or.inl hl)
      · exact Or.inr (Or.inr ⟨p, Nat.zero_le _, hp, rfl⟩))
  | succ j ih =>
    intro hj L hL hc
    have h1 := ih (by omega) L hL hc
    have h2 := reach_trans h1 (fun M hv hcov =>
      reach_trans (Q := fun L' => CoversP L' (fun l => l = neg k h ∨ EP k H l ∨
          ∃ p, j ≤ p ∧ p < k ∧ l = pos p h) ∧ CoversP L' (· ∈ holeAx j k h))
        (reach_ax hv (holeAx_mem (by omega) hk hh) (S := (· ∈ holeAx j k h)) (fun l hl => hl))
        (fun M' hv' hax => reach_zero 0 hv' ⟨hcov.mono M', hax⟩))
    refine reach_le (reach_trans h2 (fun M hv ⟨hA, hB⟩ => reach_res (j, h) hv hA hB ?_ ?_))
      (by omega)
    · intro l hl hne
      rcases hl with hl | hl | ⟨p, hp1, hp2, rfl⟩
      · exact Or.inl hl
      · exact Or.inr (Or.inl hl)
      · refine Or.inr (Or.inr ⟨p, ?_, hp2, rfl⟩)
        rcases Nat.lt_or_ge j p with h' | h'
        · exact h'
        · exact absurd (by have : p = j := by omega
                           subst this; rfl) hne
    · intro l hl hne
      simp [holeAx] at hl
      rcases hl with rfl | rfl
      · exact absurd rfl hne
      · exact Or.inl rfl

theorem reach_keep {V} {F : CNF V} {L : List (Clause V)} {c : Nat} {P : List (Clause V) → Prop}
    {S : Lit V → Prop} (h : Reach F L c P) (hS : CoversP L S) :
    Reach F L c (fun L' => P L' ∧ CoversP L' S) :=
  reach_imp h (fun M hp => ⟨hp, hS.mono M⟩)

/-- Cutting the literals `x_{k,h}`, `h ∈ Rs`, out of pigeon `k`'s axiom, each with the clause
`¬x_{k,h} ∨ E k H` obtained from `E k (H ∪ {h})` by `reach_G`. -/
theorem reach_cut {n k : Nat} {H : List Nat} (hk : k ≤ n) :
    ∀ Rs : List Nat, (∀ h ∈ Rs, h < n) → ∀ L, Valid (PHP n) L →
      (∀ h ∈ Rs, CoversP L (fun l => EP k H l ∨ ∃ p, p < k ∧ l = pos p h)) →
      Reach (PHP n) L (1 + Rs.length * (2 * k + 1))
        (CoversP · (fun l => EP k H l ∨ ∃ h, l = pos k h ∧ h < n ∧ (h ∈ H ∨ h ∉ Rs))) := by
  intro Rs
  induction Rs with
  | nil =>
    intro _ L hL _
    refine reach_le (reach_ax hL (pigeonAx_mem hk) ?_) (by simp)
    intro l hl
    simp only [pigeonAx, List.mem_map, List.mem_range] at hl
    obtain ⟨h, hh, rfl⟩ := hl
    exact Or.inr ⟨h, rfl, hh, Or.inr (by simp)⟩
  | cons h Rs ih =>
    intro hRs L hL hcov
    have hh : h < n := hRs h List.mem_cons_self
    have h1 := ih (fun h' hh' => hRs h' (List.mem_cons_of_mem _ hh')) L hL
      (fun h' hh' => hcov h' (List.mem_cons_of_mem _ hh'))
    have h2 := reach_trans h1 (fun M hv hcur =>
      reach_keep (reach_G (H := H) hk hh k (Nat.le_refl _) (L ++ M) hv
        (((hcov h List.mem_cons_self).mono M).weaken fun l hl => Or.inr hl)) hcur)
    refine reach_le (reach_trans h2 (fun M hv ⟨hB, hA⟩ => reach_res (k, h) hv hA hB ?_ ?_))
      (by simp [Nat.succ_mul]; omega)
    · intro l hl hne
      rcases hl with hl | ⟨h', rfl, hh', hor⟩
      · exact Or.inl hl
      · refine Or.inr ⟨h', rfl, hh', ?_⟩
        rcases hor with hor | hor
        · exact Or.inl hor
        · refine Or.inr ?_
          intro hm
          rcases List.mem_cons.mp hm with rfl | hm
          · exact hne rfl
          · exact hor hm
    · intro l hl hne
      rcases hl with rfl | hl | ⟨p, hp1, hp2, rfl⟩
      · exact absurd rfl hne
      · exact Or.inl hl
      · omega

/-- Level `k`: `E k H` is covered for every hole set `H` with `|H| + k ≥ n + 1`. -/
def Lev (n k : Nat) (L : List (Clause (Nat × Nat))) : Prop :=
  ∀ H ∈ subs (List.range n), n + 1 ≤ H.length + k → CoversP L (EP k H)

theorem reach_level {n k : Nat} (hk : k ≤ n) (L : List (Clause (Nat × Nat)))
    (hL : Valid (PHP n) L) (hlev : Lev n k L) :
    Reach (PHP n) L (2 ^ n * (2 * n * n + n + 1)) (Lev n (k + 1)) := by
  have h := reach_forall (F := PHP n) (Lev n k)
    (fun H L => H ∈ subs (List.range n) → n + 1 ≤ H.length + (k + 1) → CoversP L (EP (k + 1) H))
    (2 * n * n + n + 1)
    (fun L M h H hH hl => (h H hH hl).mono M) (fun H L M h hH hl => (h hH hl).mono M) ?_
    (subs (List.range n)) L hL hlev
  · rw [length_subs, List.length_range] at h
    exact reach_imp h (fun M ⟨_, hall⟩ H hH hl => hall H hH hH hl)
  · intro H L hL hlev
    by_cases hsz : H ∈ subs (List.range n) ∧ n + 1 ≤ H.length + (k + 1)
    · obtain ⟨hH, hsz⟩ := hsz
      · have hHn := (subs_props hH).2
        let Rs := (List.range n).filter (fun h => h ∉ H)
        have hRs : ∀ h ∈ Rs, h < n ∧ h ∉ H := by
          intro h hh; simp [Rs] at hh; exact hh
        have hc := reach_cut (H := H) hk Rs (fun h hh => (hRs h hh).1) L hL ?_
        · refine reach_le (reach_imp hc (fun M hcov _ _ => hcov.weaken ?_)) ?_
          · intro l hl
            rcases hl with ⟨p, h, hp, hh, rfl⟩ | ⟨h, rfl, hh, hor⟩
            · exact ⟨p, h, by omega, hh, rfl⟩
            · refine ⟨k, h, by omega, ?_, rfl⟩
              rcases hor with hor | hor
              · exact hor
              · exact Classical.byContradiction fun hn => hor (by simp [Rs, hh, hn])
          · have : Rs.length ≤ n := by
              have := List.length_filter_le (fun h => decide (h ∉ H)) (List.range n)
              simpa [Rs] using this
            have : Rs.length * (2 * k + 1) ≤ n * (2 * n + 1) := Nat.mul_le_mul this (by omega)
            have h3 : n * (2 * n + 1) = 2 * n * n + n := by
              rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm n (2 * n)]
            omega
        · intro h hh
          obtain ⟨hhn, hnH⟩ := hRs h hh
          obtain ⟨H', hH', hlen, hmem⟩ := subs_insert hH (List.mem_range.mpr hhn) hnH
          refine (hlev H' hH' (by omega)).weaken ?_
          rintro l ⟨p, h', hp, hh', rfl⟩
          rcases (hmem h').mp hh' with rfl | hh'
          · exact Or.inr ⟨p, hp, rfl⟩
          · exact Or.inl ⟨p, h', hp, hh', rfl⟩
    · exact reach_zero _ hL (fun h1 h2 => absurd ⟨h1, h2⟩ hsz)

theorem reach_levels (n : Nat) :
    ∀ k, k ≤ n + 1 → Reach (PHP n) [] (k * (2 ^ n * (2 * n * n + n + 1))) (Lev n k) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine reach_zero _ (valid_nil _) ?_
    intro H hH hl
    have := (subs_props hH).1
    simp at this hl; omega
  | succ k ih =>
    intro hk
    refine reach_le (reach_trans (ih (by omega)) (fun M hv hlev =>
      reach_level (by omega) _ hv hlev)) (Nat.le_of_eq (Nat.succ_mul _ _).symm)

/-- `PHP n` (`n+1` pigeons, `n` holes) has a resolution refutation with at most
`(n+1) · 2^n · (2n² + n + 1)` clauses. -/
theorem php_upper (n : Nat) :
    ∃ R : Refutation (PHP n), R.steps.length ≤ (n + 1) * (2 ^ n * (2 * n * n + n + 1)) := by
  obtain ⟨M, hv, hlen, hlev⟩ := reach_levels n (n + 1) (Nat.le_refl _)
  obtain ⟨D, hD, hDe⟩ := hlev [] (nil_mem_subs _) (by simp)
  have : D = [] := by
    cases D with
    | nil => rfl
    | cons l D =>
      obtain ⟨p, h, _, hh, _⟩ := hDe l List.mem_cons_self
      simp at hh
  subst this
  exact ⟨Refutation.ofValid _ hv hD, by show ([] ++ M).length ≤ _; simpa using hlen⟩

/-- Resolution size of `PHP n` is exponential with exponent `Θ(n)`: some refutation has at most
`(n+1) · 2^n · (2n²+n+1)` clauses, and every refutation has at least `(72/71)^(4⌊n/12⌋)`. -/
theorem php_size_bounds (n : Nat) :
    (∃ R : Refutation (PHP n), R.steps.length ≤ (n + 1) * (2 ^ n * (2 * n * n + n + 1))) ∧
    ∀ R : Refutation (PHP n), 72 ^ (4 * (n / 12)) ≤ 71 ^ (4 * (n / 12)) * R.steps.length :=
  ⟨php_upper n, haken n⟩

end Programme.«20261024-1110-proof-complexity».Haken

#print axioms Programme.«20261024-1110-proof-complexity».Haken.php_upper
#print axioms Programme.«20261024-1110-proof-complexity».Haken.php_size_bounds
