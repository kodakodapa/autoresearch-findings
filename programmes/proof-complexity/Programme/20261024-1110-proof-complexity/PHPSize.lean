import Programme.«20261024-1110-proof-complexity».GTSize
/-!
# A `2^{O(n)}`-size resolution refutation of the pigeonhole principle, for all `n` (core Lean 4)

Independent reproof of the upper half of pr's K9 (`Work.Haken.php_upper` in
`agents/pr/lean/Work/HakenUpper.lean`), with the same bound `(n+1)·2^n·(2n²+n+1)`.
`PHP n` is restated clause for clause from `Work.Haken.PHP` over the `Work.BSW` copy of K1's
types (pigeons `0..n`, holes `0..n-1`). The proof uses only the `Valid`/`Cov`/`Gr` machinery
of `Work.GTSize`; it shares no code with `HakenUpper.lean`.

Construction (the standard one). For a hole set `H` with `|H| = k`, let
`D k H = ⋁_{i ≤ k, g ∉ H} x_{i,g}` ("one of the pigeons `0..k` sits outside `H`").
* `k = 0`, `H = ∅`: the pigeon axiom of pigeon `0`.
* `k → k+1`, `|H| = k+1`: for each `h ∈ H`, cut `D k (H∖h)` against the hole axioms
  `¬x_{i,h} ∨ ¬x_{k+1,h}` (`i ≤ k`) to get `D (k+1) H ∨ ¬x_{k+1,h}`; then cut the pigeon
  axiom of pigeon `k+1` against these on every `x_{k+1,h}`, `h ∈ H`.
* `k = n`, `H = {0..n-1}`: `D n H` is empty.
Hole sets are enumerated as the sublists `sl (range n)`, `2^n` of them.
-/

set_option linter.unusedSectionVars false

namespace Programme.«20261024-1110-proof-complexity».PHPSize
open Programme.«20261024-1110-proof-complexity».BSW Programme.«20261024-1110-proof-complexity».GTSize

/-! ## The formula (verbatim from `Work.Haken`) -/

def pigeonAx (n p : Nat) : Clause (Nat × Nat) := (List.range n).map fun h => ⟨(p, h), true⟩

def holeAx (p q h : Nat) : Clause (Nat × Nat) := [⟨(p, h), false⟩, ⟨(q, h), false⟩]

/-- `PHP n` : `n+1` pigeons, `n` holes. -/
def PHP (n : Nat) : CNF (Nat × Nat) :=
  (List.range (n + 1)).map (pigeonAx n) ++
  (List.range n).flatMap fun h => (List.range (n + 1)).flatMap fun p =>
    ((List.range (n + 1)).filter (fun q => p < q)).map fun q => holeAx p q h

theorem pig_mem {n p : Nat} (hp : p ≤ n) : pigeonAx n p ∈ PHP n := by
  simp only [PHP, List.mem_append]
  exact Or.inl (List.mem_map.mpr ⟨p, List.mem_range.mpr (by omega), rfl⟩)

theorem hole_mem {n p q h : Nat} (hpq : p < q) (hq : q ≤ n) (hh : h < n) :
    holeAx p q h ∈ PHP n := by
  simp only [PHP, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_range, decide_eq_true_eq]
  exact Or.inr ⟨h, hh, p, by omega, q, ⟨by omega, hpq⟩, rfl⟩

/-! ## Sublists -/

def sl : List Nat → List (List Nat)
  | [] => [[]]
  | a :: l => sl l ++ (sl l).map (a :: ·)

theorem sl_length : ∀ l : List Nat, (sl l).length = 2 ^ l.length
  | [] => rfl
  | a :: l => by
    simp only [sl, List.length_append, List.length_map, sl_length l, List.length_cons,
      Nat.pow_succ]
    omega

theorem sl_self : ∀ l : List Nat, l ∈ sl l
  | [] => by simp [sl]
  | a :: l => List.mem_append_right _ (List.mem_map.mpr ⟨l, sl_self l, rfl⟩)

theorem sl_sub : ∀ (l H : List Nat), H ∈ sl l → ∀ g ∈ H, g ∈ l
  | [], H, hH, g, hg => by
    simp only [sl, List.mem_singleton] at hH; subst hH; simp at hg
  | a :: l, H, hH, g, hg => by
    simp only [sl, List.mem_append, List.mem_map] at hH
    rcases hH with hH | ⟨H', hH', rfl⟩
    · exact List.mem_cons_of_mem _ (sl_sub l H hH g hg)
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (sl_sub l H' hH' g hg)

theorem sl_erase : ∀ (l H : List Nat) (h : Nat), H ∈ sl l → H.erase h ∈ sl l
  | [], H, h, hH => by
    simp only [sl, List.mem_singleton] at hH; subst hH; simp [sl]
  | a :: l, H, h, hH => by
    simp only [sl, List.mem_append, List.mem_map] at hH ⊢
    rcases hH with hH | ⟨H', hH', rfl⟩
    · exact Or.inl (sl_erase l H h hH)
    · by_cases hah : a = h
      · subst hah; left; rw [List.erase_cons_head]; exact hH'
      · right
        refine ⟨H'.erase h, sl_erase l H' h hH', ?_⟩
        rw [List.erase_cons_tail (by simpa using hah)]

/-! ## The levels -/

/-- `Dp n k H`: the literals `x_{i,g}` with `i ≤ k`, `g < n`, `g ∉ H`. -/
def Dp (n k : Nat) (H : List Nat) (l : Lit (Nat × Nat)) : Prop :=
  ∃ i g, i ≤ k ∧ g < n ∧ g ∉ H ∧ l = pw i g

def PLev (n k : Nat) (L : List (Clause (Nat × Nat))) : Prop :=
  ∀ H ∈ sl (List.range n), H.length = k → Cov L (Dp n k H)

theorem plev_ext {n k : Nat} {L : List (Clause (Nat × Nat))} (h : PLev n k L) (M) :
    PLev n k (L ++ M) := fun H hH hl => (h H hH hl).ext M

/-- For `h ∈ H`, `|H| = k+1`: a clause inside `D (k+1) H ∪ {¬x_{k+1,h}}`, `2(k+1)` lines. -/
theorem step_E {n k : Nat} (hk : k + 1 ≤ n) {H : List Nat} (hH : H ∈ sl (List.range n))
    (hlen : H.length = k + 1) {h : Nat} (hh : h ∈ H) (L : List (Clause (Nat × Nat)))
    (hL : Valid (PHP n) L) (hlev : PLev n k L) :
    Gr (PHP n) L (2 * (k + 1)) (Cov · (fun l => Dp n (k + 1) H l ∨ l = nw (k + 1) h)) := by
  have hhn : h < n := List.mem_range.mp (sl_sub _ H hH h hh)
  have hc := hlev (H.erase h) (sl_erase _ H h hH) (by rw [List.length_erase_of_mem hh]; omega)
  let Q : Nat → List (Clause (Nat × Nat)) → Prop := fun i L =>
    Cov L (fun l => Dp n (k + 1) H l ∨ l = nw (k + 1) h ∨ ∃ i', i ≤ i' ∧ i' ≤ k ∧ l = pw i' h)
  have h0 : Q 0 L := hc.weak (by
    rintro l ⟨i, g, hi, hg, hgH, rfl⟩
    by_cases hgh : g = h
    · subst hgh; exact Or.inr (Or.inr ⟨i, Nat.zero_le _, hi, rfl⟩)
    · refine Or.inl ⟨i, g, by omega, hg, fun hm => hgH ?_, rfl⟩
      exact (List.mem_erase_of_ne hgh).mpr hm)
  have hit := gr_iter (F := PHP n) Q 2 (k + 1) ?_ (k + 1) (Nat.le_refl _) L hL h0
  · refine gr_mono hit (by rw [Nat.mul_comm]; exact Nat.le_refl _) (fun M hq => hq.weak ?_)
    rintro l (h1 | h1 | ⟨i', h1, h2, _⟩)
    · exact Or.inl h1
    · exact Or.inr h1
    · omega
  intro i hi L hL hq
  refine gr_seq (k' := 1) (gr_ax hL (hole_mem (p := i) (q := k + 1) (h := h) (by omega) hk hhn)
    (S := fun l => l = nw (k + 1) h ∨ l = ⟨(i, h), false⟩) (by
      intro l hl
      simp only [holeAx, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl rfl)) (fun M hv hB => ?_) (by omega)
  refine gr_res hv (i, h)
    (S := fun l => Dp n (k + 1) H l ∨ l = nw (k + 1) h ∨ ∃ i', i + 1 ≤ i' ∧ i' ≤ k ∧ l = pw i' h)
    (S' := fun l => l = nw (k + 1) h) ((hq.ext M).weak ?_) hB (fun l h1 => h1)
    (fun l h1 => Or.inr (Or.inl h1))
  rintro l (h1 | h1 | ⟨i', h1, h2, rfl⟩)
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr (Or.inl h1))
  · rcases Nat.lt_or_ge i i' with h3 | h3
    · exact Or.inl (Or.inr (Or.inr ⟨i', h3, h2, rfl⟩))
    · have : i' = i := by omega
      subst this; exact Or.inr rfl

/-- One hole set of size `k+1`: `D (k+1) H`, at most `(k+1)·2(k+1) + 1 + (k+1)` lines. -/
theorem step_H {n k : Nat} (hk : k + 1 ≤ n) {H : List Nat} (hH : H ∈ sl (List.range n))
    (hlen : H.length = k + 1) (L : List (Clause (Nat × Nat))) (hL : Valid (PHP n) L)
    (hlev : PLev n k L) :
    Gr (PHP n) L ((k + 1) * (2 * (k + 1)) + (1 + (k + 1) * 1)) (Cov · (Dp n (k + 1) H)) := by
  let E : Nat → Lit (Nat × Nat) → Prop := fun h l => Dp n (k + 1) H l ∨ l = nw (k + 1) h
  have p1 := gr_all (F := PHP n) (PLev n k)
    (fun t L => ∀ ht : t < H.length, Cov L (E H[t])) (2 * (k + 1)) (k + 1)
    (fun L M h => plev_ext h M) (fun t L M h ht => (h ht).ext M)
    (fun t _ L hL hl => gr_mono (step_E hk hH hlen (List.getElem_mem (by omega)) L hL hl)
      (Nat.le_refl _) (fun M h ht => h)) (k + 1) (Nat.le_refl _) L hL hlev
  refine gr_seq p1 (fun M hv ⟨_, hE⟩ => ?_) (Nat.le_refl _)
  let Q : Nat → List (Clause (Nat × Nat)) → Prop := fun t L =>
    (∀ t' < k + 1, ∀ ht : t' < H.length, Cov L (E H[t'])) ∧
    Cov L (fun l => Dp n (k + 1) H l ∨ ∃ t', t ≤ t' ∧ ∃ ht : t' < H.length, l = pw (k + 1) H[t'])
  refine gr_seq (k' := (k + 1) * 1) (gr_ax hv (pig_mem (p := k + 1) hk)
    (S := fun l => ∃ g, g < n ∧ l = pw (k + 1) g) (by
      intro l hl
      simp only [pigeonAx, List.mem_map, List.mem_range] at hl
      obtain ⟨g, hg, rfl⟩ := hl
      exact ⟨g, hg, rfl⟩)) (fun M' hv' hP => ?_) (Nat.le_refl _)
  have h0 : Q 0 ((L ++ M) ++ M') := ⟨fun t' ht' ht => (hE t' ht' ht).ext M', hP.weak (by
    rintro l ⟨g, hg, rfl⟩
    by_cases hgH : g ∈ H
    · obtain ⟨t', ht', rfl⟩ := List.mem_iff_getElem.mp hgH
      exact Or.inr ⟨t', Nat.zero_le _, ht', rfl⟩
    · exact Or.inl ⟨k + 1, g, Nat.le_refl _, hg, hgH, rfl⟩)⟩
  have hit := gr_iter (F := PHP n) Q 1 (k + 1) ?_ (k + 1) (Nat.le_refl _) _ hv' h0
  · refine gr_mono hit (Nat.le_refl _) (fun M'' ⟨_, hc⟩ => hc.weak ?_)
    rintro l (h1 | ⟨t', h1, ht, _⟩)
    · exact h1
    · omega
  intro t ht L hL ⟨hE', hc⟩
  have htl : t < H.length := by omega
  refine gr_mono (gr_res hL (k + 1, H[t])
    (S := fun l => Dp n (k + 1) H l ∨ ∃ t', t + 1 ≤ t' ∧ ∃ ht : t' < H.length, l = pw (k + 1) H[t'])
    (S' := Dp n (k + 1) H) (hc.weak ?_) (hE' t ht htl) (fun l h1 => h1) (fun l h1 => Or.inl h1))
    (Nat.le_refl _) (fun M h => ⟨fun t' ht' ht'' => (hE' t' ht' ht'').ext M, h⟩)
  rintro l (h1 | ⟨t', h1, ht', rfl⟩)
  · exact Or.inl (Or.inl h1)
  · rcases Nat.lt_or_ge t t' with h3 | h3
    · exact Or.inl (Or.inr ⟨t', h3, ht', rfl⟩)
    · have : t' = t := by omega
      subst this; exact Or.inr rfl

theorem cost_le {n k : Nat} (hk : k + 1 ≤ n) :
    (k + 1) * (2 * (k + 1)) + (1 + (k + 1) * 1) ≤ 2 * n * n + n + 1 := by
  have h1 : (k + 1) * (k + 1) ≤ n * n := Nat.mul_le_mul hk hk
  have e1 : (k + 1) * (2 * (k + 1)) = 2 * ((k + 1) * (k + 1)) := Nat.mul_left_comm _ _ _
  have e2 : 2 * n * n = 2 * (n * n) := Nat.mul_assoc _ _ _
  rw [e1, e2, Nat.mul_one]
  omega

/-- One level: `PLev n k → PLev n (k+1)`, at most `2^n·(2n²+n+1)` lines. -/
theorem step_level {n k : Nat} (hk : k + 1 ≤ n) (L : List (Clause (Nat × Nat)))
    (hL : Valid (PHP n) L) (hlev : PLev n k L) :
    Gr (PHP n) L (2 ^ n * (2 * n * n + n + 1)) (PLev n (k + 1)) := by
  let S := sl (List.range n)
  have hS : S.length = 2 ^ n := by simp only [S, sl_length, List.length_range]
  have h := gr_all (F := PHP n) (PLev n k)
    (fun j L => ∀ hj : j < S.length, S[j].length = k + 1 → Cov L (Dp n (k + 1) S[j]))
    (2 * n * n + n + 1) S.length (fun L M h => plev_ext h M) (fun j L M h hj hl => (h hj hl).ext M)
    (fun j hj L hL hl => by
      by_cases hlen : S[j].length = k + 1
      · exact gr_mono (step_H hk (List.getElem_mem hj) hlen L hL hl) (cost_le hk)
          (fun M h _ _ => h)
      · exact gr_zero hL (fun _ h' => absurd h' hlen)) S.length (Nat.le_refl _) L hL hlev
  refine gr_mono h (by rw [hS]; exact Nat.le_refl _) (fun M ⟨_, hall⟩ H hH hl => ?_)
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hH
  exact hall j hj hj hl

/-- **Independent reproof of the upper half of K9:** for every `n`, `PHP n` has a resolution
refutation with at most `(n+1)·2^n·(2n²+n+1)` clauses. -/
theorem php_upper (n : Nat) :
    ∃ R : Refutation (PHP n), R.steps.length ≤ (n + 1) * (2 ^ n * (2 * n * n + n + 1)) := by
  have base : Gr (PHP n) [] 1 (PLev n 0) := by
    refine gr_mono (gr_ax (valid_nil _) (pig_mem (p := 0) (Nat.zero_le n))
      (S := Dp n 0 []) ?_) (Nat.le_refl _) (fun M hc H _ hl => ?_)
    · intro l hl
      simp only [pigeonAx, List.mem_map, List.mem_range] at hl
      obtain ⟨g, hg, rfl⟩ := hl
      exact ⟨0, g, Nat.le_refl _, hg, List.not_mem_nil, rfl⟩
    · rw [List.eq_nil_of_length_eq_zero hl]; exact hc
  obtain ⟨M, hM, hv, hlev⟩ := gr_seq base (fun M hv hl =>
    gr_iter (F := PHP n) (fun k L => PLev n k L) (2 ^ n * (2 * n * n + n + 1)) n
      (fun k hk L hL hl => step_level (by omega) L hL hl) n (Nat.le_refl _) _ hv hl)
    (Nat.le_refl _)
  obtain ⟨D, hD, hDs⟩ := hlev (List.range n) (sl_self _) List.length_range
  have hDe : D = [] := by
    cases D with
    | nil => rfl
    | cons l D =>
      obtain ⟨i, g, _, hg, hgH, _⟩ := hDs l List.mem_cons_self
      exact absurd (List.mem_range.mpr hg) hgH
  subst hDe
  refine ⟨⟨[] ++ M, hv, hD⟩, ?_⟩
  simp only [List.nil_append]
  have hX : 1 ≤ 2 ^ n * (2 * n * n + n + 1) := Nat.mul_pos (Nat.two_pow_pos n) (Nat.succ_pos _)
  generalize 2 ^ n * (2 * n * n + n + 1) = X at hM hX ⊢
  have e : (n + 1) * X = n * X + X := Nat.succ_mul n X
  omega

end Programme.«20261024-1110-proof-complexity».PHPSize

#print axioms Programme.«20261024-1110-proof-complexity».PHPSize.php_upper
