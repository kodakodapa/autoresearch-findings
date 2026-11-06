import Programme.«20261024-1110-proof-complexity».PHPSize
/-!
# The exact resolution width of the pigeonhole principle is `n`, for all `n ≥ 2` (core Lean 4)

`PHP n` (`n+1` pigeons, `n` holes) is the formula of `Work.Haken` (restated verbatim in
`Work.PHPSize`). `X n` lists its `n(n+1)` variables.

* `php_der_width`: `PHP n` has a width-`n` resolution refutation (`Der`, the width-bounded
  derivability of `Work.BSW`) for every `n ≥ 2`.
* `php_no_der`: it has none of width `n-1`. At that width no pigeon clause is admissible, and the
  hole clauses alone are satisfied by the all-false assignment.
* `php_width`: every `Refutation` (weakening allowed) has a line with at least `n` distinct literals.

The upper bound is the standard inductive construction (the general-`n` form of K8). Pick a
pigeon `p` and, for each hole `h`, refute the residual `PHP` on the other pigeons and holes
`H∖h` under the context `¬x_{p,h}`. Then cut the pigeon clause of `p` against these contexts.
Holes left plus context literals stay at most `n`. So the width-based method (Ben-Sasson–
Wigderson) gives nothing for `PHP^{n+1}_n` beyond its initial width `n`.
-/

set_option linter.unusedSectionVars false

namespace Programme.«20261024-1110-proof-complexity».PHPWidth
open Programme.«20261024-1110-proof-complexity».BSW Programme.«20261024-1110-proof-complexity».PHPSize

/-- The variables of `PHP n`. -/
def X (n : Nat) : List (Nat × Nat) :=
  (List.range (n + 1)).flatMap fun p => (List.range n).map fun h => (p, h)

theorem mem_X {n : Nat} {v : Nat × Nat} : v ∈ X n ↔ v.1 ≤ n ∧ v.2 < n := by
  obtain ⟨p, h⟩ := v
  simp only [X, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨p', hp, h', hh, rfl, rfl⟩; exact ⟨by omega, hh⟩
  · rintro ⟨hp, hh⟩; exact ⟨p, by omega, h, hh, rfl, rfl⟩

theorem nodup_fm (n : Nat) : ∀ L : List Nat, L.Nodup →
    (L.flatMap fun p => (List.range n).map fun h => (p, h)).Nodup
  | [], _ => by simp
  | p :: L, hL => by
    rw [List.flatMap_cons, List.nodup_append]
    rw [List.nodup_cons] at hL
    refine ⟨List.Pairwise.map _ (fun a b hab e => hab (by simpa using e)) List.nodup_range, nodup_fm n L hL.2, ?_⟩
    intro a ha b hb e
    subst e
    simp only [List.mem_map, List.mem_flatMap, List.mem_range] at ha hb
    obtain ⟨h, _, rfl⟩ := ha
    obtain ⟨q, hq, h', _, e⟩ := hb
    simp only [Prod.mk.injEq] at e
    exact hL.1 (e.1 ▸ hq)

theorem nodup_X (n : Nat) : (X n).Nodup := nodup_fm n _ List.nodup_range

theorem wd_le_length {X : List (Nat × Nat)} (hX : X.Nodup) : ∀ C : Clause (Nat × Nat),
    wd X C ≤ C.length
  | [] => by simp [wd]
  | l :: D => by
    have := wd_cons hX l D; have := wd_le_length hX D; simp; omega

/-- A nodup clause over `X` has `wd = length`. -/
theorem length_le_wd {X : List (Nat × Nat)} (hX : X.Nodup) (C : Clause (Nat × Nat))
    (hC : C.Nodup) (hv : ∀ l ∈ C, l.var ∈ X) : C.length ≤ wd X C := by
  unfold wd
  rw [List.countP_eq_length_filter]
  have hp : ((lits X).filter fun l => decide (l ∈ C)).Perm C := by
    rw [List.perm_ext_iff_of_nodup ((nodup_lits hX).filter _) hC]
    intro l
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨mem_lits.mpr (hv l h), h⟩⟩
  rw [hp.length_eq]; exact Nat.le_refl _

/-- Pigeon `p` restricted to the holes `H`. -/
def pg (p : Nat) (H : List Nat) : Clause (Nat × Nat) := H.map fun h => ⟨(p, h), true⟩

def ng (p h : Nat) : Lit (Nat × Nat) := ⟨(p, h), false⟩

section Up
variable {n W : Nat}

abbrev D (n W : Nat) := Der (· ∈ PHP n) (X n) W

theorem ok_of {n W : Nat} {C : Clause (Nat × Nat)} (hv : ∀ l ∈ C, l.var ∈ X n)
    (hl : C.length ≤ W) : OK (X n) W C :=
  ⟨hv, Nat.le_trans (wd_le_length (nodup_X n) C) hl⟩

theorem hole_der (h2 : 2 ≤ W) {p q h : Nat} (hpq : p ≠ q) (hp : p ≤ n) (hq : q ≤ n) (hh : h < n) :
    ∃ B, D n W B ∧ ng p h ∈ B ∧ ng q h ∈ B ∧ ∀ m ∈ B, m = ng p h ∨ m = ng q h := by
  have hv : ∀ a b, a ≤ n → b ≤ n → ∀ l ∈ holeAx a b h, l.var ∈ X n := by
    intro a b ha hb l hl
    simp [holeAx] at hl
    rcases hl with rfl | rfl <;> exact mem_X.mpr ⟨by assumption, hh⟩
  rcases Nat.lt_or_gt_of_ne hpq with hlt | hlt
  · refine ⟨holeAx p q h, Der.ax (hole_mem hlt hq hh) (ok_of (hv p q hp hq) (by simp [holeAx]; omega)),
      by simp [holeAx, ng], by simp [holeAx, ng], ?_⟩
    intro m hm; simp [holeAx] at hm; simpa [ng] using hm
  · refine ⟨holeAx q p h, Der.ax (hole_mem hlt hp hh) (ok_of (hv q p hq hp) (by simp [holeAx]; omega)),
      by simp [holeAx, ng], by simp [holeAx, ng], ?_⟩
    intro m hm; simp [holeAx] at hm; rcases hm with h | h <;> simp [ng, h]

/-- Cutting the pigeon clause of `p` on the holes `S` against the contexts `¬x_{p,h} ∨ G`. -/
theorem strip {p : Nat} (hp : p ≤ n) {G : Clause (Nat × Nat)} (hG : ∀ l ∈ G, l.var ∈ X n) :
    ∀ S : List Nat, (∀ h ∈ S, h < n) → S.length + G.length ≤ W →
      D n W (pg p S ++ G) → (∀ h ∈ S, D n W (ng p h :: G)) → D n W G
  | [], _, _, hd, _ => by simpa [pg] using hd
  | h :: S, hS, hl, hd, hc => by
    apply strip hp hG S (fun g hg => hS g (List.mem_cons_of_mem _ hg)) (by simp at hl; omega) _
      (fun g hg => hc g (List.mem_cons_of_mem _ hg))
    have hv : ∀ l ∈ pg p S ++ G, l.var ∈ X n := by
      intro l hl'
      rcases List.mem_append.mp hl' with hl' | hl'
      · simp [pg] at hl'; obtain ⟨g, hg, rfl⟩ := hl'
        exact mem_X.mpr ⟨hp, hS g (List.mem_cons_of_mem _ hg)⟩
      · exact hG l hl'
    refine Der.res ⟨(p, h), true⟩ hd (hc h List.mem_cons_self) (by simp [pg]) (by simp [ng, Lit.neg]) ?_ ?_
      (ok_of hv (by simp at hl ⊢; simp [pg]; omega))
    · intro m hm hne
      rcases List.mem_append.mp hm with hm | hm
      · simp [pg] at hm
        rcases hm with rfl | ⟨g, hg, rfl⟩
        · exact absurd rfl hne
        · exact List.mem_append_left _ (List.mem_map.mpr ⟨g, hg, rfl⟩)
      · exact List.mem_append_right _ hm
    · intro m hm hne
      rcases List.mem_cons.mp hm with rfl | hm
      · simp [ng, Lit.neg] at hne
      · exact List.mem_append_right _ hm

/-- The induction: pigeons `P` (`|P| = k+1`), holes `H` (`|H| = k`), context `G`; if every
`pg i H ∨ G` (`i ∈ P`) is derivable then so is `G`. Width `|H| + |G| ≤ W`. -/
theorem key (h2 : 2 ≤ W) : ∀ (k : Nat) (P H : List Nat) (G : Clause (Nat × Nat)),
    P.length = k + 1 → H.length = k → P.Nodup → (∀ p ∈ P, p ≤ n) → (∀ h ∈ H, h < n) →
    (∀ l ∈ G, l.var ∈ X n) → k + G.length ≤ W →
    (∀ i ∈ P, D n W (pg i H ++ G)) → D n W G
  | 0, P, H, G, hP, hH, _, _, _, _, _, hd => by
    obtain ⟨p, hp⟩ : ∃ p, p ∈ P := by
      cases P with
      | nil => simp at hP
      | cons p _ => exact ⟨p, List.mem_cons_self⟩
    have := hd p hp
    rw [List.length_eq_zero_iff.mp hH] at this
    simpa [pg] using this
  | k + 1, P, H, G, hP, hH, hnd, hPn, hHn, hG, hW, hd => by
    obtain ⟨ps, rest, rfl⟩ : ∃ ps rest, P = ps :: rest := by
      cases P with
      | nil => simp at hP
      | cons p r => exact ⟨p, r, rfl⟩
    rw [List.nodup_cons] at hnd
    have hps : ps ≤ n := hPn ps List.mem_cons_self
    apply strip hps hG H hHn (by omega) (hd ps List.mem_cons_self)
    intro h hh
    have hhn := hHn h hh
    have hG2 : ∀ l ∈ ng ps h :: G, l.var ∈ X n := by
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · exact mem_X.mpr ⟨hps, hhn⟩
      · exact hG l hl
    apply key h2 k rest (H.erase h) (ng ps h :: G) (by simpa using hP)
      (by rw [List.length_erase_of_mem hh]; omega) hnd.2
      (fun p hp => hPn p (List.mem_cons_of_mem _ hp))
      (fun g hg => hHn g (List.erase_subset hg)) hG2 (by simp; omega)
    intro i hi
    have hin : i ≠ ps := fun e => hnd.1 (e ▸ hi)
    have hin' := hPn i (List.mem_cons_of_mem _ hi)
    obtain ⟨B, hB, hiB, hpB, hBm⟩ := hole_der h2 hin hin' hps hhn
    have hv : ∀ l ∈ pg i (H.erase h) ++ ng ps h :: G, l.var ∈ X n := by
      intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · simp [pg] at hl; obtain ⟨g, hg, rfl⟩ := hl
        exact mem_X.mpr ⟨hin', hHn g (List.erase_subset hg)⟩
      · exact hG2 l hl
    refine Der.res ⟨(i, h), true⟩ (hd i (List.mem_cons_of_mem _ hi)) hB
      (List.mem_append_left _ (by simp [pg]; exact hh)) (by simpa [ng, Lit.neg] using hiB) ?_ ?_
      (ok_of hv ?_)
    · intro m hm hne
      rcases List.mem_append.mp hm with hm | hm
      · simp [pg] at hm; obtain ⟨g, hg, rfl⟩ := hm
        have hgh : g ≠ h := fun e => hne (by rw [e])
        exact List.mem_append_left _ (by simp [pg]; exact (List.mem_erase_of_ne hgh).mpr hg)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)
    · intro m hm hne
      rcases hBm m hm with rfl | rfl
      · simp [ng, Lit.neg] at hne
      · exact List.mem_append_right _ List.mem_cons_self
    · simp [pg, List.length_erase_of_mem hh]; omega

end Up

/-- **Upper bound.** For `n ≥ 2`, `PHP n` has a resolution refutation of width `n`. -/
theorem php_der_width {n : Nat} (hn : 2 ≤ n) : Der (· ∈ PHP n) (X n) n [] := by
  apply key hn n (List.range (n + 1)) (List.range n) [] (by simp) (by simp) List.nodup_range
    (fun p hp => by simp at hp; omega) (fun h hh => by simpa using hh) (by simp) (by simp)
  intro i hi
  simp only [List.append_nil]
  have hi' : i ≤ n := by simp at hi; omega
  have : pg i (List.range n) = pigeonAx n i := rfl
  rw [this]
  refine Der.ax (pig_mem hi') (ok_of ?_ (by simp [pigeonAx]))
  intro l hl; simp [pigeonAx] at hl; obtain ⟨h, hh, rfl⟩ := hl
  exact mem_X.mpr ⟨hi', hh⟩

theorem wd_pigeon {n p : Nat} (hp : p ≤ n) : n ≤ wd (X n) (pigeonAx n p) := by
  have := length_le_wd (nodup_X n) (pigeonAx n p)
    (List.Pairwise.map _ (fun a b hab e => hab (by simpa using e)) List.nodup_range)
    (by intro l hl; simp [pigeonAx] at hl; obtain ⟨h, hh, rfl⟩ := hl; exact mem_X.mpr ⟨hp, hh⟩)
  simpa [pigeonAx] using this

/-- **Lower bound.** For `n ≥ 1`, `PHP n` has no resolution refutation of width `n - 1`. -/
theorem php_no_der {n : Nat} (hn : 1 ≤ n) : ¬ Der (· ∈ PHP n) (X n) (n - 1) [] := by
  intro hd
  -- at width `n-1` only hole clauses are admissible axioms
  have conv : ∀ C, Der (· ∈ PHP n) (X n) (n - 1) C →
      Der (fun C => C ∈ PHP n ∧ wd (X n) C ≤ n - 1) (X n) (n - 1) C := by
    intro C h
    induction h with
    | ax hax hok => exact Der.ax ⟨hax, hok.2⟩ hok
    | res l _ _ hlA hlB hA hB hok ihA ihB => exact Der.res l ihA ihB hlA hlB hA hB hok
    | weak _ hAC hok ih => exact Der.weak ih hAC hok
  have := Der.sound (fun _ => false) ?_ (conv _ hd)
  · simp [Clause.eval] at this
  intro C ⟨hC, hw⟩
  simp only [PHP, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_filter,
    List.mem_range] at hC
  rcases hC with ⟨p, hp, rfl⟩ | ⟨h, _, p, _, q, _, rfl⟩
  · have := wd_pigeon (n := n) (p := p) (by omega); omega
  · simp [holeAx, Clause.eval, Lit.eval]

/-- **Exact width, `Refutation` form.** For `n ≥ 1` every resolution refutation (weakening
allowed) of `PHP n` has a line with at least `n` distinct literals; for `n ≥ 2` width `n`
suffices (`php_der_width`). -/
theorem php_width {n : Nat} (hn : 1 ≤ n) (π : Refutation (PHP n)) :
    ∃ C ∈ π.steps, n ≤ wd (X n) C := by
  apply Classical.byContradiction
  intro hno
  apply php_no_der hn
  apply der_of_refutation (W := n - 1) _ π
  · intro C hC
    have : ¬ n ≤ wd (X n) C := fun h => hno ⟨C, hC, h⟩
    omega
  · intro C hC l hl
    simp only [PHP, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_filter,
      List.mem_range] at hC
    rcases hC with ⟨p, hp, rfl⟩ | ⟨h, hh, p, hp, q, ⟨hq, _⟩, rfl⟩
    · simp [pigeonAx] at hl; obtain ⟨h, hh, rfl⟩ := hl; exact mem_X.mpr ⟨by simp; omega, by simpa using hh⟩
    · simp [holeAx] at hl
      rcases hl with rfl | rfl
      · exact mem_X.mpr ⟨by simp; omega, by simpa using hh⟩
      · exact mem_X.mpr ⟨by simp; omega, by simpa using hh⟩

/-- Both halves together. -/
theorem php_exact_width {n : Nat} (hn : 2 ≤ n) :
    Der (· ∈ PHP n) (X n) n [] ∧ ¬ Der (· ∈ PHP n) (X n) (n - 1) [] ∧
    ∀ π : Refutation (PHP n), ∃ C ∈ π.steps, n ≤ wd (X n) C :=
  ⟨php_der_width hn, php_no_der (by omega), php_width (by omega)⟩

end Programme.«20261024-1110-proof-complexity».PHPWidth

#print axioms Programme.«20261024-1110-proof-complexity».PHPWidth.php_exact_width
