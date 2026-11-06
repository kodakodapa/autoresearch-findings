import Programme.«20261024-1633-proof-complexity».CPInterp

/-!
# Clique–colouring formulas and interpolation for tree-like cutting planes

`CC m k = A m k ++ B m k` over graph variables `p i j` (`i < j < m`), clique variables `q l i`
(`l < k`, `i < m`: vertex `i` is the `l`-th member of the clique) and colour variables `r i c`
(`i < m`, `c < k - 1`). `A` says `r` is a proper `(k-1)`-colouring of the graph `p`; `B` says `q`
picks a `k`-clique of `p`. The graph variables occur only negatively in `A`, so `Work.CPInterp.interp`
applies: a tree-like CP refutation with `s` nodes gives a monotone real formula on the graph
variables with `≤ s (2k + 5)` gates that is `≥ 1` on every graph with a `k`-clique and `≤ 0` on
every `(k-1)`-colourable graph (`cc_interp`).
-/

namespace Programme.«20261024-1633-proof-complexity».CliqueColour

open Programme.«20261024-1110-proof-complexity».Haken (Lit Clause CNF Lit.eval Clause.eval)
open Programme.«20261024-1633-proof-complexity».CP Programme.«20261024-1633-proof-complexity».CPInterp

inductive V
  | p (i j : Nat)
  | q (l i : Nat)
  | r (i c : Nat)
deriving DecidableEq

/-- `r` is a proper `(k-1)`-colouring of the graph `p`. -/
def A (m k : Nat) : CNF V :=
  (List.range m).map (fun i => (List.range (k - 1)).map fun c => ⟨V.r i c, true⟩) ++
  (List.range m).flatMap fun i => (List.range m).flatMap fun j =>
    if i < j then (List.range (k - 1)).map fun c =>
      [⟨V.p i j, false⟩, ⟨V.r i c, false⟩, ⟨V.r j c, false⟩] else []

/-- `q` is an injective map from `k` clique positions into pairwise adjacent vertices. -/
def B (m k : Nat) : CNF V :=
  (List.range k).map (fun l => (List.range m).map fun i => ⟨V.q l i, true⟩) ++
  ((List.range k).flatMap fun l => (List.range k).flatMap fun l' => (List.range m).flatMap fun i =>
    if l ≠ l' then [[⟨V.q l i, false⟩, ⟨V.q l' i, false⟩]] else []) ++
  ((List.range k).flatMap fun l => (List.range k).flatMap fun l' => (List.range m).flatMap fun i =>
    (List.range m).flatMap fun j =>
      if l ≠ l' ∧ i < j then [[⟨V.q l i, false⟩, ⟨V.q l' j, false⟩, ⟨V.p i j, true⟩]] else [])

/-- The clique–colouring CNF. -/
def CC (m k : Nat) : CNF V := A m k ++ B m k

def isR : V → Bool
  | .r _ _ => true
  | _ => false

def isQ : V → Bool
  | .q _ _ => true
  | _ => false

/-- Adjacency in the graph read off an assignment. -/
def adj (β : V → Bool) (i j : Nat) : Bool := if i < j then β (.p i j) else β (.p j i)

/-- The graph of `β` on `m` vertices has a `k`-clique. -/
def HasClique (m k : Nat) (β : V → Bool) : Prop :=
  ∃ g : Nat → Nat, (∀ l, l < k → g l < m) ∧
    ∀ l l', l < k → l' < k → l ≠ l' → g l ≠ g l' ∧ adj β (g l) (g l') = true

/-- The graph of `β` on `m` vertices is `(k-1)`-colourable. -/
def Colourable (m k : Nat) (β : V → Bool) : Prop :=
  ∃ col : Nat → Nat, (∀ i, i < m → col i < k - 1) ∧
    ∀ i j, i < j → j < m → adj β i j = true → col i ≠ col j

theorem any_of {C : Clause V} {β : V → Bool} (l : Lit V) (h : l ∈ C) (e : l.eval β = true) :
    C.eval β = true := by
  unfold Clause.eval; rw [List.any_eq_true]; exact ⟨l, h, e⟩

theorem sat_B (m k : Nat) (β : V → Bool) (h : HasClique m k β) :
    ∃ β' : V → Bool, (∀ v, shared isR isQ v = true → β' v = β v) ∧ ∀ C ∈ B m k, C.eval β' = true := by
  obtain ⟨g, hg, hc⟩ := h
  refine ⟨fun v => match v with
    | .p i j => β (.p i j) | .q l i => decide (g l = i) | .r _ _ => false, ?_, ?_⟩
  · intro v hv; cases v <;> simp_all [shared, isR, isQ]
  · intro C hC
    simp only [B, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at hC
    rcases hC with (⟨l, hl, rfl⟩ | ⟨l, hl, l', hl', i, hi, hC⟩) | ⟨l, hl, l', hl', i, hi, j, hj, hC⟩
    · exact any_of ⟨V.q l (g l), true⟩ (List.mem_map.2 ⟨g l, List.mem_range.2 (hg l hl), rfl⟩)
        (by simp [Lit.eval])
    · split at hC
      · rename_i hne
        simp only [List.mem_singleton] at hC; subst hC
        by_cases e : g l = i
        · have : g l' ≠ i := by have := (hc l l' hl hl' hne).1; omega
          exact any_of ⟨V.q l' i, false⟩ (by simp) (by simp [Lit.eval, this])
        · exact any_of ⟨V.q l i, false⟩ (by simp) (by simp [Lit.eval, e])
      · simp at hC
    · split at hC
      · rename_i hne
        simp only [List.mem_singleton] at hC; subst hC
        by_cases e : g l = i
        · by_cases e' : g l' = j
          · have := (hc l l' hl hl' hne.1).2
            rw [e, e'] at this; simp only [adj, hne.2, ite_true] at this
            exact any_of ⟨V.p i j, true⟩ (by simp) (by simp [Lit.eval, this])
          · exact any_of ⟨V.q l' j, false⟩ (by simp) (by simp [Lit.eval, e'])
        · exact any_of ⟨V.q l i, false⟩ (by simp) (by simp [Lit.eval, e])
      · simp at hC

theorem sat_A (m k : Nat) (β : V → Bool) (h : Colourable m k β) :
    ∃ β' : V → Bool, (∀ v, shared isR isQ v = true → β' v = β v) ∧ ∀ C ∈ A m k, C.eval β' = true := by
  obtain ⟨col, hcol, hp⟩ := h
  refine ⟨fun v => match v with
    | .p i j => β (.p i j) | .q _ _ => false | .r i c => decide (col i = c), ?_, ?_⟩
  · intro v hv; cases v <;> simp_all [shared, isR, isQ]
  · intro C hC
    simp only [A, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at hC
    rcases hC with ⟨i, hi, rfl⟩ | ⟨i, hi, j, hj, hC⟩
    · exact any_of ⟨V.r i (col i), true⟩ (List.mem_map.2 ⟨col i, List.mem_range.2 (hcol i hi), rfl⟩)
        (by simp [Lit.eval])
    · split at hC
      · rename_i hij
        simp only [List.mem_map, List.mem_range] at hC
        obtain ⟨c, _, rfl⟩ := hC
        by_cases ep : β (.p i j) = true
        · have := hp i j hij hj (by simp [adj, hij, ep])
          by_cases e : col i = c
          · have : col j ≠ c := by omega
            exact any_of ⟨V.r j c, false⟩ (by simp) (by simp [Lit.eval, this])
          · exact any_of ⟨V.r i c, false⟩ (by simp) (by simp [Lit.eval, e])
        · exact any_of ⟨V.p i j, false⟩ (by simp) (by simp [Lit.eval, ep])
      · simp at hC

theorem hA (m k : Nat) : ∀ C ∈ A m k, ∀ l ∈ C, isQ l.var = false := by
  intro C hC l hl
  simp only [A, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at hC
  rcases hC with ⟨i, _, rfl⟩ | ⟨i, _, j, _, hC⟩
  · simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨c, _, rfl⟩ := hl; rfl
  · split at hC
    · simp only [List.mem_map, List.mem_range] at hC
      obtain ⟨c, _, rfl⟩ := hC
      simp at hl; rcases hl with rfl | rfl | rfl <;> rfl
    · simp at hC

theorem hneg (m k : Nat) : ∀ C ∈ A m k, ∀ l ∈ C, isR l.var = false → l.pos = false := by
  intro C hC l hl hr
  simp only [A, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at hC
  rcases hC with ⟨i, _, rfl⟩ | ⟨i, _, j, _, hC⟩
  · simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨c, _, rfl⟩ := hl; simp [isR] at hr
  · split at hC
    · simp only [List.mem_map, List.mem_range] at hC
      obtain ⟨c, _, rfl⟩ := hC
      simp at hl; rcases hl with rfl | rfl | rfl <;> rfl
    · simp at hC

theorem hB (m k : Nat) : ∀ C ∈ B m k, ∀ l ∈ C, isR l.var = false := by
  intro C hC l hl
  simp only [B, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at hC
  rcases hC with (⟨l, _, rfl⟩ | ⟨_, _, _, _, _, _, hC⟩) | ⟨_, _, _, _, _, _, _, _, hC⟩
  · simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨c, _, rfl⟩ := hl; rfl
  · split at hC
    · simp at hC; subst hC; simp at hl; rcases hl with rfl | rfl <;> rfl
    · simp at hC
  · split at hC
    · simp at hC; subst hC; simp at hl; rcases hl with rfl | rfl | rfl <;> rfl
    · simp at hC

theorem hwA (m k : Nat) : ∀ C ∈ A m k, C.length ≤ k + 2 := by
  intro C hC
  simp only [A, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at hC
  rcases hC with ⟨i, _, rfl⟩ | ⟨i, _, j, _, hC⟩
  · simp; omega
  · split at hC
    · simp only [List.mem_map, List.mem_range] at hC
      obtain ⟨c, _, rfl⟩ := hC; simp; omega
    · simp at hC

/-- **Interpolation for clique–colouring.** Every tree-like cutting-planes refutation of `CC m k`
with `s` nodes over `X` yields a monotone real formula on the graph variables with at most
`s (2k + 5)` gates that is `≥ 1` on every graph with a `k`-clique and `≤ 0` on every
`(k-1)`-colourable graph. -/
theorem cc_interp (m k : Nat) (Rf : Refutation (CC m k)) :
    ∃ f t, RC (shared isR isQ) f t ∧ t ≤ Rf.size * (2 * k + 5) ∧
      (∀ α β : V → Bool, (∀ v, α v = true → β v = true) → f α ≤ f β) ∧
      ∀ β, (HasClique m k β → 1 ≤ f β) ∧ (Colourable m k β → f β ≤ 0) := by
  have hQR : ∀ v, isR v = true → isQ v = false := by intro v; cases v <;> simp [isR, isQ]
  obtain ⟨f, t, r, ht, hmono, hloc, hsep⟩ :=
    interp_width (A m k) (B m k) isR isQ (k + 2) (hwA m k) hQR (hA m k) (hB m k) (hneg m k) Rf
  refine ⟨f, t, r, by omega, hmono, fun β => ⟨fun hc => ?_, fun hc => ?_⟩⟩
  · obtain ⟨β', hag, hsat⟩ := sat_B m k β hc
    rw [← hloc β' β hag]
    have h2 := (hsep β').2
    by_cases h : 1 ≤ f β'
    · exact h
    · exact absurd hsat (h2 (by omega))
  · obtain ⟨β', hag, hsat⟩ := sat_A m k β hc
    rw [← hloc β' β hag]
    have h1 := (hsep β').1
    by_cases h : f β' ≤ 0
    · exact h
    · exact absurd hsat (h1 (by omega))

end Programme.«20261024-1633-proof-complexity».CliqueColour
