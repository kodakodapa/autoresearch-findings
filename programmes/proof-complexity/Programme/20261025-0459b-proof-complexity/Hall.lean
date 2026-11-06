import Programme.«20261025-0459b-proof-complexity».CPDagInterp

/-!
# The Hall split formula and DAG-like cutting-planes interpolation

`Hall n = A n ++ B n` over the edge variables `x i j` (`i, j < n`) of a bipartite graph
`G ⊆ K_{n,n}`.

* `A n` says that `(s, t)` is a *Hall violator*: `s_i ∧ x_ij → t_j`, and an injection `z` from
  `t` into `s` misses the point `e` of `s`, so `|t| < |s|`. Edge variables occur only negatively.
* `B n` says that `y ⊆ x` picks, for every left vertex `i`, some `j`, no `j` twice: `G` has a
  perfect matching.

`hall_interp_dag`: every DAG-like refutation `Work.CPDag.DRefutation (Hall n)` with `s` lines gives
a monotone real circuit on the edge variables with `≤ s (2n + 7)` gates, one gate of which is
`≥ 1` on every graph with a perfect matching and `≤ 0` on every graph with a Hall violator
(`S`, `T` with `N(S) ⊆ T`, `|T| < |S|`). Hall's theorem is not needed.
-/

namespace Programme.«20261025-0459b-proof-complexity».Hall

open Programme.«20261024-1110-proof-complexity».Haken (Lit Clause CNF Lit.eval Clause.eval)
open Programme.«20261024-1633-proof-complexity».CP
open Programme.«20261024-1633-proof-complexity».CPInterp
open Programme.«20261025-0459b-proof-complexity».CPDag Programme.«20261025-0459b-proof-complexity».CPDagInterp

inductive V
  | x (i j : Nat)
  | s (i : Nat)
  | t (j : Nat)
  | z (j i : Nat)
  | e (i : Nat)
  | y (i j : Nat)
deriving DecidableEq

/-- `(s, t)` is a Hall violator of the graph `x`, with `|t| < |s|` witnessed by `z` and `e`. -/
def A (n : Nat) : CNF V :=
  ((List.range n).flatMap fun i => (List.range n).map fun j =>
    [⟨V.s i, false⟩, ⟨V.x i j, false⟩, ⟨V.t j, true⟩]) ++
  ((List.range n).map fun j => ⟨V.t j, false⟩ :: (List.range n).map fun i => ⟨V.z j i, true⟩) ++
  ((List.range n).flatMap fun j => (List.range n).map fun i => [⟨V.z j i, false⟩, ⟨V.s i, true⟩]) ++
  ((List.range n).flatMap fun j => (List.range n).flatMap fun j' => (List.range n).flatMap fun i =>
    if j ≠ j' then [[⟨V.z j i, false⟩, ⟨V.z j' i, false⟩]] else []) ++
  [(List.range n).map fun i => ⟨V.e i, true⟩] ++
  ((List.range n).map fun i => [⟨V.e i, false⟩, ⟨V.s i, true⟩]) ++
  ((List.range n).flatMap fun j => (List.range n).map fun i => [⟨V.e i, false⟩, ⟨V.z j i, false⟩])

/-- `y ⊆ x` matches every left vertex, no right vertex twice. -/
def B (n : Nat) : CNF V :=
  ((List.range n).flatMap fun i => (List.range n).map fun j => [⟨V.y i j, false⟩, ⟨V.x i j, true⟩]) ++
  ((List.range n).map fun i => (List.range n).map fun j => ⟨V.y i j, true⟩) ++
  ((List.range n).flatMap fun i => (List.range n).flatMap fun i' => (List.range n).flatMap fun j =>
    if i ≠ i' then [[⟨V.y i j, false⟩, ⟨V.y i' j, false⟩]] else [])

/-- The Hall split CNF. -/
def Hall (n : Nat) : CNF V := A n ++ B n

/-- Private variables of `A`. -/
def isA : V → Bool
  | .s _ | .t _ | .z _ _ | .e _ => true
  | _ => false

/-- Private variables of `B`. -/
def isB : V → Bool
  | .y _ _ => true
  | _ => false

/-- The graph of `β` has a perfect matching. -/
def HasPM (n : Nat) (β : V → Bool) : Prop :=
  ∃ σ : Nat → Nat, (∀ i, i < n → σ i < n ∧ β (.x i (σ i)) = true) ∧
    ∀ i i', i < n → i' < n → i ≠ i' → σ i ≠ σ i'

/-- The graph of `β` has a Hall violator: `N(S) ⊆ T` and `|T| < |S|`. -/
def HasViolator (n : Nat) (β : V → Bool) : Prop :=
  ∃ S T : Nat → Bool, (∀ i j, i < n → j < n → S i = true → β (.x i j) = true → T j = true) ∧
    ((List.range n).filter T).length < ((List.range n).filter S).length

theorem any_of {C : Clause V} {β : V → Bool} (l : Lit V) (h : l ∈ C) (e : l.eval β = true) :
    C.eval β = true := by
  unfold Clause.eval; rw [List.any_eq_true]; exact ⟨l, h, e⟩

theorem sat_B (n : Nat) (β : V → Bool) (h : HasPM n β) :
    ∃ β' : V → Bool, (∀ v, shared isA isB v = true → β' v = β v) ∧ ∀ C ∈ B n, C.eval β' = true := by
  obtain ⟨σ, hσ, hinj⟩ := h
  refine ⟨fun v => match v with
    | .y i j => decide (σ i = j) | v => β v, ?_, ?_⟩
  · intro v hv; cases v <;> simp_all [shared, isA, isB]
  · intro C hC
    simp only [B, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at hC
    rcases hC with (⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, i', hi', j, hj, hC⟩
    · by_cases e : σ i = j
      · subst e; exact any_of ⟨V.x i (σ i), true⟩ (by simp) (by simp [Lit.eval, (hσ i hi).2])
      · exact any_of ⟨V.y i j, false⟩ (by simp) (by simp [Lit.eval, e])
    · exact any_of ⟨V.y i (σ i), true⟩ (List.mem_map.2 ⟨σ i, List.mem_range.2 (hσ i hi).1, rfl⟩)
        (by simp [Lit.eval])
    · split at hC
      · rename_i hne
        simp only [List.mem_singleton] at hC; subst hC
        by_cases e : σ i = j
        · have : σ i' ≠ j := by have := hinj i i' hi hi' hne; omega
          exact any_of ⟨V.y i' j, false⟩ (by simp) (by simp [Lit.eval, this])
        · exact any_of ⟨V.y i j, false⟩ (by simp) (by simp [Lit.eval, e])
      · simp at hC

theorem nodup_filter_range (n : Nat) (P : Nat → Bool) : ((List.range n).filter P).Nodup :=
  (List.nodup_range).filter _

theorem sat_A (n : Nat) (β : V → Bool) (h : HasViolator n β) :
    ∃ β' : V → Bool, (∀ v, shared isA isB v = true → β' v = β v) ∧ ∀ C ∈ A n, C.eval β' = true := by
  classical
  obtain ⟨S, T, hN, hlt⟩ := h
  let Sl := (List.range n).filter S
  let Tl := (List.range n).filter T
  have hSn : Sl.Nodup := nodup_filter_range n S
  have hTn : Tl.Nodup := nodup_filter_range n T
  have hlt' : Tl.length < Sl.length := hlt
  have memS : ∀ i, i ∈ Sl ↔ i < n ∧ S i = true := by intro i; simp [Sl]
  have memT : ∀ j, j ∈ Tl ↔ j < n ∧ T j = true := by intro j; simp [Tl]
  let zf : Nat → Nat → Bool := fun j i => decide (∃ k, ∃ h1 : k < Tl.length, ∃ h2 : k < Sl.length,
    Tl[k] = j ∧ Sl[k] = i)
  let ef : Nat → Bool := fun i => decide (∃ h : Tl.length < Sl.length, Sl[Tl.length] = i)
  refine ⟨fun v => match v with
    | .s i => S i | .t j => T j | .z j i => zf j i | .e i => ef i | v => β v, ?_, ?_⟩
  · intro v hv; cases v <;> simp_all [shared, isA, isB]
  · intro C hC
    simp only [A, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
      List.mem_singleton] at hC
    rcases hC with (((((⟨i, hi, j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, i, hi, rfl⟩) |
      ⟨j, hj, j', hj', i, hi, hC⟩) | rfl) | ⟨i, hi, rfl⟩) | ⟨j, hj, i, hi, rfl⟩
    · by_cases es : S i = true
      · by_cases ex : β (.x i j) = true
        · exact any_of ⟨V.t j, true⟩ (by simp) (by simp [Lit.eval, hN i j hi hj es ex])
        · exact any_of ⟨V.x i j, false⟩ (by simp) (by simp [Lit.eval, ex])
      · exact any_of ⟨V.s i, false⟩ (by simp) (by simp [Lit.eval, es])
    · by_cases et : T j = true
      · have hjT : j ∈ Tl := (memT j).2 ⟨hj, et⟩
        obtain ⟨k, hk, hkj⟩ := List.getElem_of_mem hjT
        have hkS : k < Sl.length := by omega
        have hiS : Sl[k] ∈ Sl := List.getElem_mem hkS
        refine any_of ⟨V.z j Sl[k], true⟩ (List.mem_cons_of_mem _ (List.mem_map.2
          ⟨Sl[k], List.mem_range.2 ((memS _).1 hiS).1, rfl⟩)) ?_
        simp only [Lit.eval, zf]; exact decide_eq_true ⟨k, hk, hkS, hkj, rfl⟩
      · exact any_of ⟨V.t j, false⟩ (by simp) (by simp [Lit.eval, et])
    · by_cases ez : zf j i = true
      · obtain ⟨k, h1, h2, _, hki⟩ := of_decide_eq_true ez
        have : i ∈ Sl := hki ▸ List.getElem_mem h2
        exact any_of ⟨V.s i, true⟩ (by simp) (by simp [Lit.eval, ((memS i).1 this).2])
      · exact any_of ⟨V.z j i, false⟩ (by simp) (by simp [Lit.eval, ez])
    · split at hC
      · rename_i hne
        simp only [List.mem_singleton] at hC; subst hC
        by_cases ez : zf j i = true
        · have ez' : zf j' i = false := by
            obtain ⟨k, h1, h2, hkj, hki⟩ := of_decide_eq_true ez
            simp only [zf, decide_eq_false_iff_not]
            rintro ⟨k', h1', h2', hkj', hki'⟩
            have : k = k' := (List.Nodup.getElem_inj hSn).mp (hki.trans hki'.symm)
            subst this; exact hne (hkj.symm.trans hkj')
          exact any_of ⟨V.z j' i, false⟩ (by simp) (by simp [Lit.eval, ez'])
        · exact any_of ⟨V.z j i, false⟩ (by simp) (by simp [Lit.eval, ez])
      · simp at hC
    · have hm : Sl[Tl.length] ∈ Sl := List.getElem_mem hlt'
      refine any_of ⟨V.e Sl[Tl.length], true⟩ (List.mem_map.2
        ⟨Sl[Tl.length], List.mem_range.2 ((memS _).1 hm).1, rfl⟩) ?_
      simp [Lit.eval, ef, hlt']
    · by_cases ee : ef i = true
      · obtain ⟨h1, hi'⟩ := of_decide_eq_true ee
        have : i ∈ Sl := hi' ▸ List.getElem_mem h1
        exact any_of ⟨V.s i, true⟩ (by simp) (by simp [Lit.eval, ((memS i).1 this).2])
      · exact any_of ⟨V.e i, false⟩ (by simp) (by simp [Lit.eval, ee])
    · by_cases ee : ef i = true
      · have ez : zf j i = false := by
          obtain ⟨h1, hi'⟩ := of_decide_eq_true ee
          simp only [zf, decide_eq_false_iff_not]
          rintro ⟨k, hk1, hk2, _, hki⟩
          have : k = Tl.length := (List.Nodup.getElem_inj hSn).mp (hki.trans hi'.symm)
          omega
        exact any_of ⟨V.z j i, false⟩ (by simp) (by simp [Lit.eval, ez])
      · exact any_of ⟨V.e i, false⟩ (by simp) (by simp [Lit.eval, ee])

theorem hA (n : Nat) : ∀ C ∈ A n, ∀ l ∈ C, isB l.var = false := by
  intro C hC l hl
  simp only [A, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
    List.mem_singleton] at hC
  rcases hC with (((((⟨i, _, j, _, rfl⟩ | ⟨j, _, rfl⟩) | ⟨j, _, i, _, rfl⟩) |
    ⟨j, _, j', _, i, _, hC⟩) | rfl) | ⟨i, _, rfl⟩) | ⟨j, _, i, _, rfl⟩
  · simp at hl; rcases hl with rfl | rfl | rfl <;> rfl
  · simp at hl; rcases hl with rfl | ⟨_, _, rfl⟩ <;> rfl
  · simp at hl; rcases hl with rfl | rfl <;> rfl
  · split at hC
    · simp at hC; subst hC; simp at hl; rcases hl with rfl | rfl <;> rfl
    · simp at hC
  · simp at hl; obtain ⟨_, _, rfl⟩ := hl; rfl
  · simp at hl; rcases hl with rfl | rfl <;> rfl
  · simp at hl; rcases hl with rfl | rfl <;> rfl

theorem hneg (n : Nat) : ∀ C ∈ A n, ∀ l ∈ C, isA l.var = false → l.pos = false := by
  intro C hC l hl hr
  simp only [A, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
    List.mem_singleton] at hC
  rcases hC with (((((⟨i, _, j, _, rfl⟩ | ⟨j, _, rfl⟩) | ⟨j, _, i, _, rfl⟩) |
    ⟨j, _, j', _, i, _, hC⟩) | rfl) | ⟨i, _, rfl⟩) | ⟨j, _, i, _, rfl⟩
  · simp at hl; rcases hl with rfl | rfl | rfl <;> simp_all [isA]
  · simp at hl; rcases hl with rfl | ⟨_, _, rfl⟩ <;> simp_all [isA]
  · simp at hl; rcases hl with rfl | rfl <;> simp_all [isA]
  · split at hC
    · simp at hC; subst hC; simp at hl; rcases hl with rfl | rfl <;> simp_all [isA]
    · simp at hC
  · simp at hl; obtain ⟨_, _, rfl⟩ := hl; simp_all [isA]
  · simp at hl; rcases hl with rfl | rfl <;> simp_all [isA]
  · simp at hl; rcases hl with rfl | rfl <;> simp_all [isA]

theorem hB (n : Nat) : ∀ C ∈ B n, ∀ l ∈ C, isA l.var = false := by
  intro C hC l hl
  simp only [B, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at hC
  rcases hC with (⟨i, _, j, _, rfl⟩ | ⟨i, _, rfl⟩) | ⟨i, _, i', _, j, _, hC⟩
  · simp at hl; rcases hl with rfl | rfl <;> rfl
  · simp at hl; obtain ⟨_, _, rfl⟩ := hl; rfl
  · split at hC
    · simp at hC; subst hC; simp at hl; rcases hl with rfl | rfl <;> rfl
    · simp at hC

theorem hwA (n : Nat) : ∀ C ∈ A n, C.length ≤ n + 3 := by
  intro C hC
  simp only [A, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
    List.mem_singleton] at hC
  rcases hC with (((((⟨i, _, j, _, rfl⟩ | ⟨j, _, rfl⟩) | ⟨j, _, i, _, rfl⟩) |
    ⟨j, _, j', _, i, _, hC⟩) | rfl) | ⟨i, _, rfl⟩) | ⟨j, _, i, _, rfl⟩
  · simp
  · simp
  · simp
  · split at hC
    · simp at hC; subst hC; simp
    · simp at hC
  · simp
  · simp
  · simp

/-- **Interpolation for the Hall split formula, DAG-like cutting planes.** Every DAG-like
refutation of `Hall n` with `s` lines yields a monotone real circuit on the edge variables with at
most `s (2n + 7)` gates, one gate of which is `≥ 1` on every graph with a perfect matching and
`≤ 0` on every graph with a Hall violator. -/
theorem hall_interp_dag (n : Nat) (Rf : DRefutation (Hall n)) :
    ∃ fs, MC (shared isA isB) fs ∧ fs.length ≤ Rf.size * (2 * n + 7) ∧ ∃ f ∈ fs,
      ∀ β, (HasPM n β → 1 ≤ f β) ∧ (HasViolator n β → f β ≤ 0) := by
  have hQR : ∀ v, isA v = true → isB v = false := by intro v; cases v <;> simp [isA, isB]
  obtain ⟨fs, hfs, hlen, f, hf, hsep⟩ :=
    interp_dag (A n) (B n) isA isB (n + 3) (hwA n) hQR (hA n) (hB n) (hneg n) Rf
  have hloc : ∀ α β : V → Bool, (∀ v, shared isA isB v = true → α v = β v) → f α = f β :=
    fun α β h => MC.local h hfs f hf
  have e : 2 * (n + 3) + 1 = 2 * n + 7 := by omega
  rw [e] at hlen
  refine ⟨fs, hfs, hlen, f, hf, fun β => ⟨fun hc => ?_, fun hc => ?_⟩⟩
  · obtain ⟨β', hag, hsat⟩ := sat_B n β hc
    rw [← hloc β' β hag]
    have h2 := (hsep β').2
    by_cases h : 1 ≤ f β'
    · exact h
    · exact absurd hsat (h2 (by omega))
  · obtain ⟨β', hag, hsat⟩ := sat_A n β hc
    rw [← hloc β' β hag]
    have h1 := (hsep β').1
    by_cases h : f β' ≤ 0
    · exact h
    · exact absurd hsat (h1 (by omega))

end Programme.«20261025-0459b-proof-complexity».Hall
