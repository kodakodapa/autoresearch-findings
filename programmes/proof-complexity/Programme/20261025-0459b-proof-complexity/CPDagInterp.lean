import Programme.«20261025-0459b-proof-complexity».CPDag
import Programme.«20261024-1633-proof-complexity».CliqueColour

/-!
# Feasible interpolation for DAG-like cutting planes into monotone real circuits (Pudlák 1997)

`MC P fs` says the list of functions `fs` (newest first) is a *monotone real circuit* over the
variables satisfying `P`: every member is a constant, an input `x_u` with `P u`, or an arbitrary
monotone function `ℤ → ℤ` / `ℤ × ℤ → ℤ` applied to members already in the list. The size is the
number of gates `fs.length`; a gate may feed any number of later gates.

`interp_dag`: from a DAG-like refutation (`Work.CPDag.DRefutation`) of `A ++ B` with `s` lines,
shared variables only negative in `A`, clauses of `A` of width `≤ w`, a monotone real circuit with
`≤ s (2w + 1)` gates on the shared variables, one of whose gates is `≥ 1` where `A` is false and
`≤ 0` where `B` is false. It is Pudlák's interpolation (the invariant `CPInterp.Inv`), carried out
line by line, so a line used twice is computed once.

`cc_interp_dag`: the instance for clique–colouring, `≤ s (2k + 5)` gates.
-/

namespace Programme.«20261025-0459b-proof-complexity».CPDagInterp

open Programme.«20261024-1110-proof-complexity».Haken (Lit Clause CNF Lit.eval Clause.eval)
open Programme.«20261024-1633-proof-complexity».CP
open Programme.«20261024-1633-proof-complexity».CPInterp
open Programme.«20261025-0459b-proof-complexity».CPDag

/-- One gate of a monotone real circuit, reading earlier gates `fs`. -/
inductive GJ {V : Type} (P : V → Bool) (fs : List ((V → Bool) → Int)) : ((V → Bool) → Int) → Prop
  | const (k : Int) : GJ P fs (fun _ => k)
  | inp (u : V) : P u = true → GJ P fs (fun β => val β u)
  | gate1 {f : (V → Bool) → Int} (g : Int → Int) : (∀ x y, x ≤ y → g x ≤ g y) → f ∈ fs →
      GJ P fs (fun β => g (f β))
  | gate2 {f h : (V → Bool) → Int} (g : Int → Int → Int) :
      (∀ x x' y y', x ≤ x' → y ≤ y' → g x y ≤ g x' y') → f ∈ fs → h ∈ fs →
      GJ P fs (fun β => g (f β) (h β))

/-- A monotone real circuit: the list of its gate functions, newest first. -/
inductive MC {V : Type} (P : V → Bool) : List ((V → Bool) → Int) → Prop
  | nil : MC P []
  | cons {fs : List ((V → Bool) → Int)} {f : (V → Bool) → Int} : MC P fs → GJ P fs f →
      MC P (f :: fs)

/-- Every gate of a monotone real circuit is non-decreasing. -/
theorem MC.mono {V : Type} {P : V → Bool} {α β : V → Bool} (h : ∀ v, α v = true → β v = true) :
    ∀ {fs : List ((V → Bool) → Int)}, MC P fs → ∀ f ∈ fs, f α ≤ f β
  | _, .nil => by simp
  | _, .cons c j => by
    have ih := MC.mono h c
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · cases j with
      | const k => exact Int.le_refl _
      | inp u _ => exact val_mono h u
      | gate1 g hg h1 => exact hg _ _ (ih _ h1)
      | gate2 g hg h1 h2 => exact hg _ _ _ _ (ih _ h1) (ih _ h2)
    · exact ih f hf

/-- Every gate of a monotone real circuit reads only the variables in `P`. -/
theorem MC.local {V : Type} {P : V → Bool} {α β : V → Bool} (h : ∀ v, P v = true → α v = β v) :
    ∀ {fs : List ((V → Bool) → Int)}, MC P fs → ∀ f ∈ fs, f α = f β
  | _, .nil => by simp
  | _, .cons c j => by
    have ih := MC.local h c
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · cases j with
      | const k => rfl
      | inp u hu => simp [val, h u hu]
      | gate1 g hg h1 => simp only [ih _ h1]
      | gate2 g hg h1 h2 => simp only [ih _ h1, ih _ h2]
    · exact ih f hf

/-- A formula with `t` gates can be appended to a circuit with `t` new gates. -/
theorem of_RC {V : Type} {P : V → Bool} {f : (V → Bool) → Int} {t : Nat} (r : RC P f t) :
    ∀ fs, MC P fs → ∃ fs', MC P fs' ∧ f ∈ fs' ∧ (∀ g ∈ fs, g ∈ fs') ∧
      fs'.length ≤ fs.length + t := by
  induction r with
  | const k =>
    intro fs c
    exact ⟨_, c.cons (GJ.const k), List.mem_cons_self .., fun g h => List.mem_cons_of_mem _ h,
      by simp⟩
  | inp u hu =>
    intro fs c
    exact ⟨_, c.cons (GJ.inp u hu), List.mem_cons_self .., fun g h => List.mem_cons_of_mem _ h,
      by simp⟩
  | gate1 g hg _ ih =>
    intro fs c
    obtain ⟨l1, c1, m1, s1, n1⟩ := ih fs c
    exact ⟨_, c1.cons (GJ.gate1 g hg m1), List.mem_cons_self ..,
      fun M h => List.mem_cons_of_mem _ (s1 _ h), by simp; omega⟩
  | gate2 g hg _ _ ih1 ih2 =>
    intro fs c
    obtain ⟨l1, c1, m1, s1, n1⟩ := ih1 fs c
    obtain ⟨l2, c2, m2, s2, n2⟩ := ih2 l1 c1
    exact ⟨_, c2.cons (GJ.gate2 g hg (s2 _ m1) m2), List.mem_cons_self ..,
      fun M h => List.mem_cons_of_mem _ (s2 _ (s1 _ h)), by simp; omega⟩

section
variable {V : Type} [DecidableEq V] (A B : CNF V) (Q R : V → Bool) (X : List V)

theorem interp_dag_chain (w : Nat)
    (hw : ∀ C ∈ A, (X.filter fun v => decide (v ∈ C.map Lit.var)).length ≤ w) (hX : X.Nodup)
    (cover : ∀ C ∈ A ++ B, ∀ l ∈ C, l.var ∈ X)
    (hQR : ∀ v, Q v = true → R v = false)
    (hA : ∀ C ∈ A, ∀ l ∈ C, R l.var = false) (hB : ∀ C ∈ B, ∀ l ∈ C, Q l.var = false)
    (hneg : ∀ C ∈ A, ∀ l ∈ C, Q l.var = false → l.pos = false) :
    ∀ {ls : List (Line V)}, Chain (A ++ B) ls →
    ∃ fs, MC (shared Q R) fs ∧ fs.length ≤ ls.length * (2 * w + 1) ∧
      ∀ L ∈ ls, ∃ f ∈ fs, Inv A B Q R X L f
  | _, .nil => ⟨[], MC.nil, by simp, by simp⟩
  | _, @Chain.cons _ _ _ ls L c j => by
    obtain ⟨fs, hfs, hlen, hinv⟩ := interp_dag_chain w hw hX cover hQR hA hB hneg c
    -- the leaf cases: a formula from `interp_node` on a one-node derivation
    have leaf : ∀ {s : Nat}, D (A ++ B) L s → s = 1 →
        ∃ fs', MC (shared Q R) fs' ∧ fs'.length ≤ (L :: ls).length * (2 * w + 1) ∧
          ∀ M ∈ L :: ls, ∃ f ∈ fs', Inv A B Q R X M f := by
      intro s d hs
      obtain ⟨f, t, r, ht, hi⟩ := interp_node A B Q R X w hw hX cover hQR hA hB hneg d
      obtain ⟨fs', c', m', s', n'⟩ := of_RC r fs hfs
      refine ⟨fs', c', ?_, ?_⟩
      · subst hs; simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at ht ⊢; omega
      · intro M hM
        rcases List.mem_cons.1 hM with rfl | hM
        · exact ⟨f, m', hi⟩
        · obtain ⟨g, hg, hgi⟩ := hinv M hM; exact ⟨g, s' g hg, hgi⟩
    -- the inner cases: one new gate
    have inner : ∀ f, GJ (shared Q R) fs f → Inv A B Q R X L f →
        ∃ fs', MC (shared Q R) fs' ∧ fs'.length ≤ (L :: ls).length * (2 * w + 1) ∧
          ∀ M ∈ L :: ls, ∃ f ∈ fs', Inv A B Q R X M f := by
      intro f hg hi
      refine ⟨f :: fs, hfs.cons hg, ?_, ?_⟩
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
      · intro M hM
        rcases List.mem_cons.1 hM with rfl | hM
        · exact ⟨f, List.mem_cons_self .., hi⟩
        · obtain ⟨g, hg, hgi⟩ := hinv M hM; exact ⟨g, List.mem_cons_of_mem _ hg, hgi⟩
    cases j with
    | ax C hC => exact leaf (D.ax C hC) rfl
    | lo u => exact leaf (D.lo u) rfl
    | hi u => exact leaf (D.hi u) rfl
    | @add L1 L2 h1 h2 =>
      obtain ⟨f1, m1, i1, j1⟩ := hinv L1 h1
      obtain ⟨f2, m2, i2, j2⟩ := hinv L2 h2
      refine inner (fun β => f1 β + f2 β)
        (GJ.gate2 (fun x y => x + y) (by intro x x' y y' _ _; omega) m1 m2) ⟨?_, ?_⟩
      · intro β hβ; have := i1 β hβ; have := i2 β hβ
        simp only [part_add]; omega
      · intro β hβ; have := j1 β hβ; have := j2 β hβ
        rw [part_add, part_add]; simp only [Line.add]; omega
    | @smul L1 k h1 =>
      obtain ⟨f1, m1, i1, j1⟩ := hinv L1 h1
      refine inner (fun β => k * f1 β)
        (GJ.gate1 (fun x => k * x)
          (fun x y h => Int.mul_le_mul_of_nonneg_left h (Int.natCast_nonneg k)) m1) ⟨?_, ?_⟩
      · intro β hβ
        simp only [part_smul]
        exact Int.mul_le_mul_of_nonneg_left (i1 β hβ) (Int.natCast_nonneg k)
      · intro β hβ
        rw [part_smul, part_smul]; simp only [Line.smul]
        have := Int.mul_le_mul_of_nonneg_left (j1 β hβ) (Int.natCast_nonneg k)
        rw [Int.mul_sub, Int.mul_add] at this; exact this
    | @div L1 k a' b' h1 hc ha hb =>
      obtain ⟨f1, m1, i1, j1⟩ := hinv L1 h1
      refine inner (fun β => cdiv k (f1 β))
        (GJ.gate1 (cdiv k) (fun x y h => Int.ediv_le_ediv (by omega) (by omega)) m1) ⟨?_, ?_⟩
      · intro β hβ
        have h1 := i1 β hβ
        rw [part_div Q X k L1 a' b' ha] at h1
        have ⟨_, h3⟩ := cdiv_spec k hc (f1 β)
        have : (k : Int) * cdiv k (f1 β) < k * (part Q X ⟨a', b'⟩ β + 1) := by
          rw [Int.mul_add]; omega
        have := lt_of_cmul this
        show cdiv k (f1 β) ≤ _; omega
      · intro β hβ
        have h1 := j1 β hβ
        rw [part_div R X k L1 a' b' ha, part_div (shared Q R) X k L1 a' b' ha] at h1
        have ⟨h2, _⟩ := cdiv_spec k hc (f1 β)
        have : (k : Int) * (b' - 1) < k * (part R X ⟨a', b'⟩ β + part (shared Q R) X ⟨a', b'⟩ β +
            cdiv k (f1 β)) := by
          rw [Int.mul_add, Int.mul_add]; omega
        have := lt_of_cmul this
        show b' - cdiv k (f1 β) ≤ _; omega

end

/-- **Feasible interpolation for DAG-like cutting planes into monotone real circuits.** -/
theorem interp_dag {V} [DecidableEq V] (A B : CNF V) (Q R : V → Bool) (w : Nat)
    (hwA : ∀ C ∈ A, C.length ≤ w)
    (hQR : ∀ v, Q v = true → R v = false)
    (hA : ∀ C ∈ A, ∀ l ∈ C, R l.var = false) (hB : ∀ C ∈ B, ∀ l ∈ C, Q l.var = false)
    (hneg : ∀ C ∈ A, ∀ l ∈ C, Q l.var = false → l.pos = false)
    (Rf : DRefutation (A ++ B)) :
    ∃ fs, MC (shared Q R) fs ∧ fs.length ≤ Rf.size * (2 * w + 1) ∧ ∃ f ∈ fs,
      ∀ β, (1 ≤ f β → ¬ ∀ C ∈ A, C.eval β = true) ∧ (f β ≤ 0 → ¬ ∀ C ∈ B, C.eval β = true) := by
  have hw : ∀ C ∈ A, (Rf.X.filter fun v => decide (v ∈ C.map Lit.var)).length ≤ w := by
    intro C hC
    have h1 := List.Nodup.length_le_of_subset (Rf.nodup.filter (fun v => decide (v ∈ C.map Lit.var)))
      (l₂ := C.map Lit.var) (by intro v hv; have := (List.mem_filter.1 hv).2; simpa using this)
    have := hwA C hC; rw [List.length_map] at h1; omega
  obtain ⟨fs, hfs, hlen, hinv⟩ :=
    interp_dag_chain A B Q R Rf.X w hw Rf.nodup Rf.cover hQR hA hB hneg Rf.chain
  obtain ⟨f, hf, iA, iB⟩ := hinv _ Rf.final
  refine ⟨fs, hfs, hlen, f, hf, fun β => ⟨?_, ?_⟩⟩
  · intro h1 hβ
    have := iA β hβ
    rw [part_vanish Q _ _ β (fun _ _ => rfl)] at this; omega
  · intro h1 hβ
    have := iB β hβ
    rw [part_vanish R _ _ β (fun _ _ => rfl), part_vanish _ _ _ β (fun _ _ => rfl)] at this
    simp only at this; omega

open Programme.«20261024-1633-proof-complexity».CliqueColour

/-- **Interpolation for clique–colouring, DAG-like cutting planes.** Every DAG-like refutation of
`CC m k` with `s` lines yields a monotone real circuit on the graph variables with at most
`s (2k + 5)` gates, one gate of which is `≥ 1` on every graph with a `k`-clique and `≤ 0` on every
`(k-1)`-colourable graph. -/
theorem cc_interp_dag (m k : Nat) (Rf : DRefutation (CC m k)) :
    ∃ fs, MC (shared isR isQ) fs ∧ fs.length ≤ Rf.size * (2 * k + 5) ∧ ∃ f ∈ fs,
      ∀ β, (HasClique m k β → 1 ≤ f β) ∧ (Colourable m k β → f β ≤ 0) := by
  have hQR : ∀ v, isR v = true → isQ v = false := by intro v; cases v <;> simp [isR, isQ]
  obtain ⟨fs, hfs, hlen, f, hf, hsep⟩ :=
    interp_dag (A m k) (B m k) isR isQ (k + 2) (hwA m k) hQR (hA m k) (hB m k) (hneg m k) Rf
  have hloc : ∀ α β : V → Bool, (∀ v, shared isR isQ v = true → α v = β v) → f α = f β :=
    fun α β h => MC.local h hfs f hf
  have e : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
  rw [e] at hlen
  refine ⟨fs, hfs, hlen, f, hf, fun β => ⟨fun hc => ?_, fun hc => ?_⟩⟩
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

end Programme.«20261025-0459b-proof-complexity».CPDagInterp
