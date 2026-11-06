import Programme.«20261024-1633-proof-complexity».CliqueColour

/-!
# DAG-like cutting planes and interpolation into monotone real circuits (Pudlák 1997)

`DD F Ls` says the list of lines `Ls` is a (DAG-like) cutting-planes derivation from `F`: every
line is a clause axiom, a bound `x_u ≥ 0` / `-x_u ≥ -1`, or follows from lines *earlier in the
list* by addition, multiplication by a natural number, or division with rounding (the rules of
`CP.D`). A line may be used any number of times. `DRefutation F` contains `0 ≥ 1`; its size is the
number of lines.

`MC P fs` says the list `fs` of functions is a monotone real circuit over the variables in `P`:
each gate is a constant, an input `x_u` with `P u`, or an arbitrary monotone unary / binary
integer function applied to *earlier* gates. The size is the number of gates.

Main results:
* `ofTree`: a tree-like refutation (`CP.Refutation`) with `s` nodes gives a DAG refutation with at
  most `s` lines, so DAG size lower bounds imply tree-like ones.
* `dsound`: soundness.
* `dinterp`: if the shared variables occur only negatively in `A` and every clause of `A` has at
  most `w` literals, a DAG refutation of `A ++ B` with `s` lines yields a monotone real circuit on
  the shared variables with at most `s (2w + 1)` gates, one of whose gates `f` satisfies
  `f β ≥ 1 → β` falsifies `A` and `f β ≤ 0 → β` falsifies `B`.
* `cc_dinterp`: for the clique–colouring CNF, a circuit with `≤ s (2k + 5)` gates whose output is
  `≥ 1` on graphs with a `k`-clique and `≤ 0` on `(k-1)`-colourable graphs.
-/

namespace Programme.«20261025-0459b-proof-complexity».CPDagPr

open Programme.«20261024-1110-proof-complexity».Haken (Lit Clause CNF Lit.eval Clause.eval)
open Programme.«20261024-1633-proof-complexity».CP
open Programme.«20261024-1633-proof-complexity».CPInterp

/-- DAG-like cutting-planes derivations: each new line follows from earlier lines. -/
inductive DD {V} [DecidableEq V] (F : CNF V) : List (Line V) → Prop
  | nil : DD F []
  | ax {Ls : List (Line V)} (C : Clause V) : DD F Ls → C ∈ F → DD F (Ls ++ [clauseLine C])
  | lo {Ls : List (Line V)} (u : V) : DD F Ls → DD F (Ls ++ [⟨fun v => if u = v then 1 else 0, 0⟩])
  | hi {Ls : List (Line V)} (u : V) : DD F Ls →
      DD F (Ls ++ [⟨fun v => if u = v then -1 else 0, -1⟩])
  | add {Ls : List (Line V)} {L M : Line V} : DD F Ls → L ∈ Ls → M ∈ Ls → DD F (Ls ++ [L.add M])
  | smul {Ls : List (Line V)} {L : Line V} (c : Nat) : DD F Ls → L ∈ Ls → DD F (Ls ++ [L.smul c])
  | div {Ls : List (Line V)} {L : Line V} (c : Nat) (a' : V → Int) (b' : Int) : DD F Ls → L ∈ Ls →
      0 < c → (∀ v, L.a v = (c : Int) * a' v) → (c : Int) * (b' - 1) < L.b → DD F (Ls ++ [⟨a', b'⟩])

/-- A DAG-like cutting-planes refutation of `F`; its size is the number of lines. -/
structure DRefutation {V} [DecidableEq V] (F : CNF V) where
  X : List V
  nodup : X.Nodup
  cover : ∀ C ∈ F, ∀ l ∈ C, l.var ∈ X
  lines : List (Line V)
  deriv : DD F lines
  contra : (⟨fun _ => 0, 1⟩ : Line V) ∈ lines

def DRefutation.size {V} [DecidableEq V] {F : CNF V} (R : DRefutation F) : Nat := R.lines.length

/-! ## Tree-like refutations are DAG refutations -/

theorem DD.append {V} [DecidableEq V] {F : CNF V} {Ls : List (Line V)} (h : DD F Ls) :
    ∀ {Ms : List (Line V)}, DD F Ms → DD F (Ms ++ Ls) := by
  induction h with
  | nil => intro Ms hM; simpa using hM
  | ax C _ hC ih => intro Ms hM; rw [← List.append_assoc]; exact DD.ax C (ih hM) hC
  | lo u _ ih => intro Ms hM; rw [← List.append_assoc]; exact DD.lo u (ih hM)
  | hi u _ ih => intro Ms hM; rw [← List.append_assoc]; exact DD.hi u (ih hM)
  | add _ hL hM' ih =>
    intro Ms hM; rw [← List.append_assoc]
    exact DD.add (ih hM) (List.mem_append_right _ hL) (List.mem_append_right _ hM')
  | smul c _ hL ih =>
    intro Ms hM; rw [← List.append_assoc]; exact DD.smul c (ih hM) (List.mem_append_right _ hL)
  | div c a' b' _ hL hc ha hb ih =>
    intro Ms hM; rw [← List.append_assoc]
    exact DD.div c a' b' (ih hM) (List.mem_append_right _ hL) hc ha hb

theorem ofD {V} [DecidableEq V] {F : CNF V} {L : Line V} {s : Nat} (d : D F L s) :
    ∃ Ls : List (Line V), DD F Ls ∧ L ∈ Ls ∧ Ls.length ≤ s := by
  induction d with
  | ax C hC => exact ⟨[clauseLine C], by simpa using DD.ax C DD.nil hC, by simp, by simp⟩
  | lo u => exact ⟨_, by simpa using DD.lo (F := F) u DD.nil, by simp, by simp⟩
  | hi u => exact ⟨_, by simpa using DD.hi (F := F) u DD.nil, by simp, by simp⟩
  | add _ _ ih1 ih2 =>
    obtain ⟨L1, d1, m1, l1⟩ := ih1
    obtain ⟨L2, d2, m2, l2⟩ := ih2
    refine ⟨(L1 ++ L2) ++ [_], DD.add (d2.append d1) (List.mem_append_left _ m1)
      (List.mem_append_right _ m2), by simp, by simp; omega⟩
  | smul c _ ih =>
    obtain ⟨L1, d1, m1, l1⟩ := ih
    exact ⟨L1 ++ [_], DD.smul c d1 m1, by simp, by simp; omega⟩
  | div c a' b' _ hc ha hb ih =>
    obtain ⟨L1, d1, m1, l1⟩ := ih
    exact ⟨L1 ++ [_], DD.div c a' b' d1 m1 hc ha hb, by simp, by simp; omega⟩

/-- Every tree-like refutation with `s` nodes gives a DAG refutation with at most `s` lines. -/
theorem ofTree {V} [DecidableEq V] {F : CNF V} (R : Refutation F) :
    ∃ R' : DRefutation F, R'.size ≤ R.size := by
  obtain ⟨Ls, d, m, l⟩ := ofD R.deriv
  exact ⟨⟨R.X, R.nodup, R.cover, Ls, d, m⟩, l⟩

/-! ## Soundness -/

theorem DD_sound {V} [DecidableEq V] {F : CNF V} (X : List V) (hX : X.Nodup)
    (cover : ∀ C ∈ F, ∀ l ∈ C, l.var ∈ X) (α : V → Bool) (hα : ∀ C ∈ F, C.eval α = true)
    {Ls : List (Line V)} (d : DD F Ls) : ∀ L ∈ Ls, L.holds X α := by
  induction d with
  | nil => simp
  | ax C _ hC ih =>
    intro L hL; rcases List.mem_append.1 hL with h | h
    · exact ih L h
    · simp at h; subst h; exact D_sound X hX cover α hα (D.ax C hC)
  | lo u _ ih =>
    intro L hL; rcases List.mem_append.1 hL with h | h
    · exact ih L h
    · simp at h; subst h; exact D_sound X hX cover α hα (D.lo u)
  | hi u _ ih =>
    intro L hL; rcases List.mem_append.1 hL with h | h
    · exact ih L h
    · simp at h; subst h; exact D_sound X hX cover α hα (D.hi u)
  | add _ h1 h2 ih =>
    intro L hL; rcases List.mem_append.1 hL with h | h
    · exact ih L h
    · simp at h; subst h
      have := ih _ h1; have := ih _ h2
      unfold Line.holds at *; rw [lhs_add]; simp only [Line.add]; omega
  | smul c _ h1 ih =>
    intro L hL; rcases List.mem_append.1 hL with h | h
    · exact ih L h
    · simp at h; subst h
      have := ih _ h1
      unfold Line.holds at *; rw [lhs_smul]; simp only [Line.smul]
      exact Int.mul_le_mul_of_nonneg_left this (Int.natCast_nonneg c)
  | @div Ls L c a' b' _ h1 hc ha hb ih =>
    intro L' hL; rcases List.mem_append.1 hL with h | h
    · exact ih L' h
    · simp at h; subst h
      have ih := ih _ h1
      unfold Line.holds at *
      have e : L.lhs X α = (c : Int) * (Line.lhs X α ⟨a', b'⟩) := by
        unfold Line.lhs; rw [← sum_mul]; congr 1; apply List.map_congr_left; intro v _
        rw [ha v, Int.mul_assoc]
      rw [e] at ih
      have : (c : Int) * (b' - 1) < (c : Int) * (Line.lhs X α ⟨a', b'⟩) := Int.lt_of_lt_of_le hb ih
      have := Int.lt_of_mul_lt_mul_left this (Int.natCast_nonneg c)
      simp only; omega

/-- DAG-like cutting planes is sound. -/
theorem dsound {V} [DecidableEq V] {F : CNF V} (R : DRefutation F) :
    ¬ ∃ α : V → Bool, ∀ C ∈ F, C.eval α = true := by
  rintro ⟨α, hα⟩
  have := DD_sound R.X R.nodup R.cover α hα R.deriv _ R.contra
  simp only [Line.holds, Line.lhs, Int.zero_mul] at this
  rw [sum_zero] at this
  omega

/-! ## Monotone real circuits -/

/-- Monotone real circuits over the variables satisfying `P`, as the list of their gate values;
every gate reads only earlier gates. -/
inductive MC {V : Type} (P : V → Bool) : List ((V → Bool) → Int) → Prop
  | nil : MC P []
  | const {fs : List ((V → Bool) → Int)} (k : Int) : MC P fs → MC P (fs ++ [fun _ => k])
  | inp {fs : List ((V → Bool) → Int)} (u : V) : P u = true → MC P fs →
      MC P (fs ++ [fun β => val β u])
  | gate1 {fs : List ((V → Bool) → Int)} {f : (V → Bool) → Int} (g : Int → Int) :
      (∀ x y, x ≤ y → g x ≤ g y) → MC P fs → f ∈ fs → MC P (fs ++ [fun β => g (f β)])
  | gate2 {fs : List ((V → Bool) → Int)} {f h : (V → Bool) → Int} (g : Int → Int → Int) :
      (∀ x x' y y', x ≤ x' → y ≤ y' → g x y ≤ g x' y') → MC P fs → f ∈ fs → h ∈ fs →
      MC P (fs ++ [fun β => g (f β) (h β)])

/-- Every gate of a monotone real circuit is non-decreasing. -/
theorem MC.mono {V : Type} {P : V → Bool} {fs : List ((V → Bool) → Int)} (c : MC P fs)
    {α β : V → Bool} (h : ∀ v, α v = true → β v = true) : ∀ f ∈ fs, f α ≤ f β := by
  induction c with
  | nil => simp
  | const k _ ih =>
    intro f hf; rcases List.mem_append.1 hf with e | e
    · exact ih f e
    · simp at e; subst e; exact Int.le_refl _
  | inp u _ _ ih =>
    intro f hf; rcases List.mem_append.1 hf with e | e
    · exact ih f e
    · simp at e; subst e; exact val_mono h u
  | gate1 g hg _ hf ih =>
    intro f' hf'; rcases List.mem_append.1 hf' with e | e
    · exact ih f' e
    · simp at e; subst e; exact hg _ _ (ih _ hf)
  | gate2 g hg _ hf hh ih =>
    intro f' hf'; rcases List.mem_append.1 hf' with e | e
    · exact ih f' e
    · simp at e; subst e; exact hg _ _ _ _ (ih _ hf) (ih _ hh)

/-- Every gate of a monotone real circuit reads only the variables in `P`. -/
theorem MC.local {V : Type} {P : V → Bool} {fs : List ((V → Bool) → Int)} (c : MC P fs)
    {α β : V → Bool} (h : ∀ v, P v = true → α v = β v) : ∀ f ∈ fs, f α = f β := by
  induction c with
  | nil => simp
  | const k _ ih =>
    intro f hf; rcases List.mem_append.1 hf with e | e
    · exact ih f e
    · simp at e; subst e; rfl
  | inp u hu _ ih =>
    intro f hf; rcases List.mem_append.1 hf with e | e
    · exact ih f e
    · simp at e; subst e; simp [val, h u hu]
  | gate1 g hg _ hf ih =>
    intro f' hf'; rcases List.mem_append.1 hf' with e | e
    · exact ih f' e
    · simp at e; subst e; simp only [ih _ hf]
  | gate2 g hg _ hf hh ih =>
    intro f' hf'; rcases List.mem_append.1 hf' with e | e
    · exact ih f' e
    · simp at e; subst e; simp only [ih _ hf, ih _ hh]

/-- A monotone real formula with `t` gates can be appended to any circuit with `≤ t` new gates. -/
theorem MC.ofRC {V : Type} {P : V → Bool} {f : (V → Bool) → Int} {t : Nat} (r : RC P f t) :
    ∀ {fs}, MC P fs → ∃ gs, MC P gs ∧ (∀ g ∈ fs, g ∈ gs) ∧ gs.length ≤ fs.length + t ∧ f ∈ gs := by
  induction r with
  | const k =>
    intro fs c
    exact ⟨_, MC.const k c, fun g hg => List.mem_append_left _ hg, by simp, by simp⟩
  | inp u hu =>
    intro fs c
    exact ⟨_, MC.inp u hu c, fun g hg => List.mem_append_left _ hg, by simp, by simp⟩
  | gate1 g hg _ ih =>
    intro fs c
    obtain ⟨gs, c1, s1, l1, m1⟩ := ih c
    exact ⟨_, MC.gate1 g hg c1 m1, fun g' hg' => List.mem_append_left _ (s1 g' hg'), by simp; omega, by simp⟩
  | gate2 g hg _ _ ih1 ih2 =>
    intro fs c
    obtain ⟨gs, c1, s1, l1, m1⟩ := ih1 c
    obtain ⟨hs, c2, s2, l2, m2⟩ := ih2 c1
    exact ⟨_, MC.gate2 g hg c2 (s2 _ m1) m2,
      fun g' hg' => List.mem_append_left _ (s2 g' (s1 g' hg')), by simp; omega, by simp⟩

/-! ## Interpolation for DAG-like cutting planes -/

section
variable {V : Type} [DecidableEq V] (A B : CNF V) (Q R : V → Bool) (X : List V)

/-- Line-by-line invariant: after `Ls`, a circuit with `≤ |Ls| (2w+1)` gates has, for each line,
a gate satisfying Pudlák's invariant `CPInterp.Inv`. -/
theorem dinterp_lines (w : Nat)
    (hw : ∀ C ∈ A, (X.filter fun v => decide (v ∈ C.map Lit.var)).length ≤ w) (hX : X.Nodup)
    (cover : ∀ C ∈ A ++ B, ∀ l ∈ C, l.var ∈ X)
    (hQR : ∀ v, Q v = true → R v = false)
    (hA : ∀ C ∈ A, ∀ l ∈ C, R l.var = false) (hB : ∀ C ∈ B, ∀ l ∈ C, Q l.var = false)
    (hneg : ∀ C ∈ A, ∀ l ∈ C, Q l.var = false → l.pos = false)
    {Ls : List (Line V)} (d : DD (A ++ B) Ls) :
    ∃ fs, MC (shared Q R) fs ∧ fs.length ≤ Ls.length * (2 * w + 1) ∧
      ∀ L ∈ Ls, ∃ f ∈ fs, Inv A B Q R X L f := by
  -- A one-node derivation contributes a formula with `≤ 2w+1` gates.
  have leaf : ∀ {L : Line V}, D (A ++ B) L 1 → ∀ {Ls : List (Line V)} {fs},
      MC (shared Q R) fs → fs.length ≤ Ls.length * (2 * w + 1) →
      (∀ L ∈ Ls, ∃ f ∈ fs, Inv A B Q R X L f) →
      ∃ gs, MC (shared Q R) gs ∧ gs.length ≤ (Ls ++ [L]).length * (2 * w + 1) ∧
        ∀ L' ∈ Ls ++ [L], ∃ f ∈ gs, Inv A B Q R X L' f := by
    intro L d1 Ls fs c hl hinv
    obtain ⟨f, t, r, ht, hI⟩ := interp_node A B Q R X w hw hX cover hQR hA hB hneg d1
    obtain ⟨gs, c1, s1, l1, m1⟩ := MC.ofRC r c
    refine ⟨gs, c1, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]; omega
    · intro L' hL'; rcases List.mem_append.1 hL' with e | e
      · obtain ⟨f', hf', hi⟩ := hinv L' e; exact ⟨f', s1 _ hf', hi⟩
      · simp at e; subst e; exact ⟨f, m1, hI⟩
  -- A derived line contributes one gate.
  have step : ∀ {Ls : List (Line V)} {fs} {L : Line V} {g : (V → Bool) → Int},
      MC (shared Q R) (fs ++ [g]) → fs.length ≤ Ls.length * (2 * w + 1) →
      (∀ L ∈ Ls, ∃ f ∈ fs, Inv A B Q R X L f) → Inv A B Q R X L g →
      ∃ gs, MC (shared Q R) gs ∧ gs.length ≤ (Ls ++ [L]).length * (2 * w + 1) ∧
        ∀ L' ∈ Ls ++ [L], ∃ f ∈ gs, Inv A B Q R X L' f := by
    intro Ls fs L g c hl hinv hI
    refine ⟨_, c, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]; omega
    · intro L' hL'; rcases List.mem_append.1 hL' with e | e
      · obtain ⟨f', hf', hi⟩ := hinv L' e; exact ⟨f', List.mem_append_left _ hf', hi⟩
      · simp at e; subst e; exact ⟨g, by simp, hI⟩
  induction d with
  | nil => exact ⟨[], MC.nil, by simp, by simp⟩
  | ax C _ hC ih =>
    obtain ⟨fs, c, hl, hinv⟩ := ih
    exact leaf (D.ax C hC) c hl hinv
  | lo u _ ih =>
    obtain ⟨fs, c, hl, hinv⟩ := ih
    exact leaf (D.lo u) c hl hinv
  | hi u _ ih =>
    obtain ⟨fs, c, hl, hinv⟩ := ih
    exact leaf (D.hi u) c hl hinv
  | add _ h1 h2 ih =>
    obtain ⟨fs, c, hl, hinv⟩ := ih
    obtain ⟨f1, m1, i1, j1⟩ := hinv _ h1
    obtain ⟨f2, m2, i2, j2⟩ := hinv _ h2
    refine step (MC.gate2 (fun x y => x + y) (by intro x x' y y' _ _; omega) c m1 m2) hl hinv ⟨?_, ?_⟩
    · intro β hβ; have := i1 β hβ; have := i2 β hβ
      simp only [part_add]; omega
    · intro β hβ; have := j1 β hβ; have := j2 β hβ
      rw [part_add, part_add]; simp only [Line.add]; omega
  | smul c' _ h1 ih =>
    obtain ⟨fs, c, hl, hinv⟩ := ih
    obtain ⟨f1, m1, i1, j1⟩ := hinv _ h1
    refine step (MC.gate1 (fun x => c' * x)
      (fun x y h => Int.mul_le_mul_of_nonneg_left h (Int.natCast_nonneg c')) c m1) hl hinv ⟨?_, ?_⟩
    · intro β hβ
      simp only [part_smul]
      exact Int.mul_le_mul_of_nonneg_left (i1 β hβ) (Int.natCast_nonneg c')
    · intro β hβ
      rw [part_smul, part_smul]; simp only [Line.smul]
      have := Int.mul_le_mul_of_nonneg_left (j1 β hβ) (Int.natCast_nonneg c')
      rw [Int.mul_sub, Int.mul_add] at this; exact this
  | @div Ls L c' a' b' _ h1 hc ha hb ih =>
    obtain ⟨fs, c, hl, hinv⟩ := ih
    obtain ⟨f1, m1, i1, j1⟩ := hinv _ h1
    refine step (MC.gate1 (cdiv c') (fun x y h => Int.ediv_le_ediv (by omega) (by omega)) c m1)
      hl hinv ⟨?_, ?_⟩
    · intro β hβ
      have h1 := i1 β hβ
      rw [part_div Q X c' L a' b' ha] at h1
      have ⟨_, h3⟩ := cdiv_spec c' hc (f1 β)
      have : (c' : Int) * cdiv c' (f1 β) < c' * (part Q X ⟨a', b'⟩ β + 1) := by
        rw [Int.mul_add]; omega
      have := lt_of_cmul this
      show cdiv c' (f1 β) ≤ _; omega
    · intro β hβ
      have h1 := j1 β hβ
      rw [part_div R X c' L a' b' ha, part_div (shared Q R) X c' L a' b' ha] at h1
      have ⟨h2, _⟩ := cdiv_spec c' hc (f1 β)
      have : (c' : Int) * (b' - 1) < c' * (part R X ⟨a', b'⟩ β + part (shared Q R) X ⟨a', b'⟩ β +
          cdiv c' (f1 β)) := by
        rw [Int.mul_add, Int.mul_add]; omega
      have := lt_of_cmul this
      show b' - cdiv c' (f1 β) ≤ _; omega

end

/-- **Feasible interpolation for DAG-like cutting planes into monotone real circuits** (Pudlák
1997). If the shared variables occur only negatively in `A` and every clause of `A` has at most
`w` literals, every DAG refutation of `A ++ B` with `s` lines yields a monotone real circuit on the
shared variables with at most `s (2w + 1)` gates and a gate `f` with: `f β ≥ 1` forces `β` to
falsify `A`, and `f β ≤ 0` forces `β` to falsify `B`. -/
theorem dinterp {V} [DecidableEq V] (A B : CNF V) (Q R : V → Bool) (w : Nat)
    (hwA : ∀ C ∈ A, C.length ≤ w)
    (hQR : ∀ v, Q v = true → R v = false)
    (hA : ∀ C ∈ A, ∀ l ∈ C, R l.var = false) (hB : ∀ C ∈ B, ∀ l ∈ C, Q l.var = false)
    (hneg : ∀ C ∈ A, ∀ l ∈ C, Q l.var = false → l.pos = false)
    (Rf : DRefutation (A ++ B)) :
    ∃ fs f, MC (shared Q R) fs ∧ fs.length ≤ Rf.size * (2 * w + 1) ∧ f ∈ fs ∧
      (∀ α β : V → Bool, (∀ v, α v = true → β v = true) → f α ≤ f β) ∧
      (∀ α β : V → Bool, (∀ v, shared Q R v = true → α v = β v) → f α = f β) ∧
      ∀ β, (1 ≤ f β → ¬ ∀ C ∈ A, C.eval β = true) ∧ (f β ≤ 0 → ¬ ∀ C ∈ B, C.eval β = true) := by
  have hw : ∀ C ∈ A, (Rf.X.filter fun v => decide (v ∈ C.map Lit.var)).length ≤ w := by
    intro C hC
    have h1 := List.Nodup.length_le_of_subset (Rf.nodup.filter (fun v => decide (v ∈ C.map Lit.var)))
      (l₂ := C.map Lit.var) (by intro v hv; have := (List.mem_filter.1 hv).2; simpa using this)
    have := hwA C hC; rw [List.length_map] at h1; omega
  obtain ⟨fs, c, hl, hinv⟩ :=
    dinterp_lines A B Q R Rf.X w hw Rf.nodup Rf.cover hQR hA hB hneg Rf.deriv
  obtain ⟨f, hf, iA, iB⟩ := hinv _ Rf.contra
  refine ⟨fs, f, c, hl, hf, fun α β h => c.mono h f hf, fun α β h => c.local h f hf,
    fun β => ⟨?_, ?_⟩⟩
  · intro h1 hβ
    have := iA β hβ
    rw [part_vanish Q _ _ β (fun _ _ => rfl)] at this; omega
  · intro h1 hβ
    have := iB β hβ
    rw [part_vanish R _ _ β (fun _ _ => rfl), part_vanish _ _ _ β (fun _ _ => rfl)] at this
    simp only at this; omega

open Programme.«20261024-1633-proof-complexity».CliqueColour in
/-- **Clique–colouring, DAG-like cutting planes.** Every DAG refutation of `CC m k` with `s` lines
yields a monotone real circuit on the edge variables with at most `s (2k + 5)` gates and an output
gate that is `≥ 1` on every graph with a `k`-clique and `≤ 0` on every `(k-1)`-colourable graph. -/
theorem cc_dinterp (m k : Nat) (Rf : DRefutation (CC m k)) :
    ∃ fs f, MC (shared isR isQ) fs ∧ fs.length ≤ Rf.size * (2 * k + 5) ∧ f ∈ fs ∧
      ∀ β, (HasClique m k β → 1 ≤ f β) ∧ (Colourable m k β → f β ≤ 0) := by
  have hQR : ∀ v, isR v = true → isQ v = false := by intro v; cases v <;> simp [isR, isQ]
  obtain ⟨fs, f, c, hl, hf, _, hloc, hsep⟩ :=
    dinterp (A m k) (B m k) isR isQ (k + 2) (hwA m k) hQR (hA m k) (hB m k) (hneg m k) Rf
  refine ⟨fs, f, c, by rw [show 2 * k + 5 = 2 * (k + 2) + 1 by omega]; exact hl, hf,
    fun β => ⟨fun hc => ?_, fun hc => ?_⟩⟩
  · obtain ⟨β', hag, hsat⟩ := sat_B m k β hc
    rw [← hloc β' β hag]
    by_cases h : 1 ≤ f β'
    · exact h
    · exact absurd hsat ((hsep β').2 (by omega))
  · obtain ⟨β', hag, hsat⟩ := sat_A m k β hc
    rw [← hloc β' β hag]
    by_cases h : f β' ≤ 0
    · exact h
    · exact absurd hsat ((hsep β').1 (by omega))

end Programme.«20261025-0459b-proof-complexity».CPDagPr

#print axioms Programme.«20261025-0459b-proof-complexity».CPDagPr.cc_dinterp
#print axioms Programme.«20261025-0459b-proof-complexity».CPDagPr.dinterp
#print axioms Programme.«20261025-0459b-proof-complexity».CPDagPr.ofTree
#print axioms Programme.«20261025-0459b-proof-complexity».CPDagPr.dsound
