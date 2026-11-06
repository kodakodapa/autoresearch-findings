import Programme.«20261024-1633-proof-complexity».CP

/-!
# DAG-like (general) cutting-planes refutations

`Chain F ls` says the list of lines `ls` (newest first) is a cutting-planes derivation from `F` in
which every line follows from lines *already in the list* by one rule (`Just`): clause axioms,
the bounds `x_u ≥ 0`, `-x_u ≥ -1`, addition, multiplication by a natural number, and division with
rounding, exactly the rules of `CP.D`. A line may be used any number of times. A `DRefutation`
contains `0 ≥ 1`; its size is the number of lines.

* `Just.sound`, `dag_sound`: the system is sound.
* `of_tree`, `Refutation.toDag`: every tree-like refutation (`CP.Refutation`) with `s` nodes gives a
  DAG refutation over the same variables with at most `s` lines.
-/

namespace Programme.«20261025-0459b-proof-complexity».CPDag

open Programme.«20261024-1110-proof-complexity».Haken (Lit Clause CNF Lit.eval Clause.eval)
open Programme.«20261024-1633-proof-complexity».CP

/-- One derivation step from the lines `ls`. -/
inductive Just {V} [DecidableEq V] (F : CNF V) (ls : List (Line V)) : Line V → Prop
  | ax (C : Clause V) : C ∈ F → Just F ls (clauseLine C)
  | lo (u : V) : Just F ls ⟨fun v => if u = v then 1 else 0, 0⟩
  | hi (u : V) : Just F ls ⟨fun v => if u = v then -1 else 0, -1⟩
  | add {L M : Line V} : L ∈ ls → M ∈ ls → Just F ls (L.add M)
  | smul {L : Line V} (c : Nat) : L ∈ ls → Just F ls (L.smul c)
  | div {L : Line V} (c : Nat) (a' : V → Int) (b' : Int) : L ∈ ls → 0 < c →
      (∀ v, L.a v = (c : Int) * a' v) → (c : Int) * (b' - 1) < L.b → Just F ls ⟨a', b'⟩

/-- A DAG-like derivation: every line is justified by the lines after it in the list. -/
inductive Chain {V} [DecidableEq V] (F : CNF V) : List (Line V) → Prop
  | nil : Chain F []
  | cons {ls : List (Line V)} {L : Line V} : Chain F ls → Just F ls L → Chain F (L :: ls)

/-- A DAG-like cutting-planes refutation of `F` over a duplicate-free variable list `X`. -/
structure DRefutation {V} [DecidableEq V] (F : CNF V) where
  X : List V
  nodup : X.Nodup
  cover : ∀ C ∈ F, ∀ l ∈ C, l.var ∈ X
  lines : List (Line V)
  chain : Chain F lines
  final : (⟨fun _ => 0, 1⟩ : Line V) ∈ lines

/-- The size of a DAG refutation: its number of lines. -/
def DRefutation.size {V} [DecidableEq V] {F : CNF V} (R : DRefutation F) : Nat := R.lines.length

/-! ## Soundness -/

theorem Just.sound {V} [DecidableEq V] {F : CNF V} (X : List V) (hX : X.Nodup)
    (cover : ∀ C ∈ F, ∀ l ∈ C, l.var ∈ X) (α : V → Bool) (hα : ∀ C ∈ F, C.eval α = true)
    {ls : List (Line V)} (hls : ∀ M ∈ ls, M.holds X α) {L : Line V} (j : Just F ls L) :
    L.holds X α := by
  cases j with
  | ax C hC => exact D_sound X hX cover α hα (D.ax C hC)
  | lo u => exact D_sound X hX cover α hα (D.lo (F := F) u)
  | hi u => exact D_sound X hX cover α hα (D.hi (F := F) u)
  | add h1 h2 =>
    have := hls _ h1; have := hls _ h2
    unfold Line.holds at *; rw [lhs_add]; simp only [Line.add]; omega
  | smul c h =>
    have ih := hls _ h
    unfold Line.holds at *; rw [lhs_smul]; simp only [Line.smul]
    exact Int.mul_le_mul_of_nonneg_left ih (Int.natCast_nonneg c)
  | @div L c a' b' h hc ha hb =>
    have ih := hls _ h
    unfold Line.holds at *
    have e : L.lhs X α = (c : Int) * (Line.lhs X α ⟨a', b'⟩) := by
      unfold Line.lhs; rw [← sum_mul]; congr 1; apply List.map_congr_left; intro v _
      rw [ha v, Int.mul_assoc]
    rw [e] at ih
    have : (c : Int) * (b' - 1) < (c : Int) * (Line.lhs X α ⟨a', b'⟩) := Int.lt_of_lt_of_le hb ih
    have := Int.lt_of_mul_lt_mul_left this (Int.natCast_nonneg c)
    simp only; omega

theorem Chain.sound {V} [DecidableEq V] {F : CNF V} (X : List V) (hX : X.Nodup)
    (cover : ∀ C ∈ F, ∀ l ∈ C, l.var ∈ X) (α : V → Bool) (hα : ∀ C ∈ F, C.eval α = true) :
    ∀ {ls : List (Line V)}, Chain F ls → ∀ M ∈ ls, M.holds X α
  | _, .nil => by simp
  | _, .cons c j => by
    have ih := Chain.sound X hX cover α hα c
    intro M hM
    rcases List.mem_cons.1 hM with rfl | hM
    · exact j.sound X hX cover α hα ih
    · exact ih M hM

/-- DAG cutting planes is sound. -/
theorem dag_sound {V} [DecidableEq V] {F : CNF V} (R : DRefutation F) :
    ¬ ∃ α : V → Bool, ∀ C ∈ F, C.eval α = true := by
  rintro ⟨α, hα⟩
  have := Chain.sound R.X R.nodup R.cover α hα R.chain _ R.final
  simp only [Line.holds, Line.lhs, Int.zero_mul] at this
  rw [sum_zero] at this
  omega

/-! ## Tree-like derivations are DAG derivations -/

theorem of_tree {V} [DecidableEq V] {F : CNF V} {L : Line V} {s : Nat} (d : D F L s) :
    ∀ ls, Chain F ls → ∃ ls', Chain F ls' ∧ L ∈ ls' ∧ (∀ M ∈ ls, M ∈ ls') ∧
      ls'.length ≤ ls.length + s := by
  induction d with
  | ax C hC =>
    intro ls c
    exact ⟨_, c.cons (Just.ax C hC), List.mem_cons_self .., fun M h => List.mem_cons_of_mem _ h,
      by simp⟩
  | lo u =>
    intro ls c
    exact ⟨_, c.cons (Just.lo u), List.mem_cons_self .., fun M h => List.mem_cons_of_mem _ h,
      by simp⟩
  | hi u =>
    intro ls c
    exact ⟨_, c.cons (Just.hi u), List.mem_cons_self .., fun M h => List.mem_cons_of_mem _ h,
      by simp⟩
  | add _ _ ih1 ih2 =>
    intro ls c
    obtain ⟨l1, c1, m1, s1, n1⟩ := ih1 ls c
    obtain ⟨l2, c2, m2, s2, n2⟩ := ih2 l1 c1
    exact ⟨_, c2.cons (Just.add (s2 _ m1) m2), List.mem_cons_self ..,
      fun M h => List.mem_cons_of_mem _ (s2 _ (s1 _ h)), by simp; omega⟩
  | smul k _ ih =>
    intro ls c
    obtain ⟨l1, c1, m1, s1, n1⟩ := ih ls c
    exact ⟨_, c1.cons (Just.smul k m1), List.mem_cons_self ..,
      fun M h => List.mem_cons_of_mem _ (s1 _ h), by simp; omega⟩
  | div k a' b' _ hc ha hb ih =>
    intro ls c
    obtain ⟨l1, c1, m1, s1, n1⟩ := ih ls c
    exact ⟨_, c1.cons (Just.div k a' b' m1 hc ha hb), List.mem_cons_self ..,
      fun M h => List.mem_cons_of_mem _ (s1 _ h), by simp; omega⟩

/-- Every tree-like refutation with `s` nodes gives a DAG refutation with `≤ s` lines. -/
theorem Refutation.toDag {V} [DecidableEq V] {F : CNF V} (Rf : Refutation F) :
    ∃ R : DRefutation F, R.X = Rf.X ∧ R.size ≤ Rf.size := by
  obtain ⟨ls, c, hm, _, hn⟩ := of_tree Rf.deriv [] Chain.nil
  exact ⟨⟨Rf.X, Rf.nodup, Rf.cover, ls, c, hm⟩, rfl, by simpa [DRefutation.size] using hn⟩

end Programme.«20261025-0459b-proof-complexity».CPDag
