import Programme.«20261102-1249-proof-complexity».UniformC3.Main
import Programme.«20261026-1402-proof-complexity».Win

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Programme.«20261102-1249-proof-complexity».UniformC3.Block
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum var rsum_add)
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt)
open Programme.«20261025-1627-proof-complexity».MomGen (canon canon_nodup mem_canon)
open Programme.«20261026-1402-proof-complexity».Win (match_row match_col nodup_mod nodup_div count_freeQ)

abbrev Ix := Fin 3
abbrev Matrix := Ix → Ix → Nat

def inc (M : Matrix) (i j : Ix) : Matrix :=
  fun r c => M r c + if r = i ∧ c = j then 1 else 0

def rc (M : Matrix) (i : Ix) := M i 0 + M i 1 + M i 2
def cc (M : Matrix) (j : Ix) := M 0 j + M 1 j + M 2 j
def total (M : Matrix) := rc M 0 + rc M 1 + rc M 2
def sum3 (f : Ix → Int) := f 0 + f 1 + f 2

def Feasible (a : Ix → Nat) (M : Matrix) : Prop :=
  ∀ i : Ix, rc M i ≤ a i ∧ cc M i ≤ a i
instance (a : Ix → Nat) (M : Matrix) : Decidable (Feasible a M) :=
  inferInstanceAs (Decidable (∀ i : Ix, rc M i ≤ a i ∧ cc M i ≤ a i))

structure Partition (n : Nat) where
  block : Nat → Ix
  size : Ix → Nat
  card : ∀ i, rsum n (fun t => if block t = i then 1 else 0) = (size i : Int)

def counts {n : Nat} (P : Partition n) (g : List Nat) : Matrix :=
  fun i j => g.countP (fun v => P.block (v/n) == i && P.block (v%n) == j)

theorem fin3_cases (i : Ix) : i = 0 ∨ i = 1 ∨ i = 2 := by
  rcases i with ⟨i,hi⟩
  rcases (show i=0 ∨ i=1 ∨ i=2 by omega) with rfl | rfl | rfl <;> simp

theorem counts_cons {n : Nat} (P : Partition n) (v : Nat) (g : List Nat) :
    counts P (v::g) = inc (counts P g) (P.block (v/n)) (P.block (v%n)) := by
  funext i j
  simp only [counts, inc, List.countP_cons]
  by_cases hi : P.block (v/n) = i <;> by_cases hj : P.block (v%n) = j <;>
    simp_all <;> grind

theorem counts_perm {n : Nat} (P : Partition n) {g h : List Nat} (hp : g.Perm h) :
    counts P g = counts P h := by
  funext i j; exact hp.countP_eq _

theorem rc_counts {n : Nat} (P : Partition n) (g : List Nat) (i : Ix) :
    rc (counts P g) i = g.countP (fun v => P.block (v/n) == i) := by
  induction g with
  | nil => simp [rc,counts]
  | cons v g ih =>
    rcases fin3_cases (P.block (v%n)) with h | h | h <;>
      simp only [rc,counts,List.countP_cons] at ih ⊢ <;>
      by_cases hi : P.block (v/n) = i <;> simp [h,hi] at * <;> omega

theorem cc_counts {n : Nat} (P : Partition n) (g : List Nat) (j : Ix) :
    cc (counts P g) j = g.countP (fun v => P.block (v%n) == j) := by
  induction g with
  | nil => simp [cc,counts]
  | cons v g ih =>
    rcases fin3_cases (P.block (v/n)) with h | h | h <;>
      simp only [cc,counts,List.countP_cons] at ih ⊢ <;>
      by_cases hj : P.block (v%n) = j <;> simp [h,hj] at * <;> omega

theorem total_counts {n : Nat} (P : Partition n) (g : List Nat) :
    total (counts P g) = g.length := by
  simp only [total, rc_counts]
  induction g with
  | nil => simp
  | cons v g ih =>
    rcases fin3_cases (P.block (v/n)) with h | h | h <;>
      simp [List.countP_cons,h] at * <;> omega

theorem counts_canon {n : Nat} (P : Partition n) {g : List Nat}
    (hn : g.Nodup) (hb : ∀ v ∈ g, v < n*n) :
    counts P (canon (n*n) g) = counts P g := by
  apply counts_perm
  apply (List.perm_ext_iff_of_nodup (canon_nodup _ _) hn).mpr
  intro v
  simp only [mem_canon]
  exact ⟨fun h => h.1, fun h => ⟨h,hb v h⟩⟩

/-- Counting free labels of one block, independent of row/column conventions. -/
theorem free_count {n : Nat} (P : Partition n) (h : Nat → Nat) (g : List Nat)
    (hnd : (g.map h).Nodup) (hb : ∀ v ∈ g, h v < n) (i : Ix) :
    rsum n (fun t => if P.block t = i ∧ ∀ v ∈ g, h v ≠ t then 1 else 0) =
      (P.size i : Int) - g.countP (fun v => P.block (h v) == i) := by
  let L := g.filter (fun v => P.block (h v) == i)
  have hL : (L.map h).Nodup := ((List.filter_sublist).map _).nodup hnd
  have hc := count_freeQ (fun t => P.block t = i) h n L hL (by
    intro v hv
    have hh := List.mem_filter.mp hv
    exact ⟨hb v hh.1, by simpa using hh.2⟩)
  have he : ∀ t < n,
      (if P.block t = i ∧ ∀ v ∈ g, h v ≠ t then (1 : Int) else 0) =
      (if P.block t = i ∧ ∀ v ∈ L, h v ≠ t then 1 else 0) := by
    intro t ht
    by_cases hi : P.block t = i
    · have hh : (∀ v ∈ g, h v ≠ t) ↔ (∀ v ∈ L, h v ≠ t) := by
        constructor
        · exact fun H v hv => H v (List.mem_filter.mp hv).1
        · intro H v hv heq
          apply H v (List.mem_filter.mpr ⟨hv,by simp [heq,hi]⟩) heq
      simp only [hi,true_and,hh]
    · simp [hi]
  rw [rsum_congr n _ _ he, hc, P.card]
  simp [L,List.countP_eq_length_filter]

theorem isum_nonneg (f : Nat → Int) (hf : ∀ t, 0 ≤ f t) : ∀ n, 0 ≤ rsum n f := by
  intro n; induction n with
  | zero => simp [rsum]
  | succ n ih => simp only [rsum]; have := hf n; omega

theorem feasible_counts {n : Nat} (hn : 0 < n) (P : Partition n) {g : List Nat}
    (hg : CM n 0 g) : Feasible P.size (counts P g) := by
  intro i
  have hr := free_count P (fun v => v/n) g (nodup_div (CM_nodup hg) hg.2)
    (fun v hv => (Nat.div_lt_iff_lt_mul hn).mpr (by simpa using CM_lt hg hv)) i
  have hc := free_count P (fun v => v%n) g (nodup_mod (CM_nodup hg) hg.2)
    (fun v _ => Nat.mod_lt _ hn) i
  have hnr := isum_nonneg (fun t => if P.block t = i ∧ ∀ v ∈ g, v/n ≠ t then 1 else 0)
    (fun _ => by split <;> omega) n
  have hnc := isum_nonneg (fun t => if P.block t = i ∧ ∀ v ∈ g, v%n ≠ t then 1 else 0)
    (fun _ => by split <;> omega) n
  rw [rc_counts,cc_counts]
  omega

/-- Regroup a sum into the three blocks. -/
theorem group3 (n : Nat) (b : Nat → Ix) (C : Nat → Prop) [DecidablePred C]
    (X : Ix → Int) :
    rsum n (fun t => if C t then X (b t) else 0) =
    sum3 (fun i => X i * rsum n (fun t => if b t = i ∧ C t then 1 else 0)) := by
  induction n with
  | zero => simp [rsum,sum3]
  | succ n ih =>
    simp only [rsum] at *
    rw [ih]
    rcases fin3_cases (b n) with h | h | h <;>
      by_cases hc : C n <;> simp [sum3,h,hc,Int.mul_add] <;> omega

/-- Reduced data sufficient for the exact library IntegralLift predicate. -/
structure Certificate (p : Nat) {n : Nat} (P : Partition n) where
  value : Matrix → Int
  unit : ∀ M, Feasible P.size M → total M = p → (p : Int) ∣ value M - 1
  row : ∀ M, Feasible P.size M → total M = p-1 → ∀ i,
    sum3 (fun j => ((P.size j : Int) - cc M j) * value (inc M i j)) = 0
  col : ∀ M, Feasible P.size M → total M = p-1 → ∀ j,
    sum3 (fun i => ((P.size i : Int) - rc M i) * value (inc M i j)) = 0


theorem row_formula {n : Nat} (hn : 0 < n) (P : Partition n) (K : Matrix → Int)
    {g : List Nat} (hg : CM n 0 g) {i : Nat} (hi : i < n) (hf : pfree n g i) :
    rowS n 0 (fun g => K (counts P g)) g i =
      sum3 (fun j => ((P.size j : Int) - cc (counts P g) j) *
        K (inc (counts P g) (P.block i) j)) := by
  unfold rowS lineS
  simp only [Nat.add_zero]
  have he : ∀ t < n,
      (if isMatch n (var n i t :: g) = true then
        K (counts P (canon (n*n) (var n i t :: g))) else 0) =
      (if ∀ v ∈ g, v%n ≠ t then K (inc (counts P g) (P.block i) (P.block t)) else 0) := by
    intro t ht
    have hm := match_row hg.2 ht hf
    by_cases hf' : ∀ v ∈ g, v%n ≠ t
    · rw [ite_eq_left (hm.mpr hf'),ite_eq_left hf']
      rw [counts_canon P (List.nodup_cons.mpr ⟨notin_of_pfree hf t ht,CM_nodup hg⟩) (by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact var_lt n 0 i t (by simpa using hi) ht
        · simpa using CM_lt hg hv),counts_cons,var_div n i t ht,var_mod n i t ht]
    · rw [ite_eq_right hf',ite_eq_right (fun h => hf' (hm.mp h))]
  rw [rsum_congr n _ _ he, group3 n P.block (fun t => ∀ v ∈ g, v%n ≠ t)
    (fun j => K (inc (counts P g) (P.block i) j))]
  unfold sum3
  have hfree : ∀ j : Ix,
      rsum n (fun t => if P.block t = j ∧ ∀ v ∈ g, v%n ≠ t then 1 else 0) =
        (P.size j : Int) - cc (counts P g) j := by
    intro j
    rw [cc_counts]
    exact free_count P (fun v => v%n) g (nodup_mod (CM_nodup hg) hg.2)
      (fun v _ => Nat.mod_lt _ hn) j
  simp only [hfree,Int.mul_comm]

theorem col_formula {n : Nat} (hn : 0 < n) (P : Partition n) (K : Matrix → Int)
    {g : List Nat} (hg : CM n 0 g) {j : Nat} (hj : j < n) (hf : hfree n g j) :
    colS n 0 (fun g => K (counts P g)) g j =
      sum3 (fun i => ((P.size i : Int) - rc (counts P g) i) *
        K (inc (counts P g) i (P.block j))) := by
  unfold colS lineS
  simp only [Nat.add_zero]
  have he : ∀ t < n,
      (if isMatch n (var n t j :: g) = true then
        K (counts P (canon (n*n) (var n t j :: g))) else 0) =
      (if ∀ v ∈ g, v/n ≠ t then K (inc (counts P g) (P.block t) (P.block j)) else 0) := by
    intro t ht
    have hm := match_col (s := t) hg.2 hj hf
    by_cases hf' : ∀ v ∈ g, v/n ≠ t
    · rw [ite_eq_left (hm.mpr hf'),ite_eq_left hf']
      rw [counts_canon P (List.nodup_cons.mpr ⟨notin_of_hfree hf t hj,CM_nodup hg⟩) (by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact var_lt n 0 t j (by simpa using ht) hj
        · simpa using CM_lt hg hv),counts_cons,var_div n t j hj,var_mod n t j hj]
    · rw [ite_eq_right hf',ite_eq_right (fun h => hf' (hm.mp h))]
  rw [rsum_congr n _ _ he, group3 n P.block (fun t => ∀ v ∈ g, v/n ≠ t)
    (fun i => K (inc (counts P g) i (P.block j)))]
  unfold sum3
  have hfree : ∀ i : Ix,
      rsum n (fun t => if P.block t = i ∧ ∀ v ∈ g, v/n ≠ t then 1 else 0) =
        (P.size i : Int) - rc (counts P g) i := by
    intro i
    rw [rc_counts]
    exact free_count P (fun v => v/n) g (nodup_div (CM_nodup hg) hg.2)
      (fun v hv => (Nat.div_lt_iff_lt_mul hn).mpr (by simpa using CM_lt hg hv)) i
  simp only [hfree,Int.mul_comm]

def Certificate.toIntegralLift {p : Nat} (hp : 2 ≤ p)
    (P : Partition (2*p-1)) (C : Certificate p P) : IntegralLift p where
  coeff := fun g => C.value (counts P g)
  unit := by
    intro g hg hl
    exact C.unit _ (feasible_counts (by omega) P hg) ((total_counts P g).trans hl)
  harmonic := by
    intro g hg hl
    have hF := feasible_counts (by omega : 0 < 2*p-1) P hg
    have ht : total (counts P g) = p-1 := (total_counts P g).trans hl
    constructor
    · intro i hi hf
      rw [row_formula (by omega) P C.value hg (by simpa using hi) hf]
      exact C.row _ hF ht _
    · intro j hj hf
      rw [col_formula (by omega) P C.value hg hj hf]
      exact C.col _ hF ht _

#print axioms Certificate.toIntegralLift
end Programme.«20261102-1249-proof-complexity».UniformC3.Block
