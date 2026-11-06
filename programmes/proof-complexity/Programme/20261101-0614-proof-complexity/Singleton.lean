import Programme.«20261101-0614-proof-complexity».UnaryUpper
import Programme.«20261031-2024-proof-complexity».ConeMixed

namespace Programme.«20261101-0614-proof-complexity».Singleton
open Programme.«20261031-2024-proof-complexity».NativeIter

def outer (y : Nat) : Lit := ((0,y),true)
def block (L y : Nat) (v : Var) : Var := (y+1,v.1*L+v.2)
def structural (L : Nat) : List Clause :=
  (List.range L).flatMap fun x => [UnaryIter.row L x] ++
    (List.range L).flatMap fun z =>
      ((List.range L).filter fun t => z < t).map fun t =>
        [UnaryIter.minus x z, UnaryIter.minus x t]
def image (L y : Nat) (c : Clause) : Clause :=
  if c ∈ structural L then (renameClause (block L y) c).eraseDups
  else (renameClause (block L y) c ++ [outer y]).eraseDups
def cnf (N L : Nat) : List Clause :=
  [(List.range N).map outer] ++
  ((List.range N).flatMap fun y =>
    ((List.range N).filter fun z => y < z).map fun z => [neg (outer y), neg (outer z)]) ++
  ((List.range N).flatMap fun y => (UnaryIter.cnf L).map (image L y))

theorem generator_spec (N L : Nat) (c : Clause) : c ∈ cnf N L ↔
    (c = (List.range N).map outer ∨
      ∃ y, y < N ∧ ∃ z, (z < N ∧ y < z) ∧
        c = [neg (outer y), neg (outer z)]) ∨
    ∃ y, y < N ∧ ∃ t, t ∈ UnaryIter.cnf L ∧ c = image L y t := by
  simp [cnf, List.mem_flatMap, List.mem_map, List.mem_filter, eq_comm, or_assoc]

theorem block_certificate (N L y : Nat) (hL : 2 ≤ L) (hy : y < N) :
    Cone (cnf N L) (L+1) (fun a => -conjunction [neg (outer y)] a) := by
  have hm (c : Clause) (hc : c ∈ UnaryIter.cnf L) : image L y c ∈ cnf N L := by
    simp only [cnf, List.mem_append]
    right
    exact List.mem_flatMap.mpr ⟨y,List.mem_range.mpr hy,List.mem_map.mpr ⟨c,hc,rfl⟩⟩
  have h := cone_identify_mixed_guard (G := cnf N L) (block L y) (neg (outer y))
    (fun c hc => by
      by_cases hs : c ∈ structural L
      · left; simpa [image, hs] using hm c hc
      · right; simpa [image, hs, neg] using hm c hc) (UnaryIter.upper L hL)
  simpa only [Rat.mul_neg, Rat.mul_one] using h

theorem upper (N L : Nat) (hN : 2 ≤ N) (hL : 2 ≤ L) :
    Refutes (cnf N L) (L+1) := by
  have h0 := block_certificate N L 0 hL (by omega)
  have h1 := block_certificate N L 1 hL (by omega)
  have hp : Cone (cnf N L) (L+1)
      (conjunction [neg (outer 0), neg (outer 1)]) :=
    Cone.positive _ (by simp [Multiplier, outer, neg]) (by simp; omega)
  have hc : [neg (outer 0), neg (outer 1)] ∈ cnf N L := by
    simp only [cnf, List.mem_append]
    left; right
    exact List.mem_flatMap.mpr ⟨0,List.mem_range.mpr (by omega),
      List.mem_map.mpr ⟨1,List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), by decide⟩,rfl⟩⟩
  have he := Cone.equation _ [] (-1) hc
    (show Admitted (L+1) [neg (outer 0), neg (outer 1)] [] from
      ⟨by simp [Multiplier], by simp; omega⟩)
  have hh := Cone.add (Cone.add (Cone.add h0 h1) hp) he
  have hid : (fun a => ((-conjunction [neg (outer 0)] a +
      -conjunction [neg (outer 1)] a) +
      conjunction [neg (outer 0), neg (outer 1)] a) +
      -1 * conjunction ([] ++ falsity [neg (outer 0), neg (outer 1)]) a) =
      (fun _ => (-1 : Rat)) := by
    funext a
    cases h : a (0,0) <;> cases k : a (0,1) <;>
      simp [conjunction, falsity, outer, neg, holds, h, k, Rat.zero_add, Rat.add_zero, Rat.add_assoc, Rat.neg_add_cancel]
  rw [hid] at hh
  exact hh

theorem cone_degree_mono {F d e f} (hde : d ≤ e) (h : Cone F d f) : Cone F e f := by
  induction h with
  | positive m hm hd => exact Cone.positive m hm (by omega)
  | equation c m r hc hd => exact Cone.equation c m r hc ⟨hd.1, by have := hd.2; omega⟩
  | zero => exact Cone.zero
  | add _ _ hf hg => exact Cone.add hf hg
  | scale r hr _ hf => exact Cone.scale r hr hf

theorem upper_bound (N L : Nat) (hN : 2 ≤ N) (hL : 2 ≤ L) :
    Refutes (cnf N L) (max N (L+1)) :=
  cone_degree_mono (Nat.le_max_right _ _) (upper N L hN hL)

#print axioms upper_bound
#print axioms block_certificate
#print axioms upper
end Programme.«20261101-0614-proof-complexity».Singleton
