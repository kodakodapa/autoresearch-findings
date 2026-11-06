import Programme.«20261026-1402-proof-complexity».BDesMain
import Programme.«20261027-0607-proof-complexity».VUnit

/-!
# `EXT 2 7 8 1` unconditionally, from K167's design lifted from `n = 4` to `n = 7`

`T0` is the library design `BDes.B` on `ontoFPHP 4 8` (12 pigeons, 4 holes), lifted to
`ontoFPHP 7 8` (15 pigeons, 7 holes) by matching the extra pigeons `12, 13, 14` to the extra holes
`4, 5, 6`: a list is sent to its `n = 4` image after deleting those fixed edges, and `T0 = 0` on lists
using any other edge at an extra pigeon or hole. Kernel evaluation checks `Bal 2 7 8 T0 T0 e` for
`e ≤ 1`; th's `VUnit.ext_unit` at `d = 1` (units only up to `1`) then gives `EXT 2 7 8 1`.
-/

namespace Programme.«20261027-0607-proof-complexity».Lift78

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma

/-- An edge of `ontoFPHP 7 8` allowed by the lift: inside the `12 × 4` block, or a fixed edge. -/
def okV (v : Nat) : Bool := (v / 7 < 12 && v % 7 < 4) || (12 ≤ v / 7 && v % 7 + 8 == v / 7)

/-- Image of a block edge in `ontoFPHP 4 8` coordinates; fixed edges are deleted. -/
def emb (v : Nat) : Option Nat := if v / 7 < 12 then some (v / 7 * 4 + v % 7) else none

def T0 (g : List Nat) : Int :=
  if g.all okV then Programme.«20261026-1402-proof-complexity».BDes.B (canon 48 (g.filterMap emb)) else 0

def allL : Nat → List (List Nat)
  | 0 => [[]]
  | e + 1 => (List.range 105).flatMap fun a => (allL e).map (a :: ·)

def okG (g : List Nat) : Bool :=
  !(canon ((7 + 8) * 7) g == g && isMatch 7 g) ||
  (((List.range 15).all fun i => !(g.all fun v => v / 7 != i) || (rowS 7 8 T0 g i - T0 g) % 2 == 0) &&
   ((List.range 7).all fun j => !(g.all fun v => v % 7 != j) || (colS 7 8 T0 g j - T0 g) % 2 == 0))

def chk (e : Nat) : Bool := (allL e).all okG

theorem mem_allL : ∀ g : List Nat, (∀ v ∈ g, v < 105) → g ∈ allL g.length
  | [], _ => by simp [allL]
  | a :: l, h => by
    simp only [allL, List.length_cons, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨a, h a (by simp), l, mem_allL l (fun v hv => h v (by simp [hv])), rfl⟩

theorem bal_of_chk {e : Nat} (h : chk e = true) : Bal 2 7 8 T0 T0 e := by
  intro g hg hl
  have hlt : ∀ v ∈ g, v < 105 := by
    intro v hv
    have := hg.1 ▸ hv
    exact ((mem_canon _ _ _).1 this).2
  have hm := mem_allL g hlt
  rw [hl] at hm
  have hok := List.all_eq_true.1 h g hm
  have hc : (canon ((7 + 8) * 7) g == g && isMatch 7 g) = true := by
    simp [hg.1, hg.2]
  simp only [okG, hc, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
    List.mem_range] at hok
  refine ⟨fun i hi hf => ?_, fun j hj hf => ?_⟩
  · have hb : (g.all fun v => v / 7 != i) = true := by
      simp only [List.all_eq_true, bne_iff_ne]; exact hf
    have := hok.1 i hi
    simp only [hb, Bool.not_true, Bool.false_or, beq_iff_eq] at this
    exact Int.dvd_of_emod_eq_zero this
  · have hb : (g.all fun v => v % 7 != j) = true := by
      simp only [List.all_eq_true, bne_iff_ne]; exact hf
    have := hok.2 j hj
    simp only [hb, Bool.not_true, Bool.false_or, beq_iff_eq] at this
    exact Int.dvd_of_emod_eq_zero this

theorem chk0 : chk 0 = true := by decide +kernel
def chunk (c : Nat) : Bool := (List.range' (15 * c) 15).all fun a => okG [a]

theorem c0 : chunk 0 = true := by decide +kernel
theorem c1 : chunk 1 = true := by decide +kernel
theorem c2 : chunk 2 = true := by decide +kernel
theorem c3 : chunk 3 = true := by decide +kernel
theorem c4 : chunk 4 = true := by decide +kernel
theorem c5 : chunk 5 = true := by decide +kernel
theorem c6 : chunk 6 = true := by decide +kernel

theorem chk1 : chk 1 = true := by
  have hc : ∀ c < 7, chunk c = true := by
    intro c hc
    match c, hc with
    | 0, _ => exact c0
    | 1, _ => exact c1
    | 2, _ => exact c2
    | 3, _ => exact c3
    | 4, _ => exact c4
    | 5, _ => exact c5
    | 6, _ => exact c6
  simp only [chk, allL, List.all_eq_true, List.mem_flatMap, List.mem_range, List.mem_map,
    List.mem_singleton]
  rintro g ⟨a, ha, l, rfl, rfl⟩
  have h := List.all_eq_true.1 (hc (a / 15) (by omega)) a
    (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  exact h
theorem T0_nil : T0 [] = 1 := by decide +kernel

/-- `T0` is a unit degree-2 design on `ontoFPHP 7 8` over `Z/2`. -/
theorem design : T0 [] = 1 ∧ ∀ e ≤ 1, Bal 2 7 8 T0 T0 e := by
  refine ⟨T0_nil, fun e he => ?_⟩
  match e, he with
  | 0, _ => exact bal_of_chk chk0
  | 1, _ => exact bal_of_chk chk1

/-- **`EXT 2 7 8 1`** (th's `EXT_2(7,8,2)`), unconditionally. -/
theorem ext1 : EXT 2 7 8 1 :=
  Programme.«20261027-0607-proof-complexity».VUnit.ext_unit (p := 2) (n := 7) (k := 8) (d := 1) (by decide) (by decide)
    (fun s h1 h2 => ⟨1, by
      have : s = 1 := by omega
      subst this; decide⟩)
    (fun e he => design.2 e he) (by rw [design.1]; decide)

end Programme.«20261027-0607-proof-complexity».Lift78

#print axioms Programme.«20261027-0607-proof-complexity».Lift78.design
#print axioms Programme.«20261027-0607-proof-complexity».Lift78.ext1
