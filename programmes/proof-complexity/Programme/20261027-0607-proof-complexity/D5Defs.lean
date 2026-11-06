import Programme.«20261026-1402-proof-complexity».ExtLemma

/-!
# A unit degree-5 design of `ontoFPHP 9 25` over `Z/5`: definitions

Pigeons `i < 34` lie in classes `i / 4` (eight classes of four, class `8 = {32, 33}`), holes `j < 9` in
classes `j / 4` (`{0..3}`, `{4..7}`, `{8}`). For a list `g` of edges, `cc g c d` counts the edges of `g`
from pigeon class `c` to hole class `d`; the type of class `c` is
`key g c = 50 (c / 4) + cc g c 0 + 5 cc g c 1 + 25 cc g c 2`, and the state code is
`kap g = ∑_{c<9} 5 ^ key g c`. The design is `T g = G (kap g)` with `G` read off a search tree.
The code is invariant under permuting the four pigeon classes of each block, permuting pigeons inside a
class and holes inside a hole class: a group of order prime to 5.
-/

namespace Programme.«20261027-0607-proof-complexity».D5

inductive Tr where
  | leaf : Tr
  | node : Nat → Nat → Nat → List (Nat × Nat) → Tr → Tr → Tr

/-- Lookup: value, level and base-5 digits stored at key `x`. -/
def find : Tr → Nat → Option (Nat × Nat × List (Nat × Nat))
  | .leaf, _ => none
  | .node k v e S l r, x => if x < k then find l x else if k < x then find r x else some (v, e, S)

def toList : Tr → List (Nat × Nat × Nat × List (Nat × Nat))
  | .leaf => []
  | .node k v e S l r => (k, v, e, S) :: (toList l ++ toList r)

theorem find_mem : ∀ (t : Tr) (x v e : Nat) (S : List (Nat × Nat)),
    find t x = some (v, e, S) → (x, v, e, S) ∈ toList t
  | .leaf, _, _, _, _, h => by simp [find] at h
  | .node k v' e' S' l r, x, v, e, S, h => by
    simp only [find] at h
    by_cases h1 : x < k
    · rw [if_pos h1] at h; simp [toList, find_mem l x v e S h]
    · rw [if_neg h1] at h
      by_cases h2 : k < x
      · rw [if_pos h2] at h; simp [toList, find_mem r x v e S h]
      · rw [if_neg h2] at h
        have : x = k := by omega
        subst this; simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; simp [toList]

/-! ## Arithmetic of states -/

/-- Pigeon multiplicity of a type: `4` in blocks `0, 1`, `2` in block `2`. -/
def Pi (i : Nat) : Nat := if i < 100 then 4 else 2
/-- Hole class sizes. -/
def Hd (d : Nat) : Nat := if d < 2 then 4 else 1
/-- Digit `d` of a type (edges into hole class `d`). -/
def dig (d i : Nat) : Nat := (i % 50) / 5 ^ d % 5
/-- Number of edges of a type. -/
def rc (i : Nat) : Nat := dig 0 i + dig 1 i + dig 2 i

/-- `∑ δ · f i` over a sparse digit list. -/
def sps (S : List (Nat × Nat)) (f : Nat → Int) : Int := S.foldr (fun p a => (p.2 : Int) * f p.1 + a) 0

/-- `∑ δ · 5 ^ i`. -/
def spv (S : List (Nat × Nat)) : Nat := S.foldr (fun p a => p.2 * 5 ^ p.1 + a) 0

/-- Strictly increasing indices below `150`, digits below `5`. -/
def spOk : Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | b, p :: S => decide (b ≤ p.1) && decide (p.1 < 150) && decide (p.2 < 5) && spOk (p.1 + 1) S

def Gt (t : Tr) (x : Nat) : Int := match find t x with
  | some (v, _, _) => (v : Int)
  | none => 0

/-- The neighbour code: one class of type `i` gains an edge into hole class `d`. -/
def nb (k i d : Nat) : Nat := k - 5 ^ i + 5 ^ (i + 5 ^ d)

/-- Column count of hole class `d`. -/
def csS (S : List (Nat × Nat)) (d : Nat) : Int := sps S (fun i => (dig d i : Int))

def lev (t : Tr) (x : Nat) : Nat := match find t x with
  | some (_, e, _) => e
  | none => 0

def isIn (t : Tr) (x : Nat) : Bool := match find t x with
  | some _ => true
  | none => false

/-- The checks at one entry. -/
def okE (t : Tr) (k e : Nat) (S : List (Nat × Nat)) : Bool :=
  !(decide (e ≤ 4)) ||
  (spOk 0 S && k == spv S &&
   S.all (fun p => !(decide (rc p.1 < Pi p.1)) ||
     ((((List.range 3).foldr (fun d a => if csS S d < Hd d then ((Hd d : Int) - csS S d) * Gt t (nb k p.1 d) + a else a) 0)
        - Gt t k) % 5 == 0 &&
      (List.range 3).all (fun d => !(decide (csS S d < Hd d)) || decide (e = 4) ||
        (isIn t (nb k p.1 d) && lev t (nb k p.1 d) == e + 1)))) &&
   (List.range 3).all (fun d => !(decide (csS S d < Hd d)) ||
     (sps S (fun i => ((Pi i : Int) - rc i) * Gt t (nb k i d)) - Gt t k) % 5 == 0))

def okT (t : Tr) : Bool := (toList t).all fun q => okE t q.1 q.2.2.1 q.2.2.2

/-! ## The design -/

/-- Edges of `g` from pigeon class `c` to hole class `d` (`v = 9 i + j`). -/
def cc (g : List Nat) (c d : Nat) : Nat := g.countP (fun v => v / 9 / 4 == c && v % 9 / 4 == d)

def key (g : List Nat) (c : Nat) : Nat := 50 * (c / 4) + cc g c 0 + 5 * cc g c 1 + 25 * cc g c 2

def nsum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | m + 1, f => nsum m f + f m

def kap (g : List Nat) : Nat := nsum 9 (fun c => 5 ^ key g c)

def T (t : Tr) (g : List Nat) : Int := Gt t (kap g)

end Programme.«20261027-0607-proof-complexity».D5
