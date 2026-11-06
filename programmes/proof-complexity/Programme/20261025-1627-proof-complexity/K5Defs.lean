import Programme.«20261025-0459-proof-complexity».OntoFPHP

/-!
# A `ℤ₁₅ × ℤ₇`-invariant weight on matchings of the `15 × 7` board

Variables `v = 7 i + j < 105` (pigeon `i < 15`, hole `j < 7`), as in `ontoFPHP 7 8`.
`rot a b` translates pigeons by `a` (mod 15) and holes by `b` (mod 7); `toZ v` is the translation
sending `v` to `0`. A list of variables is read as a set through its bit mask `mask`.
The canonical form `C l` of a set is the least mask among its translates that contain `0` (one
per member, as translations act freely), so it is a function of the orbit. `W l = 1` iff `l` is a
matching (distinct pigeons, distinct holes, all `< 105`) whose canonical form lies in the search
tree `sup` (th's K5 support, `Work.K5Sup`).
-/

namespace Programme.«20261025-1627-proof-complexity».K5Defs

open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum)

def rot (a b v : Nat) : Nat := 7 * ((v / 7 + a) % 15) + (v % 7 + b) % 7

def toZ (v w : Nat) : Nat := rot (15 - v / 7) (7 - v % 7) w

def mask (l : List Nat) : Nat := l.foldr (fun v acc => acc ||| 2 ^ v) 0

def key (l : List Nat) (v : Nat) : Nat := mask (l.map (toZ v))

def minOver (g : Nat → Nat) : List Nat → Nat
  | [] => 0
  | [v] => g v
  | v :: w :: l => min (g v) (minOver g (w :: l))

def C (l : List Nat) : Nat := minOver (key l) l

def matchB (l : List Nat) : Bool :=
  l.all fun u => u < 105 && l.all fun w => u == w || (u / 7 != w / 7 && u % 7 != w % 7)

inductive T where
  | leaf : T
  | node : T → Nat → T → T

def T.mem : T → Nat → Bool
  | .leaf, _ => false
  | .node l k r, x => if x < k then l.mem x else if k < x then r.mem x else true

def Wt (t : T) (l : List Nat) : Int := if matchB l && t.mem (C l) then 1 else 0

/-- Pigeon `i` axiom against the set `M`: `∑_j W(M ∪ {x_{ij}}) - W(M)`. -/
def pigS (t : T) (i : Nat) (M : List Nat) : Int := rsum 7 (fun j => Wt t ((i * 7 + j) :: M)) - Wt t M

/-- Hole `j` axiom against the set `M`: `∑_i W(M ∪ {x_{ij}}) - W(M)`. -/
def holS (t : T) (j : Nat) (M : List Nat) : Int := rsum 15 (fun i => Wt t ((i * 7 + j) :: M)) - Wt t M

def allB : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, f => allB n f && f n

/-- All 22 linear axioms against `M`, mod 2. -/
def axOk (t : T) (M : List Nat) : Bool :=
  allB 15 (fun i => pigS t i M % 2 == 0) && allB 7 (fun j => holS t j M % 2 == 0)

/-- The check for `M = {0, u, w}`, skipped when that is not a matching. -/
def pairOk (t : T) (u w : Nat) : Bool := !matchB [0, u, w] || axOk t [0, u, w]

end Programme.«20261025-1627-proof-complexity».K5Defs
