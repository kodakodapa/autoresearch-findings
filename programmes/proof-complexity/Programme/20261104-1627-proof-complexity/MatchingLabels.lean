import Programme.«20261029-1156-proof-complexity».StdPC

/-! Concrete coordinates for the direct NoDrop argument.
Edges use the canonical onto-FPHP variable code i*n+j. Integer coefficients
are read modulo p. No kernel-spanning or reduction theorem is assumed here. -/
namespace Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS

abbrev Matching := List (Nat × Nat)

def freeRow (M : Matching) (i : Nat) : Bool := M.all fun e => e.1 != i
def freeCol (M : Matching) (j : Nat) : Bool := M.all fun e => e.2 != j

def rows (m : Nat) (M : Matching) : List Nat := (List.range m).filter (freeRow M)
def cols (n : Nat) (M : Matching) : List Nat := (List.range n).filter (freeCol M)

/-- Enumerate once, ordered by increasing pigeon. The empty matching is
present even on an empty board. -/
def matchings (m n : Nat) : Nat → List Matching
  | 0 => [[]]
  | d + 1 => (matchings m n d).flatMap fun M =>
      ((rows m M).filter fun i => M.all fun e => e.1 < i).flatMap fun i =>
        (cols n M).map fun j => M ++ [(i,j)]

def ordered (M : Matching) : Matching := M.mergeSort (fun a b => a.1 ≤ b.1)

structure Label where
  base : Matching
  isRow : Bool
  mark : Nat
  deriving DecidableEq, Repr

abbrev Vector := List (Int × Label)

def labels (m n d : Nat) : List Label :=
  if d = 0 then [] else (matchings m n (d-1)).flatMap fun M =>
    (rows m M).map (fun i => ⟨M,true,i⟩) ++
    (cols n M).map (fun j => ⟨M,false,j⟩)

def mono (n : Nat) (M : Matching) : List Nat := M.map fun e => e.1*n+e.2

/-- Top extension sum, as an ordinary canonical polynomial. The order of
variables is immaterial under StdPC.PEq. -/
def topLabel (m n : Nat) (g : Label) : Poly Nat :=
  if g.isRow then ⟨(cols n g.base).map fun j => (1, (g.mark*n+j) :: mono n g.base)⟩
  else ⟨(rows m g.base).map fun i => (1, (i*n+g.mark) :: mono n g.base)⟩

def top (m n : Nat) (v : Vector) : Poly Nat :=
  ⟨v.flatMap fun t => (topLabel m n t.2).terms.map fun a => (t.1*a.1,a.2)⟩

def rho (n : Nat) (v : Vector) : Poly Nat :=
  ⟨v.map fun t => (t.1, mono n t.2.base)⟩

def valid (m n d : Nat) (v : Vector) : Prop := ∀ t ∈ v, t.2 ∈ labels m n d

def Kernel (p m n d : Nat) (v : Vector) : Prop :=
  valid m n d v ∧ Programme.«20261029-1156-proof-complexity».StdPC.PEq p (top m n v) ⟨[]⟩

def rr (n : Nat) (N : Matching) (a b : Nat) : Vector :=
  (cols n N).map (fun j => (1, ⟨ordered (N ++ [(b,j)]),true,a⟩)) ++
  (cols n N).map (fun j => (-1, ⟨ordered (N ++ [(a,j)]),true,b⟩))

def cc (m : Nat) (N : Matching) (a b : Nat) : Vector :=
  (rows m N).map (fun i => (1, ⟨ordered (N ++ [(i,b)]),false,a⟩)) ++
  (rows m N).map (fun i => (-1, ⟨ordered (N ++ [(i,a)]),false,b⟩))

def rc (m n : Nat) (N : Matching) (i j : Nat) : Vector :=
  ((rows m N).filter (· != i)).map (fun a => (1, ⟨ordered (N ++ [(a,j)]),true,i⟩)) ++
  ((cols n N).filter (· != j)).map (fun b => (-1, ⟨ordered (N ++ [(i,b)]),false,j⟩))

/-- Anchored divided-power syzygy. Comparisons concern E only, not N. -/
def z (m n t : Nat) (N : Matching) : Vector :=
  ((matchings m n (t-1)).filter fun E =>
    E.all fun e => freeRow N e.1 && freeCol N e.2).flatMap fun E =>
      ((rows m (N ++ E)).filter fun i => E.all fun e => e.1 < i).map
        (fun i => (1, ⟨ordered (N ++ E),true,i⟩)) ++
      ((cols n (N ++ E)).filter fun j => E.all fun e => e.2 < j).map
        (fun j => (-1, ⟨ordered (N ++ E),false,j⟩))

/-- The ordered rr, cc, rc and anchored Z families, on this board. -/
def syzygies (m n d : Nat) : List Vector :=
  (if d < 2 then [] else
    (matchings m n (d-2)).flatMap fun N =>
      (rows m N).flatMap (fun a =>
        ((rows m N).filter (fun b => a < b)).map (rr n N a)) ++
      (cols n N).flatMap (fun a =>
        ((cols n N).filter (fun b => a < b)).map (cc m N a)) ++
      (rows m N).flatMap (fun i => (cols n N).map (rc m n N i))) ++
  ((List.range d).map (· + 1)).flatMap fun t =>
    (matchings m n (d-t)).map (z m n t)

def vectorCoeff (v : Vector) (g : Label) : Int :=
  ((v.filter fun t => t.2 == g).map (·.1)).sum

def combine (c : List (Int × Vector)) : Vector :=
  c.flatMap fun t => t.2.map fun a => (t.1*a.1,a.2)

/-- Explicit coordinate spanning assertion. Quantification over raw labels
also ensures coefficients outside the finite label set vanish. -/
def Spanning (p m n d : Nat) : Prop :=
  ∀ v, Kernel p m n d v → ∃ c : List (Int × Vector),
    (∀ t ∈ c, t.2 ∈ syzygies m n d) ∧
    ∀ g, (p : Int) ∣ vectorCoeff v g - vectorCoeff (combine c) g

/-- Square obligation S(d); neither this nor Spanning is an axiom. -/
def Square (p d : Nat) : Prop := Spanning p (2*d-1) (2*d-1) d

/-- The inhomogeneous relation attached to a label. -/
def relation (m n : Nat) (g : Label) : Poly Nat :=
  (topLabel m n g).sub ⟨[(1,mono n g.base)]⟩

/-- Finite relation span W_D, expressed in canonical ordinary polynomials.
A future reduction theorem must connect this span to reduced PC lines. -/
def W (p m n D : Nat) (P : Poly Nat) : Prop :=
  ∃ v : Vector,
    (∀ t ∈ v, ∃ d, d ≤ D ∧ t.2 ∈ labels m n d) ∧
    Programme.«20261029-1156-proof-complexity».StdPC.PEq p P
      ⟨v.flatMap fun t => (relation m n t.2).terms.map fun a => (t.1*a.1,a.2)⟩

/-- Degree-one top map: the coefficient at edge (i,j) is a_i+b_j. -/
def topOne {m n : Nat} (a : Fin m → Int) (b : Fin n → Int)
    (i : Fin m) (j : Fin n) : Int := a i + b j

/-- The degree-one Z generator has row coefficients +1 and column
coefficients -1. This theorem works for every modulus, including 0 and 1. -/
theorem kernel_one_span {p m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (a : Fin m → Int) (b : Fin n → Int)
    (h : ∀ i j, (p : Int) ∣ topOne a b i j) :
    ∃ c : Int, (∀ i, (p : Int) ∣ a i - c) ∧
      (∀ j, (p : Int) ∣ b j - (-c)) := by
  let i0 : Fin m := ⟨0, hm⟩
  let j0 : Fin n := ⟨0, hn⟩
  refine ⟨a i0, ?_, ?_⟩
  · intro i
    have hi := Int.dvd_sub (h i j0) (h i0 j0)
    unfold topOne at hi
    rwa [show a i + b j0 - (a i0 + b j0) = a i - a i0 by omega] at hi
  · intro j
    simpa [topOne, Int.add_comm] using h i0 j

/-- Conversely, any multiple of Z is killed by the degree-one top map. -/
theorem kernel_one_of_span {p m n : Nat} (a : Fin m → Int) (b : Fin n → Int)
    (c : Int) (ha : ∀ i, (p : Int) ∣ a i - c)
    (hb : ∀ j, (p : Int) ∣ b j - (-c)) :
    ∀ i j, (p : Int) ∣ topOne a b i j := by
  intro i j
  have h := Int.dvd_add (ha i) (hb j)
  unfold topOne
  rwa [show a i - c + (b j - (-c)) = a i + b j by omega] at h

-- Small interface regressions against the archived finite coordinate counts.
#guard (labels 3 3 2).length == 36
#guard (syzygies 3 3 2).length == 25
#guard (labels 5 5 3).length == 1200
#guard (syzygies 5 5 3).length == 926

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.kernel_one_span
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.kernel_one_of_span
