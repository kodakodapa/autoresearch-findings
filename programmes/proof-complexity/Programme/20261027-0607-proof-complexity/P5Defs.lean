import Programme.«20261026-1402-proof-complexity».ExtLemma
import Programme.«20261027-0607-proof-complexity».P5Tab

/-! Class-function form of th's unit degree-5 design (K21) for `ontoFPHP 9 25` over `Z/5`.

Pigeon classes `[4^8, 2]` (`pc`), hole classes `[4, 4, 1]` (`hc`); variable `v = 9 i + j` lies in
cell `3 * pc i + hc j` (27 cells). A matching `g` has hash `hkey g = ∑_{v ∈ g} wt (cell v)` and the
design is `T g = look (hkey g)`: `look` reads the hashed table `P5Tab` (bucket displacement,
3-bit values). Only the kernel check `enum` below inspects `look`; the proof treats it as a black
box. `enum` checks, for every count matrix `m` (27 entries, sum `≤ 4`) within the class sizes, the
reduced row and column equations of th's P67 at `h = ∑ m_c wt c`. -/

namespace Programme.«20261027-0607-proof-complexity».P5

def wt (c : Nat) : Nat := (Wt >>> (48 * c)) % 281474976710656

/-- Forces `x` to a literal. -/
def fN (x : Nat) (k : Nat → Nat) : Nat :=
  match x with
  | 0 => k 0
  | n + 1 => k (n + 1)

def look (h : Nat) : Nat := fN h fun h =>
  fN (h % 32768) fun b => fN ((dch (b / 256) >>> (8 * (b % 256))) % 256) fun d =>
    fN ((h / 32768 + d) % 131072) fun s => (vch (s / 512) >>> (3 * (s % 512))) % 8

/-- Pigeon class: pigeons `4a..4a+3` for `a < 8`, pigeons `≥ 32` in class 8. -/
def pc (i : Nat) : Nat := if i < 32 then i / 4 else 8
/-- Hole class: holes 0-3, 4-7, 8. -/
def hc (j : Nat) : Nat := if j < 4 then 0 else if j < 8 then 1 else 2
/-- Cell of variable `v = 9 i + j`. -/
def cell (v : Nat) : Nat := 3 * pc (v / 9) + hc (v % 9)

def hkey : List Nat → Nat
  | [] => 0
  | v :: l => wt (cell v) + hkey l

/-- The design. -/
def T (g : List Nat) : Int := (look (hkey g) : Int)

/-- `∑_i m_i ψ(s + i)` (entries of `m` from index `s`); `ψ` is only evaluated at nonzero entries. -/
def sumW (ψ : Nat → Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | i, x :: l => (if x = 0 then 0 else x * ψ i) + sumW ψ (i + 1) l

/-- `∑_{a < A} f a`. -/
def nsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | a + 1 => nsum f a + f a

def Pb (a : Nat) : Nat := if a < 8 then 4 else 2
def Hb (d : Nat) : Nat := if d < 2 then 4 else 1

/-- Row counts: sums of consecutive triples. -/
def rowsOf : List Nat → List Nat
  | a :: b :: c :: rest => (a + b + c) :: rowsOf rest
  | _ => []

/-- Column counts: sums of the entries at positions `≡ 0, 1, 2` mod 3, added to `x, y, z`. -/
def colsOf : List Nat → Nat → Nat → Nat → List Nat
  | a :: b :: c :: rest, x, y, z => colsOf rest (x + a) (y + b) (z + c)
  | _, x, y, z => [x, y, z]

/-- Forces `x` to a literal before continuing (kernel evaluation is call-by-name). -/
def withN (x : Nat) (k : Nat → Bool) : Bool :=
  match x with
  | 0 => k 0
  | n + 1 => k (n + 1)

theorem withN_eq (x : Nat) (k : Nat → Bool) : withN x k = k x := by
  cases x <;> rfl

/-- Forces every entry of `xs`. -/
def forceL : List Nat → (List Nat → Bool) → Bool
  | [], k => k []
  | x :: xs, k => withN x fun x' => forceL xs fun r => k (x' :: r)

theorem forceL_eq : ∀ (xs : List Nat) (k : List Nat → Bool), forceL xs k = k xs
  | [], _ => rfl
  | x :: xs, k => by rw [forceL, withN_eq, forceL_eq]

def guard (R C : List Nat) : Bool :=
  (List.range 9).all (fun a => R.getD a 0 ≤ Pb a) && (List.range 3).all (fun d => C.getD d 0 ≤ Hb d)

def sel (d u0 u1 u2 : Nat) : Nat := if d = 0 then u0 else if d = 1 then u1 else u2

/-- Row equations: `R` row counts from class `a` on, `U` the neighbour values in triples. -/
def rowsEq (C0 C1 C2 L : Nat) : List Nat → Nat → List Nat → Bool
  | r :: R, a, u0 :: u1 :: u2 :: U =>
    (!(r < Pb a) || (4 * u0 + 4 * u1 + u2) % 5 == (C0 * u0 + C1 * u1 + C2 * u2 + L) % 5) &&
      rowsEq C0 C1 C2 L R (a + 1) U
  | _, _, _ => true

/-- `∑_a Pb a * U[3a + d]` over the triples of `U`, classes from `a` on. -/
def pS (d : Nat) : Nat → List Nat → Nat
  | a, u0 :: u1 :: u2 :: U => Pb a * sel d u0 u1 u2 + pS d (a + 1) U
  | _, _ => 0

/-- `∑_a R[a] * U[3a + d]`. -/
def qS (d : Nat) : List Nat → List Nat → Nat
  | r :: R, u0 :: u1 :: u2 :: U => r * sel d u0 u1 u2 + qS d R U
  | _, _ => 0

/-- Reduced equations at a count matrix with row counts `R`, column counts `C`,
`U[c] = T(g + cell c)` and `L = T g`. -/
def eqs (R C U : List Nat) (L : Nat) : Bool :=
  rowsEq (C.getD 0 0) (C.getD 1 0) (C.getD 2 0) L R 0 U &&
  ((List.range 3).all fun d => !(C.getD d 0 < Hb d) || pS d 0 U % 5 == (qS d R U + L) % 5)

def okM (m : List Nat) : Bool :=
  forceL (rowsOf m) fun R => forceL (colsOf m 0 0 0) fun C =>
    !guard R C ||
    withN (sumW wt 0 m) fun h => withN (look h) fun L =>
      forceL ((List.range 27).map fun c => look (h + wt c)) fun U => eqs R C U L

/-- `okM` at every `acc'' ++ acc` with `acc''` of length `c` and entries summing to `≤ b`. -/
def enum : Nat → Nat → List Nat → Bool
  | 0, _, acc => okM acc
  | c + 1, b, acc => (List.range (b + 1)).all fun v => enum c (b - v) (v :: acc)

end Programme.«20261027-0607-proof-complexity».P5
