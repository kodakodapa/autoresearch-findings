import Programme.«20261027-1434-proof-complexity».Code3
import Programme.«20261027-1434-proof-complexity».Towers

/-!
# Parametric level-3 generators at `(n, k) = (7, 8)` with explicit supports

Two families of block products (`ProdM`), with blocks given by parameters:

* `GRR π` (th's RRR): rectangles `{p_c, q_c} × {j_c, h_c}` (`c < 3`, tower `[s ≥ 1]`) ⊗ the
  all-ones block on the remaining `9` pigeons × `1` hole.
* `GTR π` (th's T ⊗ R): the `T` tower (`[s ≥ 2]`) on `{a1,a2,a3} × {h1,h2,h3}` ⊗ a rectangle
  `{r1, r2} × {s1, s2}` ⊗ the all-ones block on the remaining `9` pigeons × one hole ⊗ the pin
  `(pp, ph)`.

For valid parameters both are self-balanced at every level `e ≤ 3` (`grr_bal`, `gtr_bal`, from
`ProdM.bal_prodM`). On a canonical 3-matching `m` the value equals the number of occurrences of
`code3 m` in an explicit list of codes (`grr_count`, `gtr_count`): the 64 products of one edge
of each rectangle, resp. the 72 products of a 2-matching inside `T` and a rectangle edge.
-/

namespace Programme.«20261027-1434-proof-complexity».Gen3

set_option linter.unusedVariables false
set_option linter.deprecated false

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ProdExt (SL locL)
open Programme.«20261026-1402-proof-complexity».TExt (lf SL_lf)
open Programme.«20261027-1434-proof-complexity».ProdM Programme.«20261027-1434-proof-complexity».LocLf Programme.«20261027-1434-proof-complexity».Towers Programme.«20261027-1434-proof-complexity».Code3

/-! ## List sums and counts -/

def lsum (L : List Nat) (F : Nat → Int) : Int := (L.map F).sum

theorem lsum_cons (x : Nat) (L : List Nat) (F : Nat → Int) : lsum (x :: L) F = F x + lsum L F := by
  simp [lsum]

theorem lsum_nil (F : Nat → Int) : lsum [] F = 0 := rfl

theorem lsum_congr : ∀ (L : List Nat) (F G : Nat → Int), (∀ x ∈ L, F x = G x) → lsum L F = lsum L G
  | [], _, _, _ => rfl
  | x :: L, F, G, h => by
    rw [lsum_cons, lsum_cons, h x (by simp), lsum_congr L F G (fun y hy => h y (by simp [hy]))]

theorem lsum_add : ∀ (L : List Nat) (F G : Nat → Int), lsum L (fun x => F x + G x) = lsum L F + lsum L G
  | [], _, _ => by simp [lsum_nil]
  | x :: L, F, G => by rw [lsum_cons, lsum_cons, lsum_cons, lsum_add L F G]; omega

theorem lsum_zero : ∀ (L : List Nat), lsum L (fun _ => 0) = 0
  | [] => rfl
  | x :: L => by rw [lsum_cons, lsum_zero L]; rfl

theorem lsum_ind : ∀ (L : List Nat) (t : Nat) (A : Int),
    lsum L (fun x => if x = t then A else 0) = (L.count t : Int) * A
  | [], _, _ => by simp [lsum_nil]
  | x :: L, t, A => by
    rw [lsum_cons, lsum_ind L t A, List.count_cons]
    by_cases h : x = t
    · subst h; simp [Int.add_mul]; omega
    · simp [h]

theorem count_flatMap (K : Nat) : ∀ (L : List Nat) (f : Nat → List Nat),
    (((L.flatMap f).count K : Nat) : Int) = lsum L (fun x => ((f x).count K : Int))
  | [], _ => by simp [lsum_nil]
  | x :: L, f => by
    rw [List.flatMap_cons, List.count_append, lsum_cons, ← count_flatMap K L f]; push_cast; rfl

theorem count_map (K : Nat) (g : Nat → Nat) : ∀ (L : List Nat),
    (((L.map g).count K : Nat) : Int) = lsum L (fun z => if g z = K then 1 else 0)
  | [] => by simp [lsum_nil]
  | x :: L => by
    rw [List.map_cons, List.count_cons, lsum_cons, ← count_map K g L]
    by_cases h : g x = K <;> simp [h] <;> omega

theorem count_nodup : ∀ {L : List Nat}, L.Nodup → ∀ t : Nat,
    (L.count t : Int) = if t ∈ L then 1 else 0
  | [], _, t => by simp
  | x :: L, h, t => by
    rw [List.nodup_cons] at h
    rw [List.count_cons, Int.natCast_add, count_nodup h.2 t]
    by_cases ht : t = x
    · subst ht; simp [h.1]
    · simp [ht, show ¬ (x = t) from fun e => ht e.symm]

/-- Three nested sums of one ordered indicator. -/
theorem lsum3_ind (E0 E1 E2 : List Nat) (u v w : Nat) :
    lsum E0 (fun x => lsum E1 (fun y => lsum E2 (fun z => if x = u ∧ y = v ∧ z = w then 1 else 0))) =
      (E0.count u : Int) * ((E1.count v : Int) * (E2.count w : Int)) := by
  have h2 : ∀ x y, lsum E2 (fun z => if x = u ∧ y = v ∧ z = w then 1 else 0) =
      if y = v then (if x = u then (E2.count w : Int) else 0) else 0 := by
    intro x y
    by_cases hx : x = u <;> by_cases hy : y = v
    · rw [lsum_congr E2 _ (fun z => if z = w then 1 else 0) (fun z _ => by simp [hx, hy]), lsum_ind]; simp [hx, hy]
    all_goals (rw [lsum_congr E2 _ (fun _ => 0) (fun z _ => by simp [hx, hy]), lsum_zero]; simp [hx, hy])
  have h1 : ∀ x, lsum E1 (fun y => lsum E2 (fun z => if x = u ∧ y = v ∧ z = w then 1 else 0)) =
      if x = u then (E1.count v : Int) * (E2.count w : Int) else 0 := by
    intro x
    rw [lsum_congr E1 _ _ (fun y _ => h2 x y), lsum_ind]
    by_cases hx : x = u <;> simp [hx]
  rw [lsum_congr E0 _ _ (fun x _ => h1 x), lsum_ind]

/-! ## Grids of edges -/

def grid (P H : List Nat) : List Nat := P.flatMap (fun i => H.map (fun j => i * 7 + j))

theorem count_row (t i : Nat) : ∀ H : List Nat, (∀ j ∈ H, j < 7) →
    (((H.map (fun j => i * 7 + j)).count t : Nat) : Int) = if t / 7 = i then (H.count (t % 7) : Int) else 0
  | [], _ => by simp
  | j :: H, hH => by
    have hj := hH j (by simp)
    rw [List.map_cons, List.count_cons, List.count_cons, Int.natCast_add, Int.natCast_add,
      count_row t i H (fun j' h' => hH j' (by simp [h']))]
    have e : (i * 7 + j = t) ↔ (t / 7 = i ∧ t % 7 = j) := by
      constructor
      · intro h; subst h; omega
      · intro ⟨h1, h2⟩; omega
    by_cases h1 : t / 7 = i <;> by_cases h2 : t % 7 = j <;> simp [h1, h2, e, show (j = t % 7) ↔ (t % 7 = j) from eq_comm]

theorem count_grid (t : Nat) (H : List Nat) (hH : ∀ j ∈ H, j < 7) : ∀ P : List Nat,
    (((grid P H).count t : Nat) : Int) = (P.count (t / 7) : Int) * (H.count (t % 7) : Int)
  | [] => by simp [grid]
  | i :: P => by
    have := count_grid t H hH P
    unfold grid at this ⊢
    rw [List.flatMap_cons, List.count_append, Int.natCast_add, this, count_row t i H hH, List.count_cons, Int.natCast_add]
    by_cases h : t / 7 = i
    · subst h; simp [Int.add_mul]; omega
    · simp [h, show ¬ (i = t / 7) from fun e => h e.symm]

/-- Grid count as a block indicator. -/
theorem count_grid_blk {m c : Nat} (bp bh : Nat → Nat) (hc : c < m) {P H : List Nat}
    (hP : P.Nodup) (hH : H.Nodup) (hH7 : ∀ j ∈ H, j < 7)
    (hbp : ∀ i, bp i = c ↔ i ∈ P) (hbh : ∀ j, bh j = c ↔ j ∈ H) (t : Nat) :
    (((grid P H).count t : Nat) : Int) = if blkM m bp bh 7 t = c then 1 else 0 := by
  rw [count_grid t H hH7 P, count_nodup hP, count_nodup hH]
  have key : blkM m bp bh 7 t = c ↔ (t / 7 ∈ P ∧ t % 7 ∈ H) := by
    unfold blkM
    rw [← hbp, ← hbh]
    split
    · next h => constructor
                · intro e; exact ⟨e, by omega⟩
                · intro ⟨e1, _⟩; exact e1
    · next h => constructor
                · intro e; omega
                · intro ⟨e1, e2⟩; exact absurd ⟨by omega, by omega⟩ h
  by_cases h1 : t / 7 ∈ P <;> by_cases h2 : t % 7 ∈ H <;> simp [h1, h2, key]

/-! ## Counting block members -/

theorem rsum_eq (M x : Nat) : rsum M (fun t => if t = x then (1 : Int) else 0) = if x < M then 1 else 0 := by
  induction M with
  | zero => simp [rsum]
  | succ M ih =>
    simp only [rsum, ih]
    by_cases h : M = x
    · subst h; simp
    · by_cases h' : x < M
      · simp [h', show x < M + 1 by omega, show ¬ M = x from h]
      · simp [h', show ¬ x < M + 1 by omega, show ¬ M = x from h]

theorem rsum_mem (M : Nat) : ∀ (L : List Nat), L.Nodup → (∀ x ∈ L, x < M) →
    rsum M (fun t => if t ∈ L then (1 : Int) else 0) = L.length
  | [], _, _ => by simp
  | x :: L, hn, hl => by
    rw [List.nodup_cons] at hn
    have e : ∀ t < M, (if t ∈ x :: L then (1 : Int) else 0) =
        (if t = x then 1 else 0) + (if t ∈ L then 1 else 0) := by
      intro t _
      by_cases h1 : t = x
      · subst h1; simp [hn.1]
      · simp [h1]
    rw [rsum_congr M _ _ e, rsum_add, rsum_eq, rsum_mem M L hn.2 (fun y hy => hl y (by simp [hy]))]
    simp [hl x (by simp)]; omega

theorem rsum_class (M : Nat) (L : List Nat) (hn : L.Nodup) (hl : ∀ x ∈ L, x < M) (Q : Nat → Prop)
    [DecidablePred Q] (hQ : ∀ t, Q t ↔ t ∈ L) : rsum M (fun t => if Q t then (1 : Int) else 0) = L.length := by
  rw [← rsum_mem M L hn hl]; exact rsum_congr M _ _ (fun t _ => by simp [hQ])

theorem rsum_one' : ∀ M : Nat, rsum M (fun _ => (1 : Int)) = M
  | 0 => rfl
  | M + 1 => by simp only [rsum, rsum_one' M]; omega

theorem rsum_coclass (M : Nat) (L : List Nat) (hn : L.Nodup) (hl : ∀ x ∈ L, x < M) (Q : Nat → Prop)
    [DecidablePred Q] (hQ : ∀ t, Q t ↔ t ∉ L) :
    rsum M (fun t => if Q t then (1 : Int) else 0) = (M : Int) - L.length := by
  have e : ∀ t < M, (if Q t then (1 : Int) else 0) + (if t ∈ L then 1 else 0) = 1 := by
    intro t _; by_cases h : t ∈ L <;> simp [hQ, h]
  have h2 := rsum_add M (fun t => if Q t then (1 : Int) else 0) (fun t => if t ∈ L then 1 else 0)
  rw [rsum_congr M _ _ e, rsum_one', rsum_mem M L hn hl] at h2
  omega

/-! ## Products on 3-lists -/

theorem flM3_len (m : Nat) (bp bh : Nat → Nat) (c u v w : Nat) :
    (flM m bp bh 7 c [u, v, w]).length =
      (if blkM m bp bh 7 u = c then 1 else 0) + (if blkM m bp bh 7 v = c then 1 else 0) +
        (if blkM m bp bh 7 w = c then 1 else 0) := by
  simp only [flM, List.filter_cons, List.filter_nil, beq_iff_eq]
  by_cases h1 : blkM m bp bh 7 u = c <;> by_cases h2 : blkM m bp bh 7 v = c <;>
    by_cases h3 : blkM m bp bh 7 w = c <;> simp [h1, h2, h3]

def cnt3 (x y z c : Nat) : Nat := (if x = c then 1 else 0) + (if y = c then 1 else 0) + (if z = c then 1 else 0)

/-- A product with length-only blocks on a 3-list, through the block indices of its entries. -/
def F3 (m : Nat) (G : Nat → Nat → Int) (x y z : Nat) : Int :=
  if x < m ∧ y < m ∧ z < m then prodR m (fun c => G c (cnt3 x y z c)) else 0

theorem prodM3 (m : Nat) (bp bh : Nat → Nat) (φ : Nat → List Nat → Int) (G : Nat → Nat → Int)
    (hφ : ∀ c l, φ c l = G c l.length) (u v w : Nat) :
    ProdM m bp bh 7 φ [u, v, w] = F3 m G (blkM m bp bh 7 u) (blkM m bp bh 7 v) (blkM m bp bh 7 w) := by
  unfold ProdM F3
  have hok : okM m bp bh 7 [u, v, w] = decide (blkM m bp bh 7 u < m ∧ blkM m bp bh 7 v < m ∧ blkM m bp bh 7 w < m) := by
    simp [okM]
  rw [hok]
  by_cases h : blkM m bp bh 7 u < m ∧ blkM m bp bh 7 v < m ∧ blkM m bp bh 7 w < m
  · simp only [h, decide_true, if_true, and_self]
    exact prodR_congr m _ _ (fun c _ => by rw [hφ, flM3_len]; rfl)
  · simp [h]

/-! ## RRR generators -/

structure RP where
  p1 : Nat
  p2 : Nat
  p3 : Nat
  q1 : Nat
  q2 : Nat
  q3 : Nat
  j1 : Nat
  j2 : Nat
  j3 : Nat
  h1 : Nat
  h2 : Nat
  h3 : Nat

def d6 (a b c d e f M : Nat) : Bool :=
  a < M && b < M && c < M && d < M && e < M && f < M &&
  a != b && a != c && a != d && a != e && a != f && b != c && b != d && b != e && b != f &&
  c != d && c != e && c != f && d != e && d != f && e != f

theorem d6_spec {a b c d e f M : Nat} (h : d6 a b c d e f M = true) :
    a < M ∧ b < M ∧ c < M ∧ d < M ∧ e < M ∧ f < M ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧
    b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧ c ≠ d ∧ c ≠ e ∧ c ≠ f ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f := by
  simp only [d6, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  omega

theorem d6_lt {a b c d e f M : Nat} (h : d6 a b c d e f M = true) :
    a < M ∧ b < M ∧ c < M ∧ d < M ∧ e < M ∧ f < M := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := d6_spec h; exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem d6_ne {a b c d e f M : Nat} (h : d6 a b c d e f M = true) : a ≠ d ∧ b ≠ e ∧ c ≠ f := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -, -, -, -, h14, -, -, -, h18, -⟩ := d6_spec h; exact ⟨h9, h14, h18⟩

def RP.valid (π : RP) : Bool := d6 π.p1 π.p2 π.p3 π.q1 π.q2 π.q3 15 && d6 π.j1 π.j2 π.j3 π.h1 π.h2 π.h3 7

def bl3 (a1 b1 a2 b2 a3 b3 i : Nat) : Nat :=
  if i = a1 ∨ i = b1 then 0 else if i = a2 ∨ i = b2 then 1 else if i = a3 ∨ i = b3 then 2 else 3

def RP.bp (π : RP) : Nat → Nat := bl3 π.p1 π.q1 π.p2 π.q2 π.p3 π.q3
def RP.bh (π : RP) : Nat → Nat := bl3 π.j1 π.h1 π.j2 π.h2 π.j3 π.h3

def GRR (π : RP) : List Nat → Int := ProdM 4 π.bp π.bh 7 φRRRM

def RP.supp (π : RP) : List Nat :=
  (grid [π.p1, π.q1] [π.j1, π.h1]).flatMap (fun x => (grid [π.p2, π.q2] [π.j2, π.h2]).flatMap
    (fun y => (grid [π.p3, π.q3] [π.j3, π.h3]).map (fun z => cd x y z)))

theorem bl3_iff {a1 b1 a2 b2 a3 b3 M : Nat} (h : d6 a1 a2 a3 b1 b2 b3 M = true) (i : Nat) :
    (bl3 a1 b1 a2 b2 a3 b3 i = 0 ↔ i ∈ [a1, b1]) ∧ (bl3 a1 b1 a2 b2 a3 b3 i = 1 ↔ i ∈ [a2, b2]) ∧
    (bl3 a1 b1 a2 b2 a3 b3 i = 2 ↔ i ∈ [a3, b3]) ∧ (bl3 a1 b1 a2 b2 a3 b3 i = 3 ↔ i ∉ [a1, a2, a3, b1, b2, b3]) := by
  have := d6_spec h
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  unfold bl3
  split
  · omega
  · split
    · omega
    · split <;> omega

theorem nd2 {a b : Nat} (h : a ≠ b) : [a, b].Nodup := by simp [h]

theorem nd6 {a b c d e f M : Nat} (h : d6 a b c d e f M = true) : [a, b, c, d, e, f].Nodup := by
  have := d6_spec h; simp; omega

def gRR (c s : Nat) : Int := if c = 3 then g1 s else gR s

theorem φRRRM_eq (c : Nat) (l : List Nat) : φRRRM c l = gRR c l.length := by
  match c with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | n + 4 => simp only [gRR, show n + 4 ≠ 3 by omega, if_false]; rfl

theorem grr_bal (π : RP) (hv : π.valid = true) (e : Nat) (he : e ≤ 3) : Bal 2 7 8 (GRR π) (GRR π) e := by
  simp only [RP.valid, Bool.and_eq_true] at hv
  obtain ⟨hp, hh⟩ := hv
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := d6_lt hp; obtain ⟨n1, n2, n3⟩ := d6_ne hp
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := d6_lt hh; obtain ⟨o1, o2, o3⟩ := d6_ne hh
  have bp := bl3_iff hp; have bh := bl3_iff hh
  have cP : ∀ c < 3, rsum (7 + 8) (fun s => if π.bp s = c then (1 : Int) else 0) = (2 : Nat) := by
    intro c hc
    match c, hc with
    | 0, _ => exact rsum_class _ [π.p1, π.q1] (nd2 n1) (by simp; omega) _ (fun t => (bp t).1)
    | 1, _ => exact rsum_class _ [π.p2, π.q2] (nd2 n2) (by simp; omega) _ (fun t => (bp t).2.1)
    | 2, _ => exact rsum_class _ [π.p3, π.q3] (nd2 n3) (by simp; omega) _ (fun t => (bp t).2.2.1)
  have cH : ∀ c < 3, rsum 7 (fun s => if π.bh s = c then (1 : Int) else 0) = (2 : Nat) := by
    intro c hc
    match c, hc with
    | 0, _ => exact rsum_class _ [π.j1, π.h1] (nd2 o1) (by simp; omega) _ (fun t => (bh t).1)
    | 1, _ => exact rsum_class _ [π.j2, π.h2] (nd2 o2) (by simp; omega) _ (fun t => (bh t).2.1)
    | 2, _ => exact rsum_class _ [π.j3, π.h3] (nd2 o3) (by simp; omega) _ (fun t => (bh t).2.2.1)
  have cP3 : rsum (7 + 8) (fun s => if π.bp s = 3 then (1 : Int) else 0) = (9 : Nat) := by
    rw [rsum_coclass (7 + 8) _ (nd6 hp) (by simp; omega) (fun s => π.bp s = 3) (fun t => (bp t).2.2.2)]; rfl
  have cH3 : rsum 7 (fun s => if π.bh s = 3 then (1 : Int) else 0) = (1 : Nat) := by
    rw [rsum_coclass 7 _ (nd6 hh) (by simp; omega) (fun s => π.bh s = 3) (fun t => (bh t).2.2.2)]; rfl
  apply bal_prodM 2 (fun i _ => by unfold RP.bp bl3; split <;> (try split) <;> (try split) <;> omega)
    (fun j _ => by unfold RP.bh bl3; split <;> (try split) <;> (try split) <;> omega) φRRRM
    (fun c => by unfold φRRRM; split <;> exact SL_lf _)
    (fun c => if c = 3 then 0 else 1) (fun c => if c = 3 then 0 else 100)
  · intro c hc l hl
    match c, hc with
    | 0, _ | 1, _ | 2, _ => show gR l.length = 0; unfold gR; simp at hl; simp [hl]
    | 3, _ => simp at hl
  · intro c hc
    match c, hc with
    | 0, _ => exact lf_locbal 2 4 _ _ 0 2 2 100 gR (by omega) (by omega) (cH 0 (by omega)) (cP 0 (by omega)) (by decide)
    | 1, _ => exact lf_locbal 2 4 _ _ 1 2 2 100 gR (by omega) (by omega) (cH 1 (by omega)) (cP 1 (by omega)) (by decide)
    | 2, _ => exact lf_locbal 2 4 _ _ 2 2 2 100 gR (by omega) (by omega) (cH 2 (by omega)) (cP 2 (by omega)) (by decide)
    | 3, _ => exact lf_locbal 2 4 _ _ 3 9 1 0 g1 (by omega) (by omega) cH3 cP3 (by decide)
  · have : ∀ e ≤ 3, ∀ b < 4, e ≤ (fun c => if c = 3 then 0 else 100) b +
        natSum 4 (fun c => if c = b then 0 else (fun c => if c = 3 then 0 else 1) c) := by decide
    exact this e he

/-- Block indicator pattern of the RRR value. -/
def iR (x y z : Nat) : Int :=
  (if x = 0 ∧ y = 1 ∧ z = 2 then 1 else 0) + (if x = 0 ∧ y = 2 ∧ z = 1 then 1 else 0) +
  (if x = 1 ∧ y = 0 ∧ z = 2 then 1 else 0) + (if x = 1 ∧ y = 2 ∧ z = 0 then 1 else 0) +
  (if x = 2 ∧ y = 0 ∧ z = 1 then 1 else 0) + (if x = 2 ∧ y = 1 ∧ z = 0 then 1 else 0)

theorem F3R : ∀ x ≤ 4, ∀ y ≤ 4, ∀ z ≤ 4, F3 4 gRR x y z = iR x y z := by decide +kernel

/-- The six-term sum for RRR, as products of block indicators. -/
theorem iR_eq (I0 I1 I2 : Nat → Int) (bk : Nat → Nat) (hI0 : ∀ t, I0 t = if bk t = 0 then 1 else 0)
    (hI1 : ∀ t, I1 t = if bk t = 1 then 1 else 0) (hI2 : ∀ t, I2 t = if bk t = 2 then 1 else 0) (a b c : Nat) :
    I0 a * (I1 b * I2 c) + I0 a * (I1 c * I2 b) + I0 b * (I1 a * I2 c) + I0 b * (I1 c * I2 a) +
      I0 c * (I1 a * I2 b) + I0 c * (I1 b * I2 a) = iR (bk a) (bk b) (bk c) := by
  simp only [hI0, hI1, hI2, iR]
  by_cases ha0 : bk a = 0 <;> by_cases ha1 : bk a = 1 <;> by_cases ha2 : bk a = 2 <;>
  by_cases hb0 : bk b = 0 <;> by_cases hb1 : bk b = 1 <;> by_cases hb2 : bk b = 2 <;>
  by_cases hc0 : bk c = 0 <;> by_cases hc1 : bk c = 1 <;> by_cases hc2 : bk c = 2 <;>
  simp [ha0, ha1, ha2, hb0, hb1, hb2, hc0, hc1, hc2] <;> omega

theorem grr_count (π : RP) (hv : π.valid = true) {a b c : Nat} (hcb : c < b) (hba : b < a) (ha : a < 105) :
    GRR π [a, b, c] = ((π.supp.count (r3 a b c) : Nat) : Int) := by
  simp only [RP.valid, Bool.and_eq_true] at hv
  obtain ⟨hp, hh⟩ := hv
  obtain ⟨n1, n2, n3⟩ := d6_ne hp
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := d6_lt hh; obtain ⟨o1, o2, o3⟩ := d6_ne hh
  have bp := bl3_iff hp; have bh := bl3_iff hh
  have H7 : ∀ (j h : Nat), j < 7 → h < 7 → ∀ x ∈ [j, h], x < 7 := by intro j h hj hh x hx; simp at hx; omega
  have c0 := count_grid_blk (m := 4) π.bp π.bh (c := 0) (by omega) (nd2 n1)
    (nd2 o1) (H7 _ _ (by omega) (by omega)) (fun i => (bp i).1) (fun j => (bh j).1)
  have c1 := count_grid_blk (m := 4) π.bp π.bh (c := 1) (by omega) (nd2 n2)
    (nd2 o2) (H7 _ _ (by omega) (by omega)) (fun i => (bp i).2.1) (fun j => (bh j).2.1)
  have c2 := count_grid_blk (m := 4) π.bp π.bh (c := 2) (by omega) (nd2 n3)
    (nd2 o3) (H7 _ _ (by omega) (by omega)) (fun i => (bp i).2.2.1) (fun j => (bh j).2.2.1)
  -- value side
  have hv : GRR π [a, b, c] = iR (blkM 4 π.bp π.bh 7 a) (blkM 4 π.bp π.bh 7 b) (blkM 4 π.bp π.bh 7 c) := by
    unfold GRR
    rw [prodM3 4 π.bp π.bh φRRRM gRR φRRRM_eq]
    exact F3R _ (blkM_le _) _ (blkM_le _) _ (blkM_le _)
  -- count side
  rw [hv, RP.supp, count_flatMap]
  rw [lsum_congr _ _ (fun x => lsum (grid [π.p2, π.q2] [π.j2, π.h2]) (fun y =>
      lsum (grid [π.p3, π.q3] [π.j3, π.h3]) (fun z => ind6 a b c x y z))) (fun x _ => by
    rw [count_flatMap]
    exact lsum_congr _ _ _ (fun y _ => by
      rw [count_map]; exact lsum_congr _ _ _ (fun z _ => cd_ind hcb hba ha x y z)))]
  simp only [ind6]
  simp only [lsum_add, lsum3_ind]
  rw [c0, c0, c0, c1, c1, c1, c2, c2, c2]
  exact (iR_eq _ _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) a b c).symm

/-! ## A fast form of the RRR support for the kernel -/

def C3' (a : Nat) : Nat := Nat.div (Nat.mul (Nat.mul a (Nat.sub a 1)) (Nat.sub a 2)) 6
def C2' (a : Nat) : Nat := Nat.div (Nat.mul a (Nat.sub a 1)) 2

/-- The rank code of `{x, y, z}` by comparisons only (no guard). -/
def cd3 (x y z : Nat) : Nat :=
  cond (Nat.blt x y)
    (cond (Nat.blt y z) (Nat.add (Nat.add (C3' z) (C2' y)) x)
      (cond (Nat.blt x z) (Nat.add (Nat.add (C3' y) (C2' z)) x) (Nat.add (Nat.add (C3' y) (C2' x)) z)))
    (cond (Nat.blt x z) (Nat.add (Nat.add (C3' z) (C2' x)) y)
      (cond (Nat.blt y z) (Nat.add (Nat.add (C3' x) (C2' z)) y) (Nat.add (Nat.add (C3' x) (C2' y)) z)))

def ok3F (x y z : Nat) : Bool :=
  Nat.blt x 105 && Nat.blt y 105 && Nat.blt z 105 && !(Nat.beq x y) && !(Nat.beq y z) && !(Nat.beq x z)

def cdF (x y z : Nat) : Nat := cond (ok3F x y z) (cd3 x y z) 187460

theorem ok3_eq (x y z : Nat) : ok3 x y z = ok3F x y z := by
  apply Bool.eq_iff_iff.mpr
  unfold ok3 ok3F
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Nat.blt_eq, Bool.not_eq_true',
    Nat.beq_eq_true_eq]
  constructor
  · intro h; refine ⟨⟨⟨⟨⟨h.1.1.1.1.1, h.1.1.1.1.2⟩, h.1.1.1.2⟩, ?_⟩, ?_⟩, ?_⟩
    all_goals (cases hb : Nat.beq _ _ <;> simp_all [Nat.beq_eq])
  · intro h; refine ⟨⟨⟨⟨⟨h.1.1.1.1.1, h.1.1.1.1.2⟩, h.1.1.1.2⟩, ?_⟩, ?_⟩, ?_⟩
    all_goals (intro e; subst e; simp_all [Nat.beq_refl])

theorem cd_eq_cdF (x y z : Nat) : cd x y z = cdF x y z := by
  unfold cd cdF
  rw [ok3_eq]
  cases ok3F x y z
  · rfl
  · simp only [cond_true, if_true]
    unfold cd3 srt r3 C3 C2 C3' C2'
    by_cases h1 : x < y <;> by_cases h2 : y < z <;> by_cases h3 : x < z <;>
      simp [h1, h2, h3, Nat.blt_eq] <;> rfl

/-- The 64 codes of a product of three 4-edge blocks, written out. -/
def supp64 (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 : Nat) : List Nat :=
  [cdF a0 b0 c0, cdF a0 b0 c1, cdF a0 b0 c2, cdF a0 b0 c3,
    cdF a0 b1 c0, cdF a0 b1 c1, cdF a0 b1 c2, cdF a0 b1 c3,
    cdF a0 b2 c0, cdF a0 b2 c1, cdF a0 b2 c2, cdF a0 b2 c3,
    cdF a0 b3 c0, cdF a0 b3 c1, cdF a0 b3 c2, cdF a0 b3 c3,
    cdF a1 b0 c0, cdF a1 b0 c1, cdF a1 b0 c2, cdF a1 b0 c3,
    cdF a1 b1 c0, cdF a1 b1 c1, cdF a1 b1 c2, cdF a1 b1 c3,
    cdF a1 b2 c0, cdF a1 b2 c1, cdF a1 b2 c2, cdF a1 b2 c3,
    cdF a1 b3 c0, cdF a1 b3 c1, cdF a1 b3 c2, cdF a1 b3 c3,
    cdF a2 b0 c0, cdF a2 b0 c1, cdF a2 b0 c2, cdF a2 b0 c3,
    cdF a2 b1 c0, cdF a2 b1 c1, cdF a2 b1 c2, cdF a2 b1 c3,
    cdF a2 b2 c0, cdF a2 b2 c1, cdF a2 b2 c2, cdF a2 b2 c3,
    cdF a2 b3 c0, cdF a2 b3 c1, cdF a2 b3 c2, cdF a2 b3 c3,
    cdF a3 b0 c0, cdF a3 b0 c1, cdF a3 b0 c2, cdF a3 b0 c3,
    cdF a3 b1 c0, cdF a3 b1 c1, cdF a3 b1 c2, cdF a3 b1 c3,
    cdF a3 b2 c0, cdF a3 b2 c1, cdF a3 b2 c2, cdF a3 b2 c3,
    cdF a3 b3 c0, cdF a3 b3 c1, cdF a3 b3 c2, cdF a3 b3 c3]

def RP.suppF (π : RP) : List Nat :=
  supp64 (π.p1 * 7 + π.j1) (π.p1 * 7 + π.h1) (π.q1 * 7 + π.j1) (π.q1 * 7 + π.h1) (π.p2 * 7 + π.j2) (π.p2 * 7 + π.h2) (π.q2 * 7 + π.j2) (π.q2 * 7 + π.h2) (π.p3 * 7 + π.j3) (π.p3 * 7 + π.h3) (π.q3 * 7 + π.j3) (π.q3 * 7 + π.h3)

theorem RP.supp_eq (π : RP) : π.supp = π.suppF := by
  have e : cd = cdF := funext fun x => funext fun y => funext fun z => cd_eq_cdF x y z
  unfold RP.supp RP.suppF
  rw [e]; rfl

end Programme.«20261027-1434-proof-complexity».Gen3
