import Programme.«20261027-0607-proof-complexity».P5Defs

/-!
# Class functions on `ontoFPHP 9 25`: the reduced design equations imply `Bal`

For the design `T g = look (hkey g)` of `Work.P5Defs` (a function of the class-count matrix of `g`
through the additive hash `hkey`), the free row sum at pigeon `i` of class `a` is
`∑_{j<9} T(g + (i,j)) - ∑_{v ∈ g} T(g + (i, hole v))`, and grouping the holes by class gives
`∑_d (Hb d - col_d) T(g + cell(a,d))`; columns likewise. So `Bal 5 9 25 T T e` follows from the
reduced equations at the count matrix `mOf g`, which `enum 27 4 [] = true` checks for every count
matrix of size `≤ 4` (`bal_of_enum`).
-/

namespace Programme.«20261027-0607-proof-complexity».P5

open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum var rsum_add)
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero var_div var_mod)
open Programme.«20261025-1627-proof-complexity».MomGen (canon mem_canon canon_nodup)
open Programme.«20261026-1402-proof-complexity».ExtLemma

/-! ## Sums over lists and ranges -/

/-- `∑_{v ∈ l} φ v`. -/
def lsum (φ : Nat → Int) : List Nat → Int
  | [] => 0
  | v :: l => φ v + lsum φ l

theorem rsum_single' (φ : Nat → Int) (a : Nat) : ∀ N, a < N → rsum N (fun x => if x = a then φ x else 0) = φ a
  | 0, h => absurd h (Nat.not_lt_zero _)
  | N + 1, h => by
    simp only [rsum]
    by_cases hN : N = a
    · subst hN
      rw [rsum_zero N _ (fun t ht => by rw [if_neg (by omega)])]; simp
    · rw [rsum_single' φ a N (by omega), if_neg hN]; omega

theorem rsum_mem (N : Nat) (φ : Nat → Int) : ∀ L : List Nat, L.Nodup → (∀ x ∈ L, x < N) →
    rsum N (fun x => if x ∈ L then φ x else 0) = lsum φ L
  | [], _, _ => rsum_zero N _ (fun t _ => by simp)
  | a :: L, hn, hl => by
    have ha : a ∉ L := (List.nodup_cons.mp hn).1
    rw [rsum_congr N _ (fun x => (if x = a then φ x else 0) + (if x ∈ L then φ x else 0)) (fun x _ => by
      by_cases h1 : x = a
      · subst h1; simp [ha]
      · simp [h1])]
    rw [rsum_add, rsum_single' φ a N (hl a (by simp)),
      rsum_mem N φ L (List.nodup_cons.mp hn).2 (fun x hx => hl x (by simp [hx]))]
    rfl

theorem rsum_notmem (N : Nat) (φ : Nat → Int) (L : List Nat) (hn : L.Nodup) (hl : ∀ x ∈ L, x < N) :
    rsum N (fun x => if x ∈ L then 0 else φ x) = rsum N φ - lsum φ L := by
  have := rsum_add N (fun x => if x ∈ L then φ x else 0) (fun x => if x ∈ L then 0 else φ x)
  rw [rsum_congr N (fun x => (if x ∈ L then φ x else 0) + (if x ∈ L then 0 else φ x)) φ
    (fun x _ => by by_cases h : x ∈ L <;> simp [h]), rsum_mem N φ L hn hl] at this
  omega

theorem rsum_nonneg (φ : Nat → Int) (hφ : ∀ x, 0 ≤ φ x) : ∀ N, 0 ≤ rsum N φ
  | 0 => by simp [rsum]
  | N + 1 => by simp only [rsum]; have := rsum_nonneg φ hφ N; have := hφ N; omega

theorem rsum_ge (φ : Nat → Int) (hφ : ∀ x, 0 ≤ φ x) (i : Nat) : ∀ N, i < N → φ i ≤ rsum N φ
  | 0, h => absurd h (Nat.not_lt_zero _)
  | N + 1, h => by
    simp only [rsum]
    by_cases hi : i = N
    · subst hi; have := rsum_nonneg φ hφ i; omega
    · have := rsum_ge φ hφ i N (by omega); have := hφ N; omega

/-- Counting bound: for `L` nodup in `[0, N)` and `ψ ≥ 0`, `∑_{x ∈ L} ψ ≤ ∑_{x < N} ψ - ψ i`
when `i < N`, `i ∉ L`. -/
theorem lsum_le_free (N : Nat) (ψ : Nat → Int) (hψ : ∀ x, 0 ≤ ψ x) (L : List Nat) (hn : L.Nodup)
    (hl : ∀ x ∈ L, x < N) (i : Nat) (hi : i < N) (hiL : i ∉ L) : lsum ψ L + ψ i ≤ rsum N ψ := by
  have h1 := rsum_notmem N ψ L hn hl
  have h2 := rsum_ge (fun x => if x ∈ L then 0 else ψ x) (fun x => by by_cases h : x ∈ L <;> simp [h, hψ x])
    i N hi
  simp only [hiL, if_false] at h2
  omega

theorem lsum_le (N : Nat) (ψ : Nat → Int) (hψ : ∀ x, 0 ≤ ψ x) (L : List Nat) (hn : L.Nodup)
    (hl : ∀ x ∈ L, x < N) : lsum ψ L ≤ rsum N ψ := by
  have h1 := rsum_notmem N ψ L hn hl
  have h2 := rsum_nonneg (fun x => if x ∈ L then 0 else ψ x) (fun x => by by_cases h : x ∈ L <;> simp [h, hψ x]) N
  omega

theorem lsum_map (φ : Nat → Int) (f : Nat → Nat) : ∀ l : List Nat, lsum φ (l.map f) = lsum (fun v => φ (f v)) l
  | [] => rfl
  | v :: l => by simp only [List.map, lsum, lsum_map φ f l]

theorem lsum_congr (φ ψ : Nat → Int) : ∀ l : List Nat, (∀ v ∈ l, φ v = ψ v) → lsum φ l = lsum ψ l
  | [], _ => rfl
  | v :: l, h => by
    simp only [lsum]; rw [h v (by simp), lsum_congr φ ψ l (fun w hw => h w (by simp [hw]))]

/-- Grouping by a class map `q < K`: `∑_{v ∈ l} F(q v) = ∑_{a<K} #{v : q v = a} F a`. -/
theorem lsum_group (K : Nat) (q : Nat → Nat) (F : Nat → Int) :
    ∀ l : List Nat, (∀ v ∈ l, q v < K) →
      lsum (fun v => F (q v)) l = rsum K (fun a => lsum (fun v => if q v = a then 1 else 0) l * F a)
  | [], _ => by rw [rsum_zero K _ (fun t _ => by simp [lsum])]; rfl
  | v :: l, h => by
    simp only [lsum]
    rw [lsum_group K q F l (fun w hw => h w (by simp [hw]))]
    rw [rsum_congr K (fun a => ((if q v = a then 1 else 0) + lsum (fun v => if q v = a then 1 else 0) l) * F a)
      (fun a => (if a = q v then F a else 0) + lsum (fun v => if q v = a then 1 else 0) l * F a) (fun a _ => by
      by_cases h1 : q v = a
      · subst h1; simp [Int.add_mul]
      · simp [h1, Ne.symm h1])]
    rw [rsum_add, rsum_single' F (q v) K (h v (by simp))]

/-! ## Matchings -/

theorem nodup_map_inj (f : Nat → Nat) : ∀ l : List Nat, l.Nodup → (∀ v ∈ l, ∀ w ∈ l, f v = f w → v = w) →
    (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | v :: l, hn, h => by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_inj f l (List.nodup_cons.mp hn).2
      (fun a ha b hb => h a (by simp [ha]) b (by simp [hb]))⟩
    obtain ⟨w, hw, hfw⟩ := List.mem_map.mp hm
    have := h v (by simp) w (by simp [hw]) hfw.symm
    subst this; exact (List.nodup_cons.mp hn).1 hw

theorem cfl_false {v w : Nat} (h : cfl 9 v w = false) (hne : v ≠ w) : v / 9 ≠ w / 9 ∧ v % 9 ≠ w % 9 := by
  simp only [cfl, Bool.and_eq_false_iff, bne_eq_false_iff_eq, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  rcases h with h | h
  · exact absurd h hne
  · exact h

section
variable {g : List Nat} (hg : CM 9 25 g)
include hg

theorem g_lt : ∀ v ∈ g, v < 306 := fun _ hv => CM_lt hg hv
theorem g_nodup : g.Nodup := CM_nodup hg
theorem g_sep : ∀ v ∈ g, ∀ w ∈ g, v ≠ w → v / 9 ≠ w / 9 ∧ v % 9 ≠ w % 9 :=
  fun v hv w hw hne => cfl_false ((isMatch_iff 9 g).mp hg.2 v hv w hw) hne

theorem holes_nodup : (g.map (· % 9)).Nodup :=
  nodup_map_inj _ g (g_nodup hg) (fun v hv w hw h => by
    apply Classical.byContradiction; intro hne; exact (g_sep hg v hv w hw hne).2 h)

theorem pigeons_nodup : (g.map (· / 9)).Nodup :=
  nodup_map_inj _ g (g_nodup hg) (fun v hv w hw h => by
    apply Classical.byContradiction; intro hne; exact (g_sep hg v hv w hw hne).1 h)

/-- Adding `x` to a matching: a matching iff `x` conflicts with no member. -/
theorem isMatch_cons (x : Nat) : isMatch 9 (x :: g) = true ↔ ∀ w ∈ g, cfl 9 x w = false := by
  have hm := (isMatch_iff 9 g).mp hg.2
  rw [isMatch_iff]
  constructor
  · intro H w hw; exact H x (by simp) w (by simp [hw])
  · intro H v hv w hw
    simp only [List.mem_cons] at hv hw
    rcases hv with rfl | hv <;> rcases hw with rfl | hw
    · simp [cfl]
    · exact H w hw
    · rw [cfl_symm]; exact H v hv
    · exact hm v hv w hw

theorem row_match {i t : Nat} (hi : pfree 9 g i) (ht : t < 9) :
    isMatch 9 (var 9 i t :: g) = true ↔ t ∉ g.map (· % 9) := by
  rw [isMatch_cons hg, List.mem_map]
  have hd := var_div 9 i t ht; have hm := var_mod 9 i t ht
  constructor
  · rintro H ⟨w, hw, hwt⟩
    have := H w hw
    have hne : var 9 i t ≠ w := fun e => hi w hw (by rw [← e, hd])
    exact (cfl_false this hne).2 (by rw [hm, hwt])
  · intro H w hw
    have hne : var 9 i t ≠ w := fun e => hi w hw (by rw [← e, hd])
    have h1 : var 9 i t / 9 ≠ w / 9 := by rw [hd]; exact fun e => hi w hw e.symm
    have h2 : var 9 i t % 9 ≠ w % 9 := by rw [hm]; exact fun e => H ⟨w, hw, e.symm⟩
    simp [cfl, hne, h1, h2]

theorem col_match {j t : Nat} (hj : hfree 9 g j) (hj9 : j < 9) :
    isMatch 9 (var 9 t j :: g) = true ↔ t ∉ g.map (· / 9) := by
  rw [isMatch_cons hg, List.mem_map]
  have hd := var_div 9 t j hj9; have hm := var_mod 9 t j hj9
  constructor
  · rintro H ⟨w, hw, hwt⟩
    have := H w hw
    have hne : var 9 t j ≠ w := fun e => hj w hw (by rw [← e, hm])
    exact (cfl_false this hne).1 (by rw [hd, hwt])
  · intro H w hw
    have hne : var 9 t j ≠ w := fun e => hj w hw (by rw [← e, hm])
    have h2 : var 9 t j % 9 ≠ w % 9 := by rw [hm]; exact fun e => hj w hw e.symm
    have h1 : var 9 t j / 9 ≠ w / 9 := by rw [hd]; exact fun e => H ⟨w, hw, e.symm⟩
    simp [cfl, hne, h1, h2]

end

/-! ## The hash key -/

theorem hkey_lsum : ∀ l : List Nat, (hkey l : Int) = lsum (fun v => (wt (cell v) : Int)) l
  | [] => rfl
  | v :: l => by simp only [hkey, lsum, ← hkey_lsum l]; push_cast; rfl

theorem lsum_canon (φ : Nat → Int) {l : List Nat} (hn : l.Nodup) (hl : ∀ x ∈ l, x < 306) :
    lsum φ (canon 306 l) = lsum φ l := by
  rw [← rsum_mem 306 φ (canon 306 l) (canon_nodup _ _) (fun x hx => ((mem_canon _ _ _).mp hx).2),
    ← rsum_mem 306 φ l hn hl]
  exact rsum_congr 306 _ _ (fun x hx => by simp only [mem_canon, hx, and_true])

theorem hkey_canon {g : List Nat} (hg : CM 9 25 g) {x : Nat} (hx : x < 306) (hxg : x ∉ g) :
    hkey (canon 306 (x :: g)) = wt (cell x) + hkey g := by
  have hn : (x :: g).Nodup := List.nodup_cons.mpr ⟨hxg, g_nodup hg⟩
  have hl : ∀ y ∈ x :: g, y < 306 := by
    intro y hy; simp only [List.mem_cons] at hy; rcases hy with rfl | hy; exact hx; exact g_lt hg y hy
  have := lsum_canon (fun v => (wt (cell v) : Int)) hn hl
  rw [← hkey_lsum, lsum, ← hkey_lsum] at this
  omega

/-! ## Row and column sums of `T` -/

theorem hc_lt (j : Nat) : hc j < 3 := by unfold hc; split <;> (try split) <;> omega
theorem pc_lt (i : Nat) : pc i < 9 := by unfold pc; split <;> omega
theorem cell_lt (v : Nat) : cell v < 27 := by have := hc_lt (v % 9); have := pc_lt (v / 9); unfold cell; omega
theorem cell_div (v : Nat) : cell v / 3 = pc (v / 9) := by have := hc_lt (v % 9); unfold cell; omega
theorem cell_mod (v : Nat) : cell v % 3 = hc (v % 9) := by have := hc_lt (v % 9); unfold cell; omega

theorem rsum9_hc (F : Nat → Int) : rsum 9 (fun t => F (hc t)) = 4 * F 0 + 4 * F 1 + F 2 := by
  simp [rsum, hc]; omega

theorem rsum34_pc (F : Nat → Int) : rsum 34 (fun t => F (pc t)) = rsum 9 (fun a => (Pb a : Int) * F a) := by
  simp [rsum, pc, Pb]; omega

theorem rsum3 (F : Nat → Int) : rsum 3 F = F 0 + F 1 + F 2 := by simp [rsum]

theorem var_lt {i t : Nat} (hi : i < 34) (ht : t < 9) : var 9 i t < 306 := by unfold var; omega

theorem cell_var {i t : Nat} (ht : t < 9) : cell (var 9 i t) = 3 * pc i + hc t := by
  unfold cell; rw [var_div 9 i t ht, var_mod 9 i t ht]

/-- Free row sum of `T` at pigeon `i`. -/
theorem rowS_eval {g : List Nat} (hg : CM 9 25 g) {i : Nat} (hi : i < 34) (hf : pfree 9 g i) :
    rowS 9 25 T g i = 4 * (look (hkey g + wt (3 * pc i)) : Int) + 4 * (look (hkey g + wt (3 * pc i + 1)) : Int)
      + (look (hkey g + wt (3 * pc i + 2)) : Int)
      - lsum (fun v => (look (hkey g + wt (3 * pc i + hc (v % 9))) : Int)) g := by
  have hH := holes_nodup hg
  have hHl : ∀ x ∈ g.map (· % 9), x < 9 := by
    intro x hx; obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx; exact Nat.mod_lt _ (by decide)
  unfold rowS lineS
  rw [rsum_congr 9 _ (fun t => if t ∈ g.map (· % 9) then 0 else (look (hkey g + wt (3 * pc i + hc t)) : Int))
    (fun t ht => by
      by_cases hm : t ∈ g.map (· % 9)
      · have : isMatch 9 (var 9 i t :: g) = false := by
          cases h : isMatch 9 (var 9 i t :: g)
          · rfl
          · exact absurd hm ((row_match hg hf ht).mp h)
        simp only [this, hm, if_true]; rfl
      · have hmt := (row_match hg hf ht).mpr hm
        have hxg : var 9 i t ∉ g := fun hx => hf _ hx (var_div 9 i t ht)
        simp only [hmt, hm, if_true, if_false, T]
        rw [show (9 + 25) * 9 = 306 by rfl, hkey_canon hg (var_lt hi ht) hxg, cell_var ht, Nat.add_comm])]
  rw [rsum_notmem 9 _ _ hH hHl, lsum_map, rsum9_hc (fun d => (look (hkey g + wt (3 * pc i + d)) : Int))]
  simp only [Nat.add_zero]

/-- Free column sum of `T` at hole `j`. -/
theorem colS_eval {g : List Nat} (hg : CM 9 25 g) {j : Nat} (hj : j < 9) (hf : hfree 9 g j) :
    colS 9 25 T g j = rsum 9 (fun a => (Pb a : Int) * (look (hkey g + wt (3 * a + hc j)) : Int))
      - lsum (fun v => (look (hkey g + wt (3 * pc (v / 9) + hc j)) : Int)) g := by
  have hP := pigeons_nodup hg
  have hPl : ∀ x ∈ g.map (· / 9), x < 34 := by
    intro x hx; obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; have := g_lt hg v hv; omega
  unfold colS lineS
  rw [rsum_congr (9 + 25) _ (fun t => if t ∈ g.map (· / 9) then 0 else (look (hkey g + wt (3 * pc t + hc j)) : Int))
    (fun t ht => by
      by_cases hm : t ∈ g.map (· / 9)
      · have : isMatch 9 (var 9 t j :: g) = false := by
          cases h : isMatch 9 (var 9 t j :: g)
          · rfl
          · exact absurd hm ((col_match hg hf hj).mp h)
        simp only [this, hm, if_true]; rfl
      · have hmt := (col_match hg hf hj).mpr hm
        have hxg : var 9 t j ∉ g := fun hx => hf _ hx (var_mod 9 t j hj)
        simp only [hmt, hm, if_true, if_false, T]
        rw [show (9 + 25) * 9 = 306 by rfl, hkey_canon hg (var_lt (by omega) hj) hxg, cell_var hj, Nat.add_comm])]
  rw [show 9 + 25 = 34 by rfl, rsum_notmem 34 _ _ hP hPl, lsum_map,
    rsum34_pc (fun a => (look (hkey g + wt (3 * a + hc j)) : Int))]

/-! ## The count matrix of a matching -/

/-- `#{v ∈ l : cell v = c}`. -/
def cntL : List Nat → Nat → Nat
  | [], _ => 0
  | v :: l, c => (if cell v = c then 1 else 0) + cntL l c

/-- `[f s, f (s+1), ..., f (s+n-1)]`. -/
def mk (f : Nat → Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | s, n + 1 => f s :: mk f (s + 1) n

def mOf (g : List Nat) : List Nat := mk (cntL g) 0 27

/-- `∑_{i<n} φ (s + i)`. -/
def Sm (φ : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | s, n + 1 => φ s + Sm φ (s + 1) n

/-- `∑_{v ∈ l} φ v` in `Nat`. -/
def lsumN (φ : Nat → Nat) : List Nat → Nat
  | [] => 0
  | v :: l => φ v + lsumN φ l

theorem mk_length (f : Nat → Nat) : ∀ s n, (mk f s n).length = n
  | _, 0 => rfl
  | s, n + 1 => by simp [mk, mk_length f (s + 1) n]

theorem sumW_mk (ψ f : Nat → Nat) : ∀ s n, sumW ψ s (mk f s n) = Sm (fun c => f c * ψ c) s n
  | _, 0 => rfl
  | s, n + 1 => by
    simp only [mk, sumW, Sm, sumW_mk ψ f (s + 1) n]
    by_cases h : f s = 0 <;> simp [h]

theorem sum_mk (f : Nat → Nat) : ∀ s n, (mk f s n).sum = Sm f s n
  | _, 0 => rfl
  | s, n + 1 => by simp [mk, Sm, sum_mk f (s + 1) n]

theorem Sm_add (φ ψ : Nat → Nat) : ∀ s n, Sm (fun c => φ c + ψ c) s n = Sm φ s n + Sm ψ s n
  | _, 0 => rfl
  | s, n + 1 => by simp only [Sm, Sm_add φ ψ (s + 1) n]; omega

theorem Sm_zero (s n : Nat) : Sm (fun _ => 0) s n = 0 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [Sm, ih]

theorem Sm_single (ψ : Nat → Nat) (x : Nat) : ∀ s n, s ≤ x → x < s + n →
    Sm (fun c => if x = c then ψ c else 0) s n = ψ x
  | _, 0, h1, h2 => by omega
  | s, n + 1, h1, h2 => by
    simp only [Sm]
    by_cases hx : x = s
    · subst hx
      have : Sm (fun c => if x = c then ψ c else 0) (x + 1) n = 0 := by
        have := Sm_congr_zero x n
        exact this
      simp [this]
    · rw [if_neg hx, Sm_single ψ x (s + 1) n (by omega) (by omega)]; omega
where
  Sm_congr_zero (x : Nat) : ∀ n, Sm (fun c => if x = c then ψ c else 0) (x + 1) n = 0 := by
    intro n
    suffices ∀ s, x < s → Sm (fun c => if x = c then ψ c else 0) s n = 0 from this (x + 1) (by omega)
    induction n with
    | zero => intro s _; rfl
    | succ n ih => intro s hs; simp only [Sm]; rw [if_neg (by omega), ih (s + 1) (by omega)]

theorem cnt_Sm (ψ : Nat → Nat) : ∀ l : List Nat,
    Sm (fun c => cntL l c * ψ c) 0 27 = lsumN (fun v => ψ (cell v)) l
  | [] => by simp only [cntL, Nat.zero_mul]; exact Sm_zero 0 27
  | v :: l => by
    have e1 : (fun c => cntL (v :: l) c * ψ c) = (fun c => (if cell v = c then ψ c else 0) + cntL l c * ψ c) := by
      funext c; simp only [cntL, Nat.add_mul]; by_cases h : cell v = c <;> simp [h]
    have e2 := Sm_single ψ (cell v) 0 27 (Nat.zero_le _) (by have := cell_lt v; omega)
    have e3 := cnt_Sm ψ l
    rw [e1, Sm_add, e2, e3]; rfl

theorem lsumN_cast (φ : Nat → Nat) : ∀ l : List Nat, (lsumN φ l : Int) = lsum (fun v => (φ v : Int)) l
  | [] => rfl
  | v :: l => by simp only [lsumN, lsum, ← lsumN_cast φ l]; push_cast; rfl

theorem hkey_lsumN : ∀ l : List Nat, hkey l = lsumN (fun v => wt (cell v)) l
  | [] => rfl
  | v :: l => by simp only [hkey, lsumN, hkey_lsumN l]

theorem rows_mk (f : Nat → Nat) (a : Nat) (ha : a < 9) :
    (rowsOf (mk f 0 27)).getD a 0 = Sm (fun c => f c * (if c / 3 = a then 1 else 0)) 0 27 := by
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mk, rowsOf, Sm] <;> omega

theorem cols_mk (f : Nat → Nat) (d : Nat) (hd : d < 3) :
    (colsOf (mk f 0 27) 0 0 0).getD d 0 = Sm (fun c => f c * (if c % 3 = d then 1 else 0)) 0 27 := by
  rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl <;> simp [mk, colsOf, Sm] <;> omega

theorem rows_len (f : Nat → Nat) : (rowsOf (mk f 0 27)).length = 9 := by simp [mk, rowsOf]


/-! ## Specifications of the kernel check -/

theorem enum_spec : ∀ c b acc, enum c b acc = true →
    ∀ r : List Nat, r.length = c → r.sum ≤ b → okM (r.reverse ++ acc) = true
  | 0, _, acc, h, r, hr, _ => by
    rw [List.length_eq_zero_iff] at hr; subst hr; exact h
  | c + 1, b, acc, h, r, hr, hs => by
    match r, hr with
    | v :: r, hr =>
      simp only [enum, List.all_eq_true, List.mem_range] at h
      simp only [List.sum_cons] at hs
      have := enum_spec c (b - v) (v :: acc) (h v (by omega)) r (by simpa using hr) (by omega)
      simpa [List.reverse_cons, List.append_assoc] using this

theorem rsum_succ' (f : Nat → Int) : ∀ n, rsum (n + 1) f = f 0 + rsum n (fun a => f (a + 1))
  | 0 => by simp [rsum]
  | n + 1 => by
    rw [rsum, rsum_succ' f n, rsum]; omega

theorem getD3 (u0 u1 u2 : Nat) (U : List Nat) (a k : Nat) :
    (u0 :: u1 :: u2 :: U).getD (3 * (a + 1) + k) 0 = U.getD (3 * a + k) 0 := by
  rw [show 3 * (a + 1) + k = 3 * a + k + 1 + 1 + 1 by omega]; simp only [List.getD_cons_succ]

theorem rowsEq_spec (C0 C1 C2 L : Nat) : ∀ (R : List Nat) (s : Nat) (U : List Nat),
    rowsEq C0 C1 C2 L R s U = true → U.length = 3 * R.length → ∀ a < R.length, R.getD a 0 < Pb (s + a) →
    (4 * U.getD (3 * a) 0 + 4 * U.getD (3 * a + 1) 0 + U.getD (3 * a + 2) 0) % 5 =
      (C0 * U.getD (3 * a) 0 + C1 * U.getD (3 * a + 1) 0 + C2 * U.getD (3 * a + 2) 0 + L) % 5
  | [], _, _, _, _, a, ha, _ => absurd ha (Nat.not_lt_zero _)
  | r :: R, s, U, h, hl, a, ha, hr => by
    match U, hl with
    | u0 :: u1 :: u2 :: U, hl =>
      simp only [rowsEq, Bool.and_eq_true] at h
      cases a with
      | zero =>
        simp only [List.getD_cons_zero, Nat.add_zero] at hr
        simpa [hr] using h.1
      | succ a =>
        simp only [List.getD_cons_succ] at hr
        have := rowsEq_spec C0 C1 C2 L R (s + 1) U h.2 (by simp at hl; omega) a (by simp at ha; omega)
          (by rw [show s + 1 + a = s + (a + 1) by omega]; exact hr)
        have e0 := getD3 u0 u1 u2 U a 0
        have e1 := getD3 u0 u1 u2 U a 1
        have e2 := getD3 u0 u1 u2 U a 2
        simp only [Nat.add_zero] at e0 this
        rw [e0, e1, e2]; exact this

theorem sel_getD (d u0 u1 u2 : Nat) (U : List Nat) (hd : d < 3) :
    sel d u0 u1 u2 = (u0 :: u1 :: u2 :: U).getD d 0 := by
  rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl <;> rfl

theorem pS_spec (d : Nat) (hd : d < 3) : ∀ (n s : Nat) (U : List Nat), U.length = 3 * n →
    (pS d s U : Int) = rsum n (fun a => (Pb (s + a) : Int) * (U.getD (3 * a + d) 0 : Int))
  | 0, s, U, hl => by
    match U, hl with
    | [], _ => simp [pS, rsum]
  | n + 1, s, U, hl => by
    match U, hl with
    | u0 :: u1 :: u2 :: U, hl =>
      rw [rsum_succ', pS, sel_getD d u0 u1 u2 U hd]
      push_cast
      rw [pS_spec d hd n (s + 1) U (by simp at hl; omega)]
      congr 1
      · simp
      · apply rsum_congr; intro a _
        rw [show s + 1 + a = s + (a + 1) by omega, getD3]

theorem qS_spec (d : Nat) (hd : d < 3) : ∀ (R U : List Nat), U.length = 3 * R.length →
    (qS d R U : Int) = rsum R.length (fun a => (R.getD a 0 : Int) * (U.getD (3 * a + d) 0 : Int))
  | [], U, hl => by simp [qS, rsum]
  | r :: R, U, hl => by
    match U, hl with
    | u0 :: u1 :: u2 :: U, hl =>
      rw [List.length_cons, rsum_succ', qS, sel_getD d u0 u1 u2 U hd]
      push_cast
      rw [qS_spec d hd R U (by simp at hl; omega)]
      congr 1
      · simp
      · apply rsum_congr; intro a _
        rw [getD3]; simp only [List.getD_cons_succ]

/-! ## Assembly -/

theorem Pb_count : ∀ a < 9, rsum 34 (fun x => if pc x = a then (1 : Int) else 0) = Pb a := by decide
theorem Hb_count : ∀ d < 3, rsum 9 (fun x => if hc x = d then (1 : Int) else 0) = Hb d := by decide

section
variable {g : List Nat} (hg : CM 9 25 g)
include hg

/-- Row counts of `mOf g`, as class counts of `g`. -/
theorem rowc (a : Nat) (ha : a < 9) :
    ((rowsOf (mOf g)).getD a 0 : Int) = lsum (fun x => if pc x = a then 1 else 0) (g.map (· / 9)) := by
  rw [mOf, rows_mk _ a ha, cnt_Sm, lsumN_cast, lsum_map]
  apply lsum_congr; intro v _; rw [cell_div]; by_cases h : pc (v / 9) = a <;> simp [h]

theorem colc (d : Nat) (hd : d < 3) :
    ((colsOf (mOf g) 0 0 0).getD d 0 : Int) = lsum (fun x => if hc x = d then 1 else 0) (g.map (· % 9)) := by
  rw [mOf, cols_mk _ d hd, cnt_Sm, lsumN_cast, lsum_map]
  apply lsum_congr; intro v _; rw [cell_mod]; by_cases h : hc (v % 9) = d <;> simp [h]

theorem row_le (a : Nat) (ha : a < 9) : (rowsOf (mOf g)).getD a 0 ≤ Pb a := by
  have h1 := rowc hg a ha
  have h2 := lsum_le 34 (fun x => if pc x = a then 1 else 0) (fun x => by by_cases h : pc x = a <;> simp [h])
    _ (pigeons_nodup hg) (fun x hx => by obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; have := g_lt hg v hv; omega)
  rw [Pb_count a ha] at h2; omega

theorem col_le (d : Nat) (hd : d < 3) : (colsOf (mOf g) 0 0 0).getD d 0 ≤ Hb d := by
  have h1 := colc hg d hd
  have h2 := lsum_le 9 (fun x => if hc x = d then 1 else 0) (fun x => by by_cases h : hc x = d <;> simp [h])
    _ (holes_nodup hg) (fun x hx => by obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx; exact Nat.mod_lt _ (by decide))
  rw [Hb_count d hd] at h2; omega

theorem row_lt {i : Nat} (hi : i < 34) (hf : pfree 9 g i) : (rowsOf (mOf g)).getD (pc i) 0 < Pb (pc i) := by
  have h1 := rowc hg (pc i) (pc_lt i)
  have h2 := lsum_le_free 34 (fun x => if pc x = pc i then 1 else 0) (fun x => by by_cases h : pc x = pc i <;> simp [h])
    _ (pigeons_nodup hg) (fun x hx => by obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; have := g_lt hg v hv; omega)
    i hi (fun hx => by obtain ⟨v, hv, e⟩ := List.mem_map.mp hx; exact hf v hv e)
  rw [Pb_count _ (pc_lt i)] at h2; simp at h2; omega

theorem col_lt {j : Nat} (hj : j < 9) (hf : hfree 9 g j) : (colsOf (mOf g) 0 0 0).getD (hc j) 0 < Hb (hc j) := by
  have h1 := colc hg (hc j) (hc_lt j)
  have h2 := lsum_le_free 9 (fun x => if hc x = hc j then 1 else 0) (fun x => by by_cases h : hc x = hc j <;> simp [h])
    _ (holes_nodup hg) (fun x hx => by obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx; exact Nat.mod_lt _ (by decide))
    j hj (fun hx => by obtain ⟨v, hv, e⟩ := List.mem_map.mp hx; exact hf v hv e)
  rw [Hb_count _ (hc_lt j)] at h2; simp at h2; omega

theorem key_mOf : sumW wt 0 (mOf g) = hkey g := by
  rw [mOf, sumW_mk, cnt_Sm, hkey_lsumN]

end

theorem U_getD (h c : Nat) (hc : c < 27) :
    ((List.range 27).map fun c => look (h + wt c)).getD c 0 = look (h + wt c) := by
  simp [List.getD_eq_getElem?_getD, hc]

theorem lsumN_one : ∀ l : List Nat, lsumN (fun _ => 1) l = l.length
  | [] => rfl
  | _ :: l => by simp only [lsumN, lsumN_one l, List.length_cons]; omega

theorem U_len (h : Nat) : ((List.range 27).map fun c => look (h + wt c)).length = 3 * 9 := by simp

/-- **The reduced equations imply `Bal`.** If the kernel check `enum 27 4 []` passes, `T` is
balanced against itself at every level `e ≤ 4`. -/
theorem bal_of_enum (H : enum 27 4 [] = true) (e : Nat) (he : e ≤ 4) : Bal 5 9 25 T T e := by
  intro g hg hl
  have hok : okM (mOf g) = true := by
    have := enum_spec 27 4 [] H (mOf g).reverse (by simp [mOf, mk_length]) (by
      rw [List.sum_reverse, mOf, sum_mk]
      have := cnt_Sm (fun _ => 1) g
      simp only [Nat.mul_one] at this
      rw [this, lsumN_one]; omega)
    simpa using this
  have hguard : guard (rowsOf (mOf g)) (colsOf (mOf g) 0 0 0) = true := by
    simp only [guard, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
    exact ⟨fun a ha => row_le hg a ha, fun d hd => col_le hg d hd⟩
  simp only [okM, forceL_eq, withN_eq, hguard, Bool.not_true, Bool.false_or, key_mOf hg, eqs,
    Bool.and_eq_true, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hrows, hcols⟩ := hok
  have hRl : (rowsOf (mOf g)).length = 9 := rows_len _
  refine ⟨fun i hi hf => ?_, fun j hj hf => ?_⟩
  · -- free pigeon `i` of class `a`
    have ha := pc_lt i
    have hr := rowsEq_spec _ _ _ _ _ 0 ((List.range 27).map fun c => look (hkey g + wt c)) hrows (by rw [hRl]; exact U_len (hkey g)) (pc i) (by omega)
      (by rw [Nat.zero_add]; exact row_lt hg hi hf)
    rw [U_getD (hkey g) _ (by omega), U_getD (hkey g) _ (by omega), U_getD (hkey g) _ (by omega)] at hr
    rw [rowS_eval hg hi hf,
      lsum_group 3 (fun v => hc (v % 9)) (fun d => (look ((hkey g) + wt (3 * pc i + d)) : Int)) g (fun v _ => hc_lt _),
      rsum3]
    have c0 := colc hg 0 (by decide); have c1 := colc hg 1 (by decide); have c2 := colc hg 2 (by decide)
    rw [lsum_map] at c0 c1 c2
    rw [← c0, ← c1, ← c2]
    simp only [T, Nat.add_zero] at hr ⊢
    generalize (colsOf (mOf g) 0 0 0).getD 0 0 = C0 at hr ⊢
    generalize (colsOf (mOf g) 0 0 0).getD 1 0 = C1 at hr ⊢
    generalize (colsOf (mOf g) 0 0 0).getD 2 0 = C2 at hr ⊢
    generalize look ((hkey g) + wt (3 * pc i)) = u0 at hr ⊢
    generalize look ((hkey g) + wt (3 * pc i + 1)) = u1 at hr ⊢
    generalize look ((hkey g) + wt (3 * pc i + 2)) = u2 at hr ⊢
    generalize look (hkey g) = L at hr ⊢
    have e0 : ((C0 * u0 : Nat) : Int) = (C0 : Int) * (u0 : Int) := by push_cast; rfl
    have e1 : ((C1 * u1 : Nat) : Int) = (C1 : Int) * (u1 : Int) := by push_cast; rfl
    have e2 : ((C2 * u2 : Nat) : Int) = (C2 : Int) * (u2 : Int) := by push_cast; rfl
    omega
  · -- free hole `j` of class `d`
    have hd := hc_lt j
    have hcc := hcols (hc j) hd
    simp only [col_lt hg hj hf, decide_true, Bool.not_true, Bool.false_or, beq_iff_eq] at hcc
    have hp := pS_spec (hc j) hd 9 0 ((List.range 27).map fun c => look (hkey g + wt c)) (U_len (hkey g))
    have hq := qS_spec (hc j) hd (rowsOf (mOf g)) ((List.range 27).map fun c => look (hkey g + wt c)) (by rw [hRl]; exact U_len (hkey g))
    rw [hRl] at hq
    rw [colS_eval hg hj hf,
      lsum_group 9 (fun v => pc (v / 9)) (fun a => (look ((hkey g) + wt (3 * a + hc j)) : Int)) g (fun v _ => pc_lt _)]
    have e1 : rsum 9 (fun a => (Pb a : Int) * (look ((hkey g) + wt (3 * a + hc j)) : Int)) = (pS (hc j) 0 ((List.range 27).map fun c => look (hkey g + wt c)) : Int) := by
      rw [hp]; apply rsum_congr; intro a ha; rw [Nat.zero_add, U_getD (hkey g) _ (by omega)]
    have e2 : rsum 9 (fun a => lsum (fun v => if pc (v / 9) = a then 1 else 0) g * (look ((hkey g) + wt (3 * a + hc j)) : Int))
        = (qS (hc j) (rowsOf (mOf g)) ((List.range 27).map fun c => look (hkey g + wt c)) : Int) := by
      rw [hq]; apply rsum_congr; intro a ha
      rw [U_getD (hkey g) _ (by omega), rowc hg a ha, lsum_map]
    rw [e1, e2]
    simp only [T]
    omega

end Programme.«20261027-0607-proof-complexity».P5
