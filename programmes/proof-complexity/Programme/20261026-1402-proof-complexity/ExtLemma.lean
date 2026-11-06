import Programme.«20261025-1627-proof-complexity».OntoExt3

/-!
# Two-level extension property EXT implies no low-degree PC refutation of onto-FPHP

Matching coordinates: a set of variables of `ontoFPHP n k` is a canonical list `g`
(`canon ((n+k)*n) g = g`, decreasing); it is a matching if no two members share a pigeon
(`v / n`) or a hole (`v % n`). For `f : List Nat → Int` and a canonical matching `g`, the row sum
at pigeon `i` is `∑_j f(g + x_{ij})` over the `j` with `g + x_{ij}` a matching (`rowS`), the
column sum at hole `j` likewise (`colS`). `Bal p n k f c e`: at every canonical `e`-matching `g`,
every free row sum and every free column sum is `≡ c g` mod `p`.

`EXT p n k d` (th's `EXT_p(n,k,d+1)`, P49): every `f` that is balanced against some `c` at
level `d-1` (no condition when `d = 0`) has a `y` balanced against `f` at level `d`.

`no_refutation_of_ext`: for `p > 1`, `n > 0`, `D ≥ 1`, if `EXT p n k d` for every `d < D`,
then `ontoFPHP n k` has no degree-`D` `PPCRefutation p`. Proof: a degree-`d` design `F` gives
`f = c = (t ↦ F(x_t))`, balanced at level `d-1` by its pigeon and hole equations; EXT gives `y`;
the moment functional with values `F` below level `d+1` and `y` on `(d+1)`-matchings (`0` on
non-matchings) is a degree-`(d+1)` design extending `F`. Iterate from the degree-0 design `1`
and apply `DesignExt.ext_sound`. No hypothesis on `k` is needed.
-/

namespace Programme.«20261026-1402-proof-complexity».ExtLemma

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero prod2_eval mem_ontoFPHP
  mem_collAx mem_funcAx var_div var_mod prod2_deg mem_pig mem_hole mem_coll mem_func)
open Programme.«20261025-1627-proof-complexity».DesignExt
open Programme.«20261025-1627-proof-complexity».OntoExt2 (SN rsum_dvd rsum_pick var_lt var_decode
  sumOne_deg_pos not_dvd_one)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261025-1627-proof-complexity».OntoExt3 (mono_split rsum_sub' Fn_sub Fn_rsum rsum_pick_dvd)

/-- `v ≠ w` share a pigeon or a hole. -/
def cfl (n v w : Nat) : Bool := v != w && (v / n == w / n || v % n == w % n)

/-- No two members of `l` conflict. -/
def isMatch (n : Nat) (l : List Nat) : Bool := l.all fun v => l.all fun w => !cfl n v w

/-- Pigeon `i` is free in `g`. -/
def pfree (n : Nat) (g : List Nat) (i : Nat) : Prop := ∀ v ∈ g, v / n ≠ i
/-- Hole `j` is free in `g`. -/
def hfree (n : Nat) (g : List Nat) (j : Nat) : Prop := ∀ v ∈ g, v % n ≠ j

/-- Canonical matching. -/
def CM (n k : Nat) (g : List Nat) : Prop := canon ((n + k) * n) g = g ∧ isMatch n g = true

/-- `∑_{t<M} f(g + v_t)` over the `t` with `g + v_t` a matching. -/
def lineS (n k : Nat) (f : List Nat → Int) (g : List Nat) (v : Nat → Nat) (M : Nat) : Int :=
  rsum M (fun t => if isMatch n (v t :: g) then f (canon ((n + k) * n) (v t :: g)) else 0)

/-- Row sum at pigeon `i`. -/
def rowS (n k : Nat) (f : List Nat → Int) (g : List Nat) (i : Nat) : Int := lineS n k f g (fun j => var n i j) n
/-- Column sum at hole `j`. -/
def colS (n k : Nat) (f : List Nat → Int) (g : List Nat) (j : Nat) : Int :=
  lineS n k f g (fun i => var n i j) (n + k)

/-- At every canonical `e`-matching `g`, free row and column sums of `f` are `≡ c g` mod `p`. -/
def Bal (p n k : Nat) (f c : List Nat → Int) (e : Nat) : Prop :=
  ∀ g, CM n k g → g.length = e →
    (∀ i < n + k, pfree n g i → (p : Int) ∣ rowS n k f g i - c g) ∧
    (∀ j < n, hfree n g j → (p : Int) ∣ colS n k f g j - c g)

/-- **Two-level extension** `EXT_p(n,k,d+1)`. -/
def EXT (p n k d : Nat) : Prop :=
  ∀ f c : List Nat → Int, (∀ e, e + 1 = d → Bal p n k f c e) → ∃ y : List Nat → Int, Bal p n k y f d

/-! ## Matchings -/

theorem isMatch_iff (n : Nat) (l : List Nat) :
    isMatch n l = true ↔ ∀ v ∈ l, ∀ w ∈ l, cfl n v w = false := by
  simp [isMatch, List.all_eq_true]

theorem isMatch_congr (n : Nat) (l l' : List Nat) (h : ∀ x, x ∈ l ↔ x ∈ l') : isMatch n l = isMatch n l' := by
  apply Bool.eq_iff_iff.mpr
  rw [isMatch_iff, isMatch_iff]
  constructor
  · intro H v hv w hw; exact H v ((h v).mpr hv) w ((h w).mpr hw)
  · intro H v hv w hw; exact H v ((h v).mp hv) w ((h w).mp hw)

theorem not_match {n : Nat} {l : List Nat} (h : isMatch n l = false) :
    ∃ u ∈ l, ∃ w ∈ l, cfl n u w = true := by
  apply Classical.byContradiction; intro H
  have : isMatch n l = true := (isMatch_iff n l).mpr (fun v hv w hw => by
    cases hc : cfl n v w
    · rfl
    · exact absurd ⟨v, hv, w, hw, hc⟩ H)
  rw [this] at h; cases h

theorem cfl_symm (n v w : Nat) : cfl n v w = cfl n w v := by
  unfold cfl
  cases h1 : (v == w) <;> cases h2 : (w == v) <;> simp_all [bne] <;> grind

/-- A conflicting pair is an axiom of `ontoFPHP n k`. -/
theorem conf_ax {n k u w : Nat} (hn : 0 < n) (hu : u < (n + k) * n) (hw : w < (n + k) * n)
    (h : cfl n u w = true) : ∃ P ∈ ontoFPHP n k, P.deg = 2 ∧ ∀ a, P.eval a = xv u a * xv w a := by
  have key : ∀ x y : Nat, x < (n + k) * n → y < (n + k) * n → cfl n x y = true → x < y →
      ∃ P ∈ ontoFPHP n k, P.deg = 2 ∧ ∀ a, P.eval a = xv x a * xv y a := by
    intro x y hx hy hc hlt
    have hax : x / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hx
    have hay : y / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hy
    have hbx : x % n < n := Nat.mod_lt _ hn
    have hby : y % n < n := Nat.mod_lt _ hn
    have ex := var_decode n x; have ey := var_decode n y
    unfold var at ex ey
    simp only [cfl, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq] at hc
    obtain ⟨hxy, hc⟩ := hc
    rcases hc with hc | hc
    · have hb : x % n < y % n := by
        rcases Nat.lt_or_ge (x % n) (y % n) with h | h
        · exact h
        · exfalso; rw [hc] at ex; omega
      refine ⟨_, mem_func (mem_funcAx.mpr ⟨x / n, x % n, y % n, hax, hbx, hby, hb, rfl⟩), prod2_deg _ _, ?_⟩
      intro a; rw [prod2_eval]
      have e1 : var n (x / n) (x % n) = x := by unfold var; omega
      have e2 : var n (x / n) (y % n) = y := by unfold var; rw [hc]; omega
      rw [e1, e2]
    · have ha : x / n < y / n := by
        rcases Nat.lt_or_ge (x / n) (y / n) with h | h
        · exact h
        · exfalso
          rcases Nat.lt_or_ge (y / n) (x / n) with h' | h'
          · have : (y / n + 1) * n ≤ x / n * n := Nat.mul_le_mul_right _ h'
            rw [Nat.succ_mul] at this; omega
          · have : x / n = y / n := by omega
            apply hxy; rw [← ex, ← ey, this, hc]
      refine ⟨_, mem_coll (mem_collAx.mpr ⟨x % n, x / n, y / n, hbx, hax, hay, ha, rfl⟩), prod2_deg _ _, ?_⟩
      intro a; rw [prod2_eval]
      have e1 : var n (x / n) (x % n) = x := by unfold var; omega
      have e2 : var n (y / n) (x % n) = y := by unfold var; rw [hc]; omega
      rw [e1, e2]
  have hne : u ≠ w := by
    intro e; subst e; simp [cfl] at h
  rcases Nat.lt_or_ge u w with hl | hl
  · exact key u w hu hw h hl
  · obtain ⟨P, hP, hd, he⟩ := key w u hw hu (by rw [cfl_symm]; exact h) (by omega)
    exact ⟨P, hP, hd, fun a => by rw [he, Int.mul_comm]⟩


/-! ## Generic facts about functionals on `SN N` -/

section
variable {p n k : Nat}

theorem monoEval_append (a : Nat → Bool) (l1 l2 : List Nat) :
    monoEval a (l1 ++ l2) = monoEval a l1 * monoEval a l2 := by
  simp [monoEval, List.map_append, List.prod_append]

theorem Fm_congr {S : (Nat → Bool) → Prop} (F : Fn p S) (xs ys : List Nat) (h : ∀ x, x ∈ xs ↔ x ∈ ys) :
    F.E (fun a => monoEval a xs) = F.E (fun a => monoEval a ys) := by
  congr 1; funext a; exact monoEval_congr a xs ys h

theorem vanish {N : Nat} (F : Fn p (SN N)) (xs : List Nat) (x : Nat) (hx : x ∈ xs) (hxN : N ≤ x)
    (h : (Nat → Bool) → Int) : (p : Int) ∣ F.E (fun a => monoEval a xs * h a) := by
  rw [F.supp _ (fun _ => 0) (fun a ha => by rw [monoEval_zero ha xs x hx hxN, Int.zero_mul])]
  exact F.zero

theorem vanish0 {N : Nat} (F : Fn p (SN N)) (xs : List Nat) (x : Nat) (hx : x ∈ xs) (hxN : N ≤ x) :
    (p : Int) ∣ F.E (fun a => monoEval a xs) := by
  rw [F.supp _ (fun _ => 0) (fun a ha => monoEval_zero ha xs x hx hxN)]
  exact F.zero

theorem all_lt_or {N : Nat} (xs : List Nat) : (∀ x ∈ xs, x < N) ∨ ∃ x ∈ xs, N ≤ x := by
  by_cases h : ∃ x ∈ xs, N ≤ x
  · exact Or.inr h
  · exact Or.inl (fun x hx => by
      apply Classical.byContradiction; intro h'; exact h ⟨x, hx, by omega⟩)

theorem mem_canon' {N : Nat} {xs : List Nat} (hx : ∀ x ∈ xs, x < N) (x : Nat) : x ∈ canon N xs ↔ x ∈ xs := by
  rw [mem_canon]; constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, hx x h⟩

theorem canon_len_eq {N : Nat} {l : List Nat} (hl : l.Nodup) (hx : ∀ x ∈ l, x < N) :
    (canon N l).length = l.length := by
  have h1 := canon_length_le N l
  have h2 := nodup_len l (canon N l) hl (fun x h => (mem_canon' hx x).mpr h)
  omega

theorem canon_idem {N : Nat} (xs : List Nat) : canon N (canon N xs) = canon N xs :=
  canon_congr N _ _ (fun x hxN => by rw [mem_canon]; constructor <;> intro h <;> (try exact h.1) <;> exact ⟨h, hxN⟩)

theorem CM_lt {g : List Nat} (hg : CM n k g) {x : Nat} (hx : x ∈ g) : x < (n + k) * n := by
  rw [← hg.1] at hx; exact ((mem_canon _ _ _).mp hx).2

theorem CM_nodup {g : List Nat} (hg : CM n k g) : g.Nodup := by
  rw [← hg.1]; exact canon_nodup _ _

/-- A degree-`d` design kills monomials of length `≤ d` with a conflicting pair. -/
theorem kill (hn : 0 < n) {d : Nat} (F : Fn p (SN ((n + k) * n))) (hF : IsDesign (ontoFPHP n k) d F)
    (xs : List Nat) (hl : xs.length ≤ d) (u : Nat) (hu : u ∈ xs) (w : Nat) (hw : w ∈ xs)
    (hc : cfl n u w = true) : (p : Int) ∣ F.E (fun a => monoEval a xs) := by
  rcases all_lt_or (N := (n + k) * n) xs with hx | ⟨x, hx, hxN⟩
  case inr => exact vanish0 F xs x hx hxN
  have huw : u ≠ w := by intro e; subst e; simp [cfl] at hc
  obtain ⟨P, hP, hPd, hPe⟩ := conf_ax (k := k) hn (hx u hu) (hx w hw) hc
  obtain ⟨s, hsd⟩ : ∃ s, s = canon ((n + k) * n) xs := ⟨_, rfl⟩
  have hs : s.Nodup := hsd ▸ canon_nodup _ _
  have hms : ∀ x, x ∈ s ↔ x ∈ xs := hsd ▸ mem_canon' hx
  have hsl : s.length ≤ xs.length := hsd ▸ canon_length_le ((n + k) * n) xs
  have hus : u ∈ s := (hms u).mpr hu
  have hws : w ∈ s.erase u := (List.Nodup.mem_erase_iff hs).mpr ⟨fun e => huw e.symm, (hms w).mpr hw⟩
  obtain ⟨r, hrd⟩ : ∃ r, r = (s.erase u).erase w := ⟨_, rfl⟩
  have hr : ∀ x, x ∈ r ↔ x ≠ w ∧ x ≠ u ∧ x ∈ s := by
    intro x
    rw [hrd, List.Nodup.mem_erase_iff (List.Nodup.erase u hs), List.Nodup.mem_erase_iff hs]
  have hrl : r.length + 2 ≤ d := by
    have e1 := List.length_erase_of_mem hws
    have e2 := List.length_erase_of_mem hus
    have : 0 < s.length := List.length_pos_of_mem hus
    have : 0 < (s.erase u).length := List.length_pos_of_mem hws
    rw [hrd]
    omega
  have := hF P hP r (by rw [hPd]; exact hrl)
  have e : (fun a => monoEval a r * P.eval a) = fun a => monoEval a xs := by
    funext a
    rw [hPe, monoEval_congr a xs (r ++ [u, w]) (fun x => by
      rw [List.mem_append, hr, ← hms]; simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · intro h; by_cases h1 : x = w; · exact Or.inr (Or.inr h1)
        by_cases h2 : x = u; · exact Or.inr (Or.inl h2)
        exact Or.inl ⟨h1, h2, h⟩
      · rintro (⟨_, _, h⟩ | rfl | rfl); exact h; exact hus; exact (List.mem_of_mem_erase hws)),
      monoEval_append]
    simp [monoEval, xv]
  rwa [e] at this

/-- `F(x_g · (∑_t x_{v_t} - 1)) ≡ ∑_t F(x_{g + v_t}) - F(x_g)`. -/
theorem rowId {S : (Nat → Bool) → Prop} (F : Fn p S) (g : List Nat) (v : Nat → Nat) (M : Nat) :
    (p : Int) ∣ F.E (fun a => monoEval a g * (sumOne v M).eval a) -
      (rsum M (fun t => F.E (fun a => monoEval a (g ++ [v t]))) - F.E (fun a => monoEval a g)) := by
  have e : (fun a => monoEval a g * (sumOne v M).eval a) =
      fun a => rsum M (fun t => monoEval a (g ++ [v t])) - monoEval a g := by
    funext a; exact mono_split g v M a
  rw [e]
  have h1 := Fn_sub F (fun a => rsum M (fun t => monoEval a (g ++ [v t]))) (fun a => monoEval a g)
  have h2 := Fn_rsum F M (fun t a => monoEval a (g ++ [v t]))
  have := Int.dvd_add h1 h2
  refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp this
  exact ⟨0, by omega⟩

/-- Termwise: the sum `∑_t F(x_{g + v_t})` is the line sum of `V`. -/
theorem termsum {F : Fn p (SN ((n + k) * n))} {V : List Nat → Int} {L : Nat}
    (hK : ∀ xs : List Nat, xs.length ≤ L + 1 → ∀ u ∈ xs, ∀ w ∈ xs, cfl n u w = true →
      (p : Int) ∣ F.E (fun a => monoEval a xs))
    (hV : ∀ xs : List Nat, (∀ x ∈ xs, x < (n + k) * n) → isMatch n xs = true →
      (canon ((n + k) * n) xs).length = L + 1 → F.E (fun a => monoEval a xs) = V (canon ((n + k) * n) xs))
    {g : List Nat} (hg : CM n k g) (hgl : g.length = L) (v : Nat → Nat) (M : Nat)
    (hvN : ∀ t < M, v t < (n + k) * n) (hvg : ∀ t < M, v t ∉ g) :
    (p : Int) ∣ rsum M (fun t => F.E (fun a => monoEval a (g ++ [v t]))) - lineS n k V g v M := by
  unfold lineS
  rw [← rsum_sub']
  apply rsum_dvd
  intro t ht
  have hmem : ∀ x, x ∈ g ++ [v t] ↔ x ∈ v t :: g := fun x => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; exact or_comm
  cases hm : isMatch n (v t :: g)
  · obtain ⟨u, hu, w, hw, hc⟩ := not_match hm
    rw [if_neg (by simp), Int.sub_zero]
    exact hK _ (by simp; omega) u ((hmem u).mpr hu) w ((hmem w).mpr hw) hc
  · rw [if_pos rfl, Fm_congr F _ _ hmem]
    have hall : ∀ x ∈ v t :: g, x < (n + k) * n := by
      intro x hx; simp only [List.mem_cons] at hx
      rcases hx with rfl | hx; exact hvN t ht; exact CM_lt hg hx
    rw [hV _ hall hm (by rw [canon_len_eq (List.nodup_cons.mpr ⟨hvg t ht, CM_nodup hg⟩) hall]; simp; omega)]
    exact ⟨0, by simp⟩

theorem line_bal {F : Fn p (SN ((n + k) * n))} {V : List Nat → Int} {L : Nat}
    (hK : ∀ xs : List Nat, xs.length ≤ L + 1 → ∀ u ∈ xs, ∀ w ∈ xs, cfl n u w = true →
      (p : Int) ∣ F.E (fun a => monoEval a xs))
    (hV : ∀ xs : List Nat, (∀ x ∈ xs, x < (n + k) * n) → isMatch n xs = true →
      (canon ((n + k) * n) xs).length = L + 1 → F.E (fun a => monoEval a xs) = V (canon ((n + k) * n) xs))
    {g : List Nat} (hg : CM n k g) (hgl : g.length = L) (v : Nat → Nat) (M : Nat)
    (hvN : ∀ t < M, v t < (n + k) * n) (hvg : ∀ t < M, v t ∉ g) :
    (p : Int) ∣ F.E (fun a => monoEval a g * (sumOne v M).eval a) -
      (lineS n k V g v M - F.E (fun a => monoEval a g)) := by
  have h1 := rowId F g v M
  have h2 := termsum hK hV hg hgl v M hvN hvg
  have := Int.dvd_add h1 h2
  refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp this
  exact ⟨0, by omega⟩

/-- Occupied line: the line meets `g` at `v t0`. -/
theorem line_occ {S : (Nat → Bool) → Prop} {F : Fn p S} {g : List Nat}
    (hK : ∀ xs : List Nat, xs.length ≤ g.length + 1 → ∀ u ∈ xs, ∀ w ∈ xs, cfl n u w = true →
      (p : Int) ∣ F.E (fun a => monoEval a xs))
    (v : Nat → Nat) (M t0 : Nat) (ht0 : t0 < M) (hg0 : v t0 ∈ g)
    (hvc : ∀ t < M, t ≠ t0 → cfl n (v t) (v t0) = true) :
    (p : Int) ∣ F.E (fun a => monoEval a g * (sumOne v M).eval a) := by
  have h1 := rowId F g v M
  have h2 : (p : Int) ∣ rsum M (fun t => F.E (fun a => monoEval a (g ++ [v t]))) - F.E (fun a => monoEval a g) := by
    apply rsum_pick_dvd M t0 ht0
    intro t ht
    by_cases e : t = t0
    · rw [if_pos e]; subst e
      rw [Fm_congr F (g ++ [v t]) g (fun x => by
        simp only [List.mem_append, List.mem_singleton]; exact ⟨fun h => h.elim id (fun e => e ▸ hg0), Or.inl⟩),
        Int.sub_self]; exact ⟨0, by simp⟩
    · rw [if_neg e, Int.sub_zero]
      exact hK _ (by simp) (v t) (by simp) (v t0) (by simp [hg0]) (hvc t ht e)
  have := Int.dvd_add h1 h2
  rwa [Int.sub_add_cancel] at this

/-- Conflicting `g`. -/
theorem line_conf {S : (Nat → Bool) → Prop} {F : Fn p S} {g : List Nat}
    (hK : ∀ xs : List Nat, xs.length ≤ g.length + 1 → ∀ u ∈ xs, ∀ w ∈ xs, cfl n u w = true →
      (p : Int) ∣ F.E (fun a => monoEval a xs))
    (u : Nat) (hu : u ∈ g) (w : Nat) (hw : w ∈ g) (hc : cfl n u w = true) (v : Nat → Nat) (M : Nat) :
    (p : Int) ∣ F.E (fun a => monoEval a g * (sumOne v M).eval a) := by
  have h1 := rowId F g v M
  have h2 : (p : Int) ∣ rsum M (fun t => F.E (fun a => monoEval a (g ++ [v t]))) - F.E (fun a => monoEval a g) :=
    Int.dvd_sub (rsum_dvd _ _ _ (fun t _ => hK _ (by simp) u (by simp [hu]) w (by simp [hw]) hc))
      (hK g (by omega) u hu w hw hc)
  have := Int.dvd_add h1 h2
  rwa [Int.sub_add_cancel] at this

end

/-! ## The extension -/

section
variable {p n k : Nat}

/-- Moments: `F` below level `d+1`, `y` on `(d+1)`-matchings, `0` on other `(d+1)`-sets. -/
def W (F : Fn p (SN ((n + k) * n))) (y : List Nat → Int) (d : Nat) (l : List Nat) : Int :=
  if l.length ≤ d then F.E (fun a => monoEval a l) else if isMatch n l then y l else 0

def Ext (F : Fn p (SN ((n + k) * n))) (y : List Nat → Int) (d : Nat) : Fn p (SN ((n + k) * n)) :=
  sumWFn p ((n + k) * n) (d + 1) (W F y d)

variable (F : Fn p (SN ((n + k) * n))) (y : List Nat → Int) (d : Nat)

theorem Ext_mono (xs : List Nat) (hx : ∀ x ∈ xs, x < (n + k) * n) (hl : (canon ((n + k) * n) xs).length ≤ d + 1) :
    (Ext F y d).E (fun a => monoEval a xs) = W F y d (canon ((n + k) * n) xs) :=
  sumW_mono _ (d + 1) _ xs hx hl

theorem Ext_low (xs : List Nat) (hx : ∀ x ∈ xs, x < (n + k) * n) (hl : (canon ((n + k) * n) xs).length ≤ d) :
    (Ext F y d).E (fun a => monoEval a xs) = F.E (fun a => monoEval a xs) := by
  rw [Ext_mono F y d xs hx (by omega)]
  unfold W; rw [if_pos hl]
  congr 1; funext a; exact (monoEval_canon _ a xs hx).symm

theorem Ext_extends : Extends d (Ext F y d) F := by
  intro t ht
  rcases all_lt_or (N := (n + k) * n) t with hx | ⟨x, hxt, hxN⟩
  · rw [Ext_low F y d t hx (Nat.le_trans (canon_length_le _ t) ht), Int.sub_self]; exact ⟨0, by simp⟩
  · exact Int.dvd_sub (vanish0 _ t x hxt hxN) (vanish0 F t x hxt hxN)

variable (hn : 0 < n) (hF : IsDesign (ontoFPHP n k) d F)
include hn hF

theorem Ext_kill (xs : List Nat) (hl : xs.length ≤ d + 1) (u : Nat) (hu : u ∈ xs) (w : Nat) (hw : w ∈ xs)
    (hc : cfl n u w = true) : (p : Int) ∣ (Ext F y d).E (fun a => monoEval a xs) := by
  rcases all_lt_or (N := (n + k) * n) xs with hx | ⟨x, hxt, hxN⟩
  case inr => exact vanish0 _ xs x hxt hxN
  have hm := mem_canon' hx
  rw [Ext_mono F y d xs hx (Nat.le_trans (canon_length_le _ xs) hl)]
  unfold W
  by_cases hd : (canon ((n + k) * n) xs).length ≤ d
  · rw [if_pos hd]
    exact kill hn F hF _ hd u ((hm u).mpr hu) w ((hm w).mpr hw) hc
  · rw [if_neg hd]
    have : isMatch n (canon ((n + k) * n) xs) = false := by
      cases h : isMatch n (canon ((n + k) * n) xs)
      · rfl
      · have := (isMatch_iff n _).mp h u ((hm u).mpr hu) w ((hm w).mpr hw); rw [hc] at this; cases this
    rw [this]; exact ⟨0, by simp⟩

omit hn hF in
theorem Ext_top (xs : List Nat) (hx : ∀ x ∈ xs, x < (n + k) * n) (hmx : isMatch n xs = true)
    (hl : (canon ((n + k) * n) xs).length = d + 1) :
    (Ext F y d).E (fun a => monoEval a xs) = y (canon ((n + k) * n) xs) := by
  rw [Ext_mono F y d xs hx (by omega)]
  unfold W
  rw [if_neg (by omega), isMatch_congr n _ xs (mem_canon' hx), hmx]; rfl

/-- One line at the top level. -/
theorem Ext_line (v : Nat → Nat) (M : Nat) (hP : sumOne v M ∈ ontoFPHP n k)
    (hvN : ∀ t < M, v t < (n + k) * n) (hvc : ∀ t < M, ∀ t' < M, t ≠ t' → cfl n (v t) (v t') = true)
    (hbal : ∀ s, CM n k s → s.length = d → (∀ t < M, v t ∉ s) →
      (p : Int) ∣ lineS n k y s v M - F.E (fun a => monoEval a s))
    (m : List Nat) (hm : m.length = d) :
    (p : Int) ∣ (Ext F y d).E (fun a => monoEval a m * (sumOne v M).eval a) := by
  rcases all_lt_or (N := (n + k) * n) m with hx | ⟨x, hxt, hxN⟩
  case inr => exact vanish _ m x hxt hxN _
  obtain ⟨s, hsd⟩ : ∃ s, s = canon ((n + k) * n) m := ⟨_, rfl⟩
  have hms : ∀ x, x ∈ s ↔ x ∈ m := hsd ▸ mem_canon' hx
  have hsl : s.length ≤ d := hsd ▸ hm ▸ canon_length_le _ m
  have hsx : ∀ x ∈ s, x < (n + k) * n := fun x h => hx x ((hms x).mp h)
  have e : (fun a => monoEval a m * (sumOne v M).eval a) = fun a => monoEval a s * (sumOne v M).eval a := by
    funext a; rw [monoEval_congr a m s (fun x => (hms x).symm)]
  rw [e]
  have hKE : ∀ xs : List Nat, xs.length ≤ s.length + 1 → ∀ u ∈ xs, ∀ w ∈ xs, cfl n u w = true →
      (p : Int) ∣ (Ext F y d).E (fun a => monoEval a xs) :=
    fun xs hl u hu w hw hc => Ext_kill F y d hn hF xs (by omega) u hu w hw hc
  by_cases hlow : s.length < d
  · have hd1 := sumOne_deg v M
    have := low_kill (D := d + 1) (E := Ext F y d) (E' := F) (by simpa using hF) (by simpa using Ext_extends F y d)
      hP (m := s) (by simp; omega)
    exact this
  have hsl' : s.length = d := by omega
  cases hmt : isMatch n s
  · obtain ⟨u, hu, w, hw, hc⟩ := not_match hmt
    exact line_conf hKE u hu w hw hc v M
  have hCM : CM n k s := ⟨by rw [hsd, canon_idem], hmt⟩
  by_cases hocc : ∃ t0 < M, v t0 ∈ s
  · obtain ⟨t0, ht0, hg0⟩ := hocc
    exact line_occ hKE v M t0 ht0 hg0 (fun t ht ne => hvc t ht t0 ht0 ne)
  have hfree : ∀ t < M, v t ∉ s := fun t ht h => hocc ⟨t, ht, h⟩
  have hK1 : ∀ xs : List Nat, xs.length ≤ d + 1 → ∀ u ∈ xs, ∀ w ∈ xs, cfl n u w = true →
      (p : Int) ∣ (Ext F y d).E (fun a => monoEval a xs) :=
    fun xs hl u hu w hw hc => Ext_kill F y d hn hF xs hl u hu w hw hc
  have h1 := line_bal (V := y) hK1 (fun xs hx hmx hl => Ext_top F y d xs hx hmx hl) hCM hsl' v M hvN hfree
  have h2 := hbal s hCM hsl' hfree
  have hlow' : (Ext F y d).E (fun a => monoEval a s) = F.E (fun a => monoEval a s) :=
    Ext_low F y d s hsx (by rw [hsd, canon_idem, ← hsd]; omega)
  rw [hlow'] at h1
  have := Int.dvd_add h1 h2
  rwa [Int.sub_add_cancel] at this

end

/-! ## One extension step -/

theorem pfree_of {n : Nat} {g : List Nat} {i : Nat} (hn : 0 < n) (h : ∀ j < n, var n i j ∉ g) : pfree n g i := by
  intro v hv e
  apply h (v % n) (Nat.mod_lt _ hn)
  have := var_decode n v
  rw [e] at this; rwa [this]

theorem hfree_of {n k : Nat} {g : List Nat} {j : Nat} (hn : 0 < n) (hg : ∀ x ∈ g, x < (n + k) * n)
    (h : ∀ i < n + k, var n i j ∉ g) : hfree n g j := by
  intro v hv e
  apply h (v / n) ((Nat.div_lt_iff_lt_mul hn).mpr (hg v hv))
  have := var_decode n v
  rw [e] at this; rwa [this]

theorem notin_of_pfree {n : Nat} {g : List Nat} {i : Nat} (h : pfree n g i) (j : Nat) (hj : j < n) :
    var n i j ∉ g := fun hm => h _ hm (var_div n i j hj)

theorem notin_of_hfree {n : Nat} {g : List Nat} {j : Nat} (h : hfree n g j) (i : Nat) (hj : j < n) :
    var n i j ∉ g := fun hm => h _ hm (var_mod n i j hj)

theorem pig_cfl {n i : Nat} : ∀ t < n, ∀ t' < n, t ≠ t' → cfl n (var n i t) (var n i t') = true := by
  intro t ht t' ht' ne
  simp only [cfl, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq]
  refine ⟨fun e => ne ?_, Or.inl (by rw [var_div n i t ht, var_div n i t' ht'])⟩
  have := congrArg (· % n) e; rwa [var_mod n i t ht, var_mod n i t' ht'] at this

theorem hole_cfl {n k j : Nat} (hj : j < n) : ∀ t < n + k, ∀ t' < n + k, t ≠ t' →
    cfl n (var n t j) (var n t' j) = true := by
  intro t _ t' _ ne
  simp only [cfl, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq]
  refine ⟨fun e => ne ?_, Or.inr (by rw [var_mod n t j hj, var_mod n t' j hj])⟩
  have := congrArg (· / n) e; rwa [var_div n t j hj, var_div n t' j hj] at this

/-- **Extension step.** -/
theorem ext_step {p n k d : Nat} (hn : 0 < n) (hX : EXT p n k d) (F : Fn p (SN ((n + k) * n)))
    (hF : IsDesign (ontoFPHP n k) d F) :
    ∃ E : Fn p (SN ((n + k) * n)), IsDesign (ontoFPHP n k) (d + 1) E ∧ Extends d E F := by
  let f : List Nat → Int := fun t => F.E (fun a => monoEval a t)
  have hV : ∀ xs : List Nat, (∀ x ∈ xs, x < (n + k) * n) → isMatch n xs = true →
      (canon ((n + k) * n) xs).length = d → F.E (fun a => monoEval a xs) = f (canon ((n + k) * n) xs) :=
    fun xs hx _ _ => Fm_congr F _ _ (fun x => (mem_canon' hx x).symm)
  have hB : ∀ e, e + 1 = d → Bal p n k f f e := by
    intro e he g hg hgl
    have hK : ∀ xs : List Nat, xs.length ≤ e + 1 → ∀ u ∈ xs, ∀ w ∈ xs, cfl n u w = true →
        (p : Int) ∣ F.E (fun a => monoEval a xs) :=
      fun xs hl u hu w hw hc => kill hn F hF xs (by omega) u hu w hw hc
    refine ⟨fun i hi hfr => ?_, fun j hj hfr => ?_⟩
    · show (p : Int) ∣ lineS n k f g (fun j => var n i j) n - F.E (fun a => monoEval a g)
      have h1 := line_bal (V := f) hK (fun xs hx hm hl => hV xs hx hm (by omega)) hg hgl (fun j => var n i j) n
        (fun j hj => var_lt n k i j hi hj) (notin_of_pfree hfr)
      have h2 := hF _ (mem_pig hi) g (by have := sumOne_deg (fun j => var n i j) n; omega)
      have := Int.dvd_sub h2 h1
      refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp this
      exact ⟨0, by omega⟩
    · show (p : Int) ∣ lineS n k f g (fun i => var n i j) (n + k) - F.E (fun a => monoEval a g)
      have h1 := line_bal (V := f) hK (fun xs hx hm hl => hV xs hx hm (by omega)) hg hgl (fun i => var n i j) (n + k)
        (fun i hi => var_lt n k i j hi hj) (fun i _ => notin_of_hfree hfr i hj)
      have h2 := hF _ (mem_hole hj) g (by have := sumOne_deg (fun i => var n i j) (n + k); omega)
      have := Int.dvd_sub h2 h1
      refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp this
      exact ⟨0, by omega⟩
  obtain ⟨y, hy⟩ := hX f f hB
  refine ⟨Ext F y d, ?_, Ext_extends F y d⟩
  intro P hP m hm
  by_cases hlow : m.length + P.deg ≤ d
  · exact low_kill (D := d + 1) (E' := F) (by simpa using hF) (by simpa using Ext_extends F y d) hP (by simpa using hlow)
  rcases mem_ontoFPHP hP with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ | hc | hf
  · have h1 := sumOne_deg (fun j => var n i j) n
    have h2 := sumOne_deg_pos (fun j => var n i j) n hn
    refine Ext_line F y d hn hF _ n (mem_pig hi) (fun j hj => var_lt n k i j hi hj) pig_cfl ?_ m (by omega)
    intro s hs hsl hfr
    exact (hy s hs hsl).1 i hi (pfree_of hn hfr)
  · have h1 := sumOne_deg (fun i => var n i j) (n + k)
    have h2 := sumOne_deg_pos (fun i => var n i j) (n + k) (by omega)
    refine Ext_line F y d hn hF _ (n + k) (mem_hole hj) (fun i hi => var_lt n k i j hi hj) (hole_cfl hj) ?_ m (by omega)
    intro s hs hsl hfr
    exact (hy s hs hsl).2 j hj (hfree_of hn (fun x hx => CM_lt hs hx) hfr)
  · obtain ⟨j, i, i', hj, hi, hi', hii, rfl⟩ := mem_collAx.mp hc
    rw [prod2_deg] at hm
    have e : (fun a => monoEval a m * (prod2 (var n i j) (var n i' j)).eval a) =
        fun a => monoEval a (m ++ [var n i j, var n i' j]) := by
      funext a; rw [prod2_eval, monoEval_append]; simp [monoEval, xv]
    rw [e]
    exact Ext_kill F y d hn hF _ (by simp; omega) (var n i j) (by simp) (var n i' j) (by simp)
      (hole_cfl (k := k) hj i hi i' hi' (by omega))
  · obtain ⟨i, j, j', hi, hj, hj', hjj, rfl⟩ := mem_funcAx.mp hf
    rw [prod2_deg] at hm
    have e : (fun a => monoEval a m * (prod2 (var n i j) (var n i j')).eval a) =
        fun a => monoEval a (m ++ [var n i j, var n i j']) := by
      funext a; rw [prod2_eval, monoEval_append]; simp [monoEval, xv]
    rw [e]
    exact Ext_kill F y d hn hF _ (by simp; omega) (var n i j) (by simp) (var n i j') (by simp)
      (pig_cfl (i := i) j hj j' hj' (by omega))

/-! ## Iteration and the main theorem -/

theorem designs {p n k : Nat} (hn : 0 < n) : ∀ d, (∀ e < d, EXT p n k e) →
    ∃ E : Fn p (SN ((n + k) * n)), IsDesign (ontoFPHP n k) d E ∧ (p : Int) ∣ E.E (fun _ => 1) - 1 := by
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨sumWFn p ((n + k) * n) 0 (fun _ => 1), ?_, ?_⟩
    · intro P hP m hm
      exfalso
      rcases mem_ontoFPHP hP with ⟨i, _, rfl⟩ | ⟨j, _, rfl⟩ | hc | hf
      · have := sumOne_deg_pos (fun j => var n i j) n hn; omega
      · have := sumOne_deg_pos (fun i => var n i j) (n + k) (by omega); omega
      · obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_collAx.mp hc; rw [prod2_deg] at hm; omega
      · obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_funcAx.mp hf; rw [prod2_deg] at hm; omega
    · have e : (fun _ => (1 : Int)) = fun a => monoEval a ([] : List Nat) := by funext a; simp [monoEval]
      show (p : Int) ∣ sumW _ 0 _ (fun _ => (1 : Int)) - 1
      have hc : canon ((n + k) * n) ([] : List Nat) = [] :=
        List.eq_nil_iff_forall_not_mem.mpr (fun x h => by simp [mem_canon] at h)
      rw [e, sumW_mono _ 0 _ [] (by simp) (by rw [hc]; simp)]
      exact ⟨0, by simp⟩
  | succ d ih =>
    intro hX
    obtain ⟨F, hF, h1⟩ := ih (fun e he => hX e (by omega))
    obtain ⟨E, hE, hx⟩ := ext_step hn (hX d (by omega)) F hF
    refine ⟨E, hE, ?_⟩
    have a := hx [] (by simp)
    have e : (fun a => monoEval a ([] : List Nat)) = fun _ => (1 : Int) := by funext a; simp [monoEval]
    rw [e] at a
    have := Int.dvd_add a h1
    rwa [show E.E (fun _ => 1) - F.E (fun _ => 1) + (F.E (fun _ => 1) - 1) = E.E (fun _ => 1) - 1 by omega] at this

/-- **EXT lemma** (th, P49 §3). For `p > 1`, `n > 0`, `D ≥ 1`: if `EXT p n k d` holds for every
`d < D` (th's `EXT_p(n,k,D')` for `1 ≤ D' ≤ D`), then `ontoFPHP n k` has no degree-`D`
`PPCRefutation p`. -/
theorem no_refutation_of_ext {p n k D : Nat} (hp : 1 < p) (hn : 0 < n) (hD : 1 ≤ D)
    (hX : ∀ d < D, EXT p n k d) : ¬ PPCRefutation p (ontoFPHP n k) D := by
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  obtain ⟨E0, hE0, h1⟩ := designs hn d (fun e he => hX e (by omega))
  refine ext_sound (D := d + 1) (S := SN ((n + k) * n)) hD
    (fun F hF => ext_step hn (hX d (by omega)) F (by simpa using hF)) E0 (by simpa using hE0) ?_
  intro h
  have := Int.dvd_sub h h1
  rw [show E0.E (fun _ => 1) - (E0.E (fun _ => 1) - 1) = 1 by omega] at this
  exact not_dvd_one hp this

/-- With restriction (`OntoSubst.ontoFPHP_restrict`): EXT at levels `< D` for one `n₀ > 0` gives no
degree-`D` refutation for every `n ≥ n₀`. -/
theorem no_refutation_of_ext_ge {p n0 k D : Nat} (hp : 1 < p) (hn0 : 0 < n0) (hD : 1 ≤ D)
    (hX : ∀ d < D, EXT p n0 k d) (n : Nat) (hn : n0 ≤ n) : ¬ PPCRefutation p (ontoFPHP n k) D := by
  have base := no_refutation_of_ext hp hn0 hD hX
  obtain ⟨e, rfl⟩ : ∃ e, n = n0 + e := ⟨n - n0, by omega⟩
  clear hn
  induction e with
  | zero => exact base
  | succ e ih =>
    intro h
    exact ih (Programme.«20261025-0459-proof-complexity».OntoSubst.ontoFPHP_restrict p (n0 + e) k D hD
      (by omega) (by rwa [show n0 + e + 1 = n0 + (e + 1) by omega]))

end Programme.«20261026-1402-proof-complexity».ExtLemma

#print axioms Programme.«20261026-1402-proof-complexity».ExtLemma.no_refutation_of_ext
#print axioms Programme.«20261026-1402-proof-complexity».ExtLemma.no_refutation_of_ext_ge
