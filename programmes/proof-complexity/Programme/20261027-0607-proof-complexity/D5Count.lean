import Programme.«20261027-0607-proof-complexity».D5Lem
import Programme.«20261026-1402-proof-complexity».Win

/-!
# Row and column sums of the class-code design `T t` on matchings of `ontoFPHP 9 25`

For a matching `g` (nodup, `isMatch 9 g`, edges `< 306`):
- `row_formula`: the free row sum at pigeon `i` is `∑_{d<3} (H_d - cs_d) G(nb (kap g) (key g (i/4)) d)`;
- `col_formula`: the free column sum at hole `j` is `∑_{c<9} (P_c - rowc_c) G(nb (kap g) (key g c) (j/4))`;
- `kap_cons`: adding an edge changes the code to the neighbour code `nb`;
- `bd`, `dig_key`, `rc_key`, `Pi_key`, `cs_cc`: the counts behind the reduced equations.
-/

namespace Programme.«20261027-0607-proof-complexity».D5

open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum rsum_comm rsum_add var)
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (rsum_pick var_lt)
open Programme.«20261025-1627-proof-complexity».MomGen (canon mem_canon canon_nodup)
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».Win (match_row match_col nodup_mod nodup_div count_freeQ)

def rowc (g : List Nat) (c : Nat) : Nat := g.countP (fun v => v / 9 / 4 == c)
def csg (g : List Nat) (d : Nat) : Nat := g.countP (fun v => v % 9 / 4 == d)
def Pc (c : Nat) : Nat := if c < 8 then 4 else 2

/-- A matching of `ontoFPHP 9 25` as a list. -/
structure Mt (g : List Nat) : Prop where
  nd : g.Nodup
  im : isMatch 9 g = true
  lt : ∀ v ∈ g, v < 306

/-! ## Adding an edge -/

theorem key_cons (x : Nat) (g : List Nat) (c : Nat) :
    key (x :: g) c = key g c + if c = x / 9 / 4 then 5 ^ (x % 9 / 4) else 0 := by
  have hd : x % 9 / 4 = 0 ∨ x % 9 / 4 = 1 ∨ x % 9 / 4 = 2 := by omega
  simp only [key, cc, List.countP_cons]
  by_cases hc : c = x / 9 / 4
  · subst hc
    rcases hd with hd | hd | hd <;> simp [hd] <;> omega
  · have : (x / 9 / 4 == c) = false := by simp; omega
    simp [this, hc]

theorem kap_cons (x : Nat) (g : List Nat) (hx : x / 9 / 4 < 9) :
    kap (x :: g) = nb (kap g) (key g (x / 9 / 4)) (x % 9 / 4) := by
  have h := nsum_upd (fun c => 5 ^ key g c) (fun c => 5 ^ key (x :: g) c) (x / 9 / 4)
    (fun c hc => by rw [key_cons, if_neg hc, Nat.add_zero]) 9 hx
  have hge := nsum_ge (fun c => 5 ^ key g c) 9 (x / 9 / 4) hx
  have hfa : 5 ^ key (x :: g) (x / 9 / 4) = 5 ^ (key g (x / 9 / 4) + 5 ^ (x % 9 / 4)) := by
    rw [key_cons, if_pos rfl]
  rw [hfa] at h
  unfold kap nb; omega

theorem kap_perm {l l' : List Nat} (h : l.Perm l') : kap l = kap l' := by
  unfold kap key cc; simp only [h.countP_eq]

theorem kap_canon {x : Nat} {g : List Nat} (hm : Mt g) (hx : x < 306) (hxg : x ∉ g) :
    kap (canon 306 (x :: g)) = kap (x :: g) := by
  apply kap_perm
  apply (List.perm_ext_iff_of_nodup (canon_nodup _ _) (List.nodup_cons.mpr ⟨hxg, hm.nd⟩)).mpr
  intro a; rw [mem_canon]
  constructor
  · exact fun h => h.1
  · intro h; refine ⟨h, ?_⟩
    rcases List.mem_cons.mp h with e | e
    · subst e; exact hx
    · exact hm.lt a e

/-! ## Free lines -/

theorem hole_cls : ∀ d < 3, rsum 9 (fun t => if t / 4 = d then (1 : Int) else 0) = Hd d := by decide
theorem pig_cls : ∀ c < 9, rsum 34 (fun s => if s / 4 = c then (1 : Int) else 0) = Pc c := by decide

theorem free_holes {g : List Nat} (hm : Mt g) {d : Nat} (hd : d < 3) :
    rsum 9 (fun t => if t / 4 = d ∧ ∀ w ∈ g, w % 9 ≠ t then 1 else 0) = (Hd d : Int) - csg g d := by
  let g' := g.filter (fun v => v % 9 / 4 == d)
  have hnd : (g'.map (· % 9)).Nodup := ((List.filter_sublist).map _).nodup (nodup_mod hm.nd hm.im)
  have h := count_freeQ (fun t => t / 4 = d) (· % 9) 9 g' hnd (fun v hv => by
    have := (List.mem_filter.mp hv).2; simp at this; exact ⟨Nat.mod_lt _ (by omega), this⟩)
  have e : ∀ t < 9, (if t / 4 = d ∧ ∀ w ∈ g, w % 9 ≠ t then (1 : Int) else 0) =
      (if t / 4 = d ∧ ∀ v ∈ g', v % 9 ≠ t then 1 else 0) := by
    intro t _
    by_cases ht : t / 4 = d
    · have : (∀ w ∈ g, w % 9 ≠ t) ↔ (∀ v ∈ g', v % 9 ≠ t) := by
        constructor
        · exact fun H v hv => H v (List.mem_filter.mp hv).1
        · intro H w hw e
          exact H w (List.mem_filter.mpr ⟨hw, by simp; omega⟩) e
      simp only [ht, true_and, this]
    · simp [ht]
  rw [rsum_congr 9 _ _ e, h, hole_cls d hd]
  simp [csg, List.countP_eq_length_filter, g']

theorem free_pigs {g : List Nat} (hm : Mt g) {c : Nat} (hc : c < 9) :
    rsum 34 (fun s => if s / 4 = c ∧ ∀ w ∈ g, w / 9 ≠ s then 1 else 0) = (Pc c : Int) - rowc g c := by
  let g' := g.filter (fun v => v / 9 / 4 == c)
  have hnd : (g'.map (· / 9)).Nodup := ((List.filter_sublist).map _).nodup (nodup_div hm.nd hm.im)
  have h := count_freeQ (fun s => s / 4 = c) (· / 9) 34 g' hnd (fun v hv => by
    have h1 := (List.mem_filter.mp hv).2; have h2 := hm.lt v (List.mem_filter.mp hv).1
    simp at h1; exact ⟨by omega, h1⟩)
  have e : ∀ s < 34, (if s / 4 = c ∧ ∀ w ∈ g, w / 9 ≠ s then (1 : Int) else 0) =
      (if s / 4 = c ∧ ∀ v ∈ g', v / 9 ≠ s then 1 else 0) := by
    intro s _
    by_cases hs : s / 4 = c
    · have : (∀ w ∈ g, w / 9 ≠ s) ↔ (∀ v ∈ g', v / 9 ≠ s) := by
        constructor
        · exact fun H v hv => H v (List.mem_filter.mp hv).1
        · intro H w hw e
          exact H w (List.mem_filter.mpr ⟨hw, by simp; omega⟩) e
      simp only [hs, true_and, this]
    · simp [hs]
  rw [rsum_congr 34 _ _ e, h, pig_cls c hc]
  simp [rowc, List.countP_eq_length_filter, g']

theorem cs_le {g : List Nat} (hm : Mt g) {d : Nat} (hd : d < 3) : csg g d ≤ Hd d := by
  have h := free_holes hm hd
  have := rsum_nonneg (fun t => if t / 4 = d ∧ ∀ w ∈ g, w % 9 ≠ t then (1 : Int) else 0)
    (fun _ => by split <;> omega) 9
  omega

theorem rowc_le {g : List Nat} (hm : Mt g) {c : Nat} (hc : c < 9) : rowc g c ≤ Pc c := by
  have h := free_pigs hm hc
  have := rsum_nonneg (fun s => if s / 4 = c ∧ ∀ w ∈ g, w / 9 ≠ s then (1 : Int) else 0)
    (fun _ => by split <;> omega) 34
  omega

theorem cc_le_cs (g : List Nat) (c d : Nat) : cc g c d ≤ csg g d :=
  List.countP_mono_left (fun x _ h => by simp at h ⊢; exact h.2)

theorem bd {g : List Nat} (hm : Mt g) : Bd g := by
  intro c _
  have h0 := cs_le hm (d := 0) (by omega); have h1 := cs_le hm (d := 1) (by omega)
  have h2 := cs_le hm (d := 2) (by omega)
  have := cc_le_cs g c 0; have := cc_le_cs g c 1; have := cc_le_cs g c 2
  simp [Hd] at h0 h1 h2; omega

/-! ## Counts behind the reduced equations -/

theorem cs_cc : ∀ (g : List Nat), (∀ v ∈ g, v < 306) → ∀ d, (csg g d : Int) = rsum 9 (fun c => (cc g c d : Int))
  | [], _, d => by simp [csg, cc, rsum_zero 9 _ (fun _ _ => rfl)]
  | x :: g, h, d => by
    have ih := cs_cc g (fun v hv => h v (by simp [hv])) d
    have hx := h x (by simp)
    have e : ∀ c, (cc (x :: g) c d : Int) = (cc g c d : Int) +
        (if c = x / 9 / 4 then (if x % 9 / 4 = d then 1 else 0) else 0) := by
      intro c; simp only [cc, List.countP_cons]
      by_cases hc : c = x / 9 / 4
      · subst hc; by_cases hd : x % 9 / 4 = d <;> simp [hd]
      · have : (x / 9 / 4 == c) = false := by simp; omega
        simp [this, hc]
    rw [rsum_congr 9 _ _ (fun c _ => e c), rsum_add, rsum_pick, if_pos (by omega)]
    simp only [csg, List.countP_cons] at ih ⊢
    by_cases hd : x % 9 / 4 = d <;> simp [hd] <;> omega

theorem rowc_cc : ∀ (g : List Nat) (c : Nat), rowc g c = cc g c 0 + cc g c 1 + cc g c 2
  | [], c => by simp [rowc, cc]
  | x :: g, c => by
    have ih := rowc_cc g c
    have hd : x % 9 / 4 = 0 ∨ x % 9 / 4 = 1 ∨ x % 9 / 4 = 2 := by omega
    simp only [rowc, cc, List.countP_cons] at ih ⊢
    by_cases hc : x / 9 / 4 = c
    · rcases hd with hd | hd | hd <;> simp [hc, hd] <;> omega
    · simp [hc]; omega

theorem dig_key {g : List Nat} (hb : Bd g) {c d : Nat} (hc : c < 9) (hd : d < 3) :
    dig d (key g c) = cc g c d := by
  have := hb c hc
  have hd' : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  unfold dig key
  rcases hd' with rfl | rfl | rfl <;> simp <;> omega

theorem rc_key {g : List Nat} (hb : Bd g) {c : Nat} (hc : c < 9) : rc (key g c) = rowc g c := by
  unfold rc; rw [dig_key hb hc (by omega), dig_key hb hc (by omega), dig_key hb hc (by omega), rowc_cc]

theorem Pi_key {g : List Nat} (hb : Bd g) {c : Nat} (hc : c < 9) : Pi (key g c) = Pc c := by
  have := hb c hc
  unfold Pi Pc key
  by_cases h : c < 8
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-! ## Grouping a line sum by classes -/

theorem group (M D : Nat) (h : Nat → Nat) (hh : ∀ t < M, h t < D) (C : Nat → Prop) [DecidablePred C]
    (X : Nat → Int) :
    rsum M (fun t => if C t then X (h t) else 0) =
      rsum D (fun d => X d * rsum M (fun t => if h t = d ∧ C t then 1 else 0)) := by
  have e : ∀ d, X d * rsum M (fun t => if h t = d ∧ C t then 1 else 0) =
      rsum M (fun t => if d = h t then (if C t then X (h t) else 0) else 0) := by
    intro d; rw [← rsum_mulr]; apply rsum_congr; intro t _
    by_cases h1 : h t = d
    · subst h1; by_cases h2 : C t <;> simp [h2]
    · simp [h1, Ne.symm h1]
  rw [rsum_congr D _ _ (fun d _ => e d), rsum_comm]
  apply rsum_congr; intro t ht
  rw [rsum_pick, if_pos (hh t ht)]

/-! ## The line sums -/

theorem row_formula (t : Tr) {g : List Nat} (hm : Mt g) {i : Nat} (hi : i < 34) (hf : pfree 9 g i) :
    rowS 9 25 (T t) g i = rsum 3 (fun d => ((Hd d : Int) - csg g d) * Gt t (nb (kap g) (key g (i / 4)) d)) := by
  unfold rowS lineS
  have e : ∀ s < 9, (if isMatch 9 (var 9 i s :: g) = true then T t (canon ((9 + 25) * 9) (var 9 i s :: g)) else 0) =
      (if ∀ w ∈ g, w % 9 ≠ s then Gt t (nb (kap g) (key g (i / 4)) (s / 4)) else 0) := by
    intro s hs
    have key' := match_row hm.im hs hf
    by_cases h2 : ∀ w ∈ g, w % 9 ≠ s
    · rw [if_pos (key'.mpr h2), if_pos h2]
      have hv : var 9 i s < 306 := var_lt 9 25 i s (by omega) hs
      have hvg : var 9 i s ∉ g := fun hv' => h2 _ hv' (var_mod 9 i s hs)
      unfold T
      rw [show (9 + 25) * 9 = 306 from rfl, kap_canon hm hv hvg, kap_cons _ _ (by rw [var_div 9 i s hs]; omega),
        var_div 9 i s hs, var_mod 9 i s hs]
    · rw [if_neg h2]
      have : isMatch 9 (var 9 i s :: g) = false := by
        cases h : isMatch 9 (var 9 i s :: g)
        · rfl
        · exact absurd (key'.mp h) h2
      rw [this]; simp
  rw [rsum_congr 9 _ _ e]
  refine (group 9 3 (· / 4) (fun t ht => by omega) (fun s => ∀ w ∈ g, w % 9 ≠ s)
    (fun d => Gt t (nb (kap g) (key g (i / 4)) d))).trans ?_
  apply rsum_congr; intro d hd
  rw [free_holes hm hd, Int.mul_comm]

theorem col_formula (t : Tr) {g : List Nat} (hm : Mt g) {j : Nat} (hj : j < 9) (hf : hfree 9 g j) :
    colS 9 25 (T t) g j = rsum 9 (fun c => ((Pc c : Int) - rowc g c) * Gt t (nb (kap g) (key g c) (j / 4))) := by
  unfold colS lineS
  have e : ∀ s < 9 + 25, (if isMatch 9 (var 9 s j :: g) = true then T t (canon ((9 + 25) * 9) (var 9 s j :: g)) else 0) =
      (if ∀ w ∈ g, w / 9 ≠ s then Gt t (nb (kap g) (key g (s / 4)) (j / 4)) else 0) := by
    intro s hs
    have key' := match_col (s := s) hm.im hj hf
    by_cases h2 : ∀ w ∈ g, w / 9 ≠ s
    · rw [if_pos (key'.mpr h2), if_pos h2]
      have hv : var 9 s j < 306 := var_lt 9 25 s j hs hj
      have hvg : var 9 s j ∉ g := fun hv' => h2 _ hv' (var_div 9 s j hj)
      unfold T
      rw [show (9 + 25) * 9 = 306 from rfl, kap_canon hm hv hvg, kap_cons _ _ (by rw [var_div 9 s j hj]; omega),
        var_div 9 s j hj, var_mod 9 s j hj]
    · rw [if_neg h2]
      have : isMatch 9 (var 9 s j :: g) = false := by
        cases h : isMatch 9 (var 9 s j :: g)
        · rfl
        · exact absurd (key'.mp h) h2
      rw [this]; simp
  rw [rsum_congr (9 + 25) _ _ e]
  refine (group (9 + 25) 9 (· / 4) (fun t ht => by omega) (fun s => ∀ w ∈ g, w / 9 ≠ s)
    (fun c => Gt t (nb (kap g) (key g c) (j / 4)))).trans ?_
  apply rsum_congr; intro c hc
  rw [free_pigs hm hc, Int.mul_comm]

end Programme.«20261027-0607-proof-complexity».D5
