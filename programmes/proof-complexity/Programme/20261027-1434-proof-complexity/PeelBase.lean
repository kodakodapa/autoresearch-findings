import Programme.«20261026-1402-proof-complexity».ExtLin
import Programme.«20261026-1402-proof-complexity».Relabel
import Programme.«20261027-1434-proof-complexity».F2Lin

/-!
# Building blocks for peeling certificates on `ontoFPHP 7 8`

* permutations of `[0, m)` as products of transpositions (`mkP`), always valid;
* `canon` of lists of length at most two, computed fast (`fcanon`);
* codes of canonical matchings of size one or two (`code`, `dec`, `valid`), with a reserved
  code `K` for the link constant;
* the parity of `bv L` at `c` is the parity of the number of copies of `c` in `L`;
* relabelling moves the odd-support of a function by the inverse permutation (`relab_par`);
* a free row or column sum at a canonical matching of size `≤ 1` is a sum over a computed list
  of codes (`line_ev`).
-/

namespace Programme.«20261027-1434-proof-complexity».PeelBase

set_option linter.deprecated false
set_option linter.unusedVariables false

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt var_decode)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».Relabel
open Programme.«20261027-1434-proof-complexity».F2Lin

/-! ## Permutations from transpositions -/

def sw (m a b x : Nat) : Nat :=
  if a < m ∧ b < m then (if x = a then b else if x = b then a else x) else x

theorem sw_lt {m a b x : Nat} (hx : x < m) : sw m a b x < m := by
  unfold sw; split
  · split
    · omega
    · split <;> omega
  · exact hx

theorem sw_sw (m a b x : Nat) : sw m a b (sw m a b x) = x := by
  unfold sw
  by_cases h : a < m ∧ b < m
  · simp only [h, and_self, if_true]
    by_cases h1 : x = a
    · subst h1; simp only [if_true]; split <;> omega
    · simp only [h1, if_false]
      by_cases h2 : x = b
      · subst h2; simp
      · simp [h1, h2]
  · simp [h]

def pf (m : Nat) : List (Nat × Nat) → Nat → Nat
  | [], x => x
  | ab :: L, x => sw m ab.1 ab.2 (pf m L x)

def pg (m : Nat) : List (Nat × Nat) → Nat → Nat
  | [], x => x
  | ab :: L, x => pg m L (sw m ab.1 ab.2 x)

theorem pf_lt (m : Nat) : ∀ (L : List (Nat × Nat)) (x : Nat), x < m → pf m L x < m
  | [], _, h => h
  | _ :: L, x, h => sw_lt (pf_lt m L x h)

theorem pg_lt (m : Nat) : ∀ (L : List (Nat × Nat)) (x : Nat), x < m → pg m L x < m
  | [], _, h => h
  | _ :: L, x, h => pg_lt m L _ (sw_lt h)

theorem pg_pf (m : Nat) : ∀ (L : List (Nat × Nat)) (x : Nat), pg m L (pf m L x) = x
  | [], _ => rfl
  | ab :: L, x => by simp only [pf, pg]; rw [sw_sw]; exact pg_pf m L x

theorem pf_pg (m : Nat) : ∀ (L : List (Nat × Nat)) (x : Nat), pf m L (pg m L x) = x
  | [], _ => rfl
  | ab :: L, x => by simp only [pf, pg]; rw [pf_pg m L]; exact sw_sw _ _ _ _

def mkP (m : Nat) (L : List (Nat × Nat)) : Perm m where
  f := pf m L
  g := pg m L
  f_lt := fun x h => pf_lt m L x h
  g_lt := fun x h => pg_lt m L x h
  gf := fun x _ => pg_pf m L x
  fg := fun x _ => pf_pg m L x

def Perm.inv {m : Nat} (σ : Perm m) : Perm m where
  f := σ.g
  g := σ.f
  f_lt := σ.g_lt
  g_lt := σ.f_lt
  gf := σ.fg
  fg := σ.gf

/-! ## Canon of short lists -/

theorem canon_one' : ∀ (N x : Nat), canon N [x] = if x < N then [x] else []
  | 0, x => by simp [canon]
  | N + 1, x => by
    simp only [canon, List.mem_singleton]
    rw [canon_one' N x]
    by_cases h : N = x
    · subst h; simp
    · have : ¬ x = N := fun e => h e.symm
      simp only [h, if_false]
      by_cases h' : x < N
      · simp [h', show x < N + 1 by omega]
      · simp [h', show ¬ x < N + 1 by omega]

theorem canon_two : ∀ (N x w : Nat), w < x →
    canon N [x, w] = (if x < N then [x] else []) ++ (if w < N then [w] else [])
  | 0, x, w, _ => by simp [canon]
  | N + 1, x, w, hwx => by
    simp only [canon, List.mem_cons, List.not_mem_nil, or_false]
    rw [canon_two N x w hwx]
    by_cases h1 : N = x
    · subst h1; simp [hwx, show w < N + 1 by omega]
    · by_cases h2 : N = w
      · subst h2
        simp [show ¬ x < N by omega, show ¬ x < N + 1 by omega]
      · simp only [h1, h2, or_self, if_false]
        have e1 : (x < N + 1) = (x < N) := by apply propext; omega
        have e2 : (w < N + 1) = (w < N) := by apply propext; omega
        simp only [e1, e2]

theorem canon_nil' : ∀ N : Nat, canon N [] = []
  | 0 => rfl
  | N + 1 => by simp [canon, canon_nil' N]

theorem canon_swap' (N v w : Nat) : canon N [v, w] = canon N [w, v] :=
  canon_congr N _ _ (fun x _ => by simp [or_comm])

/-- `canon` on lists of length at most two, by comparison. -/
def fcanon : List Nat → List Nat
  | [x, w] => if w < x then [x, w] else [w, x]
  | l => l

theorem canon_short {N : Nat} {l : List Nat} (hl : ∀ x ∈ l, x < N) (hn : l.Nodup) (h2 : l.length ≤ 2) :
    canon N l = fcanon l := by
  match l, hl, hn, h2 with
  | [], _, _, _ => exact canon_nil' N
  | [x], hl, _, _ => rw [canon_one']; simp [fcanon, hl x (by simp)]
  | [x, w], hl, hn, _ =>
    have hx := hl x (by simp); have hw := hl w (by simp)
    have hne : x ≠ w := by simpa using hn
    simp only [fcanon]
    by_cases h : w < x
    · rw [canon_two N x w h]; simp [h, hx, hw]
    · have h' : x < w := by omega
      rw [canon_swap', canon_two N w x h']
      simp [h, hx, hw]
  | _ :: _ :: _ :: _, _, _, h2 => simp at h2

/-! ## Codes -/

/-- Reserved code for the link constant. -/
def K : Nat := 16384

def code : List Nat → Nat
  | [a] => a
  | [a, b] => a * 128 + b
  | _ => 0

def dec (e c : Nat) : List Nat := if e = 1 then [c] else [c / 128, c % 128]

def valid (e c : Nat) : Bool :=
  c == K || (e == 1 && decide (c < 105)) ||
    (e == 2 && decide (c / 128 < 105) && decide (c % 128 < c / 128) && isMatch 7 [c / 128, c % 128])

theorem CM_lt' {g : List Nat} (hg : CM 7 8 g) {x : Nat} (hx : x ∈ g) : x < 105 := CM_lt hg hx

theorem CM_one {m : Nat → Nat} {g : List Nat} (hg : CM 7 8 g) (hl : g.length = 1) :
    ∃ a, g = [a] ∧ a < 105 := by
  match g, hl with
  | [a], _ => exact ⟨a, rfl, CM_lt' hg (by simp)⟩

theorem CM_two {g : List Nat} (hg : CM 7 8 g) (hl : g.length = 2) :
    ∃ a b, g = [a, b] ∧ b < a ∧ a < 105 ∧ isMatch 7 [a, b] = true := by
  match g, hl with
  | [a, b], _ =>
    have ha := CM_lt' hg (x := a) (by simp)
    have hb := CM_lt' hg (x := b) (by simp)
    have hnd := CM_nodup hg
    have hne : a ≠ b := by simpa using hnd
    refine ⟨a, b, rfl, ?_, ha, hg.2⟩
    rcases Nat.lt_or_ge b a with hab | hab
    · exact hab
    have h' : a < b := by omega
    have h1 := hg.1
    rw [canon_swap', canon_two _ b a h'] at h1
    simp [show b < (7 + 8) * 7 by omega, show a < (7 + 8) * 7 by omega] at h1
    omega

theorem dec_lt (c : Nat) : c / 128 < 105 → c % 128 < c / 128 → c < K := by
  intro h1 h2; unfold K; omega

/-- A valid code other than `K` decodes to a canonical matching with that code. -/
theorem valid_pt {e c : Nat} (he : e = 1 ∨ e = 2) (hv : valid e c = true) (hK : c ≠ K) :
    CM 7 8 (dec e c) ∧ (dec e c).length = e ∧ code (dec e c) = c ∧ c < K := by
  unfold valid at hv
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hv
  rcases he with rfl | rfl
  · have hc : c < 105 := by rcases hv with (h | ⟨-, h⟩) | ⟨⟨⟨⟨h, -⟩, -⟩, -⟩, -⟩ <;> first | exact absurd h hK | exact h | omega
    refine ⟨⟨?_, ?_⟩, by simp [dec], by simp [dec, code], by unfold K; omega⟩
    · show canon _ [c] = [c]; rw [canon_one']; simp [show c < (7 + 8) * 7 by omega]
    · simp [dec, isMatch, cfl]
  · have hc : c / 128 < 105 ∧ c % 128 < c / 128 ∧ isMatch 7 [c / 128, c % 128] = true := by
      rcases hv with (h | ⟨h, -⟩) | ⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩
      · exact absurd h hK
      · omega
      · exact ⟨h2, h3, h4⟩
    obtain ⟨h1, h2, h3⟩ := hc
    refine ⟨⟨?_, ?_⟩, rfl, ?_, dec_lt c h1 h2⟩
    · show canon _ [c / 128, c % 128] = [c / 128, c % 128]
      rw [canon_two _ _ _ h2]; simp [show c / 128 < (7 + 8) * 7 by omega, show c % 128 < (7 + 8) * 7 by omega]
    · simpa [dec] using h3
    · simp only [dec, show (2 = 1) = False by decide, if_false, code]; omega

theorem code_pt {e : Nat} (he : e = 1 ∨ e = 2) {m : List Nat} (hm : CM 7 8 m) (hl : m.length = e) :
    valid e (code m) = true ∧ code m ≠ K ∧ code m < K ∧ dec e (code m) = m := by
  rcases he with rfl | rfl
  · obtain ⟨a, rfl, ha⟩ := CM_one (m := id) hm hl
    refine ⟨?_, ?_, ?_, by simp [dec, code]⟩
    · simp [code, valid, ha]
    · simp only [code]; unfold K; omega
    · simp only [code]; unfold K; omega
  · obtain ⟨a, b, rfl, hba, ha, hmt⟩ := CM_two hm hl
    have d1 : (a * 128 + b) / 128 = a := by omega
    have d2 : (a * 128 + b) % 128 = b := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [code, valid, d1, d2, ha, hba, hmt]
    · simp only [code]; unfold K; omega
    · simp only [code]; unfold K; omega
    · simp [code, dec, d1, d2]

theorem code_inj {e : Nat} (he : e = 1 ∨ e = 2) {m m' : List Nat} (hm : CM 7 8 m) (hl : m.length = e)
    (hm' : CM 7 8 m') (hl' : m'.length = e) (h : code m = code m') : m = m' := by
  rw [← (code_pt he hm hl).2.2.2, ← (code_pt he hm' hl').2.2.2, h]

/-! ## Parity of `bv` -/

def bitI (M c : Nat) : Int := if M.testBit c then 1 else 0

theorem testBit_bv (c : Nat) : ∀ L : List Nat, (bv L).testBit c = decide (L.count c % 2 = 1)
  | [] => by simp [bv]
  | x :: L => by
    simp only [bv, Nat.testBit_xor, testBit_bv c L, Nat.testBit_two_pow, List.count_cons]
    by_cases h : x = c
    · subst h
      rcases Nat.mod_two_eq_zero_or_one (L.count x) with h | h <;> simp [h, Nat.add_mod]
    · simp [h]

theorem bitI_bv (L : List Nat) (c : Nat) : (2 : Int) ∣ bitI (bv L) c - (L.count c : Int) := by
  unfold bitI; rw [testBit_bv]
  have := Nat.mod_two_eq_zero_or_one (L.count c)
  split
  · next h => simp at h; exact ⟨(1 - (L.count c : Int)) / 2, by omega⟩
  · next h => simp at h; exact ⟨-((L.count c : Int) / 2), by omega⟩

theorem bitI_xor (a b c : Nat) : (2 : Int) ∣ bitI (a ^^^ b) c - bitI a c - bitI b c := by
  unfold bitI; rw [Nat.testBit_xor]
  cases a.testBit c <;> cases b.testBit c <;> simp

/-! ## Relabelling moves the odd support -/

theorem phi_phi {σ σ' : Perm (7 + 8)} {τ τ' : Perm 7} (h1 : ∀ x < 15, σ.f (σ'.f x) = x)
    (h2 : ∀ x < 7, τ.f (τ'.f x) = x) {v : Nat} (hv : v < (7 + 8) * 7) :
    phi σ τ (phi σ' τ' v) = v := by
  unfold phi
  rw [var_div _ _ _ (τ'.f_lt _ (mod_lt' hv)), var_mod _ _ _ (τ'.f_lt _ (mod_lt' hv)),
    h1 _ (div_lt' hv), h2 _ (mod_lt' hv)]
  exact var_decode 7 v

theorem back {σ σ' : Perm (7 + 8)} {τ τ' : Perm 7} (h1 : ∀ x < 15, σ.f (σ'.f x) = x)
    (h2 : ∀ x < 7, τ.f (τ'.f x) = x) {s : List Nat} (hs : CM 7 8 s) :
    canon ((7 + 8) * 7) ((canon ((7 + 8) * 7) (s.map (phi σ' τ'))).map (phi σ τ)) = s := by
  rw [canon_map_canon, filter_all (fun x hx => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; exact phi_lt σ' τ' (CM_lt hs hv))]
  rw [List.map_map]
  have : (s.map (phi σ τ ∘ phi σ' τ')) = s := by
    conv => rhs; rw [← List.map_id s]
    apply List.map_congr_left
    intro v hv; exact phi_phi h1 h2 (CM_lt hs hv)
  rw [this]; exact hs.1

/-- Image code of a support element under the inverse relabelling. -/
def icode (σ : Perm (7 + 8)) (τ : Perm 7) (s : List Nat) : Nat :=
  code (fcanon (s.map (phi (Perm.inv σ) (Perm.inv τ))))

theorem icode_eq (σ : Perm (7 + 8)) (τ : Perm 7) {s : List Nat} (hs : CM 7 8 s) (hl : s.length ≤ 2) :
    icode σ τ s = code (canon ((7 + 8) * 7) (s.map (phi (Perm.inv σ) (Perm.inv τ)))) := by
  unfold icode
  rw [canon_short (N := (7 + 8) * 7)]
  · intro x hx; obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; exact phi_lt _ _ (CM_lt hs hv)
  · exact nodup_map_on _ (CM_nodup hs) (fun x hx y hy h => phi_inj _ _ (CM_lt hs hx) (CM_lt hs hy) h)
  · simpa using hl

theorem relab_par {e : Nat} (he : e = 1 ∨ e = 2) (σ : Perm (7 + 8)) (τ : Perm 7) (F : List Nat → Int)
    (S : List (List Nat)) (hS : ∀ s ∈ S, CM 7 8 s ∧ s.length = e)
    (hF : ∀ x, CM 7 8 x → x.length = e → (2 : Int) ∣ F x - ((S.map code).count (code x) : Int))
    {m : List Nat} (hm : CM 7 8 m) (hl : m.length = e) :
    (2 : Int) ∣ relab σ τ F m - ((S.map (icode σ τ)).count (code m) : Int) := by
  have he2 : e ≤ 2 := by omega
  obtain ⟨hcm, hcl⟩ := CM_image σ τ hm
  have h := hF _ hcm (hcl.trans hl)
  unfold relab
  suffices e : (S.map code).count (code (canon ((7 + 8) * 7) (m.map (phi σ τ)))) =
      (S.map (icode σ τ)).count (code m) by rw [← e]; exact h
  rw [List.count_eq_countP, List.count_eq_countP, List.countP_map, List.countP_map]
  apply List.countP_congr
  intro s hs
  obtain ⟨hsc, hsl⟩ := hS s hs
  have hi := CM_image (Perm.inv σ) (Perm.inv τ) hsc
  simp only [Function.comp, beq_iff_eq]
  rw [icode_eq σ τ hsc (by omega)]
  constructor
  · intro hc
    have := code_inj he hsc hsl hcm (hcl.trans hl) hc
    rw [this, back (σ := Perm.inv σ) (τ := Perm.inv τ) (fun x _ => σ.gf x (by omega))
      (fun x _ => τ.gf x (by omega)) hm]
  · intro hc
    have := code_inj he hi.1 (hi.2.trans hsl) hm hl hc
    rw [← this, back (σ := σ) (τ := τ) (fun x _ => σ.fg x (by omega)) (fun x _ => τ.fg x (by omega)) hsc]

/-! ## Line sums as code sums -/

/-- Value at a code: the link constant at `K`, the function at the decoded matching elsewhere. -/
def R (e : Nat) (r : List Nat → Int) (κ : Int) (c : Nat) : Int := if c = K then κ else r (dec e c)

def lcodes (g : List Nat) (row : Bool) (idx : Nat) : List Nat :=
  if row then (List.range 7).filterMap (fun t =>
      if isMatch 7 (var 7 idx t :: g) then some (code (fcanon (var 7 idx t :: g))) else none)
  else (List.range 15).filterMap (fun t =>
      if isMatch 7 (var 7 t idx :: g) then some (code (fcanon (var 7 t idx :: g))) else none)

def lineOK (e : Nat) (l : List Nat × Bool × Nat) : Bool :=
  l.1.length + 1 == e && l.1.all (fun v => decide (v < 105)) &&
    (if l.2.1 then decide (l.2.2 < 15) && l.1.all (fun v => v / 7 != l.2.2)
     else decide (l.2.2 < 7) && l.1.all (fun v => v % 7 != l.2.2))

theorem rsum_fm (F : Nat → Int) (P : Nat → Bool) (h : Nat → Nat) : ∀ M : Nat,
    rsum M (fun t => if P t = true then F (h t) else 0) =
      ev F ((List.range M).filterMap (fun t => if P t = true then some (h t) else none))
  | 0 => rfl
  | M + 1 => by
    rw [List.range_succ, List.filterMap_append]
    show rsum M _ + _ = _
    rw [rsum_fm F P h M]
    unfold ev; simp only [List.map_append, List.sum_append]
    congr 1
    by_cases hP : P M = true <;> simp [hP]

/-- Small canonical-matching facts for `v :: g` with `g` of length `≤ 1` and `v` free. -/
theorem cm_cons {g : List Nat} {v : Nat} (hg : ∀ w ∈ g, w < 105) (hg1 : g.length ≤ 1) (hv : v < 105)
    (hvg : v ∉ g) (hm : isMatch 7 (v :: g) = true) :
    CM 7 8 (fcanon (v :: g)) ∧ canon ((7 + 8) * 7) (v :: g) = fcanon (v :: g) ∧
      (fcanon (v :: g)).length = g.length + 1 := by
  have hl : ∀ x ∈ v :: g, x < (7 + 8) * 7 := by
    intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact hv; exact hg x hx
  have hnd : (v :: g).Nodup := by
    rw [List.nodup_cons]; refine ⟨hvg, ?_⟩
    match g, hg1 with
    | [], _ => simp
    | [_], _ => simp
  have hc := canon_short hl hnd (by simp; omega)
  have hlen : (fcanon (v :: g)).length = g.length + 1 := by
    rw [← hc, canon_len_eq hnd hl]; simp
  refine ⟨⟨?_, ?_⟩, hc, hlen⟩
  · rw [← hc]; exact canon_idem _
  · rw [← hc, isMatch_congr 7 (canon _ (v :: g)) (v :: g) (mem_canon' hl)]; exact hm

theorem line_ev {e : Nat} (he : e = 1 ∨ e = 2) (r : List Nat → Int) (κ : Int) {l : List Nat × Bool × Nat}
    (hl : lineOK e l = true) :
    CM 7 8 l.1 ∧ l.1.length + 1 = e ∧
    (l.2.1 = true → l.2.2 < 7 + 8 ∧ pfree 7 l.1 l.2.2 ∧ rowS 7 8 r l.1 l.2.2 = ev (R e r κ) (lcodes l.1 true l.2.2)) ∧
    (l.2.1 = false → l.2.2 < 7 ∧ hfree 7 l.1 l.2.2 ∧ colS 7 8 r l.1 l.2.2 = ev (R e r κ) (lcodes l.1 false l.2.2)) := by
  obtain ⟨g, row, idx⟩ := l
  have hrc : (row = true → idx < 15 ∧ ∀ v ∈ g, v / 7 ≠ idx) ∧ (row = false → idx < 7 ∧ ∀ v ∈ g, v % 7 ≠ idx) := by
    cases row <;> simp [lineOK] at hl <;> simp <;> exact ⟨hl.2.1, hl.2.2⟩
  simp only [lineOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨hlen, hlt⟩, -⟩ := hl
  simp only at hlen hlt hrc ⊢
  have hg1 : g.length ≤ 1 := by omega
  have hcm : CM 7 8 g := by
    match g, hg1 with
    | [], _ => exact ⟨canon_nil' _, rfl⟩
    | [w], _ =>
      refine ⟨?_, by simp [isMatch, cfl]⟩
      rw [canon_one']; simp [show w < (7 + 8) * 7 from hlt w (by simp)]
  -- generic term rewriting
  have term : ∀ v, v < 105 → v ∉ g → (if isMatch 7 (v :: g) = true then r (canon ((7 + 8) * 7) (v :: g)) else 0) =
      (if isMatch 7 (v :: g) = true then R e r κ (code (fcanon (v :: g))) else 0) := by
    intro v hv hvg
    by_cases hm : isMatch 7 (v :: g) = true
    · obtain ⟨hc, hcan, hfl⟩ := cm_cons hlt hg1 hv hvg hm
      have := code_pt he hc (by rw [hfl]; exact hlen)
      simp only [hm, if_true, R, this.2.1, if_false, this.2.2.2, hcan]
    · simp [hm]
  refine ⟨hcm, hlen, ?_, ?_⟩
  · intro hrow; subst hrow
    obtain ⟨hi, hfr⟩ := hrc.1 rfl
    refine ⟨hi, fun v hv => by have := hfr v hv; simpa using this, ?_⟩
    unfold rowS lineS lcodes
    rw [rsum_congr 7 _ (fun t => if isMatch 7 (var 7 idx t :: g) = true then R e r κ (code (fcanon (var 7 idx t :: g))) else 0)
      (fun t ht => term _ (var_lt 7 8 idx t hi ht) (fun hm => by
        have := hfr _ hm; rw [var_div _ _ _ ht] at this; simp at this))]
    exact rsum_fm (R e r κ) (fun t => isMatch 7 (var 7 idx t :: g)) (fun t => code (fcanon (var 7 idx t :: g))) 7
  · intro hrow; subst hrow
    obtain ⟨hj, hfr⟩ := hrc.2 rfl
    refine ⟨hj, fun v hv => by have := hfr v hv; simpa using this, ?_⟩
    unfold colS lineS lcodes
    rw [rsum_congr (7 + 8) _ (fun t => if isMatch 7 (var 7 t idx :: g) = true then R e r κ (code (fcanon (var 7 t idx :: g))) else 0)
      (fun t ht => term _ (var_lt 7 8 t idx ht hj) (fun hm => by
        have := hfr _ hm; rw [var_mod _ _ _ hj] at this; simp at this))]
    exact rsum_fm (R e r κ) (fun t => isMatch 7 (var 7 t idx :: g)) (fun t => code (fcanon (var 7 t idx :: g))) 15

theorem lcodes_lt {e : Nat} (he : e = 1 ∨ e = 2) {l : List Nat × Bool × Nat} (hl : lineOK e l = true) :
    ∀ c ∈ lcodes l.1 l.2.1 l.2.2, c < K := by
  obtain ⟨g, row, idx⟩ := l
  have hrc : (row = true → idx < 15 ∧ ∀ v ∈ g, v / 7 ≠ idx) ∧ (row = false → idx < 7 ∧ ∀ v ∈ g, v % 7 ≠ idx) := by
    cases row <;> simp [lineOK] at hl <;> simp <;> exact ⟨hl.2.1, hl.2.2⟩
  simp only [lineOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨hlen, hlt⟩, -⟩ := hl
  simp only at hlen hlt hrc ⊢
  have hg1 : g.length ≤ 1 := by omega
  have key : ∀ v, v < 105 → v ∉ g → isMatch 7 (v :: g) = true → code (fcanon (v :: g)) < K := by
    intro v hv hvg hm
    obtain ⟨hc, -, hfl⟩ := cm_cons hlt hg1 hv hvg hm
    exact (code_pt he hc (by rw [hfl]; exact hlen)).2.2.1
  intro c hc
  cases row
  · obtain ⟨hj, hfr⟩ := hrc.2 rfl
    simp only [lcodes, Bool.false_eq_true, if_false] at hc
    obtain ⟨t, ht, ht'⟩ := List.mem_filterMap.mp hc
    rw [List.mem_range] at ht
    split at ht'
    · next hm =>
      simp only [Option.some.injEq] at ht'; subst ht'
      exact key _ (var_lt 7 8 _ _ ht hj) (fun hm' => by
        have := hfr _ hm'; rw [var_mod _ _ _ hj] at this; exact this rfl) hm
    · simp at ht'
  · obtain ⟨hi, hfr⟩ := hrc.1 rfl
    simp only [lcodes, if_true] at hc
    obtain ⟨t, ht, ht'⟩ := List.mem_filterMap.mp hc
    rw [List.mem_range] at ht
    split at ht'
    · next hm =>
      simp only [Option.some.injEq] at ht'; subst ht'
      exact key _ (var_lt 7 8 _ _ hi ht) (fun hm' => by
        have := hfr _ hm'; rw [var_div _ _ _ ht] at this; exact this rfl) hm
    · simp at ht'

end Programme.«20261027-1434-proof-complexity».PeelBase
