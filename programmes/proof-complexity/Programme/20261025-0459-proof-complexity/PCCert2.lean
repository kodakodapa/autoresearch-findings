import Programme.«20261025-0459-proof-complexity».PCCert

/-!
# Indexed R-operator certificates (fast kernel check)

Same argument as `Work.PCCert.cert_sound`, with monomials addressed by an index: entry `i` holds
its monomial `mon`, the vector `row = R(m_i)` (indices), `dn` (for `x ∈ mon`, the index of
`mon.erase x`) and `up` (for `x`, the index of the monomial `t` with `t.erase x = mon`, if
listed). `dn` and `up` are checked to be mutually inverse, so `R(x · m_s)` is a lookup. Entries are
listed in `ES` (keys `0..N-1`) and found by key in a binary tree `T`.
-/

namespace Programme.«20261025-0459-proof-complexity».PCCert2

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».FinDiff Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».PCCert (lsum lsum_add lsum_mul lsum_congr lsum_dvd lsum_zero lsum_sub lsum_swap pv eval_indep)

structure Ent where
  mon : List Nat
  row : List (Int × Nat)
  dn : List (Nat × Nat)
  up : List (Nat × Nat)
deriving DecidableEq

inductive Tr where
  | lf : Tr
  | nd : Tr → Nat → Ent → Tr → Tr

def dflt : Ent := ⟨[], [], [], []⟩

def Tr.find : Tr → Nat → Ent
  | .lf, _ => dflt
  | .nd l k e r, i => if i < k then l.find i else if k < i then r.find i else e

def lk : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (a, b) :: l, x => if a = x then some b else lk l x

theorem lk_mem {l : List (Nat × Nat)} {x t : Nat} (h : lk l x = some t) : (x, t) ∈ l := by
  induction l with
  | nil => simp [lk] at h
  | cons ab l ih =>
    obtain ⟨a, b⟩ := ab
    simp only [lk] at h
    split at h
    · rename_i hax; cases h; subst hax; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

abbrev V := List (Int × Nat)

def coef (v : V) (u : Nat) : Int := lsum v (fun e => if e.2 = u then e.1 else 0)

def smul (c : Int) (v : V) : V := if c = 0 then [] else v.map fun e => (c * e.1, e.2)

def vsum {α : Type} : List α → (α → V) → V
  | [], _ => []
  | a :: l, F => F a ++ vsum l F

theorem coef_nil (u : Nat) : coef [] u = 0 := rfl

theorem coef_append (v w : V) (u : Nat) : coef (v ++ w) u = coef v u + coef w u := by
  induction v with
  | nil => simp [coef, lsum]
  | cons e v ih => simp only [List.cons_append, coef, lsum] at ih ⊢; rw [ih]; omega

theorem coef_smul (c : Int) (v : V) (u : Nat) : coef (smul c v) u = c * coef v u := by
  by_cases hc : c = 0
  · subst hc; simp [smul, coef, lsum]
  have : smul c v = v.map fun e => (c * e.1, e.2) := if_neg hc
  rw [this]; clear this
  induction v with
  | nil => simp [coef, lsum]
  | cons e v ih =>
    simp only [List.map_cons, coef, lsum] at ih ⊢
    rw [ih, Int.mul_add]; congr 1; split <;> simp

theorem coef_vsum {α : Type} (l : List α) (F : α → V) (u : Nat) :
    coef (vsum l F) u = lsum l (fun a => coef (F a) u) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [vsum, lsum, coef_append, ih]

/-! Accumulating a vector in a binary trie keyed by `0 | 2j+1 | 2j+2`, for a fast zero test. -/

inductive BT where
  | lf : BT
  | nd : Int → BT → BT → BT

def BT.get : Nat → BT → Nat → Int
  | 0, _, _ => 0
  | _ + 1, .lf, _ => 0
  | f + 1, .nd v l r, k => if k = 0 then v else if k % 2 = 1 then BT.get f l (k / 2) else BT.get f r (k / 2 - 1)

def BT.add : Nat → BT → Nat → Int → BT
  | 0, t, _, _ => t
  | f + 1, .lf, k, c =>
    if k = 0 then .nd c .lf .lf else if k % 2 = 1 then .nd 0 (BT.add f .lf (k / 2) c) .lf
    else .nd 0 .lf (BT.add f .lf (k / 2 - 1) c)
  | f + 1, .nd v l r, k, c =>
    if k = 0 then .nd (v + c) l r else if k % 2 = 1 then .nd v (BT.add f l (k / 2) c) r
    else .nd v l (BT.add f r (k / 2 - 1) c)

def BT.allZero (p : Nat) : BT → Bool
  | .lf => true
  | .nd v l r => v % (p : Int) == 0 && BT.allZero p l && BT.allZero p r

theorem BT.get_lf (f u : Nat) : BT.get f .lf u = 0 := by cases f <;> rfl

theorem BT.get_add (f : Nat) (t : BT) (k : Nat) (c : Int) (hk : k + 1 < 2 ^ f) (u : Nat) :
    BT.get f (BT.add f t k c) u = BT.get f t u + if u = k then c else 0 := by
  induction f generalizing t k u with
  | zero => simp at hk
  | succ f ih =>
    have hp : 2 ^ (f + 1) = 2 * 2 ^ f := by rw [Nat.pow_succ, Nat.mul_comm]
    -- the key bijection
    have key : ∀ u k : Nat, u ≠ 0 → k ≠ 0 →
        (u % 2 = 1 ∧ k % 2 = 1 ∧ (u / 2 = k / 2 ↔ u = k)) ∨
        (u % 2 = 0 ∧ k % 2 = 0 ∧ (u / 2 - 1 = k / 2 - 1 ↔ u = k)) ∨ (u % 2 ≠ k % 2 ∧ u ≠ k) := by
      intro u k hu hk; omega
    cases t with
    | lf =>
      simp only [BT.add, BT.get_lf, Int.zero_add]
      by_cases hk0 : k = 0
      · subst hk0; simp only [if_true]; unfold BT.get; by_cases hu : u = 0 <;> simp [hu, BT.get_lf]
      · rw [if_neg hk0]
        by_cases hk1 : k % 2 = 1
        · rw [if_pos hk1]; unfold BT.get
          by_cases hu : u = 0
          · subst hu; simp; omega
          · rw [if_neg hu]
            by_cases hu1 : u % 2 = 1
            · rw [if_pos hu1, ih .lf (k / 2) (by omega), BT.get_lf, Int.zero_add]
              by_cases h : u = k
              · subst h; simp
              · rw [if_neg (by omega), if_neg h]
            · rw [if_neg hu1, BT.get_lf, if_neg (by omega)]
        · rw [if_neg hk1]; unfold BT.get
          by_cases hu : u = 0
          · subst hu; simp; omega
          · rw [if_neg hu]
            by_cases hu1 : u % 2 = 1
            · rw [if_pos hu1, BT.get_lf, if_neg (by omega)]
            · rw [if_neg hu1, ih .lf (k / 2 - 1) (by omega), BT.get_lf, Int.zero_add]
              by_cases h : u = k
              · subst h; simp
              · rw [if_neg (by omega), if_neg h]
    | nd v l r =>
      simp only [BT.add]
      by_cases hk0 : k = 0
      · subst hk0; simp only [if_true]; unfold BT.get
        by_cases hu : u = 0
        · subst hu; simp
        · simp [hu]
      · rw [if_neg hk0]
        by_cases hk1 : k % 2 = 1
        · rw [if_pos hk1]; unfold BT.get
          by_cases hu : u = 0
          · subst hu; simp; omega
          · rw [if_neg hu, if_neg hu]
            by_cases hu1 : u % 2 = 1
            · rw [if_pos hu1, if_pos hu1, ih l (k / 2) (by omega)]
              by_cases h : u = k
              · subst h; simp
              · rw [if_neg (by omega), if_neg h]
            · rw [if_neg hu1, if_neg hu1, if_neg (by omega)]; simp
        · rw [if_neg hk1]; unfold BT.get
          by_cases hu : u = 0
          · subst hu; simp; omega
          · rw [if_neg hu, if_neg hu]
            by_cases hu1 : u % 2 = 1
            · rw [if_pos hu1, if_pos hu1, if_neg (by omega)]; simp
            · rw [if_neg hu1, if_neg hu1, ih r (k / 2 - 1) (by omega)]
              by_cases h : u = k
              · subst h; simp
              · rw [if_neg (by omega), if_neg h]

theorem BT.allZero_get (p f : Nat) (t : BT) (h : BT.allZero p t = true) (u : Nat) :
    (p : Int) ∣ BT.get f t u := by
  induction f generalizing t u with
  | zero => exact ⟨0, by simp [BT.get]⟩
  | succ f ih =>
    cases t with
    | lf => exact ⟨0, by simp [BT.get]⟩
    | nd v l r =>
      simp only [BT.allZero, Bool.and_eq_true, beq_iff_eq] at h
      unfold BT.get
      split
      · exact Int.dvd_of_emod_eq_zero h.1.1
      · split
        · exact ih l h.1.2 _
        · exact ih r h.2 _

def fuel : Nat := 24

def build (v : V) : BT := v.foldl (fun t e => BT.add fuel t e.2 e.1) .lf

theorem get_foldl (v : V) (t : BT) (hv : ∀ e ∈ v, e.2 + 1 < 2 ^ fuel) (u : Nat) :
    BT.get fuel (v.foldl (fun t e => BT.add fuel t e.2 e.1) t) u = BT.get fuel t u + coef v u := by
  induction v generalizing t with
  | nil => simp [coef, lsum]
  | cons e v ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun e' he' => hv e' (List.mem_cons_of_mem _ he')),
      BT.get_add fuel t e.2 e.1 (hv e List.mem_cons_self)]
    simp only [coef, lsum]
    by_cases h : u = e.2
    · rw [if_pos h, if_pos h.symm]; omega
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]; omega

def zeroCheck (p : Nat) (v : V) : Bool :=
  v.all (fun e => decide (e.2 + 1 < 2 ^ fuel)) && BT.allZero p (build v)

theorem zeroCheck_spec (p : Nat) (v : V) (h : zeroCheck p v = true) (u : Nat) :
    (p : Int) ∣ coef v u := by
  simp only [zeroCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  have := BT.allZero_get p fuel _ h.2 u
  unfold build at this
  rw [get_foldl v .lf h.1, BT.get_lf, Int.zero_add] at this
  exact this

/-- Sum over a keyed list with distinct keys, picking key `j`. -/
theorem lsum_key (ES : List (Nat × Ent)) (hnd : (ES.map (·.1)).Nodup) (j : Nat) (e : Ent)
    (hj : (j, e) ∈ ES) (F : Nat × Ent → Int) :
    lsum ES (fun ie => if ie.1 = j then F ie else 0) = F (j, e) := by
  induction ES with
  | nil => simp at hj
  | cons a ES ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [lsum]
    rcases List.mem_cons.mp hj with h | h
    · subst h
      rw [if_pos rfl, lsum_zero ES _ (fun b hb => by
        have hb1 : b.1 ∈ ES.map (·.1) := List.mem_map_of_mem hb
        rw [if_neg (fun (hb' : b.1 = j) => hnd.1 (hb' ▸ hb1))])]; omega
    · have hne : a.1 ≠ j := fun hh => hnd.1 (hh ▸ List.mem_map_of_mem (f := (·.1)) h)
      rw [if_neg hne, ih hnd.2 h]; omega

structure Cert where
  ES : List (Nat × Ent)
  T : Tr
  nv : Nat

namespace Cert

def N (C : Cert) : Nat := C.ES.length
def E (C : Cert) (i : Nat) : Ent := C.T.find i

/-- `R(x · m_s)`. -/
def Nv (C : Cert) (x s : Nat) : V :=
  (match lk (C.E s).up x with
    | some t => (C.E t).row
    | none => []) ++
  (if x ∈ (C.E s).mon then (C.E s).row else [])

def Rv (C : Cert) (g : (Nat → Bool) → Int) : V := vsum C.ES (fun ie => smul (cf g ie.2.mon) ie.2.row)

def RvA (C : Cert) (P : Poly Nat) : V :=
  vsum C.ES (fun ie => if ie.2.mon.all (· ∈ pv P) then smul (cf (fun a => P.eval a) ie.2.mon) ie.2.row
    else [])

def okMon (C : Cert) (ie : Nat × Ent) : Bool :=
  decide ie.2.mon.Nodup && decide ((ie.1 = 0) ↔ ie.2.mon = []) &&
  ie.2.row.all (fun e => decide (e.2 < C.N)) &&
  ie.2.mon.all (fun x => decide (x < C.nv) &&
    match lk ie.2.dn x with
    | some j => decide (j < C.N) && decide ((C.E j).mon = ie.2.mon.erase x) &&
        decide (lk (C.E j).up x = some ie.1)
    | none => false) &&
  ie.2.up.all (fun xt => decide (xt.2 < C.N) && decide (xt.1 ∈ (C.E xt.2).mon) &&
    decide (lk (C.E xt.2).dn xt.1 = some ie.1))

def check (p D : Nat) (A : List (Poly Nat)) (C : Cert) : Bool :=
  decide (C.ES.map (·.1) = List.range C.N) && decide (0 < C.N) &&
  C.ES.all (fun ie => decide (C.T.find ie.1 = ie.2)) &&
  C.ES.all C.okMon &&
  A.all (fun P => !decide (P.deg ≤ D) || zeroCheck p (C.RvA P)) &&
  (List.range C.nv).all (fun x => C.ES.all (fun s => !decide (s.2.mon.length < D) ||
    zeroCheck p (C.Nv x s.1 ++ smul (-1) (vsum s.2.row (fun e => smul e.1 (C.Nv x e.2)))))) &&
  (C.E 0).row.any (fun e => coef (C.E 0).row e.2 % (p : Int) != 0)

theorem coef_Rv (C : Cert) (g : (Nat → Bool) → Int) (u : Nat) :
    coef (C.Rv g) u = lsum C.ES (fun ie => cf g ie.2.mon * coef ie.2.row u) := by
  unfold Rv; rw [coef_vsum]; simp only [coef_smul]

theorem coef_RvA (C : Cert) (P : Poly Nat) (u : Nat) :
    coef (C.RvA P) u = coef (C.Rv (fun a => P.eval a)) u := by
  unfold RvA Rv; rw [coef_vsum, coef_vsum]
  refine lsum_congr _ _ _ (fun t _ => ?_)
  split
  · rfl
  · rename_i h
    rw [coef_nil, coef_smul]
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    have : ∃ y ∈ t.2.mon, y ∉ pv P := by
      apply Classical.byContradiction; intro hn; apply h; intro x hx
      apply Classical.byContradiction; intro hxn; exact hn ⟨x, hx, hxn⟩
    obtain ⟨y, hy, hyP⟩ := this
    have : cf (fun a => P.eval a) t.2.mon = 0 := by
      unfold cf; exact dt_mem_zero (eval_indep P y hyP) _ hy z0
    rw [this, Int.zero_mul]

def Inv (p : Nat) (C : Cert) (g : (Nat → Bool) → Int) : Prop := ∀ u, (p : Int) ∣ coef (C.Rv g) u

theorem sound (p D : Nat) (A : List (Poly Nat)) (C : Cert) (hc : check p D A C = true) :
    ¬ PPCRefutation p A D := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true, bne_iff_ne, ne_eq,
    List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨hkeys, hN⟩, hfind⟩, hok⟩, hax⟩, hmul⟩, hone⟩ := hc
  have hnd : (C.ES.map (·.1)).Nodup := by rw [hkeys]; exact List.nodup_range
  -- every index below `N` is a key, with entry `E j`
  have hmemE : ∀ j, j < C.N → (j, C.E j) ∈ C.ES := by
    intro j hj
    have : j ∈ C.ES.map (·.1) := by rw [hkeys]; exact List.mem_range.mpr hj
    obtain ⟨ie, hie, rfl⟩ := List.mem_map.mp this
    have := hfind ie hie
    have he : C.E ie.1 = ie.2 := this
    rw [he]; exact hie
  have hEof : ∀ ie ∈ C.ES, C.E ie.1 = ie.2 := fun ie hie => hfind ie hie
  have hokE : ∀ ie ∈ C.ES, C.okMon ie = true := hok
  -- unpack `okMon`
  have hmon : ∀ ie ∈ C.ES, ie.2.mon.Nodup ∧ ((ie.1 = 0) ↔ ie.2.mon = []) ∧
      (∀ e ∈ ie.2.row, e.2 < C.N) ∧
      (∀ x ∈ ie.2.mon, x < C.nv ∧ ∃ j, lk ie.2.dn x = some j ∧ j < C.N ∧
        (C.E j).mon = ie.2.mon.erase x ∧ lk (C.E j).up x = some ie.1) ∧
      (∀ xt ∈ ie.2.up, xt.2 < C.N ∧ xt.1 ∈ (C.E xt.2).mon ∧ lk (C.E xt.2).dn xt.1 = some ie.1) := by
    intro ie hie
    have h := hokE ie hie
    simp only [okMon, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    refine ⟨h1, h2, h3, fun x hx => ?_, fun xt hxt => ⟨(h5 xt hxt).1.1, (h5 xt hxt).1.2, (h5 xt hxt).2⟩⟩
    have h4x := h4 x hx
    obtain ⟨hxn, h4x⟩ := h4x
    refine ⟨hxn, ?_⟩
    revert h4x
    cases hl : lk ie.2.dn x with
    | none => simp
    | some j =>
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rintro ⟨⟨a, b⟩, c⟩; exact ⟨j, rfl, a, b, c⟩
  have key : ∀ g, PPCDerivable p A D g → C.Inv p g := by
    intro g hg
    induction hg with
    | ax P hP hd =>
      intro u
      rcases hax P hP with h | h
      · exact absurd hd h
      · have := zeroCheck_spec p _ h u
        rwa [coef_RvA C P u] at this
    | lin f g u v _ _ ihf ihg =>
      intro w
      rw [coef_Rv]
      simp only [cf_lin, Int.add_mul, Int.mul_assoc]
      rw [lsum_add, lsum_mul, lsum_mul, ← coef_Rv, ← coef_Rv]
      exact Int.dvd_add (dvd_mul_of u (ihf w)) (dvd_mul_of v (ihg w))
    | congr f g _ hfg ih =>
      intro u
      have e : coef (C.Rv f) u = coef (C.Rv g) u +
          lsum C.ES (fun ie => (cf f ie.2.mon - cf g ie.2.mon) * coef ie.2.row u) := by
        rw [coef_Rv, coef_Rv, ← lsum_add]
        exact lsum_congr _ _ _ (fun t _ => by rw [Int.sub_mul]; omega)
      rw [e]
      exact Int.dvd_add (ih u) (lsum_dvd _ _ _ (fun t _ =>
        Int.dvd_trans (cf_congr p f g hfg _) (Int.dvd_mul_right _ _)))
    | mul x g d _ hcd hdD ih =>
      intro u
      have s1 : coef (C.Rv (fun a => xv x a * g a)) u =
          lsum C.ES (fun ie => (if x ∈ ie.2.mon then cf g (ie.2.mon.erase x) + cf g ie.2.mon else 0) *
            coef ie.2.row u) := by
        rw [coef_Rv]
        exact lsum_congr _ _ _ (fun t ht => by rw [cf_mul x g _ (hmon t ht).1])
      by_cases hx : x < C.nv
      · -- step 2: regroup through `Nv`
        have s2 : lsum C.ES (fun ie => (if x ∈ ie.2.mon then cf g (ie.2.mon.erase x) + cf g ie.2.mon
              else 0) * coef ie.2.row u)
            = lsum C.ES (fun je => cf g je.2.mon * coef (C.Nv x je.1) u) := by
          -- the `up` part
          have hup : ∀ je ∈ C.ES, lsum C.ES (fun ie =>
                if x ∈ ie.2.mon ∧ lk ie.2.dn x = some je.1 then cf g je.2.mon * coef ie.2.row u else 0) =
              cf g je.2.mon * coef (match lk (C.E je.1).up x with
                | some t => (C.E t).row
                | none => []) u := by
            intro je hje
            rw [hEof je hje]
            cases hl : lk je.2.up x with
            | none =>
              simp only [coef_nil, Int.mul_zero]
              refine lsum_zero _ _ (fun ie hie => ?_)
              rw [if_neg]
              rintro ⟨hxm, hdn⟩
              obtain ⟨_, j, hj, _, _, hupj⟩ := (hmon ie hie).2.2.2.1 x hxm
              rw [hdn] at hj; cases hj
              rw [hEof je hje, hl] at hupj; cases hupj
            | some t =>
              have hmt := (hmon je hje).2.2.2.2 (x, t) (lk_mem hl)
              have ht : (t, C.E t) ∈ C.ES := hmemE t hmt.1
              rw [← lsum_key C.ES hnd t (C.E t) ht (fun ie => cf g je.2.mon * coef ie.2.row u)]
              refine lsum_congr _ _ _ (fun ie hie => ?_)
              by_cases hit : ie.1 = t
              · have hie2 : ie.2 = C.E t := by rw [← hit, hEof ie hie]
                rw [if_pos hit, if_pos]
                rw [hie2]; exact ⟨hmt.2.1, hmt.2.2⟩
              · rw [if_neg hit, if_neg]
                rintro ⟨hxm, hdn⟩
                obtain ⟨_, j, hj, _, _, hupj⟩ := (hmon ie hie).2.2.2.1 x hxm
                rw [hdn] at hj; cases hj
                rw [hEof je hje, hl] at hupj; cases hupj; exact hit rfl
          have e1 : ∀ je ∈ C.ES, cf g je.2.mon * coef (C.Nv x je.1) u =
              lsum C.ES (fun ie =>
                if x ∈ ie.2.mon ∧ lk ie.2.dn x = some je.1 then cf g je.2.mon * coef ie.2.row u else 0) +
              (if x ∈ je.2.mon then cf g je.2.mon * coef je.2.row u else 0) := by
            intro je hje
            rw [hup je hje, Nv, coef_append, Int.mul_add, hEof je hje]
            congr 1
            by_cases hxm : x ∈ je.2.mon
            · rw [if_pos hxm, if_pos hxm]
            · rw [if_neg hxm, if_neg hxm, coef_nil, Int.mul_zero]
          rw [lsum_congr _ _ _ e1, lsum_add, lsum_swap]
          have e2 : ∀ ie ∈ C.ES, lsum C.ES (fun je =>
                if x ∈ ie.2.mon ∧ lk ie.2.dn x = some je.1 then cf g je.2.mon * coef ie.2.row u else 0) =
              if x ∈ ie.2.mon then cf g (ie.2.mon.erase x) * coef ie.2.row u else 0 := by
            intro ie hie
            by_cases hxm : x ∈ ie.2.mon
            · rw [if_pos hxm]
              obtain ⟨_, j, hj, hjN, hjm, _⟩ := (hmon ie hie).2.2.2.1 x hxm
              rw [← hjm, ← lsum_key C.ES hnd j (C.E j) (hmemE j hjN)
                (fun je => cf g je.2.mon * coef ie.2.row u)]
              refine lsum_congr _ _ _ (fun je hje => ?_)
              by_cases hjj : je.1 = j
              · rw [if_pos ⟨hxm, by rw [hj, hjj]⟩, if_pos hjj]
              · rw [if_neg (fun h => hjj (by have h2 := h.2; rw [hj] at h2; exact (Option.some.inj h2).symm)), if_neg hjj]
            · rw [if_neg hxm]; exact lsum_zero _ _ (fun je _ => by rw [if_neg (fun h => hxm h.1)])
          rw [lsum_congr _ _ _ e2, ← lsum_add]
          exact lsum_congr _ _ _ (fun t _ => by split <;> simp [Int.add_mul])
        rw [s1, s2]
        -- step 3: the certificate identity, row by row
        have s3 : (p : Int) ∣ lsum C.ES (fun s => cf g s.2.mon * coef (C.Nv x s.1) u) -
            lsum C.ES (fun s => cf g s.2.mon *
              coef (vsum s.2.row (fun e => smul e.1 (C.Nv x e.2))) u) := by
          rw [← lsum_sub]
          refine lsum_dvd _ _ _ (fun s hs => ?_)
          rw [← Int.mul_sub]
          by_cases hsD : s.2.mon.length < D
          · rcases hmul x hx s hs with h | h
            · exact absurd hsD h
            · have := zeroCheck_spec p _ h u
              rw [coef_append, coef_smul, Int.neg_one_mul, ← Int.sub_eq_add_neg] at this
              exact Int.dvd_trans this (Int.dvd_mul_left _ _)
          · exact Int.dvd_trans (cf_cubeDeg hcd _ (hmon s hs).1 (by omega)) (Int.dvd_mul_right _ _)
        -- step 4: a combination of `Inv g`
        have s4 : lsum C.ES (fun s => cf g s.2.mon *
              coef (vsum s.2.row (fun e => smul e.1 (C.Nv x e.2))) u) =
            lsum C.ES (fun je => coef (C.Nv x je.1) u * coef (C.Rv g) je.1) := by
          have row_sum : ∀ s ∈ C.ES, coef (vsum s.2.row (fun e => smul e.1 (C.Nv x e.2))) u =
              lsum C.ES (fun je => coef s.2.row je.1 * coef (C.Nv x je.1) u) := by
            intro s hs
            rw [coef_vsum]; simp only [coef_smul]
            have hr := (hmon s hs).2.2.1
            clear hs
            revert hr
            induction s.2.row with
            | nil => intro _; simp only [lsum]; exact (lsum_zero _ _ (fun je _ => by simp [coef, lsum])).symm
            | cons e r ihr =>
              intro hr
              simp only [lsum]
              rw [ihr (fun e' he' => hr e' (List.mem_cons_of_mem _ he'))]
              have : ∀ je : Nat × Ent, coef (e :: r) je.1 * coef (C.Nv x je.1) u =
                  (if je.1 = e.2 then e.1 * coef (C.Nv x je.1) u else 0) +
                    coef r je.1 * coef (C.Nv x je.1) u := by
                intro je; simp only [coef, lsum]
                by_cases h : e.2 = je.1
                · rw [if_pos h, if_pos h.symm, Int.add_mul]
                · rw [if_neg h, if_neg (fun h' => h h'.symm)]; simp
              rw [lsum_congr _ _ _ (fun je _ => this je), lsum_add,
                lsum_key C.ES hnd e.2 (C.E e.2) (hmemE e.2 (hr e List.mem_cons_self))]
          rw [lsum_congr _ _ _ (fun s hs => by rw [row_sum s hs])]
          rw [lsum_congr _ _ _ (fun s _ => (lsum_mul _ _ _).symm), lsum_swap]
          refine lsum_congr _ _ _ (fun je _ => ?_)
          rw [coef_Rv, ← lsum_mul]
          exact lsum_congr _ _ _ (fun s _ => by
            rw [Int.mul_comm (coef (C.Nv x je.1) u), Int.mul_assoc, Int.mul_left_comm])
        have h4 : (p : Int) ∣ lsum C.ES (fun je => coef (C.Nv x je.1) u * coef (C.Rv g) je.1) :=
          lsum_dvd _ _ _ (fun w _ => Int.dvd_trans (ih w.1) (Int.dvd_mul_left _ _))
        rw [← s4] at h4
        have := Int.dvd_add s3 h4
        rwa [Int.sub_add_cancel] at this
      · -- `x` occurs in no listed monomial
        rw [s1, lsum_zero _ _ (fun ie hie => ?_)]
        · exact ⟨0, by simp⟩
        rw [if_neg (fun h => hx ((hmon ie hie).2.2.2.1 x h).1)]; simp
  intro hr
  have h1 := key _ hr
  obtain ⟨e, _, he⟩ := hone
  apply he
  have h0 : (0, C.E 0) ∈ C.ES := hmemE 0 hN
  have : coef (C.Rv (fun _ => 1)) e.2 = coef (C.E 0).row e.2 := by
    rw [coef_Rv, ← lsum_key C.ES hnd 0 (C.E 0) h0 (fun ie => coef ie.2.row e.2)]
    refine lsum_congr _ _ _ (fun ie hie => ?_)
    rw [cf_const]
    have := (hmon ie hie).2.1
    by_cases h : ie.1 = 0
    · rw [if_pos (this.mp h), if_pos h, Int.one_mul]
    · rw [if_neg (fun h' => h (this.mpr h')), if_neg h, Int.zero_mul]
  rw [← this]
  exact Int.emod_eq_zero_of_dvd (h1 e.2)

end Cert

end Programme.«20261025-0459-proof-complexity».PCCert2
