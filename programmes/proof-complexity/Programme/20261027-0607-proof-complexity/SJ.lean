import Programme.«20261027-0607-proof-complexity».LemKMain
import Programme.«20261026-1402-proof-complexity».ExtLin

/-!
# S_j: zero-link functions on `j`-matchings are spans of rectangle products when `j!` is a unit

Bridge from `Work.LemK` (functions on injective tuples) to `ExtLemma.Bal` (functions on canonical
matchings of `ontoFPHP n k`). A pair of tuples `(u, w)` (pigeons, holes) gives the matching
`mk n k j u w = canon (var n (u s) (w s) : s < j)`. A zero-link `f` gives `F u w = f (mk u w)`
(on valid hole tuples), whose pigeon-slot sums are column sums and whose hole-slot sums are row
sums of `f`. Lemma K over pigeons (values: functions of hole tuples), then over holes, writes
`F ≡ ∑ d · DP P u · DP Q w`. Summing over the `j!` orderings of a matching `g` turns `DP P u · DP Q w`
into the rectangle product `RP n j P Q g` (a permanent, `jp`), so `j! f ≡ ∑ d · RP`.
-/

namespace Programme.«20261027-0607-proof-complexity».SJ

open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum var)
open Programme.«20261025-1627-proof-complexity».MomGen (canon mem_canon canon_congr canon_nodup nodup_len)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt var_inj)
open Programme.«20261025-0459-proof-complexity».OntoSubst (var_div var_mod)
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin
open Programme.«20261027-0607-proof-complexity».LemK

/-- The everywhere-true ground set. -/
def allT : Nat → Bool := fun _ => true

/-- Edge list of the tuple pair. -/
def mkL (n j : Nat) (u w : Nat → Nat) : List Nat := (List.range j).map (fun s => var n (u s) (w s))

/-- The matching of the tuple pair. -/
def mk (n k j : Nat) (u w : Nat → Nat) : List Nat := canon ((n + k) * n) (mkL n j u w)

theorem mem_mkL {n j : Nat} {u w : Nat → Nat} {x : Nat} : x ∈ mkL n j u w ↔ ∃ s < j, x = var n (u s) (w s) := by
  unfold mkL; simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩

section
variable {n k j : Nat} {u w : Nat → Nat}

theorem mkL_lt (hu : Valid (n + k) allT j u) (hw : Valid n allT j w) : ∀ x ∈ mkL n j u w, x < (n + k) * n := by
  intro x hx; obtain ⟨s, hs, rfl⟩ := mem_mkL.mp hx
  exact var_lt n k _ _ (hu.1 s hs).1 (hw.1 s hs).1

theorem mkL_nodup (hu : Valid (n + k) allT j u) (hw : Valid n allT j w) : (mkL n j u w).Nodup := by
  unfold mkL List.Nodup
  rw [List.pairwise_map]
  have h := (List.nodup_range (n := j))
  unfold List.Nodup at h
  refine List.Pairwise.imp_of_mem (fun {s s'} hs hs' hne e => hne ?_) h
  rw [List.mem_range] at hs hs'
  exact hu.2.1 s hs s' hs' (var_inj n _ _ _ _ (hw.1 s hs).1 (hw.1 s' hs').1 e).1

theorem mem_mk (hu : Valid (n + k) allT j u) (hw : Valid n allT j w) {x : Nat} :
    x ∈ mk n k j u w ↔ ∃ s < j, x = var n (u s) (w s) := by
  unfold mk; rw [mem_canon' (mkL_lt hu hw), mem_mkL]

theorem mk_len (hu : Valid (n + k) allT j u) (hw : Valid n allT j w) : (mk n k j u w).length = j := by
  unfold mk; rw [canon_len_eq (mkL_nodup hu hw) (mkL_lt hu hw)]; simp [mkL]

theorem mk_CM (hu : Valid (n + k) allT j u) (hw : Valid n allT j w) : CM n k (mk n k j u w) := by
  refine ⟨canon_idem _, ?_⟩
  rw [isMatch_iff]
  intro x hx y hy
  obtain ⟨s, hs, rfl⟩ := (mem_mk hu hw).mp hx
  obtain ⟨s', hs', rfl⟩ := (mem_mk hu hw).mp hy
  unfold cfl
  rw [var_div n _ _ (hw.1 s hs).1, var_div n _ _ (hw.1 s' hs').1, var_mod n _ _ (hw.1 s hs).1,
    var_mod n _ _ (hw.1 s' hs').1]
  by_cases e : s = s'
  · subst e; simp
  · have h1 : u s ≠ u s' := fun h => e (hu.2.1 s hs s' hs' h)
    have h2 : w s ≠ w s' := fun h => e (hw.2.1 s hs s' hs' h)
    simp [h1, h2]

theorem mem_mk_skip (hu : Valid (n + k) allT (j + 1) u) (hw : Valid n allT (j + 1) w) {t : Nat} (ht : t ≤ j) {x : Nat} :
    x ∈ mk n k j (skip t u) (skip t w) ↔ ∃ s < j + 1, s ≠ t ∧ x = var n (u s) (w s) := by
  rw [mem_mk (valid_skip hu ht) (valid_skip hw ht)]
  unfold skip
  constructor
  · rintro ⟨r, hr, rfl⟩
    by_cases a : r < t
    · exact ⟨r, by omega, by omega, by simp [a]⟩
    · exact ⟨r + 1, by omega, by omega, by simp [a]⟩
  · rintro ⟨s, hs, hst, rfl⟩
    by_cases a : s < t
    · exact ⟨s, by omega, by simp [a]⟩
    · exact ⟨s - 1, by omega, by rw [if_neg (by omega), if_neg (by omega), show s - 1 + 1 = s by omega]⟩

end

theorem isMatch_cons (n x : Nat) (g : List Nat) :
    isMatch n (x :: g) = true ↔ isMatch n g = true ∧ ∀ y ∈ g, cfl n x y = false := by
  rw [isMatch_iff, isMatch_iff]
  constructor
  · intro h; exact ⟨fun a ha b hb => h a (by simp [ha]) b (by simp [hb]), fun y hy => h x (by simp) y (by simp [hy])⟩
  · rintro ⟨h1, h2⟩ a ha b hb
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · simp [cfl]
    · exact h2 b hb
    · rw [cfl_symm]; exact h2 a ha
    · exact h1 a ha b hb

open Classical in
/-- `F u w = f (mk u w)` on valid hole tuples. -/
noncomputable def Fof (n k j : Nat) (f : List Nat → Int) (u w : Nat → Nat) : Int :=
  if Valid n allT j w then f (mk n k j u w) else 0


section
variable {n k j : Nat}

/-- Pigeon-slot sums are column sums. -/
theorem sig_col (f : List Nat → Int) {u w : Nat → Nat} (hu : Valid (n + k) allT (j + 1) u)
    (hw : Valid n allT (j + 1) w) {t : Nat} (ht : t ≤ j) :
    sig (n + k) allT (j + 1) (Fof n k (j + 1) f) u t w = colS n k f (mk n k j (skip t u) (skip t w)) (w t) := by
  unfold sig colS lineS
  apply rsum_congr; intro a ha
  dsimp only
  have hn : 0 < n := by have := (hw.1 0 (by omega)).1; omega
  have hwt : w t < n := (hw.1 t (by omega)).1
  by_cases hf : Free (j + 1) u t a
  · have hv := valid_upd hu (by omega) ha rfl hf
    rw [if_pos ⟨rfl, hf⟩]
    have hm : isMatch n (var n a (w t) :: mk n k j (skip t u) (skip t w)) = true := by
      rw [isMatch_cons]
      refine ⟨(mk_CM (valid_skip hu ht) (valid_skip hw ht)).2, fun y hy => ?_⟩
      obtain ⟨s, hs, hst, rfl⟩ := (mem_mk_skip hu hw ht).mp hy
      have hws : w s < n := (hw.1 s hs).1
      unfold cfl
      rw [var_div n _ _ hwt, var_div n _ _ hws, var_mod n _ _ hwt, var_mod n _ _ hws]
      have h1 : a ≠ u s := fun e => hf s hs hst e.symm
      have h2 : w t ≠ w s := fun e => hst (hw.2.1 t (by omega) s hs e).symm
      simp [h1, h2]
    rw [if_pos hm]
    unfold Fof; rw [if_pos hw]
    congr 1
    unfold mk
    symm
    apply canon_congr; intro y hy
    rw [mem_mkL]
    constructor
    · intro h
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨t, by omega, by simp [upd]⟩
      · have h' := (mem_canon _ _ _).mp h
        obtain ⟨r, hr, hy'⟩ := mem_mkL.mp h'.1
        rw [hy']
        unfold skip
        by_cases c : r < t
        · exact ⟨r, by omega, by simp [upd, c, show r ≠ t by omega]⟩
        · exact ⟨r + 1, by omega, by simp [upd, c, show r + 1 ≠ t by omega]⟩
    · rintro ⟨s, hs, rfl⟩
      by_cases e : s = t
      · subst e; simp [upd]
      · simp only [List.mem_cons]; right
        have : var n (upd u t a s) (w s) = var n (u s) (w s) := by simp [upd, e]
        rw [this]; exact (mem_mk_skip hu hw ht).mpr ⟨s, hs, e, rfl⟩
  · rw [if_neg (fun h => hf h.2)]
    unfold Free at hf
    have : ∃ s, s < j + 1 ∧ s ≠ t ∧ u s = a := by
      apply Classical.byContradiction; intro hn'
      exact hf (fun s hs hst e => hn' ⟨s, hs, hst, e⟩)
    obtain ⟨s, hs, hst, hus⟩ := this
    have hm : isMatch n (var n a (w t) :: mk n k j (skip t u) (skip t w)) = false := by
      cases h : isMatch n (var n a (w t) :: mk n k j (skip t u) (skip t w))
      · rfl
      · rw [isMatch_cons] at h
        have hy := h.2 (var n (u s) (w s)) ((mem_mk_skip hu hw ht).mpr ⟨s, hs, hst, rfl⟩)
        have hws : w s < n := (hw.1 s hs).1
        unfold cfl at hy
        rw [var_div n _ _ hwt, var_div n _ _ hws, hus] at hy
        have h2 : var n a (w t) ≠ var n a (w s) := fun e =>
          hst (hw.2.1 t (by omega) s hs (var_inj n _ _ _ _ hwt hws e).2).symm
        simp [h2] at hy
    rw [hm]; rfl

/-- Hole-slot sums are row sums. -/
theorem sig_row (f : List Nat → Int) {u w : Nat → Nat} (hu : Valid (n + k) allT (j + 1) u)
    (hw : Valid n allT (j + 1) w) {t : Nat} (ht : t ≤ j) :
    sig n allT (j + 1) (fun w (_ : Unit) => Fof n k (j + 1) f u w) w t () =
      rowS n k f (mk n k j (skip t u) (skip t w)) (u t) := by
  unfold sig rowS lineS
  apply rsum_congr; intro b hb
  dsimp only
  have hut : u t < n + k := (hu.1 t (by omega)).1
  by_cases hf : Free (j + 1) w t b
  · have hv := valid_upd hw (by omega) hb rfl hf
    rw [if_pos ⟨rfl, hf⟩]
    have hm : isMatch n (var n (u t) b :: mk n k j (skip t u) (skip t w)) = true := by
      rw [isMatch_cons]
      refine ⟨(mk_CM (valid_skip hu ht) (valid_skip hw ht)).2, fun y hy => ?_⟩
      obtain ⟨s, hs, hst, rfl⟩ := (mem_mk_skip hu hw ht).mp hy
      have hws : w s < n := (hw.1 s hs).1
      unfold cfl
      rw [var_div n _ _ hb, var_div n _ _ hws, var_mod n _ _ hb, var_mod n _ _ hws]
      have h1 : b ≠ w s := fun e => hf s hs hst e.symm
      have h2 : u t ≠ u s := fun e => hst (hu.2.1 t (by omega) s hs e).symm
      simp [h1, h2]
    rw [if_pos hm]
    unfold Fof; rw [if_pos hv]
    congr 1
    unfold mk
    symm
    apply canon_congr; intro y hy
    rw [mem_mkL]
    constructor
    · intro h
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨t, by omega, by simp [upd]⟩
      · have h' := (mem_canon _ _ _).mp h
        obtain ⟨r, hr, hy'⟩ := mem_mkL.mp h'.1
        rw [hy']
        unfold skip
        by_cases c : r < t
        · exact ⟨r, by omega, by simp [upd, c, show r ≠ t by omega]⟩
        · exact ⟨r + 1, by omega, by simp [upd, c, show r + 1 ≠ t by omega]⟩
    · rintro ⟨s, hs, rfl⟩
      by_cases e : s = t
      · subst e; simp [upd]
      · simp only [List.mem_cons]; right
        have : var n (u s) (upd w t b s) = var n (u s) (w s) := by simp [upd, e]
        rw [this]; exact (mem_mk_skip hu hw ht).mpr ⟨s, hs, e, rfl⟩
  · rw [if_neg (fun h => hf h.2)]
    unfold Free at hf
    have : ∃ s, s < j + 1 ∧ s ≠ t ∧ w s = b := by
      apply Classical.byContradiction; intro hn'
      exact hf (fun s hs hst e => hn' ⟨s, hs, hst, e⟩)
    obtain ⟨s, hs, hst, hws'⟩ := this
    have hm : isMatch n (var n (u t) b :: mk n k j (skip t u) (skip t w)) = false := by
      cases h : isMatch n (var n (u t) b :: mk n k j (skip t u) (skip t w))
      · rfl
      · rw [isMatch_cons] at h
        have hy := h.2 (var n (u s) (w s)) ((mem_mk_skip hu hw ht).mpr ⟨s, hs, hst, rfl⟩)
        rw [hws'] at hy
        unfold cfl at hy
        rw [var_mod n _ _ hb, var_mod n _ _ hb] at hy
        have h2 : var n (u t) b ≠ var n (u s) b := fun e =>
          hst (hu.2.1 t (by omega) s hs (var_inj n _ _ _ _ hb hb e).1).symm
        simp [h2] at hy
    rw [hm]; rfl

end

/-! ## Both slot conditions from zero links -/

section
variable {p n k j : Nat}

theorem KC_pig (f : List Nat → Int) (hf : Bal p n k f (fun _ => 0) j) :
    KC (p : Int) (n + k) allT (j + 1) (Fof n k (j + 1) f) := by
  intro u hu t ht w
  by_cases hw : Valid n allT (j + 1) w
  · rw [sig_col f hu hw (by omega : t ≤ j)]
    have hg := hf (mk n k j (skip t u) (skip t w)) (mk_CM (valid_skip hu (by omega)) (valid_skip hw (by omega)))
      (mk_len (valid_skip hu (by omega)) (valid_skip hw (by omega)))
    have := hg.2 (w t) (hw.1 t ht).1 (fun v hv => by
      obtain ⟨s, hs, hst, rfl⟩ := (mem_mk_skip hu hw (by omega : t ≤ j)).mp hv
      rw [var_mod n _ _ (hw.1 s hs).1]
      exact fun e => hst (hw.2.1 s hs t ht e))
    simpa using this
  · unfold sig
    rw [rsum_zero _ _ (fun a _ => by unfold Fof; rw [if_neg hw]; split <;> rfl)]
    exact Int.dvd_zero _

theorem KC_hole (f : List Nat → Int) (hf : Bal p n k f (fun _ => 0) j) {u : Nat → Nat}
    (hu : Valid (n + k) allT (j + 1) u) :
    KC (p : Int) n allT (j + 1) (fun w (_ : Unit) => Fof n k (j + 1) f u w) := by
  intro w hw t ht x
  cases x
  rw [sig_row f hu hw (by omega : t ≤ j)]
  have hg := hf (mk n k j (skip t u) (skip t w)) (mk_CM (valid_skip hu (by omega)) (valid_skip hw (by omega)))
    (mk_len (valid_skip hu (by omega)) (valid_skip hw (by omega)))
  have := hg.1 (u t) (hu.1 t ht).1 (fun v hv => by
    obtain ⟨s, hs, hst, rfl⟩ := (mem_mk_skip hu hw (by omega : t ≤ j)).mp hv
    rw [var_div n _ _ (hw.1 s hs).1]
    exact fun e => hst (hu.2.1 s hs t ht e))
  simpa using this

end

theorem sig_lin {β W : Type} (M : Nat) (Y : Nat → Bool) (J : Nat) (L : List β) (a : β → Int)
    (H : β → (Nat → Nat) → W → Int) (u : Nat → Nat) (t : Nat) (x : W) :
    sig M Y J (fun u x => ls L (fun q => a q * H q u x)) u t x = ls L (fun q => a q * sig M Y J (H q) u t x) := by
  unfold sig
  have e : ∀ b, (if Y b = true ∧ Free J u t b then ls L (fun q => a q * H q (upd u t b) x) else 0) =
      ls L (fun q => a q * (if Y b = true ∧ Free J u t b then H q (upd u t b) x else 0)) := by
    intro b; split
    · rfl
    · rw [ls_zero]; intro q _; rw [Int.mul_zero]
  rw [rsum_congr M _ _ (fun b _ => e b), rsum_ls]
  apply ls_congr; intro q _; rw [rsum_mul]

theorem ls_dvd {β : Type} (m : Int) (L : List β) (g : β → Int) (h : ∀ q ∈ L, m ∣ g q) : m ∣ ls L g := by
  induction L with
  | nil => exact Int.dvd_zero m
  | cons a L ih => exact Int.dvd_add (h a (by simp)) (ih (fun q hq => h q (by simp [hq])))

theorem ls_dvd_congr {β : Type} (m : Int) (L : List β) (g g' : β → Int) (h : ∀ q ∈ L, m ∣ g q - g' q) :
    m ∣ ls L g - ls L g' := by
  rw [← ls_sub]; exact ls_dvd m L _ h

/-! ## The tensor step -/

theorem SJ_tuple (p n k j : Nat) (hn : 2 * (j + 1) ≤ n) (f : List Nat → Int) (hf : Bal p n k f (fun _ => 0) j) :
    ∃ T : List ((Nat → Nat × Nat) × (Nat → Nat × Nat) × Int),
      (∀ x ∈ T, VP (n + k) allT (j + 1) x.1 ∧ VP n allT (j + 1) x.2.1) ∧
      ∀ u w, Valid (n + k) allT (j + 1) u → Valid n allT (j + 1) w →
        (p : Int) ∣ f (mk n k (j + 1) u w) - ls T (fun x => x.2.2 * (DP (j + 1) x.1 u * DP (j + 1) x.2.1 w)) := by
  classical
  have cardN : ∀ M, card M allT = M := by
    intro M; unfold card; induction M with
    | zero => rfl
    | succ M ih => simp only [rsum] at ih ⊢; rw [ih]; simp [allT]
  obtain ⟨B1, hB1, hrep1⟩ := lemK (W := Nat → Nat) (p : Int) (j + 1) (n + k) allT (Fof n k (j + 1) f)
    (by rw [cardN]; push_cast; omega) (KC_pig f hf)
  have hB2 : ∀ b ∈ B1, ∃ B2 : List ((Nat → Nat × Nat) × (Unit → Int)),
      (∀ q ∈ B2, VP n allT (j + 1) q.1 ∧ LC n allT (j + 1) (fun w (_ : Unit) => b.2 w) q.2) ∧
      ∀ w, Valid n allT (j + 1) w → ∀ x, (p : Int) ∣ b.2 w - ls B2 (fun q => DP (j + 1) q.1 w * q.2 x) := by
    intro b hb
    obtain ⟨_, L, hL, hc⟩ := hB1 b hb
    apply lemK (W := Unit) (p : Int) (j + 1) n allT (fun w _ => b.2 w) (by rw [cardN]; push_cast; omega)
    intro w hw t ht x
    have e : sig n allT (j + 1) (fun w (_ : Unit) => b.2 w) w t x =
        sig n allT (j + 1) (fun w x => ls L (fun q => q.2 * (fun (q : (Nat → Nat) × Int) w (_ : Unit) => Fof n k (j + 1) f q.1 w) q w x)) w t x := by
      unfold sig; apply rsum_congr; intro a _; split
      · exact hc _
      · rfl
    rw [e, sig_lin]
    apply ls_dvd; intro q hq
    exact Int.dvd_mul_of_dvd_right (KC_hole f hf (hL q hq) w hw t ht x)
  let B2 : ((Nat → Nat × Nat) × ((Nat → Nat) → Int)) → List ((Nat → Nat × Nat) × (Unit → Int)) := fun b =>
    if h : b ∈ B1 then Classical.choose (hB2 b h) else []
  have hB2' : ∀ b (h : b ∈ B1), (∀ q ∈ B2 b, VP n allT (j + 1) q.1 ∧ LC n allT (j + 1) (fun w (_ : Unit) => b.2 w) q.2) ∧
      ∀ w, Valid n allT (j + 1) w → ∀ x, (p : Int) ∣ b.2 w - ls (B2 b) (fun q => DP (j + 1) q.1 w * q.2 x) := by
    intro b h
    have e : B2 b = Classical.choose (hB2 b h) := by simp only [B2, dif_pos h]
    rw [e]; exact Classical.choose_spec (hB2 b h)
  refine ⟨B1.flatMap (fun b => (B2 b).map (fun q => (b.1, q.1, q.2 ()))), fun x hx => ?_, fun u w hu hw => ?_⟩
  · obtain ⟨b, hb, hx'⟩ := List.mem_flatMap.mp hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx'
    exact ⟨(hB1 b hb).1, ((hB2' b hb).1 q hq).1⟩
  · have h1 := hrep1 u hu w
    have hF : Fof n k (j + 1) f u w = f (mk n k (j + 1) u w) := by unfold Fof; rw [if_pos hw]
    rw [hF] at h1
    rw [ls_flatMap]
    have h2 : (p : Int) ∣ ls B1 (fun b => DP (j + 1) b.1 u * b.2 w) -
        ls B1 (fun b => ls ((B2 b).map (fun q => (b.1, q.1, q.2 ()))) (fun x => x.2.2 * (DP (j + 1) x.1 u * DP (j + 1) x.2.1 w))) := by
      apply ls_dvd_congr; intro b hb
      rw [ls_map]
      have : (p : Int) ∣ DP (j + 1) b.1 u * (b.2 w - ls (B2 b) (fun q => DP (j + 1) q.1 w * q.2 ())) :=
        Int.dvd_mul_of_dvd_right ((hB2' b hb).2 w hw ())
      have e : DP (j + 1) b.1 u * (b.2 w - ls (B2 b) (fun q => DP (j + 1) q.1 w * q.2 ())) =
          DP (j + 1) b.1 u * b.2 w - ls (B2 b) (fun q => q.2 () * (DP (j + 1) b.1 u * DP (j + 1) q.1 w)) := by
        rw [Int.mul_sub, ← ls_mul]; congr 1; apply ls_congr; intro q _
        rw [Int.mul_comm (DP (j + 1) q.1 w), ← Int.mul_assoc, Int.mul_comm (DP (j + 1) b.1 u), Int.mul_assoc]
      rw [e] at this; exact this
    have := Int.dvd_add h1 h2
    rwa [show ∀ a b c : Int, a - b + (b - c) = a - c by intros; omega] at this

/-! ## Orderings of a list and the permanent `jp` -/

/-- All orderings of `j` distinct entries of `l` (each ordering of a nodup `l` of length `j` once). -/
def ords : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | j + 1, l => l.flatMap (fun x => (ords j (l.erase x)).map (x :: ·))

/-- Permanent-style expansion: `∑` over bijections slots → entries of `∏_s r s (entry)`. -/
def jp : Nat → (Nat → Nat → Int) → List Nat → Int
  | 0, _, _ => 1
  | j + 1, r, l => ls l (fun x => r 0 x * jp j (fun s => r (s + 1)) (l.erase x))

/-- The `j`-fold rectangle product with pigeon pairs `P` and hole pairs `Q`, on matchings. -/
def RP (n j : Nat) (P Q : Nat → Nat × Nat) : List Nat → Int :=
  jp j (fun s v => dl (P s) (v / n) * dl (Q s) (v % n))

/-- `j!`. -/
def fact : Nat → Nat
  | 0 => 1
  | j + 1 => (j + 1) * fact j

theorem getD_ge : ∀ (o : List Nat) (s : Nat), o.length ≤ s → o.getD s 0 = 0
  | [], _, _ => rfl
  | _ :: o, s, h => by
    cases s with
    | zero => simp at h
    | succ s => rw [List.getD_cons_succ]; exact getD_ge o s (by simp at h; omega)

theorem mem_getD : ∀ (o : List Nat) (x : Nat), x ∈ o ↔ ∃ s < o.length, o.getD s 0 = x
  | [], x => by simp
  | y :: o, x => by
    rw [List.mem_cons, mem_getD o x]
    constructor
    · rintro (rfl | ⟨s, hs, e⟩)
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨s + 1, by simp; omega, by rw [List.getD_cons_succ]; exact e⟩
    · rintro ⟨s, hs, e⟩
      cases s with
      | zero => left; rw [List.getD_cons_zero] at e; exact e.symm
      | succ s => right; rw [List.getD_cons_succ] at e; exact ⟨s, by simp at hs; omega, e⟩

theorem getD_inj : ∀ (o : List Nat), o.Nodup → ∀ s < o.length, ∀ s' < o.length, o.getD s 0 = o.getD s' 0 → s = s'
  | [], _, s, hs, _, _, _ => by simp at hs
  | y :: o, hn, s, hs, s', hs', e => by
    rw [List.nodup_cons] at hn
    cases s with
    | zero =>
      cases s' with
      | zero => rfl
      | succ s' =>
        rw [List.getD_cons_zero, List.getD_cons_succ] at e
        exact absurd ((mem_getD o y).mpr ⟨s', by simp at hs'; omega, e.symm⟩) hn.1
    | succ s =>
      cases s' with
      | zero =>
        rw [List.getD_cons_zero, List.getD_cons_succ] at e
        exact absurd ((mem_getD o y).mpr ⟨s, by simp at hs; omega, e⟩) hn.1
      | succ s' =>
        rw [List.getD_cons_succ, List.getD_cons_succ] at e
        have := getD_inj o hn.2 s (by simp at hs; omega) s' (by simp at hs'; omega) e
        omega

theorem ords_prop : ∀ (j : Nat) (l o : List Nat), o ∈ ords j l → l.Nodup → l.length = j →
    o.length = j ∧ o.Nodup ∧ ∀ x, x ∈ o ↔ x ∈ l
  | 0, l, o, h, _, hl => by
    simp [ords] at h; subst h
    have : l = [] := List.eq_nil_of_length_eq_zero hl
    subst this; simp
  | j + 1, l, o, h, hn, hl => by
    simp only [ords, List.mem_flatMap, List.mem_map] at h
    obtain ⟨x, hx, o', ho', rfl⟩ := h
    have hl' : (l.erase x).length = j := by rw [List.length_erase_of_mem hx]; omega
    obtain ⟨a, b, c⟩ := ords_prop j (l.erase x) o' ho' (hn.erase x) hl'
    refine ⟨by simp [a], List.nodup_cons.mpr ⟨fun hxo => ?_, b⟩, fun y => ?_⟩
    · have := (c x).mp hxo; rw [hn.mem_erase_iff] at this; exact this.1 rfl
    · rw [List.mem_cons, c y, hn.mem_erase_iff]
      constructor
      · rintro (rfl | ⟨_, h⟩)
        · exact hx
        · exact h
      · intro hy; by_cases e : y = x
        · left; exact e
        · right; exact ⟨e, hy⟩

theorem ls_const {α : Type} (l : List α) (c : Int) : ls l (fun _ => c) = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [ls_cons, ih, List.length_cons]; push_cast; rw [Int.add_mul, Int.one_mul]; omega

theorem ls_length {α β : Type} (l : List α) (g : α → List β) :
    ((l.flatMap g).length : Int) = ls l (fun x => ((g x).length : Int)) := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, ls_cons]; push_cast; rw [ih]

theorem ords_len : ∀ (j : Nat) (l : List Nat), l.Nodup → l.length = j → ((ords j l).length : Int) = fact j
  | 0, l, _, _ => by simp [ords, fact]
  | j + 1, l, hn, hl => by
    simp only [ords]
    rw [ls_length]
    have : ∀ x ∈ l, (((ords j (l.erase x)).map (x :: ·)).length : Int) = fact j := by
      intro x hx
      rw [List.length_map]
      exact ords_len j (l.erase x) (hn.erase x) (by rw [List.length_erase_of_mem hx]; omega)
    rw [ls_congr _ _ _ this, ls_const, hl]; simp [fact]

theorem rprod_first (j : Nat) (f : Nat → Int) : rprod (j + 1) f = f 0 * rprod j (fun s => f (s + 1)) := by
  rw [rprod_ins j 0 (by omega)]; rfl

theorem jp_ords : ∀ (j : Nat) (r : Nat → Nat → Int) (l : List Nat),
    jp j r l = ls (ords j l) (fun o => rprod j (fun s => r s (o.getD s 0)))
  | 0, r, l => by simp [jp, ords, rprod]
  | j + 1, r, l => by
    simp only [jp, ords]
    rw [ls_flatMap]
    apply ls_congr; intro x _
    rw [ls_map, jp_ords j (fun s => r (s + 1)) (l.erase x), ← ls_mul]
    apply ls_congr; intro o _
    rw [rprod_first]; simp [List.getD_cons_zero, List.getD_cons_succ]

theorem rprod_mul (j : Nat) (f g : Nat → Int) : rprod j f * rprod j g = rprod j (fun s => f s * g s) := by
  induction j with
  | zero => simp [rprod]
  | succ j ih => simp only [rprod]; rw [← ih]; simp only [Int.mul_assoc, Int.mul_left_comm (f j)]

/-! ## Averaging over the orderings of a matching -/

theorem SJ_avg (p n k J : Nat) (hn : 0 < n) (f : List Nat → Int)
    (T : List ((Nat → Nat × Nat) × (Nat → Nat × Nat) × Int))
    (hT : ∀ u w, Valid (n + k) allT J u → Valid n allT J w →
        (p : Int) ∣ f (mk n k J u w) - ls T (fun x => x.2.2 * (DP J x.1 u * DP J x.2.1 w)))
    (g : List Nat) (hg : CM n k g) (hgl : g.length = J) :
    (p : Int) ∣ fact J * f g - ls T (fun x => x.2.2 * RP n J x.1 x.2.1 g) := by
  have hgn : g.Nodup := CM_nodup hg
  have key : ∀ o ∈ ords J g, (p : Int) ∣ f g - ls T (fun x => x.2.2 *
      rprod J (fun s => dl (x.1 s) (o.getD s 0 / n) * dl (x.2.1 s) (o.getD s 0 % n))) := by
    intro o ho
    obtain ⟨ol, onod, omem⟩ := ords_prop J g o ho hgn hgl
    let u : Nat → Nat := fun s => o.getD s 0 / n
    let w : Nat → Nat := fun s => o.getD s 0 % n
    have inG : ∀ s < J, o.getD s 0 ∈ g := fun s hs => (omem _).mp ((mem_getD o _).mpr ⟨s, by omega, rfl⟩)
    have hne : ∀ s < J, ∀ s' < J, s ≠ s' → cfl n (o.getD s 0) (o.getD s' 0) = false ∧ o.getD s 0 ≠ o.getD s' 0 := by
      intro s hs s' hs' hss
      have hm := (isMatch_iff n g).mp hg.2 _ (inG s hs) _ (inG s' hs')
      exact ⟨hm, fun e => hss (getD_inj o onod s (by omega) s' (by omega) e)⟩
    have hu : Valid (n + k) allT J u := by
      refine ⟨fun s hs => ⟨?_, rfl⟩, fun s hs s' hs' e => ?_, fun s hs => ?_⟩
      · exact (Nat.div_lt_iff_lt_mul hn).mpr (CM_lt hg (inG s hs))
      · apply Classical.byContradiction; intro hss
        obtain ⟨h1, h2⟩ := hne s hs s' hs' hss
        unfold cfl at h1
        have hb : (o.getD s 0 != o.getD s' 0) = true := bne_iff_ne.mpr h2
        have hd : (o.getD s 0 / n == o.getD s' 0 / n) = true := beq_iff_eq.mpr e
        rw [hb, hd] at h1; simp at h1
      · show o.getD s 0 / n = 0; rw [getD_ge o s (by omega)]; simp
    have hw : Valid n allT J w := by
      refine ⟨fun s hs => ⟨Nat.mod_lt _ hn, rfl⟩, fun s hs s' hs' e => ?_, fun s hs => ?_⟩
      · apply Classical.byContradiction; intro hss
        obtain ⟨h1, h2⟩ := hne s hs s' hs' hss
        unfold cfl at h1
        have hb : (o.getD s 0 != o.getD s' 0) = true := bne_iff_ne.mpr h2
        have hd : (o.getD s 0 % n == o.getD s' 0 % n) = true := beq_iff_eq.mpr e
        rw [hb, hd] at h1; simp at h1
      · show o.getD s 0 % n = 0; rw [getD_ge o s (by omega)]; simp
    have hmk : mk n k J u w = g := by
      rw [← hg.1]; unfold mk
      apply canon_congr; intro x _
      rw [mem_mkL]
      constructor
      · rintro ⟨s, hs, rfl⟩
        show var n (o.getD s 0 / n) (o.getD s 0 % n) ∈ g
        rw [Programme.«20261025-1627-proof-complexity».OntoExt2.var_decode]; exact inG s hs
      · intro hx
        obtain ⟨s, hs, e⟩ := (mem_getD o x).mp ((omem x).mpr hx)
        refine ⟨s, by omega, ?_⟩
        show x = var n (o.getD s 0 / n) (o.getD s 0 % n)
        rw [Programme.«20261025-1627-proof-complexity».OntoExt2.var_decode, e]
    have := hT u w hu hw
    rw [hmk] at this
    refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp this
    rw [show ∀ a b c : Int, a - b - (a - c) = c - b by intros; omega, ← ls_sub]
    apply ls_dvd; intro x _
    rw [← Int.mul_sub]; apply Int.dvd_mul_of_dvd_right
    unfold DP; rw [rprod_mul, Int.sub_self]; exact Int.dvd_zero _
  have hsum := ls_dvd (p : Int) (ords J g) _ key
  rw [ls_sub, ls_const, ords_len J g hgn hgl, ls_comm] at hsum
  refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp hsum
  rw [show ∀ a b c : Int, a - b - (a - c) = c - b by intros; omega, ← ls_sub]
  apply ls_dvd; intro x _
  rw [ls_mul, ← Int.mul_sub]; apply Int.dvd_mul_of_dvd_right
  unfold RP; rw [jp_ords, Int.sub_self]; exact Int.dvd_zero _

/-- Rectangle products with valid pigeon pairs `P` and hole pairs `Q`. -/
def RPGen (n k j : Nat) (h : List Nat → Int) : Prop :=
  ∃ P Q, VP (n + k) allT j P ∧ VP n allT j Q ∧ h = RP n j P Q

theorem inSpan_ls {p n k e : Nat} {G : (List Nat → Int) → Prop} {α : Type} (L : List α) (a : α → Int)
    (h : α → List Nat → Int) (hG : ∀ x ∈ L, G (h x)) (z : List Nat → Int) (hz : G z) :
    InSpan p n k e G (fun g => ls L (fun x => a x * h x g)) := by
  induction L with
  | nil =>
    exact InSpan.congr (InSpan.smul 0 (InSpan.gen hz)) (fun g _ _ => by simp)
  | cons x L ih =>
    have h1 := InSpan.smul (a x) (InSpan.gen (p := p) (n := n) (k := k) (e := e) (hG x (by simp)))
    have h2 := ih (fun y hy => hG y (by simp [hy]))
    exact InSpan.congr (InSpan.add h1 h2) (fun g _ _ => by simp)

/-- **S_j.** For `j + 1 ≤ n/2` and `(j+1)!` a unit mod `p`, every function on `(j+1)`-matchings of
`ontoFPHP n k` with zero links (`Bal p n k f 0 j`) is, modulo `p` on canonical `(j+1)`-matchings, an
integer combination of rectangle products `RP n (j+1) P Q` (pigeon pairs `P`, hole pairs `Q`,
all `2(j+1)` pigeons and all `2(j+1)` holes distinct). -/
theorem SJ (p n k j : Nat) (hn : 2 * (j + 1) ≤ n) (hu : ∃ e : Int, (p : Int) ∣ e * (fact (j + 1) : Int) - 1)
    (f : List Nat → Int) (hf : Bal p n k f (fun _ => 0) j) : InSpan p n k (j + 1) (RPGen n k (j + 1)) f := by
  obtain ⟨e, he⟩ := hu
  obtain ⟨T, hTv, hT⟩ := SJ_tuple p n k j hn f hf
  let P0 : Nat → Nat × Nat := fun s => (2 * s, 2 * s + 1)
  have hP0 : ∀ M, 2 * (j + 1) ≤ M → VP M allT (j + 1) P0 := by
    intro M hM
    exact ⟨fun s hs => ⟨by simp [P0]; omega, rfl, by simp [P0]; omega, rfl, by simp [P0]⟩,
      fun s hs s' hs' hss => by simp [P0]; omega⟩
  have hz : RPGen n k (j + 1) (RP n (j + 1) P0 P0) := ⟨P0, P0, hP0 _ (by omega), hP0 _ hn, rfl⟩
  have hsp := inSpan_ls (p := p) (n := n) (k := k) (e := j + 1) T (fun x => e * x.2.2) (fun x => RP n (j + 1) x.1 x.2.1)
    (fun x hx => ⟨x.1, x.2.1, (hTv x hx).1, (hTv x hx).2, rfl⟩) _ hz
  refine InSpan.congr hsp (fun g hg hgl => ?_)
  have := SJ_avg p n k (j + 1) (by omega) f T hT g hg hgl
  have h2 : (p : Int) ∣ e * (fact (j + 1) * f g - ls T (fun x => x.2.2 * RP n (j + 1) x.1 x.2.1 g)) :=
    Int.dvd_mul_of_dvd_right this
  have h3 : (p : Int) ∣ (e * fact (j + 1) - 1) * f g := Int.dvd_mul_of_dvd_left he
  have h4 := Int.dvd_sub h2 h3
  have e1 : ls T (fun x => e * x.2.2 * RP n (j + 1) x.1 x.2.1 g) = e * ls T (fun x => x.2.2 * RP n (j + 1) x.1 x.2.1 g) := by
    rw [← ls_mul]; apply ls_congr; intro x _; rw [Int.mul_assoc]
  show (p : Int) ∣ f g - ls T (fun x => e * x.2.2 * RP n (j + 1) x.1 x.2.1 g)
  rw [e1]
  have : e * (↑(fact (j + 1)) * f g - ls T (fun x => x.2.2 * RP n (j + 1) x.1 x.2.1 g)) - (e * ↑(fact (j + 1)) - 1) * f g =
      f g - e * ls T (fun x => x.2.2 * RP n (j + 1) x.1 x.2.1 g) := by
    rw [Int.mul_sub, Int.sub_mul, Int.one_mul, Int.mul_assoc]; omega
  rwa [this] at h4

end Programme.«20261027-0607-proof-complexity».SJ

#print axioms Programme.«20261027-0607-proof-complexity».SJ.SJ
