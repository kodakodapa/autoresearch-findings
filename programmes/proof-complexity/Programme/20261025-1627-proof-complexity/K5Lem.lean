import Programme.«20261025-1627-proof-complexity».K5Defs
import Programme.«20261025-0459-proof-complexity».OntoSubst

/-!
# Invariance of the K5 weight and reduction of the design check to sets containing `0`

* `Wt_congr`: `Wt t l` depends only on the member set of `l`.
* `Wt_rot`: `Wt t` is invariant under every translation `rot a b` (on variables `< 105`).
* `pig_all`, `hol_all`: if the finite check `pairOk t u w` holds for all `u, w < 105` and
  `axOk t []` holds, every pigeon and hole sum `pigS`, `holS` against a set of size `≤ 3` is even.
  A nonempty set is translated so that its first member becomes `0`.
-/

namespace Programme.«20261025-1627-proof-complexity».K5Defs

open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum)
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr)

/-! ## Masks -/

theorem testBit_mask (l : List Nat) (x : Nat) : (mask l).testBit x = decide (x ∈ l) := by
  induction l with
  | nil => simp [mask]
  | cons v l ih =>
    simp only [mask, List.foldr_cons] at ih ⊢
    rw [Nat.testBit_or, ih, Nat.testBit_two_pow]
    by_cases h : x = v
    · subst h; simp
    · have : ¬ v = x := fun e => h e.symm
      simp [h, this]

theorem mask_congr {l l' : List Nat} (h : ∀ x, x ∈ l ↔ x ∈ l') : mask l = mask l' :=
  Nat.eq_of_testBit_eq (fun i => by rw [testBit_mask, testBit_mask]; simp [h])

/-! ## Membership-only functions -/

theorem all_congr_set {l l' : List Nat} (h : ∀ x, x ∈ l ↔ x ∈ l') (f : Nat → Bool) :
    l.all f = l'.all f := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro H x hx; exact H x ((h x).mpr hx)
  · intro H x hx; exact H x ((h x).mp hx)

theorem all_congr_mem {l : List Nat} {f g : Nat → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro H x hx; rw [← h x hx]; exact H x hx
  · intro H x hx; rw [h x hx]; exact H x hx

theorem matchB_congr {l l' : List Nat} (h : ∀ x, x ∈ l ↔ x ∈ l') : matchB l = matchB l' := by
  unfold matchB
  rw [all_congr_set h]
  congr 1
  funext u
  rw [all_congr_set h]

theorem minOver_le (g : Nat → Nat) : ∀ (l : List Nat), ∀ v ∈ l, minOver g l ≤ g v
  | [], v, hv => by simp at hv
  | [w], v, hv => by simp at hv; subst hv; simp [minOver]
  | w :: u :: l, v, hv => by
    simp only [minOver]
    rcases List.mem_cons.mp hv with h | h
    · subst h; exact Nat.min_le_left _ _
    · exact Nat.le_trans (Nat.min_le_right _ _) (minOver_le g (u :: l) v h)

theorem minOver_mem (g : Nat → Nat) : ∀ (l : List Nat), l ≠ [] → ∃ v ∈ l, minOver g l = g v
  | [], h => absurd rfl h
  | [w], _ => ⟨w, by simp, rfl⟩
  | w :: u :: l, _ => by
    simp only [minOver]
    obtain ⟨v, hv, e⟩ := minOver_mem g (u :: l) (by simp)
    by_cases hle : g w ≤ minOver g (u :: l)
    · exact ⟨w, by simp, Nat.min_eq_left hle⟩
    · refine ⟨v, List.mem_cons_of_mem _ hv, ?_⟩
      rw [Nat.min_eq_right (by omega), e]

theorem minOver_set (g : Nat → Nat) {l l' : List Nat} (h : ∀ x, x ∈ l ↔ x ∈ l') :
    minOver g l = minOver g l' := by
  cases l with
  | nil =>
    cases l' with
    | nil => rfl
    | cons y l' => exact absurd ((h y).mpr (by simp)) (by simp)
  | cons x l =>
    have hl' : l' ≠ [] := by intro e; subst e; exact absurd ((h x).mp (by simp)) (by simp)
    obtain ⟨v, hv, e⟩ := minOver_mem g (x :: l) (by simp)
    obtain ⟨v', hv', e'⟩ := minOver_mem g l' hl'
    have a1 := minOver_le g (x :: l) v' ((h v').mpr hv')
    have a2 := minOver_le g l' v ((h v).mp hv)
    omega

theorem minOver_ext {g g' : Nat → Nat} : ∀ (l : List Nat), (∀ v ∈ l, g v = g' v) →
    minOver g l = minOver g' l
  | [], _ => rfl
  | [w], h => by simp only [minOver]; exact h w (by simp)
  | w :: u :: l, h => by
    simp only [minOver]
    rw [h w (by simp), minOver_ext (u :: l) (fun v hv => h v (List.mem_cons_of_mem _ hv))]

theorem minOver_map (g f : Nat → Nat) : ∀ (l : List Nat),
    minOver g (l.map f) = minOver (fun v => g (f v)) l
  | [] => rfl
  | [w] => rfl
  | w :: u :: l => by
    have ih := minOver_map g f (u :: l)
    simp only [List.map_cons] at ih ⊢
    simp only [minOver]
    rw [ih]

theorem C_congr {l l' : List Nat} (h : ∀ x, x ∈ l ↔ x ∈ l') : C l = C l' := by
  unfold C
  have e : key l = key l' := by
    funext v; unfold key; apply mask_congr
    intro x; simp only [List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, (h y).mp hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, (h y).mpr hy, rfl⟩
  rw [e]; exact minOver_set _ h

theorem Wt_congr (t : T) {l l' : List Nat} (h : ∀ x, x ∈ l ↔ x ∈ l') : Wt t l = Wt t l' := by
  unfold Wt; rw [matchB_congr h, C_congr h]

/-! ## Translations -/

theorem rot_lt (a b v : Nat) : rot a b v < 105 := by unfold rot; omega

theorem rot_div (a b v : Nat) : rot a b v / 7 = (v / 7 + a) % 15 := by unfold rot; omega

theorem rot_mod (a b v : Nat) : rot a b v % 7 = (v % 7 + b) % 7 := by unfold rot; omega

theorem rot_inj (a b u w : Nat) (hu : u < 105) (hw : w < 105) (h : rot a b u = rot a b w) : u = w := by
  unfold rot at h; omega

theorem toZ_rot (a b v w : Nat) (hv : v < 105) (hw : w < 105) :
    toZ (rot a b v) (rot a b w) = toZ v w := by
  unfold toZ
  have h1 := rot_div a b v
  have h2 := rot_mod a b v
  generalize rot a b v = r at h1 h2
  unfold rot; omega

theorem toZ_self (v : Nat) (hv : v < 105) : toZ v v = 0 := by unfold toZ rot; omega

theorem matchB_rot (a b : Nat) (l : List Nat) (hl : ∀ x ∈ l, x < 105) :
    matchB (l.map (rot a b)) = matchB l := by
  unfold matchB
  rw [List.all_map]
  apply all_congr_mem
  intro u hu
  simp only [Function.comp]
  rw [List.all_map]
  have hu' := hl u hu
  have e1 : decide (rot a b u < 105) = decide (u < 105) := by
    simp [rot_lt, hu']
  rw [e1]
  congr 1
  apply all_congr_mem
  intro w hw
  have hw' := hl w hw
  simp only [Function.comp]
  have q1 : (rot a b u == rot a b w) = (u == w) := by
    apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
    exact ⟨rot_inj a b u w hu' hw', fun e => by rw [e]⟩
  have q2 : (rot a b u / 7 != rot a b w / 7) = (u / 7 != w / 7) := by
    rw [rot_div, rot_div]
    apply Bool.eq_iff_iff.mpr; simp only [bne_iff_ne, ne_eq]
    constructor <;> intro h1 h2 <;> apply h1 <;> omega
  have q3 : (rot a b u % 7 != rot a b w % 7) = (u % 7 != w % 7) := by
    rw [rot_mod, rot_mod]
    apply Bool.eq_iff_iff.mpr; simp only [bne_iff_ne, ne_eq]
    constructor <;> intro h1 h2 <;> apply h1 <;> omega
  rw [q1, q2, q3]

theorem C_rot (a b : Nat) (l : List Nat) (hl : ∀ x ∈ l, x < 105) :
    C (l.map (rot a b)) = C l := by
  unfold C
  rw [minOver_map]
  apply minOver_ext
  intro v hv
  unfold key
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro w hw
  exact toZ_rot a b v w (hl v hv) (hl w hw)

theorem Wt_rot (t : T) (a b : Nat) (l : List Nat) (hl : ∀ x ∈ l, x < 105) :
    Wt t (l.map (rot a b)) = Wt t l := by
  unfold Wt; rw [matchB_rot a b l hl, C_rot a b l hl]

/-! ## Reindexing the axiom sums -/

theorem rsum_shift7 (f : Nat → Int) (b : Nat) : rsum 7 (fun j => f ((j + b) % 7)) = rsum 7 f := by
  rw [rsum_congr 7 _ (fun j => f ((j + b % 7) % 7)) (fun j _ => by
    congr 1; omega)]
  have : b % 7 < 7 := Nat.mod_lt _ (by decide)
  generalize b % 7 = c at this
  rcases c with _ | _ | _ | _ | _ | _ | _ | c <;> (try omega) <;> simp [rsum] <;> omega

theorem rsum_shift15 (f : Nat → Int) (a : Nat) : rsum 15 (fun i => f ((i + a) % 15)) = rsum 15 f := by
  rw [rsum_congr 15 _ (fun i => f ((i + a % 15) % 15)) (fun i _ => by
    congr 1; omega)]
  have : a % 15 < 15 := Nat.mod_lt _ (by decide)
  generalize a % 15 = c at this
  rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | c <;> (try omega) <;>
    simp [rsum] <;> omega

theorem rot_var (a b i j : Nat) (hj : j < 7) : rot a b (i * 7 + j) = (i + a) % 15 * 7 + (j + b) % 7 := by
  unfold rot; omega

theorem pigS_rot (t : T) (a b i : Nat) (M : List Nat) (hM : ∀ x ∈ M, x < 105) (hi : i < 15) :
    pigS t i M = pigS t ((i + a) % 15) (M.map (rot a b)) := by
  unfold pigS
  rw [Wt_rot t a b M hM]
  have e : rsum 7 (fun j => Wt t ((i * 7 + j) :: M)) =
      rsum 7 (fun j => Wt t (((i + a) % 15 * 7 + j) :: M.map (rot a b))) := by
    rw [← rsum_shift7 (fun j => Wt t (((i + a) % 15 * 7 + j) :: M.map (rot a b))) b]
    refine rsum_congr _ _ _ (fun j hj => ?_)
    rw [← Wt_rot t a b ((i * 7 + j) :: M) (by
      intro x hx; rcases List.mem_cons.mp hx with h | h
      · subst h; omega
      · exact hM x h)]
    simp only [List.map_cons, rot_var a b i j hj]
  rw [e]

theorem holS_rot (t : T) (a b j : Nat) (M : List Nat) (hM : ∀ x ∈ M, x < 105) (hj : j < 7) :
    holS t j M = holS t ((j + b) % 7) (M.map (rot a b)) := by
  unfold holS
  rw [Wt_rot t a b M hM]
  have e : rsum 15 (fun i => Wt t ((i * 7 + j) :: M)) =
      rsum 15 (fun i => Wt t ((i * 7 + (j + b) % 7) :: M.map (rot a b))) := by
    rw [← rsum_shift15 (fun i => Wt t ((i * 7 + (j + b) % 7) :: M.map (rot a b))) a]
    refine rsum_congr _ _ _ (fun i hi => ?_)
    rw [← Wt_rot t a b ((i * 7 + j) :: M) (by
      intro x hx; rcases List.mem_cons.mp hx with h | h
      · subst h; omega
      · exact hM x h)]
    simp only [List.map_cons, rot_var a b i j hj]
  rw [e]

/-! ## Reduction -/

theorem allB_spec {n : Nat} {f : Nat → Bool} (h : allB n f = true) : ∀ x < n, f x = true := by
  induction n with
  | zero => intro x hx; omega
  | succ n ih =>
    simp only [allB, Bool.and_eq_true] at h
    intro x hx
    by_cases e : x = n
    · subst e; exact h.2
    · exact ih h.1 x (by omega)

theorem matchB_cons_false {l : List Nat} (x : Nat) (h : matchB l = false) : matchB (x :: l) = false := by
  rw [Bool.eq_false_iff] at h ⊢
  intro h'; apply h
  unfold matchB at h' ⊢
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h' ⊢
  intro u hu
  obtain ⟨h1, h2⟩ := h' u (List.mem_cons_of_mem _ hu)
  exact ⟨h1, fun w hw => h2 w (List.mem_cons_of_mem _ hw)⟩

theorem Wt_nm (t : T) {l : List Nat} (h : matchB l = false) : Wt t l = 0 := by
  unfold Wt; simp [h]

theorem dvd_of_mod (x : Int) (h : (x % 2 == 0) = true) : (2 : Int) ∣ x :=
  Int.dvd_of_emod_eq_zero (by simpa using h)

theorem rsum_zero0 (m : Nat) (f : Nat → Int) (h : ∀ j, f j = 0) : rsum m f = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [rsum, ih, h, Int.add_zero]

/-- A set `M` of size `≤ 3` (as a list, vars `< 105`) with first member `v`: its translate by
`toZ v` has the members of `[0, u, w]` for some `u, w < 105`. -/
theorem norm_set (v : Nat) (rest : List Nat) (hv : v < 105) (hr : ∀ x ∈ rest, x < 105)
    (hl : rest.length ≤ 2) :
    ∃ u w, u < 105 ∧ w < 105 ∧ ∀ x, x ∈ (v :: rest).map (rot (15 - v / 7) (7 - v % 7)) ↔ x ∈ [0, u, w] := by
  have h0 : rot (15 - v / 7) (7 - v % 7) v = 0 := toZ_self v hv
  match rest, hl with
  | [], _ => exact ⟨0, 0, by decide, by decide, fun x => by simp [h0]⟩
  | [u], _ =>
    exact ⟨rot (15 - v / 7) (7 - v % 7) u, rot (15 - v / 7) (7 - v % 7) u, rot_lt _ _ u, rot_lt _ _ u,
      fun x => by simp [h0]⟩
  | [u, w], _ =>
    exact ⟨rot (15 - v / 7) (7 - v % 7) u, rot (15 - v / 7) (7 - v % 7) w, rot_lt _ _ u, rot_lt _ _ w,
      fun x => by simp [h0]⟩

theorem pigS_congr (t : T) (i : Nat) {l l' : List Nat} (h : ∀ x, x ∈ l ↔ x ∈ l') : pigS t i l = pigS t i l' := by
  unfold pigS
  have e : rsum 7 (fun j => Wt t ((i * 7 + j) :: l)) = rsum 7 (fun j => Wt t ((i * 7 + j) :: l')) :=
    rsum_congr _ _ _ (fun j _ => Wt_congr t (fun x => by simp [h]))
  rw [e, Wt_congr t h]

theorem holS_congr (t : T) (j : Nat) {l l' : List Nat} (h : ∀ x, x ∈ l ↔ x ∈ l') : holS t j l = holS t j l' := by
  unfold holS
  have e : rsum 15 (fun i => Wt t ((i * 7 + j) :: l)) = rsum 15 (fun i => Wt t ((i * 7 + j) :: l')) :=
    rsum_congr _ _ _ (fun i _ => Wt_congr t (fun x => by simp [h]))
  rw [e, Wt_congr t h]

section
variable (t : T) (hchk : ∀ u < 105, ∀ w < 105, pairOk t u w = true) (h0 : axOk t [] = true)
include hchk h0

theorem base_all (u w : Nat) (hu : u < 105) (hw : w < 105) :
    (∀ i < 15, (2 : Int) ∣ pigS t i [0, u, w]) ∧ (∀ j < 7, (2 : Int) ∣ holS t j [0, u, w]) := by
  have hc := hchk u hu w hw
  unfold pairOk at hc
  cases hm : matchB [0, u, w] with
  | false =>
    refine ⟨fun i _ => ?_, fun j _ => ?_⟩
    · unfold pigS; rw [Wt_nm t hm, rsum_zero0 _ _ (fun j => Wt_nm t (matchB_cons_false _ hm))]
      exact ⟨0, by simp⟩
    · unfold holS; rw [Wt_nm t hm, rsum_zero0 _ _ (fun j => Wt_nm t (matchB_cons_false _ hm))]
      exact ⟨0, by simp⟩
  | true =>
    simp only [hm, Bool.not_true, Bool.false_or] at hc
    unfold axOk at hc
    simp only [Bool.and_eq_true] at hc
    exact ⟨fun i hi => dvd_of_mod _ (allB_spec hc.1 i hi), fun j hj => dvd_of_mod _ (allB_spec hc.2 j hj)⟩

theorem lin_all (M : List Nat) (hM : ∀ x ∈ M, x < 105) (hl : M.length ≤ 3) :
    (∀ i < 15, (2 : Int) ∣ pigS t i M) ∧ (∀ j < 7, (2 : Int) ∣ holS t j M) := by
  match M with
  | [] =>
    unfold axOk at h0
    simp only [Bool.and_eq_true] at h0
    exact ⟨fun i hi => dvd_of_mod _ (allB_spec h0.1 i hi), fun j hj => dvd_of_mod _ (allB_spec h0.2 j hj)⟩
  | v :: rest =>
    have hv := hM v (by simp)
    have hr : ∀ x ∈ rest, x < 105 := fun x hx => hM x (List.mem_cons_of_mem _ hx)
    obtain ⟨u, w, hu, hw, hs⟩ := norm_set v rest hv hr (by simp at hl; omega)
    obtain ⟨b1, b2⟩ := base_all t hchk h0 u w hu hw
    refine ⟨fun i hi => ?_, fun j hj => ?_⟩
    · rw [pigS_rot t (15 - v / 7) (7 - v % 7) i _ hM hi, pigS_congr t _ hs]
      exact b1 _ (Nat.mod_lt _ (by decide))
    · rw [holS_rot t (15 - v / 7) (7 - v % 7) j _ hM hj, holS_congr t _ hs]
      exact b2 _ (Nat.mod_lt _ (by decide))

end

end Programme.«20261025-1627-proof-complexity».K5Defs
