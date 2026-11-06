import Programme.«20261025-0805-proof-complexity».MApprox
import Programme.«20261024-1633-proof-complexity».Sunflower

/-!
# Closing matching approximators (M2 of P88)

Entries of a matching approximator (`Work.MApprox.MA`) are edge lists. A **pluck** takes a
sunflower of entries and replaces the lowest-valued chosen petal `P` by its *inner* edges `I`
(the edges of `P` with both endpoints in the vertex core `C`), keeping its value.

The sunflower is taken over the encoding `enc n P` (left vertex `i ↦ 4i`, right `j ↦ 4j+1`, edge
`(i,j) ↦ 4(in+j)+2`, for vertices `< n`), so distinct edge sets have distinct codes and no fibre
bound is needed. Inside the sunflower a pigeonhole on the inner matchings (at most
`(2ℓ+1)^{2ℓ}` codes) gives `p` petals with the same inner edges, none of them all-inner.

Facts (`mclose`, threshold `thr p ℓ = (3ℓ)! (p (2ℓ+1)^{2ℓ})^{3ℓ}`):
* the base is kept and the result has at most `thr p ℓ` entries and satisfies `MInv n ℓ`;
* values never drop, on any graph;
* a value rises on `H` only at one of `≤ wt` recorded events `(C, I, Ps)` (`MEv`) with `I` present
  in `H` and no member of `Ps` present. In an event, `|Ps| = p`, every `P ∈ Ps` contains `I`,
  every edge of `P` outside `I` has an endpoint outside `C` (in th's coordinates `vs`), and two
  members of `Ps` share vertices only inside `C`.
-/

namespace Programme.«20261025-0805-proof-complexity».MPluck

open Programme.«20261025-0805-proof-complexity».MApprox
open Programme.«20261025-0805-proof-complexity».PermCount (fitsP)
open Programme.«20261024-1633-proof-complexity».Sunflower (fact sunflower Distinct Petals)

/-! ## Invariant and encoding -/

/-- Entries: duplicate-free partial matchings with at most `ℓ` edges on vertices `< n`. -/
def MInv (n ℓ : Nat) (a : MA) : Prop :=
  ∀ e ∈ a.ents, e.1.Nodup ∧ isM e.1 = true ∧ e.1.length ≤ ℓ ∧ ∀ x ∈ e.1, x.1 < n ∧ x.2 < n

def enc (n : Nat) (P : List (Nat × Nat)) : List Nat :=
  P.flatMap fun e => [4 * e.1, 4 * e.2 + 1, 4 * (e.1 * n + e.2) + 2]

theorem mem_enc {n : Nat} {P : List (Nat × Nat)} {y : Nat} :
    y ∈ enc n P ↔ ∃ e ∈ P, y = 4 * e.1 ∨ y = 4 * e.2 + 1 ∨ y = 4 * (e.1 * n + e.2) + 2 := by
  simp only [enc, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]

theorem enc_length (n : Nat) (P : List (Nat × Nat)) : (enc n P).length = 3 * P.length := by
  induction P with
  | nil => rfl
  | cons e P ih => simp [enc, List.flatMap_cons] at *; omega

theorem pair_inj {n a b c d : Nat} (hb : b < n) (hd : d < n) (h : a * n + b = c * n + d) :
    a = c ∧ b = d := by
  have hn : 0 < n := by omega
  have h1 : (b + a * n) / n = a := by
    rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb]; omega
  have h2 : (d + c * n) / n = c := by
    rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hd]; omega
  have hac : a = c := by
    rw [← h1, ← h2, Nat.add_comm b, Nat.add_comm d, h]
  subst hac
  exact ⟨rfl, by omega⟩

/-- Edge point of a bounded edge list. -/
theorem edge_enc {n : Nat} {P : List (Nat × Nat)} (hP : ∀ x ∈ P, x.1 < n ∧ x.2 < n)
    {e : Nat × Nat} (he : e.2 < n) : 4 * (e.1 * n + e.2) + 2 ∈ enc n P ↔ e ∈ P := by
  rw [mem_enc]
  constructor
  · rintro ⟨f, hf, h⟩
    have hfe : f.1 * n + f.2 = e.1 * n + e.2 := by omega
    obtain ⟨h1, h2⟩ := pair_inj (hP f hf).2 he hfe
    have : f = e := Prod.ext h1 h2
    exact this ▸ hf
  · intro h; exact ⟨e, h, by omega⟩

theorem left_enc {n : Nat} {P : List (Nat × Nat)} {i : Nat} :
    4 * i ∈ enc n P ↔ 2 * i ∈ vs P := by
  rw [mem_enc, mem_vs]
  constructor
  · rintro ⟨e, he, h⟩; exact ⟨e, he, by omega⟩
  · rintro ⟨e, he, h⟩; exact ⟨e, he, by omega⟩

theorem right_enc {n : Nat} {P : List (Nat × Nat)} {j : Nat} :
    4 * j + 1 ∈ enc n P ↔ 2 * j + 1 ∈ vs P := by
  rw [mem_enc, mem_vs]
  constructor
  · rintro ⟨e, he, h⟩; exact ⟨e, he, by omega⟩
  · rintro ⟨e, he, h⟩; exact ⟨e, he, by omega⟩

/-- Every point of `vs P` is a left or right point of an edge. -/
theorem vs_enc {n : Nat} {P : List (Nat × Nat)} {x : Nat} (h : x ∈ vs P) :
    (∃ i, x = 2 * i ∧ 4 * i ∈ enc n P) ∨ (∃ j, x = 2 * j + 1 ∧ 4 * j + 1 ∈ enc n P) := by
  obtain ⟨e, he, hx⟩ := mem_vs.1 h
  rcases hx with hx | hx
  · exact Or.inl ⟨e.1, hx, mem_enc.2 ⟨e, he, Or.inl rfl⟩⟩
  · exact Or.inr ⟨e.2, hx, mem_enc.2 ⟨e, he, Or.inr (Or.inl rfl)⟩⟩

/-! ## Same edge set -/

def same (P Q : List (Nat × Nat)) : Bool := P.all (fun e => decide (e ∈ Q)) && Q.all (fun e => decide (e ∈ P))

theorem same_iff {P Q : List (Nat × Nat)} : same P Q = true ↔ ∀ e, e ∈ P ↔ e ∈ Q := by
  simp only [same, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨h1, h2⟩ e => ⟨h1 e, h2 e⟩, fun h => ⟨fun e => (h e).1, fun e => (h e).2⟩⟩

theorem pres_same {H : Nat → Nat → Bool} {P Q : List (Nat × Nat)} (h : same P Q = true) :
    pres H P ↔ pres H Q :=
  ⟨pres_sub fun e he => (same_iff.1 h e).2 he, pres_sub fun e he => (same_iff.1 h e).1 he⟩

/-- Distinct edge sets (within the bound) have distinct codes. -/
theorem distinct_enc {n : Nat} {P Q : List (Nat × Nat)} (hP : ∀ x ∈ P, x.1 < n ∧ x.2 < n)
    (hQ : ∀ x ∈ Q, x.1 < n ∧ x.2 < n) (h : same P Q = false) :
    ∃ y, ¬ (y ∈ enc n P ↔ y ∈ enc n Q) := by
  have : ¬ ∀ e, e ∈ P ↔ e ∈ Q := fun h' => by rw [same_iff.2 h'] at h; exact Bool.noConfusion h
  apply Classical.byContradiction
  intro hn
  apply this
  intro e
  constructor
  · intro he
    have := (edge_enc hP (hP e he).2).2 he
    have hy : 4 * (e.1 * n + e.2) + 2 ∈ enc n Q :=
      (Classical.byContradiction fun hy => hn ⟨_, fun hi => hy (hi.1 this)⟩)
    exact (edge_enc hQ (hP e he).2).1 hy
  · intro he
    have := (edge_enc hQ (hQ e he).2).2 he
    have hy : 4 * (e.1 * n + e.2) + 2 ∈ enc n P :=
      (Classical.byContradiction fun hy => hn ⟨_, fun hi => hy (hi.2 this)⟩)
    exact (edge_enc hP (hQ e he).2).1 hy

/-! ## Merging entries with the same edge set -/

/-- Total number of edges in the entries. -/
def wt (l : List Ent) : Nat := (l.map fun e => e.1.length).sum

def ins (x : Ent) : List Ent → List Ent
  | [] => [x]
  | y :: l => if same x.1 y.1 then (y.1, max x.2 y.2) :: l else y :: ins x l

def mrg : List Ent → List Ent
  | [] => []
  | x :: l => ins x (mrg l)

theorem ins_mem (x : Ent) : ∀ l : List Ent, ∀ z ∈ ins x l, z.1 = x.1 ∨ ∃ y ∈ l, z.1 = y.1
  | [], z, h => by simp [ins] at h; exact Or.inl (h ▸ rfl)
  | y :: l, z, h => by
    unfold ins at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr ⟨y, List.mem_cons_self .., rfl⟩
      · exact Or.inr ⟨z, List.mem_cons_of_mem _ h, rfl⟩
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr ⟨z, List.mem_cons_self .., rfl⟩
      · rcases ins_mem x l z h with h | ⟨w, hw, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, h⟩

theorem same_symm {P Q : List (Nat × Nat)} (h : same P Q = true) : same Q P = true :=
  same_iff.2 fun e => (same_iff.1 h e).symm

theorem ins_pw (x : Ent) : ∀ l : List Ent, l.Pairwise (fun u v => same u.1 v.1 = false) →
    (ins x l).Pairwise (fun u v => same u.1 v.1 = false)
  | [], _ => List.pairwise_singleton _ _
  | y :: l, h => by
    have ⟨h1, h2⟩ := List.pairwise_cons.1 h
    unfold ins
    split
    · exact List.pairwise_cons.2 ⟨fun z hz => h1 z hz, h2⟩
    · rename_i hxy
      refine List.pairwise_cons.2 ⟨fun z hz => ?_, ins_pw x l h2⟩
      rcases ins_mem x l z hz with h | ⟨w, hw, h⟩
      · rw [h]
        cases hs : same y.1 x.1
        · rfl
        · exact absurd (same_symm hs) hxy
      · rw [h]; exact h1 w hw

theorem ins_eval (H : Nat → Nat → Bool) (v₀ : Int) (x : Ent) :
    ∀ l : List Ent, evalL H v₀ (ins x l) = evalL H v₀ (x :: l)
  | [] => rfl
  | y :: l => by
    unfold ins
    split
    · rename_i hxy
      have hp := pres_same (H := H) hxy
      simp only [evalL]
      by_cases hy : pres H y.1
      · have hx : pres H x.1 := hp.2 hy
        simp only [if_pos hy, if_pos hx]; omega
      · have hx : ¬ pres H x.1 := fun h => hy (hp.1 h)
        simp only [if_neg hy, if_neg hx]
    · have ih := ins_eval H v₀ x l
      simp only [evalL] at ih ⊢
      rw [ih]
      by_cases hy : pres H y.1 <;> by_cases hx : pres H x.1 <;> simp only [hy, hx, if_true, if_false]
      all_goals omega

theorem ins_wt (x : Ent) : ∀ l : List Ent, wt (ins x l) ≤ x.1.length + wt l
  | [] => by simp [ins, wt]
  | y :: l => by
    have ih := ins_wt x l
    unfold ins
    split <;> simp only [wt, List.map_cons, List.sum_cons] at * <;> omega

theorem mrg_facts : ∀ l : List Ent,
    (∀ z ∈ mrg l, ∃ y ∈ l, z.1 = y.1) ∧ (mrg l).Pairwise (fun u v => same u.1 v.1 = false) ∧
    wt (mrg l) ≤ wt l ∧ ∀ H v₀, evalL H v₀ (mrg l) = evalL H v₀ l
  | [] => ⟨by simp [mrg], List.Pairwise.nil, Nat.le_refl _, fun _ _ => rfl⟩
  | x :: l => by
    obtain ⟨h1, h2, h3, h4⟩ := mrg_facts l
    refine ⟨fun z hz => ?_, ins_pw x _ h2, ?_, fun H v₀ => ?_⟩
    · rcases ins_mem x _ z hz with h | ⟨w, hw, h⟩
      · exact ⟨x, List.mem_cons_self .., h⟩
      · obtain ⟨y, hy, h'⟩ := h1 w hw
        exact ⟨y, List.mem_cons_of_mem _ hy, h.trans h'⟩
    · have := ins_wt x (mrg l)
      simp only [mrg, wt, List.map_cons, List.sum_cons] at *; omega
    · show evalL H v₀ (ins x (mrg l)) = _
      rw [ins_eval]
      simp only [evalL, h4]

def mg (a : MA) : MA := ⟨a.base, mrg a.ents⟩

/-! ## Pigeonhole and code lists -/

theorem pigeon {α β : Type} [DecidableEq β] (f : α → β) (p : Nat) : ∀ (U : List β) (L : List α),
    (∀ a ∈ L, f a ∈ U) → p * U.length < L.length →
    ∃ u, p < (L.filter fun a => decide (f a = u)).length
  | [], L, hU, hL => by
    cases L with
    | nil => simp at hL
    | cons a L => exact absurd (hU a (List.mem_cons_self ..)) (by simp)
  | u :: U, L, hU, hL => by
    by_cases hu : p < (L.filter fun a => decide (f a = u)).length
    · exact ⟨u, hu⟩
    · let L' := L.filter fun a => !decide (f a = u)
      have hs := Programme.«20261024-1633-proof-complexity».Sunflower.len_split
        (fun a => decide (f a = u)) L
      have hL' : p * U.length < L'.length := by
        simp only [List.length_cons, Nat.mul_succ] at hL
        simp only [L']; omega
      have hU' : ∀ a ∈ L', f a ∈ U := by
        intro a ha
        have ⟨ha1, ha2⟩ := List.mem_filter.1 ha
        rcases List.mem_cons.1 (hU a ha1) with h | h
        · simp [h] at ha2
        · exact h
      obtain ⟨w, hw⟩ := pigeon f p U L' hU' hL'
      exact ⟨w, Nat.lt_of_lt_of_le hw ((List.filter_sublist.filter _).length_le)⟩

/-- All lists of length `t` over the alphabet `A`. -/
def allL {α : Type} (A : List α) : Nat → List (List α)
  | 0 => [[]]
  | t + 1 => A.flatMap fun a => (allL A t).map (a :: ·)

theorem allL_length {α : Type} (A : List α) : ∀ t, (allL A t).length = A.length ^ t
  | 0 => rfl
  | t + 1 => by
    have h : ∀ B : List α, (B.flatMap fun a => (allL A t).map (a :: ·)).length
        = B.length * (allL A t).length := by
      intro B; induction B with
      | nil => simp
      | cons b B ih => simp only [List.flatMap_cons, List.length_append, List.length_map, ih,
          List.length_cons, Nat.succ_mul]; omega
    show (A.flatMap fun a => (allL A t).map (a :: ·)).length = _
    rw [h, allL_length A t, Nat.pow_succ, Nat.mul_comm]

theorem mem_allL {α : Type} (A : List α) : ∀ l : List α, (∀ x ∈ l, x ∈ A) → l ∈ allL A l.length
  | [], _ => List.mem_singleton_self _
  | x :: l, h => by
    simp only [allL, List.length_cons, List.mem_flatMap, List.mem_map]
    exact ⟨x, h x (List.mem_cons_self ..), l,
      mem_allL A l fun y hy => h y (List.mem_cons_of_mem _ hy), rfl⟩

/-- An edge with both endpoints in the vertex core `C` (coordinates of `vs`). -/
def inner (C : List Nat) (e : Nat × Nat) : Bool := decide (2 * e.1 ∈ C) && decide (2 * e.2 + 1 ∈ C)

/-- Partner of the left vertex `i` inside `C`, if any. -/
def pc (C : List Nat) (P : List (Nat × Nat)) (i : Nat) : Option Nat :=
  (P.find? fun e => e.1 == i && decide (2 * e.2 + 1 ∈ C)).map (·.2)

/-- The inner matching of `P` as a code over the left points of `C`. -/
def code (C : List Nat) (P : List (Nat × Nat)) : List (Option Nat) := (C.map (· / 2)).map (pc C P)

def alph (C : List Nat) : List (Option Nat) := none :: C.map fun x => some (x / 2)

theorem code_mem (C : List Nat) (P : List (Nat × Nat)) : code C P ∈ allL (alph C) C.length := by
  have h := mem_allL (alph C) (code C P) ?_
  · simpa [code] using h
  intro x hx
  simp only [code, List.map_map, List.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  simp only [Function.comp, pc]
  cases hf : P.find? (fun e => e.1 == y / 2 && decide (2 * e.2 + 1 ∈ C)) with
  | none => exact List.mem_cons_self ..
  | some e =>
    have := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    simp only [Option.map_some, alph, List.mem_cons, List.mem_map]
    exact Or.inr ⟨2 * e.2 + 1, this.2, by congr 1; omega⟩

theorem inj_of_nodup_map {g : Nat × Nat → Nat} : ∀ {P : List (Nat × Nat)}, (P.map g).Nodup →
    ∀ x ∈ P, ∀ y ∈ P, g x = g y → x = y
  | [], _, x, hx, _, _, _ => by simp at hx
  | z :: P, h, x, hx, y, hy, hxy => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 hx with h1 | h1 <;> rcases List.mem_cons.1 hy with h2 | h2
    · exact h1.trans h2.symm
    · subst h1; exact absurd (hxy ▸ List.mem_map_of_mem h2) h.1
    · subst h2; exact absurd (hxy.symm ▸ List.mem_map_of_mem h1) h.1
    · exact inj_of_nodup_map h.2 x h1 y h2 hxy

theorem pc_of {C : List Nat} {P : List (Nat × Nat)} (hP : isM P = true) {e : Nat × Nat}
    (he : e ∈ P) (hr : 2 * e.2 + 1 ∈ C) : pc C P e.1 = some e.2 := by
  have hl : (P.map (·.1)).Nodup := by simp only [isM, decide_eq_true_eq] at hP; exact hP.1
  unfold pc
  cases hf : P.find? (fun f => f.1 == e.1 && decide (2 * f.2 + 1 ∈ C)) with
  | none =>
    have := List.find?_eq_none.1 hf e he
    simp [hr] at this
  | some f =>
    have h1 := List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    have : f = e := inj_of_nodup_map hl f h2 e he h1.1
    simp [this]

theorem of_pc {C : List Nat} {P : List (Nat × Nat)} {i j : Nat} (h : pc C P i = some j) :
    (i, j) ∈ P := by
  unfold pc at h
  cases hf : P.find? (fun f => f.1 == i && decide (2 * f.2 + 1 ∈ C)) with
  | none => rw [hf] at h; simp at h
  | some f =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have h1 := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    have h2 := List.mem_of_find?_eq_some hf
    have : f = (i, j) := Prod.ext h1.1 h
    exact this ▸ h2

/-- Equal codes give equal inner edges. -/
theorem code_inner {C : List Nat} {P Q : List (Nat × Nat)} (hP : isM P = true)
    (h : code C P = code C Q) {e : Nat × Nat} (he : e ∈ P) (hi : inner C e = true) : e ∈ Q := by
  simp only [inner, Bool.and_eq_true, decide_eq_true_eq] at hi
  have hmem : e.1 ∈ C.map (· / 2) := List.mem_map.2 ⟨2 * e.1, hi.1, by omega⟩
  have := (List.map_inj_left.1 h) e.1 hmem
  rw [pc_of hP he hi.2] at this
  exact of_pc this.symm

theorem isM_sub {P Q : List (Nat × Nat)} (h : P.Sublist Q) (hQ : isM Q = true) : isM P = true := by
  simp only [isM, decide_eq_true_eq] at *
  exact ⟨(h.map _).nodup hQ.1, (h.map _).nodup hQ.2⟩

theorem le1 {α : Type} {R : α → α → Prop} (q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, ∀ y ∈ l, q x = true → q y = true → ¬ R x y) → l.Pairwise R →
      (l.filter q).length ≤ 1
  | [], _, _ => by simp
  | x :: l, hq, h => by
    have ⟨h1, h2⟩ := List.pairwise_cons.1 h
    by_cases hx : q x = true
    · have : l.filter q = [] := List.filter_eq_nil_iff.2 fun y hy hy' =>
        hq x (List.mem_cons_self ..) y (List.mem_cons_of_mem _ hy) hx hy' (h1 y hy)
      simp [hx, this]
    · simp only [List.filter_cons, hx, Bool.false_eq_true, ite_false]
      exact le1 q l (fun x hx y hy => hq x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) h2

theorem exists_min : ∀ l : List Ent, l ≠ [] → ∃ x ∈ l, ∀ y ∈ l, x.2 ≤ y.2
  | [], h => absurd rfl h
  | [x], _ => ⟨x, by simp, fun y hy => by simp at hy; subst hy; exact Int.le_refl _⟩
  | x :: z :: l, _ => by
    obtain ⟨w, hw, hmin⟩ := exists_min (z :: l) (by simp)
    by_cases hxw : x.2 ≤ w.2
    · refine ⟨x, List.mem_cons_self .., fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact Int.le_refl _
      · exact Int.le_trans hxw (hmin y hy)
    · refine ⟨w, List.mem_cons_of_mem _ hw, fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · omega
      · exact hmin y hy

theorem wt_erase : ∀ {l : List Ent} {e : Ent}, e ∈ l → wt (l.erase e) + e.1.length = wt l
  | x :: l, e, h => by
    by_cases hx : x = e
    · subst hx; simp [wt, List.erase_cons_head]; omega
    · rw [List.erase_cons_tail (by simpa using hx)]
      have h' : e ∈ l := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hx
        · exact h
      have := wt_erase h'
      simp only [wt, List.map_cons, List.sum_cons] at *; omega

/-! ## One pluck -/

/-- A pluck event `(C, I, Ps)`: vertex core `C` (coordinates of `vs`), inner edges `I` on `C`,
and `p` petals, each a bounded partial matching containing `I` with an edge outside `I`, every
edge outside `I` having an endpoint outside `C`; two petals share vertices only inside `C`. -/
def MEv (p ℓ n : Nat) (ev : List Nat × List (Nat × Nat) × List (List (Nat × Nat))) : Prop :=
  ev.2.2.length = p ∧ ev.1.length ≤ 2 * ℓ ∧
  (∀ e ∈ ev.2.1, 2 * e.1 ∈ ev.1 ∧ 2 * e.2 + 1 ∈ ev.1) ∧
  (∀ P ∈ ev.2.2, P.Nodup ∧ isM P = true ∧ P.length ≤ ℓ ∧ (∀ x ∈ P, x.1 < n ∧ x.2 < n) ∧
    (∀ e ∈ ev.2.1, e ∈ P) ∧ (∃ e ∈ P, e ∉ ev.2.1) ∧
    (∀ e ∈ P, e ∉ ev.2.1 → 2 * e.1 ∉ ev.1 ∨ 2 * e.2 + 1 ∉ ev.1)) ∧
  ev.2.2.Pairwise (fun P Q => ∀ x, x ∈ vs P → x ∈ vs Q → x ∈ ev.1)

/-- The sunflower threshold: `(3ℓ)! (p (2ℓ+1)^{2ℓ})^{3ℓ}`. -/
def thr (p ℓ : Nat) : Nat := fact (3 * ℓ) * (p * (2 * ℓ + 1) ^ (2 * ℓ)) ^ (3 * ℓ)

theorem mpluck_step (p ℓ n : Nat) (hp : 1 ≤ p) (a : MA) (hI : MInv n ℓ a)
    (hd : a.ents.Pairwise (fun u v => same u.1 v.1 = false)) (hB : thr p ℓ < a.ents.length) :
    ∃ b : MA, ∃ ev : List Nat × List (Nat × Nat) × List (List (Nat × Nat)),
      b.base = a.base ∧ MEv p ℓ n ev ∧ MInv n ℓ b ∧ wt b.ents < wt a.ents ∧
      (∀ H, eval a H ≤ eval b H) ∧
      (∀ H, eval b H ≤ eval a H ∨ (pres H ev.2.1 ∧ ∀ P ∈ ev.2.2, ¬ pres H P)) := by
  let N0 := (2 * ℓ + 1) ^ (2 * ℓ)
  let σ : Ent → List Nat := fun e => enc n e.1
  have hlen : ∀ e ∈ a.ents, (σ e).length ≤ 3 * ℓ := by
    intro e he; simp only [σ, enc_length]; have := (hI e he).2.2.1; omega
  have hdist : a.ents.Pairwise (Distinct σ) :=
    hd.imp_of_mem fun hu hv h => distinct_enc (hI _ hu).2.2.2 (hI _ hv).2.2.2 h
  obtain ⟨G, hGl, hGF, hGd, hGp⟩ := sunflower (p * N0 + 1) (3 * ℓ) σ a.ents hlen hdist
    (by simpa [thr, N0] using hB)
  obtain ⟨S₀, hS₀⟩ : ∃ S₀, S₀ ∈ G := List.exists_mem_of_ne_nil G (by
    intro h; rw [h] at hGl; simp at hGl)
  let C := (vs S₀.1).filter fun x => G.all fun E => decide (x ∈ vs E.1)
  have hCG : ∀ x ∈ C, ∀ E ∈ G, x ∈ vs E.1 := by
    intro x hx E hE
    have := (List.mem_filter.1 hx).2
    simp only [List.all_eq_true, decide_eq_true_eq] at this
    exact this E hE
  have hClen : C.length ≤ 2 * ℓ := by
    have h1 := List.length_filter_le (fun x => G.all fun E => decide (x ∈ vs E.1)) (vs S₀.1)
    have h2 := vs_length S₀.1
    have h3 := (hI S₀ (hGF S₀ hS₀)).2.2.1
    simp only [C]; omega
  -- two petals share vertices only inside `C`
  have hpet : G.Pairwise (fun E F => ∀ x, x ∈ vs E.1 → x ∈ vs F.1 → x ∈ C) := by
    apply hGp.imp
    intro E F h x hxE hxF
    have hall : ∀ R ∈ G, x ∈ vs R.1 := by
      rcases vs_enc (n := n) hxE with ⟨i, rfl, hi⟩ | ⟨j, rfl, hj⟩
      · intro R hR
        exact left_enc.1 (h _ hi (left_enc.2 hxF) R hR)
      · intro R hR
        exact right_enc.1 (h _ hj (right_enc.2 hxF) R hR)
    exact List.mem_filter.2 ⟨hall S₀ hS₀, by simpa using hall⟩
  -- pigeonhole on the inner codes
  have hU : (allL (alph C) C.length).length ≤ N0 := by
    rw [allL_length]
    have : (alph C).length = C.length + 1 := by simp [alph]
    rw [this]
    exact Nat.le_trans (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_right (by omega) hClen)
  obtain ⟨u, hu⟩ := pigeon (fun E : Ent => code C E.1) p (allL (alph C) C.length) G
    (fun E _ => code_mem C E.1) (by rw [hGl]; have := Nat.mul_le_mul_left p hU; omega)
  let Gu := G.filter fun E => decide (code C E.1 = u)
  let q : Ent → Bool := fun E => E.1.any fun e => !inner C e
  have hGuG : Gu.Sublist G := List.filter_sublist
  have hcode : ∀ E ∈ Gu, code C E.1 = u := fun E hE => by simpa using (List.mem_filter.1 hE).2
  -- at most one all-inner petal per code
  have hall1 : (Gu.filter fun E => !q E).length ≤ 1 := by
    apply le1 (R := Distinct σ) _ Gu _ (hGd.sublist hGuG)
    intro E hE F hF hqE hqF hEF
    have hin : ∀ X ∈ Gu, (!q X) = true → ∀ e ∈ X.1, inner C e = true := by
      intro X _ hX e he
      simp only [q, Bool.not_eq_true', List.any_eq_false, Bool.not_eq_false] at hX
      exact hX e he
    have hME := (hI E (hGF E (hGuG.subset hE))).2.1
    have hMF := (hI F (hGF F (hGuG.subset hF))).2.1
    have hc : code C E.1 = code C F.1 := (hcode E hE).trans (hcode F hF).symm
    have hs : ∀ e, e ∈ E.1 ↔ e ∈ F.1 := fun e =>
      ⟨fun h => code_inner hME hc h (hin E hE hqE e h),
       fun h => code_inner hMF hc.symm h (hin F hF hqF e h)⟩
    obtain ⟨y, hy⟩ := hEF
    apply hy
    simp only [σ, mem_enc]
    exact ⟨fun ⟨e, he, h⟩ => ⟨e, (hs e).1 he, h⟩, fun ⟨e, he, h⟩ => ⟨e, (hs e).2 he, h⟩⟩
  have hGu0 : p ≤ (Gu.filter q).length := by
    have := Programme.«20261024-1633-proof-complexity».Sunflower.len_split q Gu
    have : p < Gu.length := hu
    omega
  let Ps := (Gu.filter q).take p
  have hPsl : Ps.length = p := by simp [Ps]; omega
  have hPsG : Ps.Sublist G := (List.take_sublist _ _).trans (List.filter_sublist.trans hGuG)
  have hPsGu : ∀ E ∈ Ps, E ∈ Gu ∧ q E = true := fun E hE =>
    List.mem_filter.1 ((List.take_sublist _ _).subset hE)
  obtain ⟨Em, hEm, hmin⟩ := exists_min Ps (by intro h; rw [h] at hPsl; simp at hPsl; omega)
  have hEma : Em ∈ a.ents := hGF Em (hPsG.subset hEm)
  have hIEm := hI Em hEma
  let I := Em.1.filter (inner C)
  have hIsub : I.Sublist Em.1 := List.filter_sublist
  have hIin : ∀ e ∈ I, inner C e = true := fun e he => (List.mem_filter.1 he).2
  -- facts on each petal
  have hpf : ∀ E ∈ Ps, (∀ e ∈ I, e ∈ E.1) ∧ (∃ e ∈ E.1, e ∉ I) ∧
      (∀ e ∈ E.1, e ∉ I → 2 * e.1 ∉ C ∨ 2 * e.2 + 1 ∉ C) := by
    intro E hE
    obtain ⟨hEGu, hqE⟩ := hPsGu E hE
    have hc : code C Em.1 = code C E.1 := (hcode Em (hPsGu Em hEm).1).trans (hcode E hEGu).symm
    have hME := (hI E (hGF E (hPsG.subset hE))).2.1
    refine ⟨fun e he => code_inner hIEm.2.1 hc (hIsub.subset he) (hIin e he), ?_, ?_⟩
    · simp only [q, List.any_eq_true, Bool.not_eq_true'] at hqE
      obtain ⟨e, he, hne⟩ := hqE
      exact ⟨e, he, fun h => by rw [hIin e h] at hne; exact Bool.noConfusion hne⟩
    · intro e he hnI
      have hni : inner C e = false := by
        cases hie : inner C e
        · rfl
        · exact absurd (List.mem_filter.2 ⟨code_inner hME hc.symm he hie, hie⟩) hnI
      simp only [inner, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hni
      exact hni
  have hIlt : I.length < Em.1.length := by
    obtain ⟨e, he, hnI⟩ := (hpf Em hEm).2.1
    apply List.length_filter_lt_length_iff_exists.2
    refine ⟨e, he, ?_⟩
    intro h; exact hnI (List.mem_filter.2 ⟨he, h⟩)
  refine ⟨⟨a.base, (I, Em.2) :: a.ents.erase Em⟩, (C, I, Ps.map Prod.fst), rfl, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by simp [hPsl], hClen, ?_, ?_, ?_⟩
    · intro e he
      have := hIin e he
      simp only [inner, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this
    · intro P hP
      obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hP
      have := hI E (hGF E (hPsG.subset hE))
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2, hpf E hE⟩
    · exact List.pairwise_map.2 (hpet.sublist hPsG)
  · intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨hIsub.nodup hIEm.1, isM_sub hIsub hIEm.2.1,
        Nat.le_trans hIsub.length_le hIEm.2.2.1, fun x hx => hIEm.2.2.2 x (hIsub.subset hx)⟩
    · exact hI e ((List.erase_sublist ..).subset he)
  · have := wt_erase hEma
    show I.length + wt (a.ents.erase Em) < wt a.ents
    omega
  · intro H
    apply eval_le_of
    intro e he hpe
    rcases List.mem_cons.1 he with h | h
    · exact h ▸ evalL_base H _ _
    · by_cases hx : e = Em
      · subst hx
        exact eval_ent (e := (I, e.2)) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          (pres_sub (fun x hx => hIsub.subset hx) hpe)
      · exact eval_ent (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ((List.mem_erase_of_ne hx).2 h))) hpe
  · intro H
    by_cases hb : pres H I ∧ ∀ P ∈ Ps.map Prod.fst, ¬ pres H P
    · exact Or.inr hb
    · left
      apply eval_le_of
      intro e he hpe
      rcases List.mem_cons.1 he with h | h
      · exact h ▸ evalL_base H _ _
      · rcases List.mem_cons.1 h with h | h
        · subst h
          obtain ⟨P, hP, hpP⟩ : ∃ P ∈ Ps.map Prod.fst, pres H P := by
            apply Classical.byContradiction
            intro hn
            exact hb ⟨hpe, fun P hP hc => hn ⟨P, hP, hc⟩⟩
          obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hP
          exact Int.le_trans (hmin E hE) (eval_ent (List.mem_cons_of_mem _ (hGF E (hPsG.subset hE))) hpP)
        · exact eval_ent (List.mem_cons_of_mem _ ((List.erase_sublist ..).subset h)) hpe

/-! ## Closing -/

/-- **Closing matching approximators.** Every approximator with `MInv n ℓ` closes to `b` with the
same base, `MInv n ℓ`, and at most `thr p ℓ` entries; `b` is never below `a`, and above `a` on `H`
only at one of at most `wt a` recorded events `MEv p ℓ n` whose inner edges `I` are present in
`H` and none of whose petals is. -/
theorem mclose (p ℓ n : Nat) (hp : 1 ≤ p) : ∀ N (a : MA), wt a.ents < N → MInv n ℓ a →
    ∃ b : MA, ∃ evs : List (List Nat × List (Nat × Nat) × List (List (Nat × Nat))),
      b.base = a.base ∧ MInv n ℓ b ∧ b.ents.length ≤ thr p ℓ ∧ evs.length ≤ wt a.ents ∧
      (∀ ev ∈ evs, MEv p ℓ n ev) ∧
      (∀ H, eval a H ≤ eval b H) ∧
      (∀ H, eval b H ≤ eval a H ∨ ∃ ev ∈ evs, pres H ev.2.1 ∧ ∀ P ∈ ev.2.2, ¬ pres H P) := by
  intro N
  induction N with
  | zero => intro a h; omega
  | succ N ih =>
    intro a hw hI
    obtain ⟨m1, m2, m3, m4⟩ := mrg_facts a.ents
    have m4' : ∀ H, eval (mg a) H = eval a H := fun H => m4 H a.base
    have hI' : MInv n ℓ (mg a) := by
      intro e he
      obtain ⟨e', he', h⟩ := m1 e he
      rw [h]; exact hI e' he'
    by_cases hbig : thr p ℓ < (mg a).ents.length
    · obtain ⟨b1, ev, hb1, hEv, hIb1, hwb1, hge, hle⟩ := mpluck_step p ℓ n hp (mg a) hI' m2 hbig
      have hw1 : wt b1.ents < N := by
        have : wt (mg a).ents ≤ wt a.ents := m3
        omega
      obtain ⟨b, evs, c1, c2, c3, c4, c5, c6, c7⟩ := ih b1 hw1 hIb1
      refine ⟨b, ev :: evs, by rw [c1, hb1]; rfl, c2, c3, ?_, ?_, ?_, ?_⟩
      · have : wt (mg a).ents ≤ wt a.ents := m3
        simp only [List.length_cons]; omega
      · intro e he
        rcases List.mem_cons.1 he with h | h
        · exact h ▸ hEv
        · exact c5 e h
      · intro H
        rw [← m4' H]
        exact Int.le_trans (hge H) (c6 H)
      · intro H
        rcases c7 H with h | ⟨e, he, hc⟩
        · rcases hle H with h' | h'
          · left; rw [← m4' H]; exact Int.le_trans h h'
          · exact Or.inr ⟨ev, List.mem_cons_self .., h'⟩
        · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, hc⟩
    · exact ⟨mg a, [], rfl, hI', by omega, by simp, by simp,
        fun H => Int.le_of_eq (m4' H).symm, fun H => Or.inl (Int.le_of_eq (m4' H))⟩

/-- `wt` is at most `ℓ` times the number of entries under `MInv`. -/
theorem wt_le (n ℓ : Nat) : ∀ (l : List Ent), (∀ e ∈ l, e.1.length ≤ ℓ) → wt l ≤ ℓ * l.length
  | [], _ => by simp [wt]
  | e :: l, h => by
    have := wt_le n ℓ l fun x hx => h x (List.mem_cons_of_mem _ hx)
    have h1 := h e (List.mem_cons_self ..)
    simp only [wt, List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ] at *
    omega

end Programme.«20261025-0805-proof-complexity».MPluck

#print axioms Programme.«20261025-0805-proof-complexity».MPluck.mpluck_step
#print axioms Programme.«20261025-0805-proof-complexity».MPluck.mclose
