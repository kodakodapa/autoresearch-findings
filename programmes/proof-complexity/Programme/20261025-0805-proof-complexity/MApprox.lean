import Programme.«20261025-0805-proof-complexity».PermCount

/-!
# Matching approximators (M1 of P88)

Approximators for monotone real formulas on the edge variables of $K_{n,n}$, with entries indexed
by edge lists `P : List (Nat × Nat)` (left vertex, right vertex). On a bipartite graph `H` an
approximator evaluates to the maximum of its base value and of the values of the entries all of
whose edges are present in `H`.

Deterministic layer (no counting):
* `amap_eval`, `comb_eval`: unary and binary monotone gates are **exact on every graph** (edge
  presence is closed under unions, unlike clique tests);
* `trim_le`, `trim_ge`: deleting entries with more than `ℓ` edges only lowers values, and is exact
  when no long entry is present;
* `dropM_le`, `dropM_pm`: deleting entries that are not matchings only lowers values, and is exact
  on the perfect-matching graphs `pmG σ` for duplicate-free `σ`;
* `pm_fits`: an entry present in `pmG σ` fits `σ` in the sense of `Work.PermCount.fitsP`, so
  `Work.PermCount.pm_count` counts the perfect matchings hit by a trimmed entry;
* `vG`: the Hall-violator graphs of P88 (edge `(i,j)` absent iff `i ∈ S`, `j ∉ T`) and the vertex
  encoding `vs` (left `i ↦ 2i`, right `j ↦ 2j+1`) used for the vertex sunflowers of M2.
-/

namespace Programme.«20261025-0805-proof-complexity».MApprox

open Programme.«20261025-0805-proof-complexity».PermCount (fitsP)

abbrev Ent := List (Nat × Nat) × Int

/-- All edges of `P` are present in `H`. -/
def pres (H : Nat → Nat → Bool) (P : List (Nat × Nat)) : Prop := ∀ e ∈ P, H e.1 e.2 = true

instance (H : Nat → Nat → Bool) (P : List (Nat × Nat)) : Decidable (pres H P) := by
  unfold pres; infer_instance

theorem pres_append {H : Nat → Nat → Bool} {P Q : List (Nat × Nat)} :
    pres H (P ++ Q) ↔ pres H P ∧ pres H Q := by
  simp only [pres, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

theorem pres_sub {H : Nat → Nat → Bool} {P Q : List (Nat × Nat)} (h : ∀ e ∈ P, e ∈ Q)
    (hQ : pres H Q) : pres H P := fun e he => hQ e (h e he)

structure MA where
  base : Int
  ents : List Ent

def evalL (H : Nat → Nat → Bool) (v₀ : Int) : List Ent → Int
  | [] => v₀
  | e :: A => if pres H e.1 then max e.2 (evalL H v₀ A) else evalL H v₀ A

def eval (a : MA) (H : Nat → Nat → Bool) : Int := evalL H a.base a.ents

/-- Entries together with the base entry `([], base)`. -/
def ent (a : MA) : List Ent := ([], a.base) :: a.ents

theorem evalL_base (H : Nat → Nat → Bool) (v₀ : Int) : ∀ A, v₀ ≤ evalL H v₀ A
  | [] => Int.le_refl _
  | e :: A => by
    have := evalL_base H v₀ A
    unfold evalL; split <;> omega

theorem evalL_ent (H : Nat → Nat → Bool) (v₀ : Int) :
    ∀ A, ∀ e ∈ A, pres H e.1 → e.2 ≤ evalL H v₀ A
  | [], _, h, _ => by simp at h
  | x :: A, e, h, hp => by
    have ih := evalL_ent H v₀ A
    unfold evalL
    rcases List.mem_cons.1 h with rfl | h
    · rw [if_pos hp]; omega
    · have := ih e h hp
      split <;> omega

theorem evalL_attain (H : Nat → Nat → Bool) (v₀ : Int) :
    ∀ A, evalL H v₀ A = v₀ ∨ ∃ e ∈ A, pres H e.1 ∧ evalL H v₀ A = e.2
  | [] => Or.inl rfl
  | x :: A => by
    have ih := evalL_attain H v₀ A
    unfold evalL
    split
    · rename_i hx
      by_cases hm : x.2 ≤ evalL H v₀ A
      · rw [Int.max_eq_right hm]
        rcases ih with h | ⟨e, he, hp, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, hp, h⟩
      · rw [Int.max_eq_left (by omega)]
        exact Or.inr ⟨x, List.mem_cons_self .., hx, rfl⟩
    · rcases ih with h | ⟨e, he, hp, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, hp, h⟩

/-- `eval` is the maximum over the present entries of `ent a`. -/
theorem eval_ent {a : MA} {H : Nat → Nat → Bool} {e : Ent} (h : e ∈ ent a) (hp : pres H e.1) :
    e.2 ≤ eval a H := by
  rcases List.mem_cons.1 h with rfl | h
  · exact evalL_base H _ _
  · exact evalL_ent H _ _ e h hp

theorem eval_attain (a : MA) (H : Nat → Nat → Bool) :
    ∃ e ∈ ent a, pres H e.1 ∧ eval a H = e.2 := by
  rcases evalL_attain H a.base a.ents with h | ⟨e, he, hp, h⟩
  · exact ⟨([], a.base), List.mem_cons_self .., by simp [pres], h⟩
  · exact ⟨e, List.mem_cons_of_mem _ he, hp, h⟩

/-- Domination: if every present entry of `a` is dominated by `c`, then `eval a ≤ c`. -/
theorem eval_le_of {a : MA} {H : Nat → Nat → Bool} {c : Int}
    (h : ∀ e ∈ ent a, pres H e.1 → e.2 ≤ c) : eval a H ≤ c := by
  obtain ⟨e, he, hp, h'⟩ := eval_attain a H
  rw [h']; exact h e he hp

/-! ## Gates -/

def constA (k : Int) : MA := ⟨k, []⟩

theorem const_eval (k : Int) (H : Nat → Nat → Bool) : eval (constA k) H = k := rfl

/-- Input approximator of the edge variable `(i,j)`. -/
def inpA (i j : Nat) : MA := ⟨0, [([(i, j)], 1)]⟩

theorem inp_eval (i j : Nat) (H : Nat → Nat → Bool) :
    eval (inpA i j) H = if H i j then 1 else 0 := by
  by_cases h : H i j = true
  · have : pres H [(i, j)] := by simp [pres, h]
    simp [eval, evalL, inpA, this, h]; decide
  · have : ¬ pres H [(i, j)] := by simp [pres, h]
    simp [eval, evalL, inpA, this, h]

def amap (g : Int → Int) (a : MA) : MA := ⟨g a.base, a.ents.map fun e => (e.1, g e.2)⟩

theorem amap_eval (g : Int → Int) (hg : ∀ x y, x ≤ y → g x ≤ g y) (a : MA)
    (H : Nat → Nat → Bool) : eval (amap g a) H = g (eval a H) := by
  apply Int.le_antisymm
  · apply eval_le_of
    intro e he hp
    rcases List.mem_cons.1 he with rfl | he
    · exact hg _ _ (evalL_base H _ _)
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      exact hg _ _ (eval_ent (List.mem_cons_of_mem _ he0) hp)
  · obtain ⟨e, he, hp, h⟩ := eval_attain a H
    rw [h]
    rcases List.mem_cons.1 he with rfl | he
    · exact evalL_base H _ _
    · exact eval_ent (e := (e.1, g e.2)) (List.mem_cons_of_mem _ (List.mem_map_of_mem he)) hp

/-- Union of edge lists, without repeating edges of `P`. -/
def uni (P Q : List (Nat × Nat)) : List (Nat × Nat) := P ++ Q.filter fun e => !decide (e ∈ P)

theorem mem_uni {P Q : List (Nat × Nat)} {e : Nat × Nat} : e ∈ uni P Q ↔ e ∈ P ∨ e ∈ Q := by
  simp only [uni, List.mem_append, List.mem_filter]
  by_cases h : e ∈ P <;> simp [h]

theorem pres_uni {H : Nat → Nat → Bool} {P Q : List (Nat × Nat)} :
    pres H (uni P Q) ↔ pres H P ∧ pres H Q := by
  simp only [pres, mem_uni]
  exact ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

/-- Binary gate: `{(P ∪ Q, φ v w)}` over the entries of `a` and `b`, including base entries. -/
def comb (φ : Int → Int → Int) (a b : MA) : MA :=
  ⟨φ a.base b.base, ((ent a).flatMap fun e => (ent b).map fun f => (uni e.1 f.1, φ e.2 f.2)).tail⟩

theorem comb_ent (φ : Int → Int → Int) (a b : MA) :
    ent (comb φ a b) = (ent a).flatMap fun e => (ent b).map fun f => (uni e.1 f.1, φ e.2 f.2) := by
  simp [comb, ent, uni]

theorem mem_comb {φ : Int → Int → Int} {a b : MA} {x : Ent} (h : x ∈ ent (comb φ a b)) :
    ∃ e ∈ ent a, ∃ f ∈ ent b, x = (uni e.1 f.1, φ e.2 f.2) := by
  rw [comb_ent] at h
  obtain ⟨e, he, hx⟩ := List.mem_flatMap.1 h
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
  exact ⟨e, he, f, hf, rfl⟩

theorem comb_len (φ : Int → Int → Int) (a b : MA) :
    (comb φ a b).ents.length + 1 = (a.ents.length + 1) * (b.ents.length + 1) := by
  have h := congrArg List.length (comb_ent φ a b)
  have hl : ∀ l : List Ent, (l.flatMap fun e => (ent b).map fun f => (uni e.1 f.1, φ e.2 f.2)).length
      = l.length * (b.ents.length + 1) := by
    intro l; induction l with
    | nil => simp
    | cons x l ih =>
      have e1 : (ent b).length = b.ents.length + 1 := rfl
      simp only [List.flatMap_cons, List.length_append, List.length_map, ih, e1,
        List.length_cons, Nat.succ_mul]; omega
  rw [hl] at h
  simpa [ent] using h

/-- **Binary gates are exact on every graph.** -/
theorem comb_eval (φ : Int → Int → Int) (hφ : ∀ x x' y y', x ≤ x' → y ≤ y' → φ x y ≤ φ x' y')
    (a b : MA) (H : Nat → Nat → Bool) : eval (comb φ a b) H = φ (eval a H) (eval b H) := by
  apply Int.le_antisymm
  · apply eval_le_of
    intro x hx hp
    obtain ⟨e, he, f, hf, rfl⟩ := mem_comb hx
    obtain ⟨h1, h2⟩ := pres_uni.1 hp
    exact hφ _ _ _ _ (eval_ent he h1) (eval_ent hf h2)
  · obtain ⟨e, he, h1, he'⟩ := eval_attain a H
    obtain ⟨f, hf, h2, hf'⟩ := eval_attain b H
    rw [he', hf']
    have hx : (uni e.1 f.1, φ e.2 f.2) ∈ ent (comb φ a b) := by
      rw [comb_ent]
      exact List.mem_flatMap.2 ⟨e, he, List.mem_map.2 ⟨f, hf, rfl⟩⟩
    exact eval_ent hx (pres_uni.2 ⟨h1, h2⟩)

/-! ## Deleting entries -/

/-- Keep the entries satisfying `q`. -/
def keep (q : Ent → Bool) (a : MA) : MA := ⟨a.base, a.ents.filter q⟩

theorem keep_le (q : Ent → Bool) (a : MA) (H : Nat → Nat → Bool) :
    eval (keep q a) H ≤ eval a H := by
  apply eval_le_of
  intro e he hp
  rcases List.mem_cons.1 he with rfl | he
  · exact evalL_base H _ _
  · exact eval_ent (List.mem_cons_of_mem _ (List.mem_filter.1 he).1) hp

theorem keep_ge (q : Ent → Bool) (a : MA) (H : Nat → Nat → Bool)
    (h : ∀ e ∈ a.ents, pres H e.1 → q e = true) : eval a H ≤ eval (keep q a) H := by
  apply eval_le_of
  intro e he hp
  rcases List.mem_cons.1 he with rfl | he
  · exact evalL_base H _ _
  · exact eval_ent (List.mem_cons_of_mem _ (List.mem_filter.2 ⟨he, h e he hp⟩)) hp

/-- Delete entries with more than `ℓ` edges. -/
def trim (ℓ : Nat) (a : MA) : MA := keep (fun e => decide (e.1.length ≤ ℓ)) a

theorem trim_le (ℓ : Nat) (a : MA) (H : Nat → Nat → Bool) : eval (trim ℓ a) H ≤ eval a H :=
  keep_le _ a H

theorem trim_ge (ℓ : Nat) (a : MA) (H : Nat → Nat → Bool)
    (h : ∀ e ∈ a.ents, pres H e.1 → e.1.length ≤ ℓ) : eval a H ≤ eval (trim ℓ a) H :=
  keep_ge _ a H fun e he hp => by simpa using h e he hp

/-- `P` is a partial matching (left ends distinct, right ends distinct). -/
def isM (P : List (Nat × Nat)) : Bool := decide ((P.map (·.1)).Nodup ∧ (P.map (·.2)).Nodup)

/-- Delete the entries that are not partial matchings. -/
def dropM (a : MA) : MA := keep (fun e => isM e.1) a

theorem dropM_le (a : MA) (H : Nat → Nat → Bool) : eval (dropM a) H ≤ eval a H := keep_le _ a H

/-- The perfect matching `i ↦ σ[i]` as a bipartite graph. -/
def pmG (σ : List Nat) (i j : Nat) : Bool := σ[i]? == some j

theorem nodup_map_of {f : Nat × Nat → Nat} :
    ∀ {P : List (Nat × Nat)}, P.Nodup → (∀ x ∈ P, ∀ y ∈ P, f x = f y → x = y) → (P.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: P, hn, h => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_of hn.2 fun u hu v hv => h u (List.mem_cons_of_mem _ hu) v
      (List.mem_cons_of_mem _ hv)⟩
    obtain ⟨y, hy, hxy⟩ := List.mem_map.1 hm
    exact hn.1 (h y (List.mem_cons_of_mem _ hy) x (List.mem_cons_self ..) hxy ▸ hy)

theorem getElem?_inj {σ : List Nat} (hσ : σ.Nodup) {i i' j : Nat} (h : σ[i]? = some j)
    (h' : σ[i']? = some j) : i = i' := by
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.1 h
  obtain ⟨hi', e'⟩ := List.getElem?_eq_some_iff.1 h'
  exact (List.Nodup.getElem_inj hσ).1 (e.trans e'.symm)

/-- A duplicate-free edge list present in a perfect matching graph is a partial matching. -/
theorem pres_pm_isM {σ : List Nat} (hσ : σ.Nodup) {P : List (Nat × Nat)} (hP : P.Nodup)
    (hp : pres (pmG σ) P) : isM P = true := by
  have hp' : ∀ e ∈ P, σ[e.1]? = some e.2 := fun e he => by simpa [pmG] using hp e he
  simp only [isM, decide_eq_true_eq]
  refine ⟨nodup_map_of hP fun x hx y hy hxy => ?_, nodup_map_of hP fun x hx y hy hxy => ?_⟩
  · have h1 := hp' x hx; have h2 := hp' y hy
    rw [hxy, h2] at h1
    exact Prod.ext hxy (Option.some.inj h1).symm
  · have h1 := hp' x hx; have h2 := hp' y hy
    rw [← hxy] at h2
    exact Prod.ext (getElem?_inj hσ h1 h2) hxy

theorem dropM_pm (a : MA) {σ : List Nat} (hσ : σ.Nodup) (hn : ∀ e ∈ a.ents, e.1.Nodup) :
    eval a (pmG σ) ≤ eval (dropM a) (pmG σ) :=
  keep_ge _ a _ fun e he hp => pres_pm_isM hσ (hn e he) hp

theorem pm_fits {σ : List Nat} {P : List (Nat × Nat)} (hp : pres (pmG σ) P) : fitsP P σ = true := by
  simp only [fitsP, List.all_eq_true]
  intro e he
  simpa [pmG] using hp e he

theorem fits_pm {σ : List Nat} {P : List (Nat × Nat)} (h : fitsP P σ = true) : pres (pmG σ) P := by
  simp only [fitsP, List.all_eq_true] at h
  intro e he
  simpa [pmG] using h e he

theorem nodup_uni {P Q : List (Nat × Nat)} (hP : P.Nodup) (hQ : Q.Nodup) : (uni P Q).Nodup := by
  have hf : (Q.filter fun e => !decide (e ∈ P)).Nodup := List.Sublist.nodup List.filter_sublist hQ
  refine List.nodup_append.2 ⟨hP, hf, fun x hx y hy hxy => ?_⟩
  subst hxy
  simp [List.mem_filter, hx] at hy

/-! ## Negative test graphs and the vertex encoding -/

/-- The Hall-violator graph of P88: edge `(i,j)` absent iff `S i` and not `T j`. -/
def vG (S T : Nat → Bool) (i j : Nat) : Bool := !(S i && !T j)

/-- Vertex set of an edge list, left `i ↦ 2i`, right `j ↦ 2j+1`. -/
def vs (P : List (Nat × Nat)) : List Nat := P.flatMap fun e => [2 * e.1, 2 * e.2 + 1]

theorem mem_vs {P : List (Nat × Nat)} {x : Nat} :
    x ∈ vs P ↔ ∃ e ∈ P, x = 2 * e.1 ∨ x = 2 * e.2 + 1 := by
  simp only [vs, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]

theorem vs_length (P : List (Nat × Nat)) : (vs P).length = 2 * P.length := by
  induction P with
  | nil => rfl
  | cons e P ih => simp [vs, List.flatMap_cons] at *; omega

theorem vs_uni_sub {P Q : List (Nat × Nat)} {x : Nat} (h : x ∈ vs (uni P Q)) :
    x ∈ vs P ∨ x ∈ vs Q := by
  obtain ⟨e, he, hx⟩ := mem_vs.1 h
  rcases mem_uni.1 he with he | he
  · exact Or.inl (mem_vs.2 ⟨e, he, hx⟩)
  · exact Or.inr (mem_vs.2 ⟨e, he, hx⟩)

/-! ## Finishing a gate without closing -/

/-- The long matching entries deleted by `trim ℓ (dropM c)`: the positive error sets. -/
def longM (ℓ : Nat) (c : MA) : List (List (Nat × Nat)) :=
  ((c.ents.filter fun e => isM e.1 && decide (ℓ < e.1.length)).map Prod.fst)

theorem longM_length (ℓ : Nat) (c : MA) : (longM ℓ c).length ≤ c.ents.length := by
  simp only [longM, List.length_map]; exact List.length_filter_le _ _

theorem longM_mem {ℓ : Nat} {c : MA} {P : List (Nat × Nat)} (h : P ∈ longM ℓ c) :
    isM P = true ∧ ℓ < P.length := by
  simp only [longM, List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨e, ⟨_, h1, h2⟩, rfl⟩ := h
  exact ⟨h1, h2⟩

/-- `trim ℓ (dropM c)` only lowers values, and on every perfect matching `σ` it is exact unless
`σ` contains one of the entries of `longM ℓ c`. -/
theorem finish0 (ℓ : Nat) (c : MA) (hn : ∀ e ∈ c.ents, e.1.Nodup) :
    (∀ H, eval (trim ℓ (dropM c)) H ≤ eval c H) ∧
    (∀ σ : List Nat, σ.Nodup →
      eval c (pmG σ) ≤ eval (trim ℓ (dropM c)) (pmG σ) ∨ ∃ P ∈ longM ℓ c, fitsP P σ = true) := by
  refine ⟨fun H => Int.le_trans (trim_le ℓ _ H) (dropM_le c H), fun σ hσ => ?_⟩
  by_cases h : ∃ P ∈ longM ℓ c, fitsP P σ = true
  · exact Or.inr h
  · left
    refine Int.le_trans (dropM_pm c hσ hn) (trim_ge ℓ _ _ fun e he hp => ?_)
    have he' := List.mem_filter.1 he
    apply Nat.le_of_not_lt
    intro hl
    apply h
    refine ⟨e.1, List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he'.1, ?_⟩, rfl⟩, pm_fits hp⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨he'.2, hl⟩

end Programme.«20261025-0805-proof-complexity».MApprox

#print axioms Programme.«20261025-0805-proof-complexity».MApprox.comb_eval
#print axioms Programme.«20261025-0805-proof-complexity».MApprox.dropM_pm
#print axioms Programme.«20261025-0805-proof-complexity».MApprox.amap_eval
#print axioms Programme.«20261025-0805-proof-complexity».MApprox.finish0
