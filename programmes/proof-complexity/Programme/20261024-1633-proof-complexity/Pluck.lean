import Programme.«20261024-1633-proof-complexity».RealApprox

/-!
# Plucking sunflowers within a value class

The non-deterministic layer of the approximation method for monotone real formulas (C1 step 2).
An approximator (`Work.RealApprox.Approx`) is *closed* when, inside each value class, its entry
sets are pairwise distinct as sets and no more than `B` of them occur. Closing an approximator
repeatedly removes `p` petals of a sunflower that lie in one value class `v` and adds the core
with value `v`:
* `pluck_ge`: plucking never lowers the value, on any graph (so no positive errors);
* `pluck_le`: it can raise the value on `G` only if the core is a clique of `G` and no petal is
  (the events counted by `Work.Colour.petal_count`);
* `pluck_len`: it removes at least `p - 1` entries;
* `ddA_eval`: removing set-equivalent duplicates in a value class is exact.

`close` closes any approximator given the sunflower lemma as the hypothesis `SF p ℓ B`
(`Work.Sunflower.sunflower_sets` gives `SF p ℓ (ℓ! (p-1)^ℓ)`), and records the pluck events.
`class_count`: an approximator whose values lie in `(lo, lo + R]` with at most `B` entries per
class has at most `R B` entries.
-/

namespace Programme.«20261024-1633-proof-complexity».Pluck

open Programme.«20261024-1633-proof-complexity».RealApprox

/-! ## Comparing approximators -/

theorem dom {a b : Approx} {G : Nat → Nat → Bool}
    (h : ∀ e ∈ ent a, clq G e.1 → ∃ e' ∈ ent b, clq G e'.1 ∧ e.2 ≤ e'.2) :
    eval a G ≤ eval b G := by
  apply eval_le_of_cover
  intro e he hc
  obtain ⟨e', he', hc', hle⟩ := h e he hc
  exact Int.le_trans hle (eval_ent he' hc')

theorem clq_congr {G : Nat → Nat → Bool} {S T : List Nat} (h : ∀ y, y ∈ S ↔ y ∈ T) :
    clq G S ↔ clq G T :=
  ⟨clq_sub (fun i hi => (h i).2 hi), clq_sub (fun i hi => (h i).1 hi)⟩

/-! ## Cores -/

theorem clq_len1 (G : Nat → Nat → Bool) : ∀ {Y : List Nat}, Y.length ≤ 1 → clq G Y
  | [], _ => clq_nil G
  | [a], _ => by
    intro i hi j hj hij
    simp at hi hj
    exact absurd (hi.trans hj.symm) hij
  | _ :: _ :: _, h => by simp at h

/-- Cores of size at most one are replaced by the empty set (both are cliques of every graph). -/
def nc (Y : List Nat) : List Nat := if Y.length ≤ 1 then [] else Y

theorem clq_nc (G : Nat → Nat → Bool) (Y : List Nat) : clq G (nc Y) ↔ clq G Y := by
  unfold nc
  split
  · exact ⟨fun _ => clq_len1 G (by assumption), fun _ => clq_nil G⟩
  · exact Iff.rfl

theorem nc_sub (Y : List Nat) : ∀ x ∈ nc Y, x ∈ Y := by
  unfold nc; split
  · intro x h; simp at h
  · intro x h; exact h

theorem ns_of_nodup : ∀ {Y : List Nat}, Y.Nodup → 2 ≤ Y.length → ns Y := by
  intro Y hY hl i hi
  match Y, hY, hl with
  | a :: b :: Y', hY, _ =>
    have hab : a ≠ b := by
      have := List.nodup_cons.1 hY
      exact fun h => this.1 (h ▸ List.mem_cons_self ..)
    by_cases h : i = a
    · exact ⟨b, by simp, fun e => hab (h ▸ e.symm)⟩
    · exact ⟨a, List.mem_cons_self .., fun e => h e.symm⟩

theorem ns_nc {Y : List Nat} (hY : Y.Nodup) : ns (nc Y) := by
  unfold nc; split
  · exact ns_nil
  · exact ns_of_nodup hY (by omega)

/-! ## Plucking -/

/-- Entries kept by a pluck of the petals `P` in value class `v`. -/
def keep (v : Int) (P : List (List Nat)) (e : List Nat × Int) : Bool :=
  !(decide (e.2 = v) && decide (e.1 ∈ P))

/-- Remove the entries of value `v` whose set is a petal in `P`, add the core `Y` with value `v`. -/
def pluck (Y : List Nat) (v : Int) (P : List (List Nat)) (a : Approx) : Approx :=
  ⟨a.base, (nc Y, v) :: a.ents.filter (keep v P)⟩

theorem mem_ent_pluck {Y : List Nat} {v : Int} {P : List (List Nat)} {a : Approx}
    {e : List Nat × Int} (h : e ∈ ent (pluck Y v P a)) : e = (nc Y, v) ∨ e ∈ ent a := by
  rcases List.mem_cons.1 h with h | h
  · exact Or.inr (h ▸ List.mem_cons_self ..)
  · rcases List.mem_cons.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ (List.mem_filter.1 h).1)

/-- Plucking never lowers the value. -/
theorem pluck_ge {Y : List Nat} {v : Int} {P : List (List Nat)} (a : Approx)
    (hY : ∀ S ∈ P, ∀ x ∈ Y, x ∈ S) (G : Nat → Nat → Bool) :
    eval a G ≤ eval (pluck Y v P a) G := by
  apply dom
  intro e he hc
  rcases List.mem_cons.1 he with h | h
  · exact ⟨e, h ▸ List.mem_cons_self .., hc, Int.le_refl _⟩
  · by_cases hk : keep v P e = true
    · exact ⟨e, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_filter.2 ⟨h, hk⟩)),
        hc, Int.le_refl _⟩
    · have hk' : e.2 = v ∧ e.1 ∈ P := by simpa [keep] using hk
      refine ⟨(nc Y, v), List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_, Int.le_of_eq hk'.1⟩
      exact (clq_nc G Y).2 (clq_sub (hY e.1 hk'.2) hc)

/-- Plucking raises the value on `G` only if the core is a clique and no petal is. -/
theorem pluck_le {Y : List Nat} {v : Int} {P : List (List Nat)} (a : Approx)
    (G : Nat → Nat → Bool) (h : clq G Y → ∃ S ∈ P, (S, v) ∈ a.ents ∧ clq G S) :
    eval (pluck Y v P a) G ≤ eval a G := by
  apply dom
  intro e he hc
  rcases mem_ent_pluck he with h' | h'
  · subst h'
    obtain ⟨S, _, hS, hcS⟩ := h ((clq_nc G Y).1 hc)
    exact ⟨(S, v), List.mem_cons_of_mem _ hS, hcS, Int.le_refl _⟩
  · exact ⟨e, h', hc, Int.le_refl _⟩

/-! ## Length bookkeeping -/

theorem len_split {α : Type} (q : α → Bool) : ∀ l : List α,
    (l.filter q).length + (l.filter (fun x => !q x)).length = l.length
  | [] => rfl
  | x :: l => by
    have := len_split q l
    cases h : q x <;> simp [List.filter_cons, h] <;> omega

theorem nodup_len_le {α : Type} [DecidableEq α] : ∀ {P L : List α}, P.Nodup → (∀ x ∈ P, x ∈ L) →
    P.length ≤ L.length
  | [], _, _, _ => Nat.zero_le _
  | x :: P, L, hP, h => by
    have hx := h x (List.mem_cons_self ..)
    have hP' := List.nodup_cons.1 hP
    have := nodup_len_le (L := L.erase x) hP'.2 (fun y hy =>
      (List.mem_erase_of_ne (fun e => hP'.1 (by rw [← e]; exact hy))).2 (h y (List.mem_cons_of_mem _ hy)))
    rw [List.length_erase_of_mem hx] at this
    have := List.length_pos_of_mem hx
    simp; omega

/-- A pluck of `p` distinct petals of class `v` removes at least `p - 1` entries. -/
theorem pluck_len {Y : List Nat} {v : Int} {P : List (List Nat)} (a : Approx) (hP : P.Nodup)
    (hin : ∀ S ∈ P, (S, v) ∈ a.ents) :
    (pluck Y v P a).ents.length + P.length ≤ a.ents.length + 1 := by
  have hs := len_split (keep v P) a.ents
  have : P.length ≤ ((a.ents.filter fun x => !keep v P x).map Prod.fst).length := by
    apply nodup_len_le hP
    intro S hS
    exact List.mem_map.2 ⟨(S, v), List.mem_filter.2 ⟨hin S hS, by simp [keep, hS]⟩, rfl⟩
  simp only [List.length_map] at this
  show (a.ents.filter (keep v P)).length + 1 + P.length ≤ a.ents.length + 1
  omega

/-! ## Removing duplicates inside a value class -/

/-- Set equivalence, decided. -/
def seqv (S T : List Nat) : Bool := S.all (fun y => decide (y ∈ T)) && T.all (fun y => decide (y ∈ S))

theorem seqv_iff {S T : List Nat} : seqv S T = true ↔ ∀ y, y ∈ S ↔ y ∈ T := by
  simp only [seqv, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun h y => ⟨h.1 y, h.2 y⟩, fun h => ⟨fun y => (h y).1, fun y => (h y).2⟩⟩

/-- Same value and equivalent set. -/
def twin (e e' : List Nat × Int) : Bool := decide (e'.2 = e.2) && seqv e'.1 e.1

/-- Keep the first entry of every class of twins (`n` is fuel, at least the length). -/
def ddF : Nat → List (List Nat × Int) → List (List Nat × Int)
  | _, [] => []
  | 0, l => l
  | n + 1, e :: l => e :: ddF n (l.filter fun e' => !twin e e')

def dd (l : List (List Nat × Int)) : List (List Nat × Int) := ddF l.length l

theorem ddF_facts : ∀ n (l : List (List Nat × Int)), l.length ≤ n →
    (∀ x ∈ ddF n l, x ∈ l) ∧
    (∀ x ∈ l, ∃ y ∈ ddF n l, y.2 = x.2 ∧ ∀ z, z ∈ y.1 ↔ z ∈ x.1) ∧
    (ddF n l).Pairwise (fun x y => x.2 = y.2 → ∃ z, ¬ (z ∈ x.1 ↔ z ∈ y.1)) ∧
    (ddF n l).length ≤ l.length
  | _, [], _ => by simp [ddF]
  | 0, _ :: _, h => by simp at h
  | n + 1, e :: l, h => by
    have hl : (l.filter fun e' => !twin e e').length ≤ n := by
      have := List.length_filter_le (fun e' => !twin e e') l
      simp at h; omega
    obtain ⟨h1, h2, h3, h4⟩ := ddF_facts n _ hl
    simp only [ddF]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with hx | hx
      · exact hx ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_filter.1 (h1 x hx)).1
    · intro x hx
      rcases List.mem_cons.1 hx with hx | hx
      · exact ⟨e, List.mem_cons_self .., by rw [hx], fun z => by rw [hx]⟩
      · by_cases ht : twin e x = true
        · simp only [twin, Bool.and_eq_true, decide_eq_true_eq] at ht
          exact ⟨e, List.mem_cons_self .., ht.1.symm, fun z => (seqv_iff.1 ht.2 z).symm⟩
        · obtain ⟨y, hy, hy2, hy1⟩ := h2 x (List.mem_filter.2 ⟨hx, by simpa using ht⟩)
          exact ⟨y, List.mem_cons_of_mem _ hy, hy2, hy1⟩
    · refine List.Pairwise.cons ?_ h3
      intro y hy hv
      have hy' := (List.mem_filter.1 (h1 y hy)).2
      simp only [twin, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hy'
      rcases hy' with hy' | hy'
      · exact absurd hv.symm hy'
      · have : ¬ ∀ z, z ∈ y.1 ↔ z ∈ e.1 := fun hh => by
          rw [seqv_iff.2 hh] at hy'; exact Bool.noConfusion hy'
        apply Classical.byContradiction
        intro hn
        apply this
        intro z
        by_cases hz : z ∈ e.1 ↔ z ∈ y.1
        · exact hz.symm
        · exact absurd ⟨z, hz⟩ hn
    · have := List.length_filter_le (fun e' => !twin e e') l
      simp only [List.length_cons]; omega

theorem dd_facts (l : List (List Nat × Int)) :
    (∀ x ∈ dd l, x ∈ l) ∧
    (∀ x ∈ l, ∃ y ∈ dd l, y.2 = x.2 ∧ ∀ z, z ∈ y.1 ↔ z ∈ x.1) ∧
    (dd l).Pairwise (fun x y => x.2 = y.2 → ∃ z, ¬ (z ∈ x.1 ↔ z ∈ y.1)) ∧
    (dd l).length ≤ l.length :=
  ddF_facts _ l (Nat.le_refl _)

def ddA (a : Approx) : Approx := ⟨a.base, dd a.ents⟩

theorem ddA_eval (a : Approx) (G : Nat → Nat → Bool) : eval (ddA a) G = eval a G := by
  obtain ⟨h1, h2, _, _⟩ := dd_facts a.ents
  apply Int.le_antisymm
  · apply dom
    intro e he hc
    rcases List.mem_cons.1 he with h | h
    · exact ⟨e, h ▸ List.mem_cons_self .., hc, Int.le_refl _⟩
    · exact ⟨e, List.mem_cons_of_mem _ (h1 e h), hc, Int.le_refl _⟩
  · apply dom
    intro e he hc
    rcases List.mem_cons.1 he with h | h
    · exact ⟨e, h ▸ List.mem_cons_self .., hc, Int.le_refl _⟩
    · obtain ⟨y, hy, hy2, hy1⟩ := h2 e h
      exact ⟨y, List.mem_cons_of_mem _ hy, (clq_congr hy1).2 hc, Int.le_of_eq hy2.symm⟩

/-! ## Closing an approximator -/

/-- The sunflower lemma with threshold `B`, as a hypothesis (`Work.Sunflower.sunflower_sets`
proves it for `B = ℓ! (p-1)^ℓ`). -/
def SF (p ℓ B : Nat) : Prop :=
  ∀ F : List (List Nat), (∀ S ∈ F, S.length ≤ ℓ) →
    F.Pairwise (fun S T => ∃ y, ¬ (y ∈ S ↔ y ∈ T)) → B < F.length →
    ∃ G : List (List Nat), G.length = p ∧ (∀ S ∈ G, S ∈ F) ∧
      G.Pairwise (fun S T => ∃ y, ¬ (y ∈ S ↔ y ∈ T)) ∧
      G.Pairwise (fun S T => ∀ y, y ∈ S → y ∈ T → ∀ R ∈ G, y ∈ R)

/-- Entry sets: duplicate-free, at most `ℓ` vertices, all `< m`, no singleton part. -/
def Inv (ℓ m : Nat) (a : Approx) : Prop :=
  ∀ e ∈ a.ents, e.1.Nodup ∧ e.1.length ≤ ℓ ∧ (∀ x ∈ e.1, x < m) ∧ ns e.1

/-- A pluck event: core `Y` and `p` duplicate-free petals of size `≤ ℓ` on vertices `< m`, any two
meeting inside `Y`. -/
def Ev (p ℓ m : Nat) (ev : List Nat × List (List Nat)) : Prop :=
  ev.2.length = p ∧ (∀ S ∈ ev.2, S.Nodup ∧ S.length ≤ ℓ ∧ ∀ x ∈ S, x < m) ∧
    ev.2.Pairwise (fun S T => ∀ x, x ∈ S → x ∈ T → x ∈ ev.1)

/-- Class `v` of `a`: the entries with value `v`. -/
def cls (a : Approx) (v : Int) : List (List Nat × Int) := a.ents.filter fun e => decide (e.2 = v)

/-- One pluck on a duplicate-free approximator with an oversized class. -/
theorem pluck_step (p ℓ m B : Nat) (hp : 2 ≤ p) (hSF : SF p ℓ B) (a : Approx) (hI : Inv ℓ m a)
    (hd : a.ents.Pairwise (fun x y => x.2 = y.2 → ∃ z, ¬ (z ∈ x.1 ↔ z ∈ y.1)))
    (v : Int) (hv : B < (cls a v).length) :
    ∃ Y P, Ev p ℓ m (Y, P) ∧ Inv ℓ m (pluck Y v P a) ∧
      (pluck Y v P a).ents.length + (p - 1) ≤ a.ents.length ∧
      (∀ e ∈ (pluck Y v P a).ents, ∃ e' ∈ a.ents, e'.2 = e.2) ∧
      (∀ G, eval a G ≤ eval (pluck Y v P a) G) ∧
      (∀ G, eval (pluck Y v P a) G ≤ eval a G ∨ (clq G Y ∧ ∀ S ∈ P, ¬ clq G S)) := by
  let F := (cls a v).map Prod.fst
  have hFm : ∀ S ∈ F, (S, v) ∈ a.ents := by
    intro S hS
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hS
    have := List.mem_filter.1 he
    have hv : e.2 = v := by simpa using this.2
    exact hv ▸ this.1
  have hlen : ∀ S ∈ F, S.length ≤ ℓ := fun S hS => (hI _ (hFm S hS)).2.1
  have hpw : F.Pairwise (fun S T => ∃ y, ¬ (y ∈ S ↔ y ∈ T)) := by
    apply List.pairwise_map.2
    apply List.Pairwise.imp_of_mem (R := fun x y => x.2 = y.2 → ∃ z, ¬ (z ∈ x.1 ↔ z ∈ y.1))
    · intro x y hx hy h
      have hx2 : x.2 = v := by simpa using (List.mem_filter.1 hx).2
      have hy2 : y.2 = v := by simpa using (List.mem_filter.1 hy).2
      exact h (hx2.trans hy2.symm)
    · exact List.Pairwise.filter _ hd
  obtain ⟨G, hGl, hGF, hGd, hGp⟩ := hSF F hlen hpw (by simpa [F] using hv)
  have hGne : G ≠ [] := by intro h; subst h; simp at hGl; omega
  obtain ⟨S₀, G', hG⟩ : ∃ S₀ G', G = S₀ :: G' := by
    cases G with
    | nil => exact absurd rfl hGne
    | cons S₀ G' => exact ⟨S₀, G', rfl⟩
  let Y := S₀.filter fun x => G.all fun R => decide (x ∈ R)
  have hYsub : ∀ S ∈ G, ∀ x ∈ Y, x ∈ S := by
    intro S hS x hx
    have := (List.mem_filter.1 hx).2
    simp only [List.all_eq_true, decide_eq_true_eq] at this
    exact this S hS
  have hS₀ : S₀ ∈ G := hG ▸ List.mem_cons_self ..
  have hI₀ := hI _ (hFm S₀ (hGF S₀ hS₀))
  have hYnd : Y.Nodup :=
    List.nodup_iff_pairwise_ne.2 (List.Pairwise.filter _ (List.nodup_iff_pairwise_ne.1 hI₀.1))
  have hGnd : G.Nodup := List.nodup_iff_pairwise_ne.2 (hGd.imp fun {S T} ⟨y, hy⟩ e => by
    subst e; exact hy Iff.rfl)
  have hEv : Ev p ℓ m (Y, G) := by
    refine ⟨hGl, fun S hS => ?_, ?_⟩
    · have := hI _ (hFm S (hGF S hS)); exact ⟨this.1, this.2.1, this.2.2.1⟩
    · apply hGp.imp
      intro S T h x hxS hxT
      have hall := h x hxS hxT
      exact List.mem_filter.2 ⟨hall S₀ hS₀, by simpa using hall⟩
  refine ⟨Y, G, hEv, ?_, ?_, ?_, fun Gr => pluck_ge a hYsub Gr, fun Gr => ?_⟩
  · intro e he
    rcases List.mem_cons.1 he with h | h
    · subst h
      refine ⟨?_, ?_, ?_, ns_nc hYnd⟩
      · unfold nc; split
        · exact List.nodup_nil
        · exact hYnd
      · have := List.length_filter_le (fun x => G.all fun R => decide (x ∈ R)) S₀
        unfold nc; split
        · simp
        · have : S₀.length ≤ ℓ := hI₀.2.1
          exact Nat.le_trans (List.length_filter_le _ _) this
      · intro x hx
        exact hI₀.2.2.1 x (List.mem_filter.1 (nc_sub Y x hx)).1
    · exact hI e (List.mem_filter.1 h).1
  · have := pluck_len (Y := Y) a hGnd (fun S hS => hFm S (hGF S hS))
    omega
  · intro e he
    rcases List.mem_cons.1 he with h | h
    · subst h; exact ⟨(S₀, v), hFm S₀ (hGF S₀ hS₀), rfl⟩
    · exact ⟨e, (List.mem_filter.1 h).1, rfl⟩
  · by_cases hb : clq Gr Y ∧ ∀ S ∈ G, ¬ clq Gr S
    · exact Or.inr hb
    · left
      apply pluck_le a Gr
      intro hY
      have : ∃ S ∈ G, clq Gr S := by
        apply Classical.byContradiction
        intro hn
        exact hb ⟨hY, fun S hS hc => hn ⟨S, hS, hc⟩⟩
      obtain ⟨S, hS, hc⟩ := this
      exact ⟨S, hS, hFm S (hGF S hS), hc⟩

/-- **Closing.** Every approximator satisfying `Inv` can be closed: the result `b` has the same
base, values among those of `a`, at most `B` entries per class, value never below `a`'s, and
above `a`'s on `G` only at a recorded pluck event whose core is a clique of `G` and no petal is;
there are at most `|a| / (p - 1)` events. -/
theorem close (p ℓ m B : Nat) (hp : 2 ≤ p) (hSF : SF p ℓ B) : ∀ n (a : Approx),
    a.ents.length ≤ n → Inv ℓ m a →
    ∃ b : Approx, ∃ evs : List (List Nat × List (List Nat)),
      b.base = a.base ∧ Inv ℓ m b ∧ (∀ e ∈ b.ents, ∃ e' ∈ a.ents, e'.2 = e.2) ∧
      (∀ v, (cls b v).length ≤ B) ∧
      evs.length * (p - 1) + b.ents.length ≤ a.ents.length ∧
      (∀ ev ∈ evs, Ev p ℓ m ev) ∧
      (∀ G, eval a G ≤ eval b G) ∧
      (∀ G, eval b G ≤ eval a G ∨ ∃ ev ∈ evs, clq G ev.1 ∧ ∀ S ∈ ev.2, ¬ clq G S) := by
  intro n
  induction n with
  | zero =>
    intro a ha hI
    have hd := dd_facts a.ents
    refine ⟨ddA a, [], rfl, fun e he => hI e (hd.1 e he), fun e he => ⟨e, hd.1 e he, rfl⟩,
      fun v => ?_, ?_, by simp, fun G => Int.le_of_eq (ddA_eval a G).symm,
      fun G => Or.inl (Int.le_of_eq (ddA_eval a G))⟩
    · have h1 := List.length_filter_le (fun e => decide (e.2 = v)) (dd a.ents)
      have h2 := hd.2.2.2
      show (List.filter _ (dd a.ents)).length ≤ B
      omega
    · simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]; exact hd.2.2.2
  | succ n ih =>
    intro a ha hI
    have hd := dd_facts a.ents
    have hI' : Inv ℓ m (ddA a) := fun e he => hI e (hd.1 e he)
    by_cases hbig : ∃ v, B < (cls (ddA a) v).length
    · obtain ⟨v, hv⟩ := hbig
      obtain ⟨Y, P, hEv, hIp, hlp, hvp, hge, hle⟩ := pluck_step p ℓ m B hp hSF (ddA a) hI' hd.2.2.1 v hv
      have hda : (ddA a).ents.length ≤ a.ents.length := hd.2.2.2
      obtain ⟨b, evs, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8⟩ :=
        ih (pluck Y v P (ddA a)) (by omega) hIp
      refine ⟨b, (Y, P) :: evs, hb1, hb2, ?_, hb4, ?_, ?_, ?_, ?_⟩
      · intro e he
        obtain ⟨e1, he1, h1⟩ := hb3 e he
        obtain ⟨e2, he2, h2⟩ := hvp e1 he1
        exact ⟨e2, hd.1 e2 he2, h2.trans h1⟩
      · simp only [List.length_cons, Nat.succ_mul]; omega
      · intro ev hev
        rcases List.mem_cons.1 hev with h | h
        · exact h ▸ hEv
        · exact hb6 ev h
      · intro G
        rw [← ddA_eval a G]
        exact Int.le_trans (hge G) (hb7 G)
      · intro G
        rcases hb8 G with h | ⟨ev, hev, hc⟩
        · rcases hle G with h' | h'
          · left; rw [← ddA_eval a G]; exact Int.le_trans h h'
          · exact Or.inr ⟨(Y, P), List.mem_cons_self .., h'⟩
        · exact Or.inr ⟨ev, List.mem_cons_of_mem _ hev, hc⟩
    · refine ⟨ddA a, [], rfl, hI', fun e he => ⟨e, hd.1 e he, rfl⟩,
        fun v => Nat.le_of_not_lt fun h => hbig ⟨v, h⟩, ?_, by simp,
        fun G => Int.le_of_eq (ddA_eval a G).symm, fun G => Or.inl (Int.le_of_eq (ddA_eval a G))⟩
      simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]; exact hd.2.2.2

/-! ## Counting entries by value class -/

theorem ff_le {α : Type} (p r : α → Bool) : ∀ l : List α,
    ((l.filter p).filter r).length ≤ (l.filter r).length
  | [] => Nat.le_refl _
  | x :: l => by
    have := ff_le p r l
    cases hp : p x <;> cases hr : r x <;>
      simp only [List.filter_cons, hp, hr, ite_true, ite_false, Bool.false_eq_true, List.length_cons] <;>
      omega

theorem class_count (B : Nat) (lo : Int) : ∀ (R : Nat) (l : List (List Nat × Int)),
    (∀ e ∈ l, lo < e.2 ∧ e.2 ≤ lo + R) →
    (∀ v : Int, (l.filter fun e => decide (e.2 = v)).length ≤ B) → l.length ≤ R * B
  | 0, [], _, _ => by simp
  | 0, e :: _, h, _ => by have := h e (List.mem_cons_self ..); omega
  | R + 1, l, h, hc => by
    have hs := len_split (fun e : List Nat × Int => decide (e.2 = lo + (R + 1 : Nat))) l
    have h1 := hc (lo + (R + 1 : Nat))
    have h2 := class_count B lo R (l.filter fun x => !decide (x.2 = lo + (R + 1 : Nat))) (by
        intro e he
        have := List.mem_filter.1 he
        have hne : ¬ e.2 = lo + (R + 1 : Nat) := by simpa using this.2
        have := h e this.1
        constructor
        · exact this.1
        · have : e.2 ≤ lo + (R + 1 : Nat) := this.2
          push_cast at this hne ⊢; omega)
      (fun v => Nat.le_trans (ff_le _ _ l) (hc v))
    rw [Nat.succ_mul]
    omega

end Programme.«20261024-1633-proof-complexity».Pluck
