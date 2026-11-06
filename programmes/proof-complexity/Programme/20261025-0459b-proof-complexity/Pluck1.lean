import Programme.«20261024-1633-proof-complexity».Pluck

/-!
# Value-independent plucking

The library's `Pluck.close` bounds the entries of an approximator *per value class*; for formulas
with unbounded ranges that gives no bound. Here a pluck replaces only the **lowest-valued** petal
of a sunflower by the core, with that petal's value:
* the value never drops, on any graph (the core is contained in the removed petal);
* it rises on `G` only if the core is a clique of `G` and none of the `p` petals is (every petal
  carries a value at least the core's new value);
* the total size of the entry sets strictly decreases, so at most `wt a` plucks happen.

`close1`: every approximator satisfying `Inv` closes to one with at most `B` entries in total
(given the sunflower lemma `SF (p+1) ℓ B`), with at most `wt a ≤ ℓ |a|` recorded events.
-/

namespace Programme.«20261025-0459b-proof-complexity».Pluck1

open Programme.«20261024-1633-proof-complexity».RealApprox
open Programme.«20261024-1633-proof-complexity».Pluck

/-- Total size of the entry sets. -/
def wt (l : List (List Nat × Int)) : Nat := (l.map fun e => e.1.length).sum

theorem wt_sub : ∀ {l l' : List (List Nat × Int)}, l.Sublist l' → wt l ≤ wt l'
  | _, _, .slnil => Nat.le_refl _
  | _, _, .cons x h => by have := wt_sub h; simp only [wt, List.map_cons, List.sum_cons] at *; omega
  | _, _, .cons₂ x h => by have := wt_sub h; simp only [wt, List.map_cons, List.sum_cons] at *; omega

theorem wt_erase : ∀ {l : List (List Nat × Int)} {e : List Nat × Int}, e ∈ l →
    wt (l.erase e) + e.1.length = wt l
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

theorem ddF_sub : ∀ n (l : List (List Nat × Int)), (ddF n l).Sublist l
  | _, [] => by simp [ddF]
  | 0, _ :: _ => by simp [ddF]
  | n + 1, e :: l => by
    simp only [ddF]
    exact (ddF_sub n _).trans List.filter_sublist |>.cons_cons e

/-! ## Merging entries with equivalent sets (keep the maximal value) -/

/-- The largest value among `d` and the entries of `l` whose set is equivalent to `S`. -/
def mv (l : List (List Nat × Int)) (S : List Nat) (d : Int) : Int :=
  l.foldr (fun x acc => if seqv x.1 S then max x.2 acc else acc) d

theorem mv_facts (S : List Nat) (d : Int) : ∀ l : List (List Nat × Int),
    d ≤ mv l S d ∧ (∀ x ∈ l, seqv x.1 S = true → x.2 ≤ mv l S d) ∧
    (mv l S d = d ∨ ∃ x ∈ l, seqv x.1 S = true ∧ mv l S d = x.2)
  | [] => by simp [mv]
  | x :: l => by
    obtain ⟨h1, h2, h3⟩ := mv_facts S d l
    have e : mv (x :: l) S d = if seqv x.1 S then max x.2 (mv l S d) else mv l S d := rfl
    by_cases hx : seqv x.1 S = true
    · rw [e, if_pos hx]
      refine ⟨by omega, fun y hy hs => ?_, ?_⟩
      · rcases List.mem_cons.1 hy with rfl | hy
        · omega
        · have := h2 y hy hs; omega
      · by_cases hm : x.2 ≤ mv l S d
        · rw [Int.max_eq_right hm]
          rcases h3 with h3 | ⟨y, hy, hs, he⟩
          · exact Or.inl h3
          · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hs, he⟩
        · rw [Int.max_eq_left (by omega)]
          exact Or.inr ⟨x, List.mem_cons_self .., hx, rfl⟩
    · rw [e, if_neg hx]
      refine ⟨h1, fun y hy hs => ?_, ?_⟩
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact absurd hs hx
        · exact h2 y hy hs
      · rcases h3 with h3 | ⟨y, hy, hs, he⟩
        · exact Or.inl h3
        · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hs, he⟩

theorem seqv_trans {S T U : List Nat} (h1 : seqv S T = true) (h2 : seqv T U = true) :
    seqv S U = true :=
  seqv_iff.2 fun y => (seqv_iff.1 h1 y).trans (seqv_iff.1 h2 y)

theorem seqv_symm {S T : List Nat} (h : seqv S T = true) : seqv T S = true :=
  seqv_iff.2 fun y => (seqv_iff.1 h y).symm

theorem seqv_refl (S : List Nat) : seqv S S = true := seqv_iff.2 fun _ => Iff.rfl

def mmap (l : List (List Nat × Int)) : List (List Nat × Int) :=
  l.map fun e => (e.1, mv l e.1 e.2)

/-- Merge: entries with equivalent sets get the maximal value, then twins are removed. -/
def mg (a : Approx) : Approx := ⟨a.base, dd (mmap a.ents)⟩

/-- Two entries of `mmap l` with equivalent sets carry the same value. -/
theorem mmap_eq {l : List (List Nat × Int)} {e f : List Nat × Int} (he : e ∈ l) (hf : f ∈ l)
    (h : seqv e.1 f.1 = true) : mv l e.1 e.2 = mv l f.1 f.2 := by
  have A := mv_facts e.1 e.2 l
  have B := mv_facts f.1 f.2 l
  -- each value is attained by an entry equivalent to the common set
  have ae : ∃ x ∈ l, seqv x.1 e.1 = true ∧ mv l e.1 e.2 = x.2 := by
    rcases A.2.2 with h' | h'
    · exact ⟨e, he, seqv_refl _, h'⟩
    · exact h'
  have af : ∃ x ∈ l, seqv x.1 f.1 = true ∧ mv l f.1 f.2 = x.2 := by
    rcases B.2.2 with h' | h'
    · exact ⟨f, hf, seqv_refl _, h'⟩
    · exact h'
  obtain ⟨x, hx, hxs, hxe⟩ := ae
  obtain ⟨y, hy, hys, hye⟩ := af
  have h1 := B.2.1 x hx (seqv_trans hxs h)
  have h2 := A.2.1 y hy (seqv_trans hys (seqv_symm h))
  omega

theorem mg_facts (a : Approx) :
    (mg a).base = a.base ∧
    (∀ e ∈ (mg a).ents, ∃ e' ∈ a.ents, e'.1 = e.1) ∧
    (mg a).ents.Pairwise (fun x y => ∃ z, ¬ (z ∈ x.1 ↔ z ∈ y.1)) ∧
    wt (mg a).ents ≤ wt a.ents ∧
    (∀ G, eval (mg a) G = eval a G) := by
  obtain ⟨d1, d2, d3, _⟩ := dd_facts (mmap a.ents)
  have hmem : ∀ x ∈ mmap a.ents, ∃ e ∈ a.ents, x = (e.1, mv a.ents e.1 e.2) := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    exact ⟨e, he, rfl⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨e', he', rfl⟩ := hmem e (d1 e he)
    exact ⟨e', he', rfl⟩
  · apply d3.imp_of_mem
    intro x y hx hy hv
    obtain ⟨ex, hex, rfl⟩ := hmem x (d1 x hx)
    obtain ⟨ey, hey, rfl⟩ := hmem y (d1 y hy)
    apply Classical.byContradiction
    intro hn
    have hs : ∀ z, z ∈ ex.1 ↔ z ∈ ey.1 := fun z =>
      Classical.byContradiction fun hz => hn ⟨z, hz⟩
    obtain ⟨z, hz⟩ := hv (mmap_eq hex hey (seqv_iff.2 hs))
    exact hz (hs z)
  · have h1 := wt_sub (ddF_sub (mmap a.ents).length (mmap a.ents))
    have h2 : wt (mmap a.ents) = wt a.ents := by
      simp only [wt, mmap, List.map_map]; rfl
    show wt (dd (mmap a.ents)) ≤ _
    unfold dd; omega
  · intro G
    apply Int.le_antisymm
    · apply dom
      intro e he hc
      rcases List.mem_cons.1 he with h | h
      · exact ⟨e, h ▸ List.mem_cons_self .., hc, Int.le_refl _⟩
      · obtain ⟨e', he', rfl⟩ := hmem e (d1 e h)
        rcases (mv_facts e'.1 e'.2 a.ents).2.2 with h' | ⟨x, hx, hxs, hxe⟩
        · exact ⟨e', List.mem_cons_of_mem _ he', hc, Int.le_of_eq h'⟩
        · exact ⟨x, List.mem_cons_of_mem _ hx, (clq_congr (seqv_iff.1 hxs)).2 hc, Int.le_of_eq hxe⟩
    · apply dom
      intro e he hc
      rcases List.mem_cons.1 he with h | h
      · exact ⟨e, h ▸ List.mem_cons_self .., hc, Int.le_refl _⟩
      · have hm : (e.1, mv a.ents e.1 e.2) ∈ mmap a.ents := List.mem_map.2 ⟨e, h, rfl⟩
        obtain ⟨y, hy, hy2, hy1⟩ := d2 _ hm
        refine ⟨y, List.mem_cons_of_mem _ hy, (clq_congr hy1).2 hc, ?_⟩
        rw [hy2]
        exact (mv_facts e.1 e.2 a.ents).1

/-! ## One pluck -/

/-- Replace the entry `e` by the core `Y` with `e`'s value. -/
def pluck1 (Y : List Nat) (e : List Nat × Int) (a : Approx) : Approx :=
  ⟨a.base, (nc Y, e.2) :: a.ents.erase e⟩

theorem filter_seqv_le1 (Y : List Nat) : ∀ l : List (List Nat),
    l.Pairwise (fun S T => ∃ y, ¬ (y ∈ S ↔ y ∈ T)) → (l.filter fun S => seqv S Y).length ≤ 1
  | [], _ => by simp
  | S :: l, h => by
    have ⟨h1, h2⟩ := List.pairwise_cons.1 h
    by_cases hS : seqv S Y = true
    · have : l.filter (fun S => seqv S Y) = [] := by
        apply List.filter_eq_nil_iff.2
        intro T hT hTY
        obtain ⟨y, hy⟩ := h1 T hT
        exact hy ((seqv_iff.1 hS y).trans (seqv_iff.1 hTY y).symm)
      simp [List.filter_cons, hS, this]
    · simp only [List.filter_cons, hS, Bool.false_eq_true, ite_false]
      exact filter_seqv_le1 Y l h2

theorem exists_min : ∀ l : List (List Nat × Int), l ≠ [] → ∃ x ∈ l, ∀ y ∈ l, x.2 ≤ y.2
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

theorem pluck1_step (p ℓ m B : Nat) (hp : 1 ≤ p) (hSF : SF (p + 1) ℓ B) (a : Approx)
    (hI : Inv ℓ m a) (hd : a.ents.Pairwise (fun x y => ∃ z, ¬ (z ∈ x.1 ↔ z ∈ y.1)))
    (hB : B < a.ents.length) :
    ∃ b : Approx, ∃ ev : List Nat × List (List Nat),
      b.base = a.base ∧ Ev p ℓ m ev ∧ Inv ℓ m b ∧ wt b.ents < wt a.ents ∧
      (∀ G, eval a G ≤ eval b G) ∧
      (∀ G, eval b G ≤ eval a G ∨ (clq G ev.1 ∧ ∀ S ∈ ev.2, ¬ clq G S)) := by
  let F := a.ents.map Prod.fst
  have hlen : ∀ S ∈ F, S.length ≤ ℓ := by
    intro S hS
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hS
    exact (hI e he).2.1
  have hpw : F.Pairwise (fun S T => ∃ y, ¬ (y ∈ S ↔ y ∈ T)) := List.pairwise_map.2 hd
  obtain ⟨G, hGl, hGF, hGd, hGp⟩ := hSF F hlen hpw (by simpa [F] using hB)
  obtain ⟨S₀, G', hG⟩ : ∃ S₀ G', G = S₀ :: G' := by
    cases G with
    | nil => simp at hGl
    | cons S₀ G' => exact ⟨S₀, G', rfl⟩
  have hS₀ : S₀ ∈ G := hG ▸ List.mem_cons_self ..
  have hentF : ∀ S ∈ F, ∃ e ∈ a.ents, e.1 = S := by
    intro S hS
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hS
    exact ⟨e, he, rfl⟩
  obtain ⟨e₀, he₀, he₀1⟩ := hentF S₀ (hGF S₀ hS₀)
  have hI₀ := hI e₀ he₀
  rw [he₀1] at hI₀
  let Y := S₀.filter fun x => G.all fun R => decide (x ∈ R)
  have hYsub : ∀ S ∈ G, ∀ x ∈ Y, x ∈ S := by
    intro S hS x hx
    have := (List.mem_filter.1 hx).2
    simp only [List.all_eq_true, decide_eq_true_eq] at this
    exact this S hS
  have hYnd : Y.Nodup :=
    List.nodup_iff_pairwise_ne.2 (List.Pairwise.filter _ (List.nodup_iff_pairwise_ne.1 hI₀.1))
  -- petals not equivalent to the core
  let P0 := G.filter fun S => !seqv S Y
  have hP0 : p ≤ P0.length := by
    have h1 := filter_seqv_le1 Y G hGd
    have h2 := len_split (fun S => seqv S Y) G
    simp only [P0]; omega
  let P := P0.take p
  have hPl : P.length = p := by simp [P]; omega
  have hPsub : P.Sublist G := (List.take_sublist _ _).trans List.filter_sublist
  have hPne : ∀ S ∈ P, seqv S Y = false := by
    intro S hS
    have := (List.mem_filter.1 ((List.take_sublist _ _).subset hS)).2
    simpa using this
  -- the lowest-valued entry among the petals
  let E := a.ents.filter fun e => decide (e.1 ∈ P)
  have hEne : E ≠ [] := by
    obtain ⟨S, hS⟩ : ∃ S, S ∈ P := by
      cases hP : P with
      | nil => rw [hP] at hPl; simp at hPl; omega
      | cons S _ => exact ⟨S, List.mem_cons_self ..⟩
    obtain ⟨e, he, rfl⟩ := hentF S (hGF S (hPsub.subset hS))
    intro h
    have : e ∈ E := List.mem_filter.2 ⟨he, by simpa using hS⟩
    rw [h] at this; simp at this
  obtain ⟨es, hes, hmin⟩ := exists_min E hEne
  have hes' := List.mem_filter.1 hes
  have hesa : es ∈ a.ents := hes'.1
  have hesP : es.1 ∈ P := by simpa using hes'.2
  have hesG : es.1 ∈ G := hPsub.subset hesP
  have hYes : ∀ x ∈ Y, x ∈ es.1 := hYsub es.1 hesG
  have hIes := hI es hesa
  have hYlt : Y.length < es.1.length := by
    have hn := hPne es.1 hesP
    obtain ⟨z, hz⟩ : ∃ z, z ∈ es.1 ∧ z ∉ Y := by
      apply Classical.byContradiction
      intro h
      have : seqv es.1 Y = true := seqv_iff.2 fun y =>
        ⟨fun hy => Classical.byContradiction fun hy' => h ⟨y, hy, hy'⟩, fun hy => hYes y hy⟩
      rw [this] at hn; exact Bool.noConfusion hn
    have := nodup_len_le (P := z :: Y) (L := es.1) (List.nodup_cons.2 ⟨hz.2, hYnd⟩)
      (fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hz.1
        · exact hYes x hx)
    simp at this; omega
  have hncl : (nc Y).length ≤ Y.length := by
    unfold nc; split
    · simp
    · exact Nat.le_refl _
  refine ⟨pluck1 Y es a, (Y, P), rfl, ?_, ?_, ?_, fun Gr => ?_, fun Gr => ?_⟩
  · refine ⟨hPl, fun S hS => ?_, ?_⟩
    · obtain ⟨e, he, rfl⟩ := hentF S (hGF S (hPsub.subset hS))
      have := hI e he; exact ⟨this.1, this.2.1, this.2.2.1⟩
    · apply (hGp.sublist hPsub).imp
      intro S T h x hxS hxT
      have hall := h x hxS hxT
      exact List.mem_filter.2 ⟨hall S₀ hS₀, by simpa using hall⟩
  · intro e he
    rcases List.mem_cons.1 he with h | h
    · subst h
      refine ⟨?_, ?_, ?_, ns_nc hYnd⟩
      · unfold nc; split
        · exact List.nodup_nil
        · exact hYnd
      · exact Nat.le_trans hncl (Nat.le_trans (List.length_filter_le _ _) hI₀.2.1)
      · intro x hx
        exact hI₀.2.2.1 x (List.mem_filter.1 (nc_sub Y x hx)).1
    · exact hI e ((List.erase_sublist ..).subset h)
  · have := wt_erase hesa
    show (nc Y).length + wt (a.ents.erase es) < wt a.ents
    omega
  · apply dom
    intro e he hc
    rcases List.mem_cons.1 he with h | h
    · exact ⟨e, h ▸ List.mem_cons_self .., hc, Int.le_refl _⟩
    · by_cases hx : e = es
      · subst hx
        refine ⟨(nc Y, e.2), List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_, Int.le_refl _⟩
        exact (clq_nc Gr Y).2 (clq_sub hYes hc)
      · exact ⟨e, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ((List.mem_erase_of_ne hx).2 h)),
          hc, Int.le_refl _⟩
  · by_cases hb : clq Gr Y ∧ ∀ S ∈ P, ¬ clq Gr S
    · exact Or.inr hb
    · left
      apply dom
      intro e he hc
      rcases List.mem_cons.1 he with h | h
      · exact ⟨e, h ▸ List.mem_cons_self .., hc, Int.le_refl _⟩
      · rcases List.mem_cons.1 h with h | h
        · subst h
          have hY : clq Gr Y := (clq_nc Gr Y).1 hc
          obtain ⟨S, hS, hcS⟩ : ∃ S ∈ P, clq Gr S := by
            apply Classical.byContradiction
            intro hn
            exact hb ⟨hY, fun S hS hc => hn ⟨S, hS, hc⟩⟩
          obtain ⟨e, he, rfl⟩ := hentF S (hGF S (hPsub.subset hS))
          exact ⟨e, List.mem_cons_of_mem _ he, hcS,
            hmin e (List.mem_filter.2 ⟨he, by simpa using hS⟩)⟩
        · exact ⟨e, List.mem_cons_of_mem _ ((List.erase_sublist ..).subset h), hc, Int.le_refl _⟩

/-! ## Closing -/

/-- **Closing, value-independent.** Given the sunflower lemma `SF (p+1) ℓ B`, every approximator
satisfying `Inv` closes to `b` with the same base and at most `B` entries in total; `b` is never
below `a`, and above `a` on `G` only at one of at most `wt a` recorded events (`Ev p ℓ m`) whose
core is a clique of `G` and none of whose `p` petals is. -/
theorem close1 (p ℓ m B : Nat) (hp : 1 ≤ p) (hSF : SF (p + 1) ℓ B) : ∀ n (a : Approx),
    wt a.ents < n → Inv ℓ m a →
    ∃ b : Approx, ∃ evs : List (List Nat × List (List Nat)),
      b.base = a.base ∧ Inv ℓ m b ∧ b.ents.length ≤ B ∧ evs.length ≤ wt a.ents ∧
      (∀ ev ∈ evs, Ev p ℓ m ev) ∧
      (∀ G, eval a G ≤ eval b G) ∧
      (∀ G, eval b G ≤ eval a G ∨ ∃ ev ∈ evs, clq G ev.1 ∧ ∀ S ∈ ev.2, ¬ clq G S) := by
  intro n
  induction n with
  | zero => intro a h; omega
  | succ n ih =>
    intro a hw hI
    obtain ⟨m1, m2, m3, m4, m5⟩ := mg_facts a
    have hI' : Inv ℓ m (mg a) := by
      intro e he
      obtain ⟨e', he', h⟩ := m2 e he
      rw [← h]; exact hI e' he'
    by_cases hbig : B < (mg a).ents.length
    · obtain ⟨b1, ev, hb1, hEv, hIb1, hwb1, hge, hle⟩ := pluck1_step p ℓ m B hp hSF (mg a) hI' m3 hbig
      obtain ⟨b, evs, c1, c2, c3, c4, c5, c6, c7⟩ := ih b1 (by omega) hIb1
      refine ⟨b, ev :: evs, by rw [c1, hb1, m1], c2, c3, by simp; omega, ?_, ?_, ?_⟩
      · intro e he
        rcases List.mem_cons.1 he with h | h
        · exact h ▸ hEv
        · exact c5 e h
      · intro G
        rw [← m5 G]
        exact Int.le_trans (hge G) (c6 G)
      · intro G
        rcases c7 G with h | ⟨e, he, hc⟩
        · rcases hle G with h' | h'
          · left; rw [← m5 G]; exact Int.le_trans h h'
          · exact Or.inr ⟨ev, List.mem_cons_self .., h'⟩
        · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, hc⟩
    · exact ⟨mg a, [], m1, hI', by omega, by simp, by simp,
        fun G => Int.le_of_eq (m5 G).symm, fun G => Or.inl (Int.le_of_eq (m5 G))⟩

end Programme.«20261025-0459b-proof-complexity».Pluck1

#print axioms Programme.«20261025-0459b-proof-complexity».Pluck1.close1
