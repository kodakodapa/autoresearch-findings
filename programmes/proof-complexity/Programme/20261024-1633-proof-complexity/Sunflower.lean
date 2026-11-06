/-!
# The Erdős–Rado sunflower lemma

A family of `F.length` items, each carrying a finite set `σ a` (a list of naturals) with at most
`ℓ` entries, pairwise distinct as sets, and with more than `ℓ! (p-1)^ℓ` items, contains `p` items
forming a sunflower: whenever a point lies in two of the chosen sets, it lies in all of them.

The family is indexed by an arbitrary type `α` (e.g. weighted clique indicators in the
approximation method); `sunflower_sets` is the special case of a list of sets.
Proof: greedy maximal disjoint subfamily, else pigeonhole on its union and induction on `ℓ`.
-/

namespace Programme.«20261024-1633-proof-complexity».Sunflower

def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

theorem fact_pos : ∀ n, 0 < fact n
  | 0 => by decide
  | n+1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

variable {α : Type}

/-- The sets of `a` and `b` differ. -/
def Distinct (σ : α → List Nat) (a b : α) : Prop := ∃ y, ¬ (y ∈ σ a ↔ y ∈ σ b)

/-- `G` is a sunflower: a point in two members (at distinct positions) is in every member. -/
def Petals (σ : α → List Nat) (G : List α) : Prop :=
  G.Pairwise (fun a b => ∀ y, y ∈ σ a → y ∈ σ b → ∀ c ∈ G, y ∈ σ c)

def Disj (σ : α → List Nat) (a b : α) : Prop := ∀ y, y ∈ σ a → y ∉ σ b

def disjB (s t : List Nat) : Bool := s.all (fun y => !t.contains y)

theorem disjB_iff (s t : List Nat) : disjB s t = true ↔ ∀ y, y ∈ s → y ∉ t := by
  simp [disjB, List.all_eq_true]

/-- Greedy maximal pairwise disjoint subfamily. -/
def greedy (σ : α → List Nat) : List α → List α → List α
  | acc, [] => acc
  | acc, a :: l =>
    if acc.all (fun b => disjB (σ a) (σ b)) then greedy σ (acc ++ [a]) l else greedy σ acc l

theorem greedy_mem (σ : α → List Nat) : ∀ (acc l : List α) a, a ∈ greedy σ acc l → a ∈ acc ∨ a ∈ l
  | acc, [], a, h => Or.inl h
  | acc, b :: l, a, h => by
    simp only [greedy] at h
    split at h
    · rcases greedy_mem σ _ _ _ h with h | h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · simp at h; subst h; simp
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases greedy_mem σ _ _ _ h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem greedy_acc (σ : α → List Nat) : ∀ (acc l : List α) a, a ∈ acc → a ∈ greedy σ acc l
  | acc, [], a, h => h
  | acc, b :: l, a, h => by
    simp only [greedy]; split
    · exact greedy_acc σ _ _ _ (List.mem_append_left _ h)
    · exact greedy_acc σ _ _ _ h

theorem greedy_disj (σ : α → List Nat) : ∀ (acc l : List α),
    acc.Pairwise (Disj σ) → (greedy σ acc l).Pairwise (Disj σ)
  | acc, [], h => h
  | acc, b :: l, h => by
    simp only [greedy]; split
    · next hb =>
      apply greedy_disj
      rw [List.pairwise_append]
      refine ⟨h, List.pairwise_singleton _ _, ?_⟩
      intro a ha c hc
      simp at hc; subst hc
      rw [List.all_eq_true] at hb
      have := (disjB_iff _ _).1 (hb a ha)
      intro y h1 h2; exact this y h2 h1
    · exact greedy_disj σ _ _ h

theorem greedy_cover (σ : α → List Nat) : ∀ (acc l : List α), (∀ a ∈ l, σ a ≠ []) →
    ∀ a ∈ l, ∃ b ∈ greedy σ acc l, ∃ y, y ∈ σ a ∧ y ∈ σ b
  | acc, [], _, a, h => by simp at h
  | acc, b :: l, hne, a, h => by
    have hne' : ∀ a ∈ l, σ a ≠ [] := fun a ha => hne a (List.mem_cons_of_mem _ ha)
    simp only [greedy]; split
    · next hb =>
      rcases List.mem_cons.1 h with h | h
      · subst h
        obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ (hne a (by simp))
        exact ⟨a, greedy_acc σ _ _ _ (by simp), y, hy, hy⟩
      · exact greedy_cover σ _ _ hne' a h
    · next hb =>
      rcases List.mem_cons.1 h with h | h
      · subst h
        have : ∃ c ∈ acc, disjB (σ a) (σ c) = false := by simpa [List.all_eq_true] using hb
        obtain ⟨c, hc, hd⟩ := this
        have hn : ¬ ∀ y, y ∈ σ a → y ∉ σ c := fun h => by
          rw [(disjB_iff _ _).2 h] at hd; exact absurd hd (by decide)
        have ⟨y, hy1, hy2⟩ : ∃ y, y ∈ σ a ∧ y ∈ σ c :=
          Classical.byContradiction fun h' => hn (fun y h1 h2 => h' ⟨y, h1, h2⟩)
        exact ⟨c, greedy_acc σ _ _ _ hc, y, hy1, hy2⟩
      · exact greedy_cover σ _ _ hne' a h

/-! Counting. -/

def cnt (σ : α → List Nat) (L : List α) (y : Nat) : Nat := (L.filter (fun a => decide (y ∈ σ a))).length

theorem sum_add (U : List Nat) (f g : Nat → Nat) :
    (U.map (fun y => f y + g y)).sum = (U.map f).sum + (U.map g).sum := by
  induction U with
  | nil => rfl
  | cons y U ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_le {β : Type} (U : List β) (f : β → Nat) (M : Nat) (h : ∀ y ∈ U, f y ≤ M) :
    (U.map f).sum ≤ U.length * M := by
  induction U with
  | nil => simp
  | cons y U ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := h y (by simp); have := ih (fun z hz => h z (List.mem_cons_of_mem _ hz)); omega

theorem sum_ind_pos (U s : List Nat) (h : ∃ y ∈ U, y ∈ s) :
    1 ≤ (U.map (fun y => if y ∈ s then 1 else 0)).sum := by
  induction U with
  | nil => simp at h
  | cons z U ih =>
    simp only [List.map_cons, List.sum_cons]
    by_cases hz : z ∈ s
    · simp only [hz, ite_true]; omega
    · obtain ⟨y, hy, hys⟩ := h
      rcases List.mem_cons.1 hy with rfl | hy
      · exact absurd hys hz
      · have := ih ⟨y, hy, hys⟩; omega

theorem cover_count (σ : α → List Nat) (U : List Nat) : ∀ L : List α,
    (∀ a ∈ L, ∃ y ∈ U, y ∈ σ a) → L.length ≤ (U.map (cnt σ L)).sum
  | [], _ => by simp
  | a :: L, h => by
    have e : U.map (cnt σ (a :: L)) = U.map (fun y => cnt σ L y + (if y ∈ σ a then 1 else 0)) := by
      apply List.map_congr_left
      intro y _
      by_cases hy : y ∈ σ a <;> simp [cnt, hy]
    rw [e, sum_add]
    have h1 := cover_count σ U L (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have h2 := sum_ind_pos U (σ a) (h a (by simp))
    simp only [List.length_cons]; omega

theorem len_split (q : α → Bool) : ∀ L : List α,
    (L.filter (fun a => !q a)).length + (L.filter q).length = L.length
  | [] => rfl
  | a :: L => by
    have := len_split q L
    cases h : q a <;> simp [h] <;> omega

theorem empty_le_one (σ : α → List Nat) : ∀ L : List α,
    L.Pairwise (Distinct σ) → (∀ a ∈ L, σ a = []) → L.length ≤ 1
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | a :: b :: t, hp, he => by
    exfalso
    obtain ⟨y, hy⟩ := List.rel_of_pairwise_cons hp (List.mem_cons_self ..)
    rw [he a (by simp), he b (by simp)] at hy
    simp at hy

theorem filter_ne_lt (x : Nat) : ∀ s : List Nat, x ∈ s →
    (s.filter (fun y => decide (y ≠ x))).length < s.length
  | [], h => by simp at h
  | z :: s, h => by
    by_cases hz : z = x
    · subst hz
      have := List.length_filter_le (fun y => !decide (y = z)) s
      simp; omega
    · have hs : x ∈ s := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hz
        · exact h
      have := filter_ne_lt x s hs
      simp [hz]; omega

/-- Pairwise disjoint, at least one of each pair nonempty: distinct and a sunflower. -/
theorem good (σ : α → List Nat) (L : List α)
    (h : L.Pairwise (fun a b => Disj σ a b ∧ (σ a ≠ [] ∨ σ b ≠ []))) :
    L.Pairwise (Distinct σ) ∧ Petals σ L := by
  refine ⟨h.imp ?_, h.imp ?_⟩
  · intro a b ⟨hd, hn⟩
    rcases hn with hn | hn
    · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hn
      exact ⟨y, fun hi => hd y hy (hi.1 hy)⟩
    · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hn
      exact ⟨y, fun hi => hd y (hi.2 hy) hy⟩
  · intro a b ⟨hd, _⟩ y h1 h2
    exact absurd h2 (hd y h1)

/-- **Erdős–Rado sunflower lemma** (indexed form). -/
theorem sunflower (p : Nat) (ℓ : Nat) (σ : α → List Nat) (F : List α)
    (hlen : ∀ a ∈ F, (σ a).length ≤ ℓ) (hF : F.Pairwise (Distinct σ))
    (hbig : fact ℓ * (p-1)^ℓ < F.length) :
    ∃ G : List α, G.length = p ∧ (∀ a ∈ G, a ∈ F) ∧ G.Pairwise (Distinct σ) ∧ Petals σ G := by
  rcases p with _ | _ | p
  · exact ⟨[], rfl, by simp, List.Pairwise.nil, List.Pairwise.nil⟩
  · match F, hbig with
    | a :: _, _ =>
      exact ⟨[a], rfl, by simp, List.pairwise_singleton _ _, List.pairwise_singleton _ _⟩
  induction ℓ generalizing σ F with
  | zero =>
    exfalso
    have he : ∀ a ∈ F, σ a = [] := fun a ha => List.eq_nil_of_length_eq_zero (by have := hlen a ha; omega)
    have := empty_le_one σ F hF he
    simp [fact] at hbig; omega
  | succ ℓ ih =>
    let F₀ := F.filter (fun a => !decide (σ a = []))
    let Fe := F.filter (fun a => decide (σ a = []))
    have hsplit : F₀.length + Fe.length = F.length := len_split _ F
    have he1 : Fe.length ≤ 1 := empty_le_one σ Fe (hF.filter _) (fun a ha => by
      simpa using (List.mem_filter.1 ha).2)
    have hF₀ : ∀ a ∈ F₀, a ∈ F ∧ σ a ≠ [] := fun a ha => by
      have := List.mem_filter.1 ha; exact ⟨this.1, by simpa using this.2⟩
    let G := greedy σ [] F₀
    have hGmem : ∀ a ∈ G, a ∈ F₀ := fun a ha => by
      rcases greedy_mem σ [] F₀ a ha with h | h
      · simp at h
      · exact h
    have hGR : G.Pairwise (fun a b => Disj σ a b ∧ (σ a ≠ [] ∨ σ b ≠ [])) :=
      (greedy_disj σ [] F₀ List.Pairwise.nil).imp_of_mem
        (fun ha _ hd => ⟨hd, Or.inl (hF₀ _ (hGmem _ ha)).2⟩)
    by_cases hp1 : p + 2 ≤ G.length
    · refine ⟨G.take (p+2), by simp [List.length_take]; omega, fun a ha => ?_, ?_⟩
      · exact (hF₀ a (hGmem a ((List.take_sublist _ _).subset ha))).1
      · exact good σ _ (hGR.sublist (List.take_sublist _ _))
    by_cases hp2 : p + 2 ≤ G.length + Fe.length
    · have hpos : 0 < Fe.length := by omega
      obtain ⟨e0, he0⟩ := List.exists_mem_of_length_pos hpos
      have he0' := List.mem_filter.1 he0
      have he0e : σ e0 = [] := by simpa using he0'.2
      refine ⟨G ++ [e0], by simp; omega, fun a ha => ?_, ?_⟩
      · rcases List.mem_append.1 ha with ha | ha
        · exact (hF₀ a (hGmem a ha)).1
        · simp at ha; subst ha; exact he0'.1
      · apply good
        rw [List.pairwise_append]
        refine ⟨hGR, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        simp at hb; subst hb
        refine ⟨fun y _ hy => ?_, Or.inl (hF₀ _ (hGmem _ ha)).2⟩
        rw [he0e] at hy; simp at hy
    -- pigeonhole on the union of the greedy family
    let U := G.flatMap σ
    have hcov : ∀ a ∈ F₀, ∃ y ∈ U, y ∈ σ a := fun a ha => by
      obtain ⟨b, hb, y, hy1, hy2⟩ := greedy_cover σ [] F₀ (fun a ha => (hF₀ a ha).2) a ha
      exact ⟨y, List.mem_flatMap.2 ⟨b, hb, hy2⟩, hy1⟩
    have hU : U.length ≤ G.length * (ℓ+1) := by
      rw [List.length_flatMap]
      exact sum_le G _ _ (fun a ha => hlen a (hF₀ a (hGmem a ha)).1)
    let M := fact ℓ * (p+1)^ℓ
    have hMpos : 0 < M := Nat.mul_pos (fact_pos ℓ) (Nat.pow_pos (by omega))
    have hx : ∃ x ∈ U, M < cnt σ F₀ x := by
      apply Classical.byContradiction
      intro hn
      have hle : ∀ x ∈ U, cnt σ F₀ x ≤ M := fun x hx =>
        Nat.le_of_not_lt (fun h => hn ⟨x, hx, h⟩)
      have h1 := cover_count σ U F₀ hcov
      have h2 := sum_le U _ _ hle
      have h3 : U.length * M ≤ G.length * (ℓ+1) * M := Nat.mul_le_mul_right M hU
      have hb : fact (ℓ+1) * (p+2-1)^(ℓ+1) = (p+1) * ((ℓ+1) * M) := by
        have : p + 2 - 1 = p + 1 := by omega
        simp only [fact, Nat.pow_succ, M, this]
        simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      rw [hb] at hbig
      have hq : p + 1 = (p + 1 - Fe.length) + Fe.length := by omega
      have h4 : G.length * ((ℓ+1) * M) ≤ (p + 1 - Fe.length) * ((ℓ+1) * M) :=
        Nat.mul_le_mul_right _ (by omega)
      have h5 : (p+1) * ((ℓ+1) * M) = (p + 1 - Fe.length) * ((ℓ+1) * M) + Fe.length * ((ℓ+1) * M) := by
        rw [← Nat.add_mul, ← hq]
      have h6 : Fe.length * 1 ≤ Fe.length * ((ℓ+1) * M) :=
        Nat.mul_le_mul_left _ (Nat.mul_pos (Nat.succ_pos ℓ) hMpos)
      rw [Nat.mul_assoc] at h3
      omega
    obtain ⟨x, _, hxM⟩ := hx
    -- remove `x` from the sets containing it and recurse
    let H := F₀.filter (fun a => decide (x ∈ σ a))
    let σ' : α → List Nat := fun a => (σ a).filter (fun y => decide (y ≠ x))
    have hH : ∀ a ∈ H, a ∈ F ∧ x ∈ σ a := fun a ha => by
      have := List.mem_filter.1 ha; exact ⟨(hF₀ a this.1).1, by simpa using this.2⟩
    have hmem' : ∀ a y, y ∈ σ' a ↔ y ∈ σ a ∧ y ≠ x := fun a y => by simp [σ']
    have hlen' : ∀ a ∈ H, (σ' a).length ≤ ℓ := fun a ha => by
      have := filter_ne_lt x (σ a) (hH a ha).2
      have := hlen a (hH a ha).1
      simp only [σ']; omega
    have hHd : H.Pairwise (Distinct σ') := by
      have : H.Pairwise (Distinct σ) := (hF.filter _).filter _
      refine this.imp_of_mem (fun ha hb ⟨y, hy⟩ => ⟨y, fun hi => hy ?_⟩)
      have hyx : y ≠ x := by
        intro h; subst h; exact hy ⟨fun _ => (hH _ hb).2, fun _ => (hH _ ha).2⟩
      rw [hmem', hmem'] at hi
      exact ⟨fun h => (hi.1 ⟨h, hyx⟩).1, fun h => (hi.2 ⟨h, hyx⟩).1⟩
    obtain ⟨G2, hG2l, hG2m, hG2d, hG2p⟩ := ih σ' H hlen' hHd hxM
    refine ⟨G2, hG2l, fun a ha => (hH a (hG2m a ha)).1, ?_, ?_⟩
    · refine hG2d.imp (fun ⟨y, hy⟩ => ⟨y, fun hi => hy ?_⟩)
      rw [hmem', hmem']
      exact ⟨fun h => ⟨hi.1 h.1, h.2⟩, fun h => ⟨hi.2 h.1, h.2⟩⟩
    · refine hG2p.imp_of_mem (fun ha hb hP y h1 h2 c hc => ?_)
      by_cases hyx : y = x
      · subst hyx; exact (hH c (hG2m c hc)).2
      · exact ((hmem' c y).1 (hP y ((hmem' _ y).2 ⟨h1, hyx⟩) ((hmem' _ y).2 ⟨h2, hyx⟩) c hc)).1

/-- **Erdős–Rado sunflower lemma**: more than `ℓ! (p-1)^ℓ` pairwise distinct sets (as
duplicate-free-up-to-membership lists) of size at most `ℓ` contain `p` distinct members
forming a sunflower. -/
theorem sunflower_sets (p ℓ : Nat) (F : List (List Nat))
    (hlen : ∀ S ∈ F, S.length ≤ ℓ) (hF : F.Pairwise (fun S T => ∃ y, ¬ (y ∈ S ↔ y ∈ T)))
    (hbig : fact ℓ * (p-1)^ℓ < F.length) :
    ∃ G : List (List Nat), G.length = p ∧ (∀ S ∈ G, S ∈ F) ∧
      G.Pairwise (fun S T => ∃ y, ¬ (y ∈ S ↔ y ∈ T)) ∧
      G.Pairwise (fun S T => ∀ y, y ∈ S → y ∈ T → ∀ R ∈ G, y ∈ R) :=
  sunflower p ℓ id F hlen hF hbig

end Programme.«20261024-1633-proof-complexity».Sunflower

#print axioms Programme.«20261024-1633-proof-complexity».Sunflower.sunflower_sets
