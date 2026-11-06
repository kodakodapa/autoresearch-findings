/-!
# Counting colourings: the sunflower step of the approximation method

`tot q W f c` is the sum of `f` over all recolourings of the vertex list `W` with colours `< q`
(base colouring `c` off `W`); `tot_one`: with `f = 1` it is `q ^ |W|`.

`petal_count`: for sets `S₁,…,S_p` (duplicate-free, size `≤ ℓ`, inside `V`) whose pairwise
intersections lie in `Y`, the number of colourings of `V` for which `Y` is rainbow and no `Sᵢ` is
rainbow is at most `C(ℓ,2)^p · q^(|V|-p)`, i.e. a fraction `≤ (C(ℓ,2)/q)^p`.
Proof: each non-rainbow `Sᵢ` has a monochromatic pair with an endpoint `uᵢ ∉ Y`; union bound over
the choice of pairs; the `uᵢ` are distinct and are no other pair's second endpoint, so with them
summed innermost each choice costs at most `q^(|V|-p)`.
-/

namespace Programme.«20261024-1633-proof-complexity».Colour

def sm : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | q+1, a => sm q a + a q

def upd (c : Nat → Nat) (u x : Nat) : Nat → Nat := fun w => if w = u then x else c w

/-- Sum of `f` over all recolourings of `W` with colours `< q`, base colouring `c`. -/
def tot (q : Nat) : List Nat → ((Nat → Nat) → Nat) → (Nat → Nat) → Nat
  | [], f, c => f c
  | u :: W, f, c => sm q (fun x => tot q W f (upd c u x))

theorem sm_add (q : Nat) (a b : Nat → Nat) : sm q (fun x => a x + b x) = sm q a + sm q b := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [sm, ih]; omega

theorem sm_mono (q : Nat) (a b : Nat → Nat) (h : ∀ x, a x ≤ b x) : sm q a ≤ sm q b := by
  induction q with
  | zero => exact Nat.le_refl _
  | succ q ih => exact Nat.add_le_add ih (h q)

theorem sm_const (q k : Nat) : sm q (fun _ => k) = q * k := by
  induction q with
  | zero => simp [sm]
  | succ q ih => simp only [sm, ih, Nat.succ_mul]

theorem sm_comm (q r : Nat) (a : Nat → Nat → Nat) :
    sm q (fun x => sm r (fun y => a x y)) = sm r (fun y => sm q (fun x => a x y)) := by
  induction q with
  | zero => simp only [sm]; rw [sm_const]; simp
  | succ q ih => simp only [sm]; rw [ih, sm_add]

theorem sm_le_one (q t : Nat) (a : Nat → Nat) (h : ∀ x, a x ≤ if x = t then 1 else 0) :
    sm q a ≤ 1 := by
  have key : ∀ q, sm q a ≤ if t < q then 1 else 0 := by
    intro q
    induction q with
    | zero => simp [sm]
    | succ q ih =>
      simp only [sm]
      have hq := h q
      by_cases h1 : t < q
      · rw [ite_eq_left h1] at ih
        rw [ite_eq_right (by omega)] at hq
        rw [ite_eq_left (by omega)]; omega
      · rw [ite_eq_right h1] at ih
        by_cases h2 : q = t
        · rw [ite_eq_left h2] at hq; rw [ite_eq_left (by omega)]; omega
        · rw [ite_eq_right h2] at hq; rw [ite_eq_right (by omega)]; omega
  have := key q
  split at this <;> omega

theorem upd_same (c : Nat → Nat) (u x : Nat) : upd c u x u = x := by simp [upd]

theorem upd_ne (c : Nat → Nat) (u x w : Nat) (h : w ≠ u) : upd c u x w = c w := by
  simp [upd, h]

theorem upd_comm (c : Nat → Nat) (u w x y : Nat) (h : u ≠ w) :
    upd (upd c u x) w y = upd (upd c w y) u x := by
  funext z
  simp only [upd]
  by_cases h1 : z = w <;> by_cases h2 : z = u <;> simp_all

theorem tot_append (q : Nat) (A B : List Nat) (f : (Nat → Nat) → Nat) (c : Nat → Nat) :
    tot q (A ++ B) f c = tot q A (fun c' => tot q B f c') c := by
  induction A generalizing c with
  | nil => rfl
  | cons u A ih => simp only [List.cons_append, tot, ih]

theorem tot_perm (q : Nat) {l₁ l₂ : List Nat} (h : l₁.Perm l₂) :
    ∀ f c, tot q l₁ f c = tot q l₂ f c := by
  induction h with
  | nil => intro f c; rfl
  | cons x _ ih => intro f c; simp only [tot, ih]
  | swap x y l =>
    intro f c
    simp only [tot]
    by_cases hxy : x = y
    · subst hxy; rfl
    · rw [sm_comm]
      congr 1; funext a; congr 1; funext b
      rw [upd_comm c y x b a (Ne.symm hxy)]
  | trans _ _ ih1 ih2 => intro f c; rw [ih1, ih2]

theorem tot_mono (q : Nat) (W : List Nat) (f g : (Nat → Nat) → Nat) (h : ∀ c, f c ≤ g c) :
    ∀ c, tot q W f c ≤ tot q W g c := by
  induction W with
  | nil => exact h
  | cons u W ih => intro c; exact sm_mono q _ _ (fun x => ih _)

theorem tot_const (q : Nat) (W : List Nat) (k : Nat) :
    ∀ c, tot q W (fun _ => k) c = q ^ W.length * k := by
  induction W with
  | nil => intro c; simp [tot]
  | cons u W ih =>
    intro c
    simp only [tot, ih, sm_const, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_comm (q ^ W.length) q, Nat.mul_assoc]

theorem tot_one (q : Nat) (W : List Nat) (c : Nat → Nat) : tot q W (fun _ => 1) c = q ^ W.length := by
  rw [tot_const]; simp

theorem tot_add (q : Nat) (W : List Nat) (f g : (Nat → Nat) → Nat) :
    ∀ c, tot q W (fun c => f c + g c) c = tot q W f c + tot q W g c := by
  induction W with
  | nil => intro c; rfl
  | cons u W ih => intro c; simp only [tot, ih]; rw [sm_add]

theorem tot_sum {β : Type} (q : Nat) (W : List Nat) (g : β → (Nat → Nat) → Nat) (L : List β)
    (c : Nat → Nat) :
    tot q W (fun c => (L.map (fun b => g b c)).sum) c = (L.map (fun b => tot q W (g b) c)).sum := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil]; rw [tot_const]; simp
  | cons b L ih => simp only [List.map_cons, List.sum_cons]; rw [tot_add, ih]

theorem tot_zero_of (q : Nat) (W : List Nat) (f : (Nat → Nat) → Nat) :
    ∀ c, (∀ c', (∀ u, u ∉ W → c' u = c u) → f c' = 0) → tot q W f c = 0 := by
  induction W with
  | nil => intro c h; exact h c (fun _ _ => rfl)
  | cons u W ih =>
    intro c h
    have : (fun x => tot q W f (upd c u x)) = fun _ => 0 := by
      funext x
      apply ih
      intro c' hc'
      apply h c'
      intro w hw
      have hw1 : w ≠ u := fun e => hw (e ▸ List.mem_cons_self)
      have hw2 : w ∉ W := fun e => hw (List.mem_cons_of_mem _ e)
      rw [hc' w hw2, upd_ne c u x w hw1]
    simp only [tot, this, sm_const, Nat.mul_zero]

/-- If every vertex of `W` is forced to copy a vertex outside `W` whenever `f ≠ 0`, the
sum over `W` of a `0/1` function is at most `1`. -/
theorem tot_det (q : Nat) (W : List Nat) (f : (Nat → Nat) → Nat) (hW : W.Nodup)
    (h1 : ∀ c, f c ≤ 1) (hd : ∀ w ∈ W, ∃ v, v ∉ W ∧ ∀ c, f c ≠ 0 → c w = c v) :
    ∀ c, tot q W f c ≤ 1 := by
  induction W with
  | nil => exact h1
  | cons u W ih =>
    intro c
    rw [List.nodup_cons] at hW
    obtain ⟨v, hv, hdet⟩ := hd u List.mem_cons_self
    have hvu : v ≠ u := fun e => hv (e ▸ List.mem_cons_self)
    have hvW : v ∉ W := fun e => hv (List.mem_cons_of_mem _ e)
    have ih' := ih hW.2 (fun w hw => by
      obtain ⟨v', hv', h'⟩ := hd w (List.mem_cons_of_mem _ hw)
      exact ⟨v', fun e => hv' (List.mem_cons_of_mem _ e), h'⟩)
    apply sm_le_one q (c v)
    intro x
    by_cases hx : x = c v
    · rw [ite_eq_left hx]; exact ih' _
    · rw [ite_eq_right hx]
      apply Nat.le_of_eq
      apply tot_zero_of
      intro c' hc'
      apply Classical.byContradiction
      intro hne
      have e := hdet c' hne
      rw [hc' u hW.1, hc' v hvW, upd_same, upd_ne c u x v hvu] at e
      exact hx e

/-! ## Rainbow sets, pairs, choices -/

def rb (c : Nat → Nat) (S : List Nat) : Prop := ∀ a ∈ S, ∀ b ∈ S, a ≠ b → c a ≠ c b

instance (c : Nat → Nat) (S : List Nat) : Decidable (rb c S) := by unfold rb; infer_instance

def prs : List Nat → List (Nat × Nat)
  | [] => []
  | a :: l => l.map (fun b => (a, b)) ++ prs l

/-- `ch2 n = n(n-1)/2`. -/
def ch2 : Nat → Nat
  | 0 => 0
  | n+1 => ch2 n + n

theorem prs_length (l : List Nat) : (prs l).length = ch2 l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [prs, List.length_append, List.length_map, ih, List.length_cons, ch2]; omega

theorem ch2_mono {n m : Nat} (h : n ≤ m) : ch2 n ≤ ch2 m := by
  induction m with
  | zero => rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | succ m ih =>
    by_cases h' : n = m + 1
    · rw [h']; exact Nat.le_refl _
    · have := ih (by omega); simp only [ch2]; omega

theorem mem_prs {l : List Nat} (hl : l.Nodup) {e : Nat × Nat} (he : e ∈ prs l) :
    e.1 ∈ l ∧ e.2 ∈ l ∧ e.1 ≠ e.2 := by
  induction l with
  | nil => simp [prs] at he
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    simp only [prs, List.mem_append, List.mem_map] at he
    rcases he with ⟨b, hb, rfl⟩ | he
    · exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ hb,
      by intro h; apply hl.1; simp only at h; rw [h]; exact hb⟩
    · obtain ⟨h1, h2, h3⟩ := ih hl.2 he
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2, h3⟩

theorem prs_cover {l : List Nat} (hl : l.Nodup) {a b : Nat} (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : (a, b) ∈ prs l ∨ (b, a) ∈ prs l := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    simp only [prs, List.mem_append, List.mem_map]
    rw [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact Or.inl (Or.inl ⟨b, hb, rfl⟩)
    · exact Or.inr (Or.inl ⟨a, ha, rfl⟩)
    · rcases ih hl.2 ha hb with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)

def orient (Y : List Nat) (e : Nat × Nat) : Nat × Nat := if e.1 ∈ Y then (e.2, e.1) else e

/-- Pairs of `S` with an endpoint outside `Y`, oriented so that the first one is outside `Y`. -/
def opts (Y S : List Nat) : List (Nat × Nat) :=
  ((prs S).filter (fun e => decide (e.1 ∉ Y ∨ e.2 ∉ Y))).map (orient Y)

theorem opts_length (Y S : List Nat) : (opts Y S).length ≤ ch2 S.length := by
  unfold opts; rw [List.length_map, ← prs_length]; exact List.length_filter_le _ _

theorem mem_opts {Y S : List Nat} (hS : S.Nodup) {e : Nat × Nat} (he : e ∈ opts Y S) :
    e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 ≠ e.2 ∧ e.1 ∉ Y := by
  unfold opts at he
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at he
  obtain ⟨e0, ⟨h0, hy⟩, rfl⟩ := he
  obtain ⟨h1, h2, h3⟩ := mem_prs hS h0
  unfold orient
  by_cases hY : e0.1 ∈ Y
  · rw [ite_eq_left hY]
    exact ⟨h2, h1, Ne.symm h3, by rcases hy with h | h; exact absurd hY h; exact h⟩
  · rw [ite_eq_right hY]; exact ⟨h1, h2, h3, hY⟩

theorem opts_hit {Y S : List Nat} (hS : S.Nodup) {c : Nat → Nat} (hY : rb c Y) (hn : ¬ rb c S) :
    ∃ e ∈ opts Y S, c e.1 = c e.2 := by
  have : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ c a = c b := by
    apply Classical.byContradiction
    intro hne
    apply hn
    intro a ha b hb hab hc
    exact hne ⟨a, ha, b, hb, hab, hc⟩
  obtain ⟨a, ha, b, hb, hab, hc⟩ := this
  have hout : a ∉ Y ∨ b ∉ Y := by
    apply Classical.byContradiction
    intro h
    have ha' : a ∈ Y := Classical.byContradiction (fun e => h (Or.inl e))
    have hb' : b ∈ Y := Classical.byContradiction (fun e => h (Or.inr e))
    exact hY a ha' b hb' hab hc
  have key : ∀ e0 : Nat × Nat, e0 ∈ prs S → (e0.1 ∉ Y ∨ e0.2 ∉ Y) → c e0.1 = c e0.2 →
      ∃ e ∈ opts Y S, c e.1 = c e.2 := by
    intro e0 h0 hy hc0
    refine ⟨orient Y e0, ?_, ?_⟩
    · unfold opts
      exact List.mem_map.mpr ⟨e0, List.mem_filter.mpr ⟨h0, decide_eq_true hy⟩, rfl⟩
    · unfold orient; split
      · exact hc0.symm
      · exact hc0
  rcases prs_cover hS ha hb hab with h | h
  · exact key (a, b) h hout hc
  · exact key (b, a) h (by rcases hout with h' | h'; exact Or.inr h'; exact Or.inl h') hc.symm

def chs : List (List (Nat × Nat)) → List (List (Nat × Nat))
  | [] => [[]]
  | A :: As => A.flatMap (fun e => (chs As).map (fun ch => e :: ch))

theorem len_flatMap_cons (A : List (Nat × Nat)) (B : List (List (Nat × Nat))) :
    (A.flatMap (fun e => B.map (fun ch => e :: ch))).length = A.length * B.length := by
  induction A with
  | nil => simp
  | cons a A ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, ih, List.length_cons,
      Nat.succ_mul]
    omega

theorem chs_length (k : Nat) (As : List (List (Nat × Nat))) (h : ∀ A ∈ As, A.length ≤ k) :
    (chs As).length ≤ k ^ As.length := by
  induction As with
  | nil => simp [chs]
  | cons A As ih =>
    simp only [chs, len_flatMap_cons, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_comm (k ^ As.length) k]
    exact Nat.mul_le_mul (h A List.mem_cons_self)
      (ih (fun B hB => h B (List.mem_cons_of_mem _ hB)))

theorem mem_chs_cons {A : List (Nat × Nat)} {As : List (List (Nat × Nat))}
    {ch : List (Nat × Nat)} (h : ch ∈ chs (A :: As)) :
    ∃ e ∈ A, ∃ ch' ∈ chs As, ch = e :: ch' := by
  simp only [chs, List.mem_flatMap, List.mem_map] at h
  obtain ⟨e, he, ch', hch', rfl⟩ := h
  exact ⟨e, he, ch', hch', rfl⟩

theorem chs_hit (P : Nat × Nat → Prop) (As : List (List (Nat × Nat)))
    (h : ∀ A ∈ As, ∃ e ∈ A, P e) : ∃ ch ∈ chs As, ∀ e ∈ ch, P e := by
  induction As with
  | nil => exact ⟨[], by simp [chs], by simp⟩
  | cons A As ih =>
    obtain ⟨e, he, hP⟩ := h A List.mem_cons_self
    obtain ⟨ch, hch, hP'⟩ := ih (fun B hB => h B (List.mem_cons_of_mem _ hB))
    refine ⟨e :: ch, ?_, ?_⟩
    · simp only [chs, List.mem_flatMap, List.mem_map]
      exact ⟨e, he, ch, hch, rfl⟩
    · intro x hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hP
      · exact hP' x hx

/-- Structure of a choice: first endpoints distinct, outside `Y`, never a second endpoint. -/
theorem chs_props (Y : List Nat) (Ss : List (List Nat)) (hS : ∀ S ∈ Ss, S.Nodup)
    (hsf : Ss.Pairwise (fun S T => ∀ x, x ∈ S → x ∈ T → x ∈ Y)) :
    ∀ ch ∈ chs (Ss.map (opts Y)),
      (∀ e ∈ ch, ∃ S ∈ Ss, e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 ∉ Y) ∧ (ch.map Prod.fst).Nodup ∧
      (∀ e ∈ ch, ∀ e' ∈ ch, e.1 ≠ e'.2) ∧ ch.length = Ss.length := by
  induction Ss with
  | nil => intro ch h; simp [chs] at h; subst h; simp
  | cons S Ss ih =>
    intro ch hch
    rw [List.pairwise_cons] at hsf
    have hS' : ∀ T ∈ Ss, T.Nodup := fun T hT => hS T (List.mem_cons_of_mem _ hT)
    obtain ⟨e, he, ch', hch', rfl⟩ := mem_chs_cons hch
    obtain ⟨h1, h2, h3⟩ := ih hS' hsf.2 ch' hch'
    obtain ⟨e1, e2, e12, e1Y⟩ := mem_opts (hS S List.mem_cons_self) he
    -- a point of `S` and of a later petal lies in `Y`
    have cross : ∀ e' ∈ ch', ∀ x, x ∈ S → (x = e'.1 ∨ x = e'.2) → x ∈ Y := by
      intro e' he' x hx hx'
      obtain ⟨T, hT, t1, t2, _⟩ := h1 e' he'
      exact hsf.1 T hT x hx (by rcases hx' with rfl | rfl; exact t1; exact t2)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨S, List.mem_cons_self, e1, e2, e1Y⟩
      · obtain ⟨T, hT, h⟩ := h1 x hx
        exact ⟨T, List.mem_cons_of_mem _ hT, h⟩
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, h2⟩
      intro hm
      obtain ⟨e', he', hfe⟩ := List.mem_map.mp hm
      exact e1Y (cross e' he' e.1 e1 (Or.inl hfe.symm))
    · intro x hx y hy
      rw [List.mem_cons] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact e12
      · intro hxy; exact e1Y (cross y hy x.1 e1 (Or.inr hxy))
      · intro hxy
        obtain ⟨_, _, _, _, x1Y⟩ := h1 x hx
        exact x1Y (cross x hx x.1 (hxy ▸ e2) (Or.inl rfl))
      · exact h3.1 x hx y hy
    · simp [h3.2]

theorem nodup_length_le {l₁ l₂ : List Nat} (h : l₁.Nodup) (hs : ∀ x ∈ l₁, x ∈ l₂) :
    l₁.length ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    rw [List.nodup_cons] at h
    have ha := hs a List.mem_cons_self
    have := ih h.2 (l₂ := l₂.erase a) (fun x hx =>
      (List.mem_erase_of_ne (fun e : x = a => h.1 (e ▸ hx))).mpr (hs x (List.mem_cons_of_mem _ hx)))
    rw [List.length_erase_of_mem ha] at this
    have : 0 < l₂.length := List.length_pos_of_mem ha
    simp only [List.length_cons]; omega

def ind (ch : List (Nat × Nat)) (c : Nat → Nat) : Nat := if ∀ e ∈ ch, c e.1 = c e.2 then 1 else 0

theorem choice_term (q : Nat) (hq : 0 < q) (V : List Nat) (hV : V.Nodup) (ch : List (Nat × Nat))
    (hin : ∀ e ∈ ch, e.1 ∈ V) (hnd : (ch.map Prod.fst).Nodup) (hx : ∀ e ∈ ch, ∀ e' ∈ ch, e.1 ≠ e'.2)
    (c : Nat → Nat) : tot q V (ind ch) c ≤ q ^ (V.length - ch.length) := by
  let us := ch.map Prod.fst
  let pr : Nat → Bool := fun w => decide (w ∉ us)
  let rest := V.filter pr
  let W := V.filter (fun w => !pr w)
  have hperm := List.filter_append_perm pr V
  have hlen := hperm.length_eq
  rw [List.length_append] at hlen
  have hmemW : ∀ w, w ∈ W ↔ w ∈ V ∧ w ∈ us := by
    intro w; simp [W, pr, List.mem_filter]
  have hWl : ch.length ≤ W.length := by
    have := nodup_length_le hnd (l₂ := W) (fun x hx => by
      rw [hmemW]
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact ⟨hin e he, hx⟩)
    rwa [List.length_map] at this
  have hWd : W.length = (V.filter (fun w => !pr w)).length := rfl
  have hrd : rest.length = (V.filter pr).length := rfl
  rw [← tot_perm q hperm, tot_append]
  have hin1 : ∀ c', tot q W (ind ch) c' ≤ 1 := by
    apply tot_det q W (ind ch) (List.Pairwise.filter _ hV)
    · intro c'; unfold ind; split <;> omega
    · intro w hw
      obtain ⟨_, hwu⟩ := (hmemW w).mp hw
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hwu
      refine ⟨e.2, ?_, ?_⟩
      · intro h2
        obtain ⟨_, h2u⟩ := (hmemW _).mp h2
        obtain ⟨e', he', hee⟩ := List.mem_map.mp h2u
        exact hx e' he' e he hee
      · intro c' h0
        unfold ind at h0
        split at h0
        · rename_i hall; exact hall e he
        · exact absurd rfl h0
  calc tot q rest (fun c' => tot q W (ind ch) c') c
      ≤ tot q rest (fun _ => 1) c := tot_mono q rest _ _ hin1 c
    _ = q ^ rest.length := tot_one q rest c
    _ ≤ q ^ (V.length - ch.length) := Nat.pow_le_pow_right hq (by omega)

theorem le_sum_of_mem {β : Type} (g : β → Nat) (L : List β) (x : β) (hx : x ∈ L) :
    g x ≤ (L.map g).sum := by
  induction L with
  | nil => simp at hx
  | cons y L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · have := ih hx; omega

theorem sum_le {β : Type} (g : β → Nat) (L : List β) (k : Nat) (h : ∀ x ∈ L, g x ≤ k) :
    (L.map g).sum ≤ L.length * k := by
  induction L with
  | nil => simp
  | cons y L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have := h y List.mem_cons_self
    omega

/-- The sunflower step: among the `q ^ |V|` colourings of `V` (`tot_one`), at most
`C(ℓ,2)^p q^(|V|-p)` make `Y` rainbow and none of the `p` petals rainbow. -/
theorem petal_count (q ℓ : Nat) (hq : 0 < q) (Y V : List Nat) (Ss : List (List Nat))
    (hV : V.Nodup) (hS : ∀ S ∈ Ss, S.Nodup ∧ S.length ≤ ℓ ∧ ∀ x ∈ S, x ∈ V)
    (hsf : Ss.Pairwise (fun S T => ∀ x, x ∈ S → x ∈ T → x ∈ Y)) (c : Nat → Nat) :
    tot q V (fun c => if rb c Y ∧ ∀ S ∈ Ss, ¬ rb c S then 1 else 0) c
      ≤ ch2 ℓ ^ Ss.length * q ^ (V.length - Ss.length) := by
  let As := Ss.map (opts Y)
  have hpt : ∀ c', (if rb c' Y ∧ ∀ S ∈ Ss, ¬ rb c' S then 1 else 0)
      ≤ ((chs As).map (fun ch => ind ch c')).sum := by
    intro c'
    split
    · rename_i hb
      obtain ⟨ch, hch, hP⟩ := chs_hit (fun e => c' e.1 = c' e.2) As (by
        intro A hA
        obtain ⟨S, hS', rfl⟩ := List.mem_map.mp hA
        exact opts_hit (hS S hS').1 hb.1 (hb.2 S hS'))
      have := le_sum_of_mem (fun ch => ind ch c') (chs As) ch hch
      have h1 : ind ch c' = 1 := by unfold ind; rw [ite_eq_left hP]
      omega
    · exact Nat.zero_le _
  have hprops := chs_props Y Ss (fun S h => (hS S h).1) hsf
  calc _ ≤ tot q V (fun c' => ((chs As).map (fun ch => ind ch c')).sum) c :=
        tot_mono q V _ _ hpt c
    _ = ((chs As).map (fun ch => tot q V (ind ch) c)).sum := tot_sum q V ind (chs As) c
    _ ≤ (chs As).length * q ^ (V.length - Ss.length) := by
        apply sum_le
        intro ch hch
        obtain ⟨h1, h2, h3, h4⟩ := hprops ch hch
        rw [← h4]
        apply choice_term q hq V hV ch _ h2 h3 c
        intro e he
        obtain ⟨S, hS', he1, _⟩ := h1 e he
        exact (hS S hS').2.2 e.1 he1
    _ ≤ ch2 ℓ ^ Ss.length * q ^ (V.length - Ss.length) := by
        apply Nat.mul_le_mul_right
        have := chs_length (ch2 ℓ) As (by
          intro A hA
          obtain ⟨S, hS', rfl⟩ := List.mem_map.mp hA
          exact Nat.le_trans (opts_length Y S) (ch2_mono (hS S hS').2.1))
        rwa [List.length_map] at this

end Programme.«20261024-1633-proof-complexity».Colour


#print axioms Programme.«20261024-1633-proof-complexity».Colour.petal_count
