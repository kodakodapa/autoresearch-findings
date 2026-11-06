import Programme.«20261025-0459b-proof-complexity».Indep

/-!
# Coordinate symmetries of `Work.Indep.asg`

`asg U` (all assignments on the coordinates `U`, false elsewhere) is duplicate-free for
duplicate-free `U` and contains exactly the assignments that are false off `U`. Hence:
* `cnt_asg_congr`: counts over `asg U` depend only on the set of coordinates of `U`;
* `cnt_asg_swap`: counts are invariant under an involution `σ` of the coordinates preserving `U`.
-/

namespace Programme.«20261025-0459b-proof-complexity».AsgPerm

open Programme.«20261025-0459b-proof-complexity».Indep

theorem mem_ext (U : List Nat) : ∀ (L : List (Nat → Bool)) (α : Nat → Bool),
    α ∈ ext U L ↔ ∃ a ∈ L, ∀ y, y ∉ U → α y = a y := by
  induction U with
  | nil => intro L α; exact ⟨fun h => ⟨α, h, fun _ _ => rfl⟩, fun ⟨a, ha, h⟩ =>
      (funext fun y => h y (List.not_mem_nil)) ▸ ha⟩
  | cons x U ih =>
    intro L α
    rw [show ext (x :: U) L = ext U (L.flatMap fun a => [upd a x false, upd a x true]) from rfl, ih]
    constructor
    · rintro ⟨b, hb, hα⟩
      obtain ⟨a, ha, hb⟩ := List.mem_flatMap.1 hb
      refine ⟨a, ha, fun y hy => ?_⟩
      have hyx : y ≠ x := fun e => hy (e ▸ List.mem_cons_self ..)
      rw [hα y (fun h => hy (List.mem_cons_of_mem _ h))]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> simp [upd, hyx]
    · rintro ⟨a, ha, hα⟩
      refine ⟨upd a x (α x), List.mem_flatMap.2 ⟨a, ha, ?_⟩, fun y hy => ?_⟩
      · cases α x <;> simp
      · by_cases hyx : y = x
        · subst hyx; simp [upd]
        · simp only [upd, hyx, ite_false]
          exact hα y (fun h => by
            rcases List.mem_cons.1 h with h | h
            · exact hyx h
            · exact hy h)

theorem mem_asg (U : List Nat) (α : Nat → Bool) : α ∈ asg U ↔ ∀ y, y ∉ U → α y = false := by
  unfold asg; rw [mem_ext]; simp

theorem nodup_step (x : Nat) : ∀ L : List (Nat → Bool), L.Nodup → (∀ a ∈ L, a x = false) →
    (L.flatMap fun a => [upd a x false, upd a x true]).Nodup
  | [], _, _ => List.nodup_nil
  | a :: L, hL, hx => by
    rw [List.flatMap_cons, List.nodup_append]
    have ha : a ∉ L := (List.nodup_cons.1 hL).1
    refine ⟨?_, nodup_step x L (List.nodup_cons.1 hL).2
      (fun b hb => hx b (List.mem_cons_of_mem _ hb)), ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
        and_true, not_false_eq_true]
      intro h; have := congrFun h x; simp [upd] at this
    · intro c hc d hd hcd
      obtain ⟨b, hb, hd⟩ := List.mem_flatMap.1 hd
      subst hcd
      have hab : a = b := by
        funext y
        by_cases hyx : y = x
        · subst hyx; rw [hx a (List.mem_cons_self ..), hx b (List.mem_cons_of_mem _ hb)]
        · have h1 : ∀ v, upd a x v y = a y := fun v => by simp [upd, hyx]
          have h2 : ∀ v, upd b x v y = b y := fun v => by simp [upd, hyx]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hd
          rcases hc with rfl | rfl <;> rcases hd with h | h <;>
            (have := congrFun h y; simp only [h1, h2] at this; exact this)
      exact ha (hab ▸ hb)

theorem nodup_ext (U : List Nat) : ∀ L : List (Nat → Bool), U.Nodup → L.Nodup →
    (∀ a ∈ L, ∀ y ∈ U, a y = false) → (ext U L).Nodup := by
  induction U with
  | nil => intro L _ hL _; exact hL
  | cons x U ih =>
    intro L hU hL h0
    have hxU : x ∉ U := (List.nodup_cons.1 hU).1
    apply ih _ (List.nodup_cons.1 hU).2 (nodup_step x L hL fun a ha => h0 a ha x
      (List.mem_cons_self ..))
    intro b hb y hy
    obtain ⟨a, ha, hb⟩ := List.mem_flatMap.1 hb
    have hyx : y ≠ x := fun e => hxU (e ▸ hy)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp [upd, hyx, h0 a ha y (List.mem_cons_of_mem _ hy)]

theorem nodup_asg {U : List Nat} (hU : U.Nodup) : (asg U).Nodup :=
  nodup_ext U _ hU (List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩) (by simp)

theorem cnt_perm {L L' : List (Nat → Bool)} (h : L.Perm L') (P : (Nat → Bool) → Prop)
    [DecidablePred P] : cnt L P = cnt L' P := (h.filter _).length_eq

/-- Counts over `asg U` depend only on the coordinate set. -/
theorem cnt_asg_congr {U U' : List Nat} (hU : U.Nodup) (hU' : U'.Nodup) (h : ∀ y, y ∈ U ↔ y ∈ U')
    (P : (Nat → Bool) → Prop) [DecidablePred P] : cnt (asg U) P = cnt (asg U') P := by
  apply cnt_perm
  rw [List.perm_ext_iff_of_nodup (nodup_asg hU) (nodup_asg hU')]
  intro α; rw [mem_asg, mem_asg]
  exact ⟨fun h1 y hy => h1 y (fun e => hy ((h y).1 e)),
    fun h1 y hy => h1 y (fun e => hy ((h y).2 e))⟩

/-- Counts over `asg U` are invariant under a coordinate involution preserving `U`. -/
theorem cnt_asg_swap {U : List Nat} (hU : U.Nodup) (σ : Nat → Nat) (hσ : ∀ y, σ (σ y) = y)
    (hσU : ∀ y, y ∈ U ↔ σ y ∈ U) (P : (Nat → Bool) → Prop) [DecidablePred P] :
    cnt (asg U) P = cnt (asg U) (fun α => P (fun y => α (σ y))) := by
  have hperm : ((asg U).map fun α => fun y => α (σ y)).Perm (asg U) := by
    rw [List.perm_ext_iff_of_nodup _ (nodup_asg hU)]
    · intro γ
      rw [List.mem_map, mem_asg]
      constructor
      · rintro ⟨α, hα, rfl⟩ y hy
        exact (mem_asg U α).1 hα (σ y) (fun e => hy ((hσU y).2 e))
      · intro hγ
        refine ⟨fun y => γ (σ y), (mem_asg U _).2 fun y hy => hγ (σ y) (fun e => hy ?_), ?_⟩
        · exact (hσU y).2 e
        · funext y; simp [hσ]
    · exact List.Pairwise.map _ (fun a b hab e => hab (funext fun y => by
        have := congrFun e (σ y); simpa [hσ] using this)) (nodup_asg hU)
  rw [← cnt_perm hperm]
  unfold cnt; rw [List.filter_map, List.length_map]; rfl

end Programme.«20261025-0459b-proof-complexity».AsgPerm
