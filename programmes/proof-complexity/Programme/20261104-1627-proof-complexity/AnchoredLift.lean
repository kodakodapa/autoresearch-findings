import Programme.«20261104-1627-proof-complexity».PigeonGenerators
import Programme.«20261104-1627-proof-complexity».OmissionPairing

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels

/-- The smaller-board enumeration is exactly the larger enumeration avoiding
its final row, including multiplicities (expressed as a list permutation). -/
theorem matchings_last_filter_perm (m n d : Nat) :
    ((matchings (m+1) n d).filter fun E => E.all fun e => e.1 != m).Perm
      (matchings m n d) := by
  apply List.perm_ext_iff_of_nodup
    ((matchings_nodup (m+1) n d).filter _) (matchings_nodup m n d) |>.mpr
  intro E
  simp only [List.mem_filter, Bool.and_eq_true, List.all_eq_true, bne_iff_ne]
  constructor
  · intro h
    exact matching_drop_last E h.1 h.2
  · intro h
    refine ⟨matching_add_last E h, ?_⟩
    intro e he
    have := matching_rows_lt h e he
    omega

theorem z_lift_mem {m n d t : Nat} {N : Matching}
    (ht : t ∈ (List.range d).map (· + 1))
    (hN : N ∈ matchings m n (d-t)) :
    z (m+1) n t N ∈ syzygies (m+1) n d := by
  unfold syzygies
  apply List.mem_append_right
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨t, List.mem_map.mp ht, N, matching_add_last N hN, rfl⟩

theorem z_one_first_block (m n : Nat) (N : Matching) :
    splitPigeon m 1 (z (m+1) n 1 N) =
      splitPigeon m 1 (z m n 1 N) := by
  have ft {α : Type} (l : List α) : l.filter (fun _ => true) = l :=
    List.filter_eq_self.mpr (by simp)
  simp only [z, Nat.sub_self, matchings, List.filter_cons,
    List.all_nil, Bool.true_eq, ↓reduceIte, List.filter_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    ft, List.append_nil]
  rw [rows_succ]
  simp only [List.filter_append, List.map_append, splitPigeon_append]
  have extra : splitPigeon m 1
      ((if freeRow N m then [m] else []).map
        fun i => (1, (⟨ordered N,true,i⟩ : Label))) = [] := by
    cases h : freeRow N m <;>
      simp [h, splitPigeon, pigeonBlock]
    split <;> simp_all
  rw [extra]
  simp

/-- One matching's contribution to the anchored generator. -/
def zPart (m n : Nat) (N E : Matching) : Vector :=
  ((rows m (N ++ E)).filter fun i => E.all fun e => e.1 < i).map
    (fun i => (1, ⟨ordered (N ++ E),true,i⟩)) ++
  ((cols n (N ++ E)).filter fun j => E.all fun e => e.2 < j).map
    (fun j => (-1, ⟨ordered (N ++ E),false,j⟩))

theorem zPart_first_block (m n : Nat) (N E : Matching) :
    splitPigeon m 1 (zPart (m+1) n N E) =
      splitPigeon m 1 (zPart m n N E) := by
  unfold zPart
  rw [rows_succ]
  simp only [List.filter_append, List.map_append, splitPigeon_append]
  have extra : splitPigeon m 1
      (((if freeRow (N ++ E) m then [m] else []).filter
        fun i => E.all fun e => e.1 < i).map
        fun i => (1, (⟨ordered (N ++ E),true,i⟩ : Label))) = [] := by
    cases h : freeRow (N ++ E) m <;>
      simp [h, splitPigeon, pigeonBlock]
    split <;> simp_all
  rw [extra]
  simp

theorem zPart_used_last (m a n : Nat) (N E : Matching)
    (h : ¬(E.all fun e => e.1 != m) = true) :
    splitPigeon m 1 (zPart a n N E) = [] := by
  have he : ∃ e ∈ E, e.1 = m := by
    apply Classical.byContradiction
    intro hn
    apply h
    simp only [List.all_eq_true, bne_iff_ne]
    intro e he hm
    exact hn ⟨e, he, hm⟩
  obtain ⟨e, he, hm⟩ := he
  have hu (b : Bool) (i : Nat) :
      usesPigeon m ⟨ordered (N ++ E),b,i⟩ = true := by
    simp only [usesPigeon, List.any_eq_true]
    exact ⟨e, by simpa [ordered] using List.mem_append_right N he, by simpa [hm]⟩
  have nilmap (l : List Nat) (b : Bool) (c : Int) :
      splitPigeon m 1 (l.map fun i => (c, (⟨ordered (N ++ E),b,i⟩ : Label))) = [] := by
    induction l with
    | nil => rfl
    | cons i l ih => simpa [splitPigeon, pigeonBlock, hu] using ih
  simp only [zPart, splitPigeon_append, nilmap, List.append_nil]

private theorem flatMap_filter_skip {α β : Type} (l : List α)
    (p : α → Bool) (f : α → List β) (h : ∀ x ∈ l, p x ≠ true → f x = []) :
    l.flatMap f = (l.filter p).flatMap f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih (by intro x hx; exact h x (by simp [hx]))
    by_cases ha : p a = true
    · simp [ha, ih']
    · simp [ha, h a (by simp) ha, ih']

/-- General anchored lifts preserve the first block up to list order. -/
theorem z_first_block_perm (m n t : Nat) (N : Matching) :
    (splitPigeon m 1 (z (m+1) n t N)).Perm
      (splitPigeon m 1 (z m n t N)) := by
  let good : Matching → Bool := fun E =>
    E.all fun e => freeRow N e.1 && freeCol N e.2
  let avoids : Matching → Bool := fun E => E.all fun e => e.1 != m
  let f : Matching → Vector := fun E => splitPigeon m 1 (zPart m n N E)
  have expand (a : Nat) : splitPigeon m 1 (z a n t N) =
      ((matchings a n (t-1)).filter good).flatMap
        (fun E => splitPigeon m 1 (zPart a n N E)) := by
    simp only [z, splitPigeon, List.filter_flatMap, zPart, good]
  rw [expand, expand]
  simp only [zPart_first_block]
  change (((matchings (m+1) n (t-1)).filter good).flatMap f).Perm
    (((matchings m n (t-1)).filter good).flatMap f)
  rw [flatMap_filter_skip _ avoids f (by
    intro E _ hE
    exact zPart_used_last m m n N E hE)]
  have commute : (((matchings (m+1) n (t-1)).filter good).filter avoids) =
      (((matchings (m+1) n (t-1)).filter avoids).filter good) := by
    simp only [List.filter_filter]
    congr 1
    funext E
    exact Bool.and_comm _ _
  rw [commute]
  exact ((matchings_last_filter_perm m n (t-1)).filter good).flatMap_right f

theorem vectorCoeff_perm {u v : Vector} (h : u.Perm v) (g : Label) :
    vectorCoeff u g = vectorCoeff v g := by
  have sums {a b : List Int} (hp : a.Perm b) : a.sum = b.sum := by
    induction hp with
    | nil => rfl
    | cons x hp ih => simp only [List.sum_cons, ih]
    | swap x y l => simp only [List.sum_cons]; omega
    | trans hp hq ih ij => exact ih.trans ij
  exact sums ((h.filter fun t => t.2 == g).map (fun t => t.1))

/-- Every named generator lifts to the enlarged board with identical G1
aggregate coordinates. No spanning or Lprime assumption is needed. -/
theorem syzygy_first_block_lift {m n d : Nat} {u : Vector}
    (hu : u ∈ syzygies m n d) :
    ∃ v ∈ syzygies (m+1) n d, ∀ g,
      vectorCoeff (splitPigeon m 1 v) g = vectorCoeff (splitPigeon m 1 u) g := by
  unfold syzygies at hu
  rcases List.mem_append.mp hu with hu | hu
  · split at hu
    · simp at hu
    · rename_i hd
      have hd' : 2 ≤ d := by omega
      simp only [List.mem_flatMap, List.mem_append, List.mem_map, List.mem_filter] at hu
      obtain ⟨N, hN, hu⟩ := hu
      rcases hu with (hu | hu) | hu
      · obtain ⟨a, ha, b, hb, rfl⟩ := hu
        exact ⟨rr n N a b, rr_lift_mem hd' hN ha hb.1 (by simpa using hb.2),
          fun _ => rfl⟩
      · obtain ⟨a, ha, b, hb, rfl⟩ := hu
        refine ⟨cc (m+1) N a b, cc_lift_mem hd' hN ha hb.1 (by simpa using hb.2), ?_⟩
        intro g
        rw [cc_first_block]
      · obtain ⟨i, hi, j, hj, rfl⟩ := hu
        refine ⟨rc (m+1) n N i j, rc_lift_mem hd' hN hi hj, ?_⟩
        intro g
        rw [rc_first_block]
  · simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨t, ht, N, hN, rfl⟩ := hu
    exact ⟨z (m+1) n t N, z_lift_mem (List.mem_map.mpr ht) hN,
      vectorCoeff_perm (z_first_block_perm m n t N)⟩

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.matchings_last_filter_perm
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.z_lift_mem
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.z_one_first_block

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.z_first_block_perm

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.syzygy_first_block_lift
