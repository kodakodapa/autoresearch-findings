/- Hole mirror of canonical AnchoredLift; adapted with attribution. -/
import Programme.«20261104-1627-proof-complexity».HoleGenerators
import Programme.«20261104-1627-proof-complexity».AnchoredLift
namespace Programme.«20261104-1627-proof-complexity».HoleAnchoredLift
open Programme.«20261104-1627-proof-complexity».MatchingLabels Programme.«20261104-1627-proof-complexity».HoleProjection Programme.«20261104-1627-proof-complexity».HoleGenerators
/-- The smaller-board enumeration is exactly the larger enumeration avoiding
its final row, including multiplicities (expressed as a list permutation). -/
theorem matchings_last_hole_filter_perm (m n d : Nat) :
    ((matchings m (n+1) d).filter fun E => E.all fun e => e.2 != n).Perm
      (matchings m n d) := by
  apply List.perm_ext_iff_of_nodup
    ((matchings_nodup m (n+1) d).filter _) (matchings_nodup m n d) |>.mpr
  intro E
  simp only [List.mem_filter, Bool.and_eq_true, List.all_eq_true, bne_iff_ne]
  constructor
  · intro h
    exact matching_drop_hole E h.1 h.2
  · intro h
    refine ⟨matching_add_hole E h, ?_⟩
    intro e he
    have := matching_cols_lt h e he
    omega

theorem z_lift_mem {m n d t : Nat} {N : Matching}
    (ht : t ∈ (List.range d).map (· + 1))
    (hN : N ∈ matchings m n (d-t)) :
    z m (n+1) t N ∈ syzygies m (n+1) d := by
  unfold syzygies
  apply List.mem_append_right
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨t, List.mem_map.mp ht, N, matching_add_hole N hN, rfl⟩

theorem z_one_first_block (m n : Nat) (N : Matching) :
    splitHole n 1 (z m (n+1) 1 N) =
      splitHole n 1 (z m n 1 N) := by
  have ft {α : Type} (l : List α) : l.filter (fun _ => true) = l :=
    List.filter_eq_self.mpr (by simp)
  simp only [z, Nat.sub_self, matchings, List.filter_cons,
    List.all_nil, Bool.true_eq, ↓reduceIte, List.filter_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    ft, List.append_nil]
  rw [cols_succ]
  simp only [List.filter_append, List.map_append, splitHole_append]
  have extra : splitHole n 1
      ((if freeCol N n then [n] else []).map
        fun i => (-1, (⟨ordered N,false,i⟩ : Label))) = [] := by
    cases h : freeCol N n <;>
      simp [h, splitHole, holeBlock]
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
    splitHole n 1 (zPart m (n+1) N E) =
      splitHole n 1 (zPart m n N E) := by
  unfold zPart
  rw [cols_succ]
  simp only [List.filter_append, List.map_append, splitHole_append]
  have extra : splitHole n 1
      (((if freeCol (N ++ E) n then [n] else []).filter
        fun i => E.all fun e => e.2 < i).map
        fun i => (-1, (⟨ordered (N ++ E),false,i⟩ : Label))) = [] := by
    cases h : freeCol (N ++ E) n <;>
      simp [h, splitHole, holeBlock]
    split <;> simp_all
  rw [extra]
  simp

theorem zPart_used_last (m a n : Nat) (N E : Matching)
    (h : ¬(E.all fun e => e.2 != n) = true) :
    splitHole n 1 (zPart m a N E) = [] := by
  have he : ∃ e ∈ E, e.2 = n := by
    apply Classical.byContradiction
    intro hn
    apply h
    simp only [List.all_eq_true, bne_iff_ne]
    intro e he hm
    exact hn ⟨e, he, hm⟩
  obtain ⟨e, he, hm⟩ := he
  have hu (b : Bool) (i : Nat) :
      usesHole n ⟨ordered (N ++ E),b,i⟩ = true := by
    simp only [usesHole, List.any_eq_true]
    exact ⟨e, by simpa [ordered] using List.mem_append_right N he, by simpa [hm]⟩
  have nilmap (l : List Nat) (b : Bool) (c : Int) :
      splitHole n 1 (l.map fun i => (c, (⟨ordered (N ++ E),b,i⟩ : Label))) = [] := by
    induction l with
    | nil => rfl
    | cons i l ih => simpa [splitHole, holeBlock, hu] using ih
  simp only [zPart, splitHole_append, nilmap, List.append_nil]

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
    (splitHole n 1 (z m (n+1) t N)).Perm
      (splitHole n 1 (z m n t N)) := by
  let good : Matching → Bool := fun E =>
    E.all fun e => freeRow N e.1 && freeCol N e.2
  let avoids : Matching → Bool := fun E => E.all fun e => e.2 != n
  let f : Matching → Vector := fun E => splitHole n 1 (zPart m n N E)
  have expand (a : Nat) : splitHole n 1 (z m a t N) =
      ((matchings m a (t-1)).filter good).flatMap
        (fun E => splitHole n 1 (zPart m a N E)) := by
    simp only [z, splitHole, List.filter_flatMap, zPart, good]
  rw [expand, expand]
  simp only [zPart_first_block]
  change (((matchings m (n+1) (t-1)).filter good).flatMap f).Perm
    (((matchings m n (t-1)).filter good).flatMap f)
  rw [flatMap_filter_skip _ avoids f (by
    intro E _ hE
    exact zPart_used_last m n n N E hE)]
  have commute : (((matchings m (n+1) (t-1)).filter good).filter avoids) =
      (((matchings m (n+1) (t-1)).filter avoids).filter good) := by
    simp only [List.filter_filter]
    congr 1
    funext E
    exact Bool.and_comm _ _
  rw [commute]
  exact ((matchings_last_hole_filter_perm m n (t-1)).filter good).flatMap_right f


theorem syzygy_first_block_lift {m n d : Nat} {u : Vector}
    (hu : u ∈ syzygies m n d) :
    ∃ v ∈ syzygies m (n+1) d, ∀ g,
      vectorCoeff (splitHole n 1 v) g = vectorCoeff (splitHole n 1 u) g := by
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
        refine ⟨rr (n+1) N a b, Programme.«20261104-1627-proof-complexity».HoleGenerators.rr_lift_mem hd' hN ha hb.1 (by simpa using hb.2), ?_⟩
        intro g
        rw [Programme.«20261104-1627-proof-complexity».HoleGenerators.rr_first_block]
      · obtain ⟨a, ha, b, hb, rfl⟩ := hu
        exact ⟨cc m N a b, Programme.«20261104-1627-proof-complexity».HoleGenerators.cc_lift_mem hd' hN ha hb.1 (by simpa using hb.2), fun _ => rfl⟩
      · obtain ⟨i, hi, j, hj, rfl⟩ := hu
        refine ⟨rc m (n+1) N i j, Programme.«20261104-1627-proof-complexity».HoleGenerators.rc_lift_mem hd' hN hi hj, ?_⟩
        intro g
        rw [Programme.«20261104-1627-proof-complexity».HoleGenerators.rc_first_block]
  · simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨t, ht, N, hN, rfl⟩ := hu
    exact ⟨z m (n+1) t N, Programme.«20261104-1627-proof-complexity».HoleAnchoredLift.z_lift_mem (List.mem_map.mpr ht) hN,
      vectorCoeff_perm (Programme.«20261104-1627-proof-complexity».HoleAnchoredLift.z_first_block_perm m n t N)⟩

end Programme.«20261104-1627-proof-complexity».HoleAnchoredLift
#print axioms Programme.«20261104-1627-proof-complexity».HoleAnchoredLift.z_one_first_block
#print axioms Programme.«20261104-1627-proof-complexity».HoleAnchoredLift.z_first_block_perm
#print axioms Programme.«20261104-1627-proof-complexity».HoleAnchoredLift.syzygy_first_block_lift

