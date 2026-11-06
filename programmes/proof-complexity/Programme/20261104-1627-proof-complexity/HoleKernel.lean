import Programme.«20261104-1627-proof-complexity».HoleCoefficientTransport
import Programme.«20261104-1627-proof-complexity».HoleProjection
namespace Programme.«20261104-1627-proof-complexity».HoleKernel
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261104-1627-proof-complexity».HoleCoefficientTransport Programme.«20261104-1627-proof-complexity».HoleProjection

theorem push_last_edge {n : Nat} (hn : 0<n) (i j : Nat) (hj : j<n) :
    pushCode n n (i*n+j) = i*(n+1)+j := by
  rw [pushCode_edge hn n i j hj]
  simp [omitHole, hj]

theorem mono_last {n : Nat} (hn : 0<n) (M : Matching)
    (hb : ∀ e ∈ M, e.2<n) :
    (mono n M).map (pushCode n n) = mono (n+1) M := by
  simp only [mono, List.map_map]
  apply List.map_congr_left
  intro e he
  exact push_last_edge hn e.1 e.2 (hb e he)

theorem push_avoids {n : Nat} (hn : 0<n) (x : Nat) :
    pushCode n n x % (n+1) < n := by
  have hx := Nat.mod_lt x hn
  have he : pushCode n n x = (x/n)*(n+1)+x%n := by simp [pushCode, omitHole, hx]
  rw [he, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  exact hx

private theorem cf_zero_hole {n : Nat} (hn : 0<n)
    (L : List (Int × List Nat)) (u : List Nat)
    (hL : ∀ t ∈ L, ∃ x ∈ t.2, x % (n+1) = n) :
    cf L (u.map (pushCode n n)) = 0 := by
  have hf : L.filter (fun t => decide (t.2.Perm (u.map (pushCode n n)))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht hp
    obtain ⟨x,hx,he⟩ := hL t ht
    have hm := (of_decide_eq_true hp).mem_iff.mp hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hm
    have := push_avoids hn y
    omega
  simp [cf,hf]

private theorem cols_succ (n : Nat) (M : Matching) :
    cols (n+1) M = cols n M ++ if freeCol M n then [n] else [] := by
  simp only [cols, List.range_succ, List.filter_append]
  cases h : freeCol M n <;> simp [h]

private theorem first_coeff {m n d : Nat} (hn : 0<n) (g : Label)
    (hg : g ∈ labels m n d) (u : List Nat) :
    coeff (topLabel m (n+1) g) (u.map (pushCode n n)) =
      coeff (topLabel m n g) u := by
  have hbase : ∀ e ∈ g.base, e.2<n := by
    unfold labels at hg
    split at hg
    · contradiction
    · obtain ⟨M,hM,hg⟩ := List.mem_flatMap.mp hg
      rcases List.mem_append.mp hg with hg | hg <;>
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg <;> exact matching_cols_lt hM
  have hm := mono_last hn g.base hbase
  cases hr : g.isRow
  · have hj : g.mark<n := by
      unfold labels at hg
      split at hg
      · contradiction
      · obtain ⟨M,hM,hg⟩ := List.mem_flatMap.mp hg
        rcases List.mem_append.mp hg with hg | hg <;> obtain ⟨a,ha,he⟩ := List.mem_map.mp hg
        · have := congrArg Label.isRow he; simp [hr] at this
        · have ha' := List.mem_range.mp (List.mem_filter.mp ha).1
          have := congrArg Label.mark he
          simpa [← this] using ha'
    have he : topLabel m (n+1) g = rename (pushCode n n) (topLabel m n g) := by
      simp only [topLabel, hr, Bool.false_eq_true, ↓reduceIte, rename, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      simp [push_last_edge hn i g.mark hj, hm]
    rw [he, coeff_rename (Programme.«20261104-1627-proof-complexity».HoleCodeTransport.pushCode_injective hn)]
  · have he : (topLabel m (n+1) g).terms =
        (rename (pushCode n n) (topLabel m n g)).terms ++
        ((if freeCol g.base n then [n] else []).map fun j => (1,(g.mark*(n+1)+j)::mono (n+1) g.base)) := by
      simp only [topLabel, hr, ↓reduceIte, cols_succ, List.map_append, rename, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j hj
      have hj' := List.mem_range.mp (List.mem_filter.mp hj).1
      simp [push_last_edge hn g.mark j hj', hm]
    change cf _ _ = _
    rw [he, cf_append]
    have hz : cf ((if freeCol g.base n then [n] else []).map fun j =>
        (1,(g.mark*(n+1)+j)::mono (n+1) g.base)) (u.map (pushCode n n)) = 0 := by
      apply cf_zero_hole hn
      intro t ht
      split at ht
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at ht
        subst t
        refine ⟨g.mark*(n+1)+n, by simp, ?_⟩
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      · simp at ht
    rw [hz, Int.add_zero]
    exact coeff_rename (Programme.«20261104-1627-proof-complexity».HoleCodeTransport.pushCode_injective hn) _ _
private theorem nonfirst_zero {m n d : Nat} (hn : 0<n) (g : Label)
    (_hg : g ∈ labels m (n+1) d) (hb : holeBlock n g ≠ 1) (u : List Nat) :
    coeff (topLabel m (n+1) g) (u.map (pushCode n n)) = 0 := by
  apply cf_zero_hole hn
  intro t ht
  by_cases huse : usesHole n g = true
  · obtain ⟨e,he,hen⟩ := List.any_eq_true.mp huse
    have hen : e.2 = n := by simpa using hen
    have hx : e.1*(n+1)+n ∈ mono (n+1) g.base := by
      exact List.mem_map.mpr ⟨e,he,by simp [hen]⟩
    unfold topLabel at ht
    split at ht <;> obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht <;>
      refine ⟨e.1*(n+1)+n,List.mem_cons_of_mem _ hx,?_⟩ <;>
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  · have hu : usesHole n g = false := Bool.eq_false_iff.mpr huse
    have hr : g.isRow = false ∧ g.mark = n := by
      cases hi : g.isRow <;> simp_all [holeBlock]
    simp only [topLabel,hr.1,Bool.false_eq_true,↓reduceIte] at ht
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
    refine ⟨i*(n+1)+g.mark,by simp,?_⟩
    rw [hr.2,Nat.add_comm,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt (by omega)]

private theorem cf_scaled (a : Int) (L : List (Int × List Nat)) (u : List Nat) :
    cf (L.map fun b => (a*b.1,b.2)) u = a * cf L u := by
  induction L with
  | nil => simp [cf]
  | cons b L ih =>
    by_cases h : b.2.Perm u <;> simp [cf,h] at ih ⊢ <;> simp_all [Int.mul_add]

theorem splitHole_one_coeff {m n d : Nat} (hn : 0<n) (v : Vector)
    (hv : valid m (n+1) d v) (u : List Nat) :
    coeff (top m n (splitHole n 1 v)) u =
      coeff (top m (n+1) v) (u.map (pushCode n n)) := by
  induction v with
  | nil => simp [splitHole,top,coeff,cf]
  | cons t v ih =>
    have ht := hv t List.mem_cons_self
    have hi := ih (fun a ha => hv a (List.mem_cons_of_mem t ha))
    by_cases hb : holeBlock n t.2 = 1
    · simp only [splitHole,List.filter_cons,hb,beq_self_eq_true,↓reduceIte]
      change cf (_ ++ _) u = cf (_ ++ _) (u.map (pushCode n n))
      rw [cf_append,cf_append,cf_scaled,cf_scaled]
      rw [show cf (topLabel m (n+1) t.2).terms (u.map (pushCode n n)) =
        cf (topLabel m n t.2).terms u from first_coeff hn t.2 (label_drop_hole t.2 ht hb) u]
      exact congrArg (fun x => t.1 * cf (topLabel m n t.2).terms u + x) hi
    · simp only [splitHole,List.filter_cons,show (holeBlock n t.2 == 1) = false by simp [hb],↓reduceIte]
      change _ = cf (_ ++ _) (u.map (pushCode n n))
      rw [cf_append,cf_scaled,show cf (topLabel m (n+1) t.2).terms (u.map (pushCode n n)) = 0 from
        nonfirst_zero hn t.2 ht hb u]
      simpa only [Int.mul_zero,Int.zero_add,coeff,top,splitHole,List.flatMap,Bool.false_eq_true,ite_false] using hi

theorem splitHole_one_kernel {p m n d : Nat} (hn : 0<n) {v : Vector}
    (hv : Kernel p m (n+1) d v) : Kernel p m n d (splitHole n 1 v) := by
  refine ⟨splitHole_one_valid hv.1,fun u => ?_⟩
  rw [splitHole_one_coeff hn v hv.1 u]
  simpa [coeff,cf] using hv.2 (u.map (pushCode n n))
end Programme.«20261104-1627-proof-complexity».HoleKernel
#print axioms Programme.«20261104-1627-proof-complexity».HoleKernel.splitHole_one_coeff
#print axioms Programme.«20261104-1627-proof-complexity».HoleKernel.splitHole_one_kernel
