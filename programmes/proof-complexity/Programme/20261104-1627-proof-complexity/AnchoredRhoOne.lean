import Programme.«20261104-1627-proof-complexity».HomogeneousLabels

namespace Programme.«20261104-1627-proof-complexity».AnchoredRhoOne
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC

private theorem filter_ne_length (L : List Nat) (hL : L.Nodup) (a : Nat) (ha : a ∈ L) :
    (L.filter (· != a)).length + 1 = L.length := by
  induction L with
  | nil => simp at ha
  | cons b L ih =>
    have hp := List.nodup_cons.mp hL
    by_cases he : b = a
    · subst b
      have hf : L.filter (· != a) = L := List.filter_eq_self.mpr (by
        intro x hx
        simp only [bne_iff_ne]
        intro h; subst x; exact hp.1 hx)
      simp [hf]
    · have ha' : a ∈ L := (List.mem_cons.mp ha).resolve_left (Ne.symm he)
      have hh := ih hp.2 ha'
      simp [he, hh]

theorem free_coordinates_length {m n s : Nat} {N : Matching}
    (hN : N ∈ matchings m n s) :
    (rows m N).length + s = m ∧ (cols n N).length + s = n := by
  induction s generalizing N with
  | zero =>
    have : N = [] := by simpa [matchings] using hN
    subst N
    have er : rows m [] = List.range m := by simp [rows, freeRow, List.filter_eq_self]
    have ec : cols n [] = List.range n := by simp [cols, freeCol, List.filter_eq_self]
    simp [er, ec]
  | succ s ih =>
    simp only [matchings, List.mem_flatMap, List.mem_map] at hN
    obtain ⟨M,hM,i,hi,j,hj,rfl⟩ := hN
    have hh := ih hM
    have hi' : i ∈ rows m M := (List.mem_filter.mp hi).1
    have hr := filter_ne_length (rows m M) (List.nodup_range.filter _) i hi'
    have hc := filter_ne_length (cols n M) (List.nodup_range.filter _) j hj
    have er : rows m (M ++ [(i,j)]) = (rows m M).filter (· != i) := by
      unfold rows
      rw [List.filter_filter]
      congr 1
      funext x
      simp [freeRow, List.all_append, Bool.and_comm, bne_comm]
    have ec : cols n (M ++ [(i,j)]) = (cols n M).filter (· != j) := by
      unfold cols
      rw [List.filter_filter]
      congr 1
      funext x
      simp [freeCol, List.all_append, Bool.and_comm, bne_comm]
    rw [er, ec]
    constructor <;> omega

private theorem repeated_coeff (L : List Nat) (a : Int) (v u : List Nat) :
    cf (L.map fun _ => (a,v)) u = if v.Perm u then (L.length : Int)*a else 0 := by
  induction L with
  | nil => simp [cf]
  | cons x L ih =>
    by_cases h : v.Perm u <;> simp [cf, h, Int.add_mul, Int.add_comm] at ih ⊢ <;> exact ih

/-- Exact integer rho coefficient; no modular or spanning hypothesis. -/
theorem rho_z_one_coeff {m n s : Nat} {N : Matching}
    (hN : N ∈ matchings m n s) (u : List Nat) :
    coeff (rho n (z m n 1 N)) u =
      if (mono n N).Perm u then (m : Int) - n else 0 := by
  have hex : z m n 1 N =
      (rows m N).map (fun i => (1,⟨ordered N,true,i⟩)) ++
      (cols n N).map (fun j => (-1,⟨ordered N,false,j⟩)) := by
    simp only [z, Nat.sub_self, matchings, List.filter_cons, List.all_nil,
      Bool.true_eq, ↓reduceIte, List.filter_nil, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    simp [rows, cols]
  have hp : (mono n (ordered N)).Perm (mono n N) :=
    (List.mergeSort_perm N _).map _
  have he : (mono n (ordered N)).Perm u ↔ (mono n N).Perm u :=
    ⟨fun h => hp.symm.trans h, fun h => hp.trans h⟩
  rw [hex]
  simp only [rho, List.map_append, List.map_map, Function.comp_def, coeff, cf_append]
  rw [repeated_coeff, repeated_coeff]
  have hh := free_coordinates_length hN
  have hr : ((rows m N).length : Int) + s = m := by exact_mod_cast hh.1
  have hc : ((cols n N).length : Int) + s = n := by exact_mod_cast hh.2
  by_cases h : (mono n N).Perm u <;> simp [he, h] <;> omega

/-- The positive anchored identity at t=1 has an empty relation witness. -/
theorem anchored_identity_one {p m n s : Nat} {N : Matching}
    (hN : N ∈ matchings m n s) :
    W p m n s ((rho n (z m n 1 N)).sub
      ⟨[((m : Int)-n, mono n N)]⟩) := by
  refine ⟨[], ?_, ?_⟩
  · simp
  · intro u
    have hh := rho_z_one_coeff hN u
    change (p : Int) ∣ coeff ((rho n (z m n 1 N)).sub
      ⟨[((m : Int)-n, mono n N)]⟩) u - coeff (⟨[]⟩ : Poly Nat) u
    simp only [Poly.sub, coeff, cf_append, List.map_cons, List.map_nil]
    change (p : Int) ∣ coeff (rho n (z m n 1 N)) u +
      cf [(-((m : Int)-n), mono n N)] u - cf [] u
    rw [hh]
    by_cases h : (mono n N).Perm u <;> simp [cf, h]
    rw [show (m : Int) - n + -((m : Int)-n) = 0 by omega]
    exact Int.dvd_zero _

end Programme.«20261104-1627-proof-complexity».AnchoredRhoOne
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredRhoOne.free_coordinates_length
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredRhoOne.rho_z_one_coeff

#print axioms Programme.«20261104-1627-proof-complexity».AnchoredRhoOne.anchored_identity_one
