import Programme.«20261104-1627-proof-complexity».BoundedRelationCertificates
import Programme.«20261104-1627-proof-complexity».ExtensionOrder
namespace Programme.«20261104-1627-proof-complexity».MixedRhoLowering
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261104-1627-proof-complexity».MatchingLabels
theorem edge_eval (n : Nat) (M : Matching) (i j : Nat) (a : Nat → Bool) :
    monoEval a (mono n (ordered (M ++ [(i,j)]))) = monoEval a ((i*n+j)::mono n M) := by
  have h : monoEval a (mono n (ordered (M ++ [(i,j)]))) = monoEval a (mono n (M ++ [(i,j)])) :=
    by
      rw [Programme.«20261025-0459-proof-complexity».MatchQuot.monoEval_all,
        Programme.«20261025-0459-proof-complexity».MatchQuot.monoEval_all]
      congr 1
      apply propext
      constructor
      · intro h x hx
        exact h x ((mono_ordered_perm n (M ++ [(i,j)])).mem_iff.mpr hx)
      · intro h x hx
        exact h x ((mono_ordered_perm n (M ++ [(i,j)])).mem_iff.mp hx)
  rw [h]
  simp [mono, monoEval, List.prod_append, Int.mul_comm]
theorem signed_sum (L : List Nat) (f : Nat → Int) :
    (L.map (fun x => -f x)).sum = -(L.map f).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp [ih, Int.neg_add]
theorem remove_sum (L : List Nat) (hL : L.Nodup) (i : Nat) (hi : i ∈ L)
    (f : Nat → Int) :
    ((L.filter (· != i)).map f).sum + f i = (L.map f).sum := by
  induction L with
  | nil => simp at hi
  | cons x L ih =>
    obtain ⟨hx, hL⟩ := List.nodup_cons.mp hL
    by_cases h : x = i
    · subst x
      have hf : L.filter (· != i) = L := by
        apply List.filter_eq_self.mpr
        intro a ha
        simp only [bne_iff_ne]
        intro he
        exact hx (he ▸ ha)
      simp [hf, Int.add_comm]
    · have hiL : i ∈ L := (List.mem_cons.mp hi).resolve_left (Ne.symm h)
      have hh := ih hL hiL
      simp only [List.filter_cons, bne_iff_ne]
      rw [if_pos h]
      simp only [List.map_cons, List.sum_cons]
      omega

theorem rho_rc_eval (m n : Nat) (N : Matching) (i j : Nat)
    (hi : i ∈ rows m N) (hj : j ∈ cols n N) (a : Nat → Bool) :
    (rho n (rc m n N i j)).eval a =
      (relation m n ⟨N,false,j⟩).eval a - (relation m n ⟨N,true,i⟩).eval a := by
  have hr := remove_sum (rows m N) (List.nodup_range.filter _) i hi
    (fun x => monoEval a ((x*n+j)::mono n N))
  have hc := remove_sum (cols n N) (List.nodup_range.filter _) j hj
    (fun x => monoEval a ((i*n+x)::mono n N))
  simp only [rc, rho, Poly.eval, List.map_append, List.sum_append, List.map_map,
    Function.comp_def, Int.one_mul, Int.neg_one_mul]
  simp only [edge_eval]
  rw [signed_sum]
  simp [relation, Poly.sub, topLabel, Poly.eval, List.map_map, Function.comp_def,
    Int.sub_eq_add_neg, Int.neg_add] 
  omega
theorem rc_lowering {p n k i j : Nat} (N : Matching)
    (hi : i < n+k) (hj : j < n)
    (fi : ∀ e ∈ N, e.1 ≠ i) (fj : ∀ e ∈ N, e.2 ≠ j)
    (hr : ∀ e ∈ N, e.1 < n+k) (hc : ∀ e ∈ N, e.2 < n) :
    NSIn p (ontoFPHP n k) (N.length+1) (rho n (rc (n+k) n N i j)).eval := by
  have hir : i ∈ rows (n+k) N := by
    simp only [rows, List.mem_filter, List.mem_range, freeRow, List.all_eq_true,
      bne_iff_ne]
    exact ⟨hi, fi⟩
  have hjc : j ∈ cols n N := by
    simp only [cols, List.mem_filter, List.mem_range, freeCol, List.all_eq_true,
      bne_iff_ne]
    exact ⟨hj, fj⟩
  apply nsIn_congr (nsIn_lin 1 (-1)
    (Programme.«20261104-1627-proof-complexity».ColumnRelationCertificate.column_relation_nsIn N hj fj hc)
    (Programme.«20261104-1627-proof-complexity».RowRelationCertificate.row_relation_nsIn N hi fi hr))
  intro a
  rw [rho_rc_eval (n+k) n N i j hir hjc]
  simp [Int.sub_eq_add_neg]
#print axioms rho_rc_eval
#print axioms rc_lowering
end Programme.«20261104-1627-proof-complexity».MixedRhoLowering
