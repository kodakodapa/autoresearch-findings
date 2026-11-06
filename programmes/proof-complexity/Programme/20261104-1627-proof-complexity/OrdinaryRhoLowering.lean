import Programme.«20261104-1627-proof-complexity».BoundedRelationCertificates
import Programme.«20261104-1627-proof-complexity».ExtensionOrder
namespace Programme.«20261104-1627-proof-complexity».OrdinaryRhoLowering
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261104-1627-proof-complexity».MatchingLabels
private theorem edge_eval (n : Nat) (M : Matching) (i j : Nat) (a : Nat → Bool) :
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
private theorem signed_sum (L : List Nat) (f : Nat → Int) :
    (L.map (fun x => -f x)).sum = -(L.map f).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp [ih, Int.neg_add]
theorem rho_rr_eval (m n : Nat) (N : Matching) (i j : Nat) (a : Nat → Bool) :
    (rho n (rr n N i j)).eval a =
      (relation m n ⟨N,true,j⟩).eval a - (relation m n ⟨N,true,i⟩).eval a := by
  simp only [rr, rho, Poly.eval, List.map_append, List.sum_append, List.map_map,
    Function.comp_def, Int.one_mul, Int.neg_one_mul]
  simp only [edge_eval]
  rw [signed_sum]
  simp [relation, Poly.sub, Int.neg_add, topLabel, Poly.eval, List.map_map, Function.comp_def, Int.sub_eq_add_neg,
    Int.add_assoc, Int.add_comm, Int.add_left_comm]
  omega
theorem rho_cc_eval (m n : Nat) (N : Matching) (i j : Nat) (a : Nat → Bool) :
    (rho n (cc m N i j)).eval a =
      (relation m n ⟨N,false,j⟩).eval a - (relation m n ⟨N,false,i⟩).eval a := by
  simp only [cc, rho, Poly.eval, List.map_append, List.sum_append, List.map_map,
    Function.comp_def, Int.one_mul, Int.neg_one_mul]
  simp only [edge_eval]
  rw [signed_sum]
  simp [relation, Poly.sub, Int.neg_add, topLabel, Poly.eval, List.map_map, Function.comp_def, Int.sub_eq_add_neg,
    Int.add_assoc, Int.add_comm, Int.add_left_comm]
  omega
theorem rr_lowering {p n k i j : Nat} (N : Matching)
    (hi : i < n+k) (hj : j < n+k)
    (fi : ∀ e ∈ N, e.1 ≠ i) (fj : ∀ e ∈ N, e.1 ≠ j)
    (hb : ∀ e ∈ N, e.1 < n+k) :
    NSIn p (ontoFPHP n k) (N.length+1) (rho n (rr n N i j)).eval := by
  apply nsIn_congr (nsIn_lin 1 (-1)
    (Programme.«20261104-1627-proof-complexity».RowRelationCertificate.row_relation_nsIn N hj fj hb)
    (Programme.«20261104-1627-proof-complexity».RowRelationCertificate.row_relation_nsIn N hi fi hb))
  intro a
  rw [rho_rr_eval (n+k)]
  simp [Int.sub_eq_add_neg]
theorem cc_lowering {p n k i j : Nat} (N : Matching)
    (hi : i < n) (hj : j < n)
    (fi : ∀ e ∈ N, e.2 ≠ i) (fj : ∀ e ∈ N, e.2 ≠ j)
    (hb : ∀ e ∈ N, e.2 < n) :
    NSIn p (ontoFPHP n k) (N.length+1) (rho n (cc (n+k) N i j)).eval := by
  apply nsIn_congr (nsIn_lin 1 (-1)
    (Programme.«20261104-1627-proof-complexity».ColumnRelationCertificate.column_relation_nsIn N hj fj hb)
    (Programme.«20261104-1627-proof-complexity».ColumnRelationCertificate.column_relation_nsIn N hi fi hb))
  intro a
  rw [rho_cc_eval]
  simp [Int.sub_eq_add_neg]
#print axioms rr_lowering
#print axioms cc_lowering
end Programme.«20261104-1627-proof-complexity».OrdinaryRhoLowering
