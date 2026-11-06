import Programme.«20261101-0614-proof-complexity».PairCode
namespace Programme.«20261101-0614-proof-complexity».Composition
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».RestrictionTarget
noncomputable def decode (q : Nat) : Nat × Nat := by
  classical
  exact if h : ∃ ab : Nat × Nat, pair ab.1 ab.2 = q then Classical.choose h else (0,0)
theorem decode_pair (a b : Nat) : decode (pair a b) = (a,b) := by
  classical
  have h : ∃ ab : Nat × Nat, pair ab.1 ab.2 = pair a b := ⟨(a,b),rfl⟩
  simp only [decode, dif_pos h]
  have he := pair_injective (Classical.choose_spec h)
  exact Prod.ext he.1 he.2

noncomputable def globalSub (M N : Nat) : Substitution := fun v =>
  let ab := decode v.2
  if v.1 = 0 then
    if ab.1 = M then .inl (ab.2 == N)
    else if ab.2 = N then .inl false else .inr v
  else if v.1 = 1 then
    if ab.1 = N then .inl ((decode ab.2).2 == 0) else .inr v
  else if v.1 = 2 then
    if ab.1 = N then .inl ((decode ab.2).2 == M)
    else if (decode ab.2).2 = M then .inl false
    else if M = 1 then .inl true else .inr v
  else .inr v

theorem global_spec (M N : Nat) : RestrictionSpec (globalSub M N) M N := by
  constructor
  · intro a y ha hy
    simp [globalSub, fVar, decode_pair, show a ≠ M by omega, show y ≠ N by omega]
  · intro y x z hy
    simp [globalSub, sVar, decode_pair, show y ≠ N by omega]
  · intro y x a hy ha
    simp [globalSub, gVar, decode_pair, show y ≠ N by omega, show a ≠ M by omega]
  · intro y x hy
    simp [globalSub, gVar, decode_pair, show y ≠ N by omega]
  · intro x a
    simp [globalSub, gVar, decode_pair]
  · simp [globalSub, fVar, decode_pair]

theorem global_extra (M N : Nat) :
    (∀ a, a < M → globalSub M N (fVar a N) = .inl false) ∧
    (∀ y, globalSub M N (fVar M y) = .inl (y == N)) ∧
    (∀ x z, globalSub M N (sVar N x z) = .inl (z == 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    simp [globalSub, fVar, decode_pair, show a ≠ M by omega]
  · intro y
    simp [globalSub, fVar, decode_pair]
  · intro x z
    simp [globalSub, sVar, decode_pair]
#print axioms global_spec
#print axioms global_extra
end Programme.«20261101-0614-proof-complexity».Composition
