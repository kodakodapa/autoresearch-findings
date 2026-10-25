-- Rebased from th P252/P267; TernSymmetry proof by sk.
/- Verbatim copy of sk's Programme/Skeptic/TernSymmetry.lean (P225), used by th's TernClosure. -/
import Programme.«20261021-1639-ontological».Atlas.HenkinMinimal
/- D14 (th P218/P219) audit: the two premises of the Fraenkel–Mostowski closure argument for
`tern`, with the abelian group of coordinatewise Z/3 shifts (a subgroup of the tree
automorphisms in P219), filtered by the tail stabilisers K_n = {shifts vanishing below n}.
(1) `based3_iff_shifts`: a set of worlds is K_n-invariant iff it is `Based3 n`, so the symmetric
    sets at type w → o are exactly th's admitted carrier.
(2) `pos3_shift`: th's positivity `pos3` (recursive ternary majority) is invariant under EVERY
    shift, so the positivity constant is a symmetric parameter. R (universal) and actuality (⊤)
    are trivially invariant. -/
namespace Programme.«20261021-1639-ontological».Atlas.TernSymmetry
open Programme.«20261021-1639-ontological».Atlas.HenkinMinimal

def shift (m v : W3) : W3 := fun k => v k + m k

theorem shift_zero_below {m : W3} {n : Nat} (hm : ∀ k, k < n → m k = 0) (v : W3) :
    ∀ k, k < n → shift m v k = v k := fun k hk => by simp [shift, hm k hk]

theorem fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  rcases x with ⟨_ | _ | _ | n, h⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega

theorem based3_iff_shifts (n : Nat) (s : W3 → Prop) :
    Based3 n s ↔ ∀ m : W3, (∀ k, k < n → m k = 0) → ∀ v, s (shift m v) ↔ s v := by
  constructor
  · intro hb m hm v
    exact hb _ _ (shift_zero_below hm v)
  · intro h v v' hag
    have hm : ∀ k, k < n → (fun j => v' j - v j) k = 0 := fun k hk => by simp [hag k hk]
    have he : shift (fun j => v' j - v j) v = v' := by
      funext k; simp only [shift]
      rcases fin3_cases (v k) with h1 | h1 | h1 <;> rcases fin3_cases (v' k) with h2 | h2 | h2 <;>
        rw [h1, h2] <;> decide
    rw [← he]; exact (h _ hm v).symm

theorem maj3_perm (A B C : Prop) :
    (maj3 B C A ↔ maj3 A B C) ∧ (maj3 C A B ↔ maj3 A B C) := by
  unfold maj3
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp [hA, hB, hC]

theorem maj3_rot (f : Fin 3 → Prop) (c : Fin 3) :
    maj3 (f (0 + c)) (f (1 + c)) (f (2 + c)) ↔ maj3 (f 0) (f 1) (f 2) := by
  rcases fin3_cases c with rfl | rfl | rfl
  · exact Iff.rfl
  · rw [show (0 : Fin 3) + 1 = 1 by decide, show (1 : Fin 3) + 1 = 2 by decide,
      show (2 : Fin 3) + 1 = 0 by decide]
    exact (maj3_perm _ _ _).1
  · rw [show (0 : Fin 3) + 2 = 2 by decide, show (1 : Fin 3) + 2 = 0 by decide,
      show (2 : Fin 3) + 2 = 1 by decide]
    exact (maj3_perm _ _ _).2

theorem upd_shift (m v : W3) (d : Nat) (i : Fin 3) :
    shift m (upd v d i) = upd (shift m v) d (i + m d) := by
  funext k; by_cases h : k = d
  · subst h; simp [shift, upd]
  · simp [shift, upd, h]

/-- Recursive majority commutes with shifts. -/
theorem rm_shift (s : W3 → Prop) (m : W3) :
    ∀ k d v, rm k d (fun u => s (shift m u)) v ↔ rm k d s (shift m v) := by
  intro k
  induction k with
  | zero => intro d v; exact Iff.rfl
  | succ k ih =>
    intro d v
    show maj3 _ _ _ ↔ maj3 _ _ _
    rw [maj3_congr (ih _ _) (ih _ _) (ih _ _), upd_shift, upd_shift, upd_shift]
    exact maj3_rot (fun j => rm k (d + 1) s (upd (shift m v) d j)) (m d)

/-- At depth `d`, `rm k d s` only reads coordinates below `d` when `s` is `Based3 (d+k)`. -/
theorem rm_local (s : W3 → Prop) :
    ∀ k d v v', Based3 (d + k) s → (∀ j, j < d → v j = v' j) → (rm k d s v ↔ rm k d s v') := by
  intro k
  induction k with
  | zero => intro d v v' hb hag; exact hb v v' hag
  | succ k ih =>
    intro d v v' hb hag
    have hb' : Based3 (d + 1 + k) s := by
      have : d + 1 + k = d + (k + 1) := by omega
      rw [this]; exact hb
    have hc : ∀ i, rm k (d + 1) s (upd v d i) ↔ rm k (d + 1) s (upd v' d i) := fun i =>
      ih _ _ _ hb' fun j hj => by
        by_cases h : j = d
        · subst h; simp [upd]
        · simp [upd, h]; exact hag j (by omega)
    exact maj3_congr (hc 0) (hc 1) (hc 2)

/-- th's positivity is invariant under every shift (no stabiliser needed). -/
theorem pos3_shift (m : W3) (s : W3 → Prop) (n : Nat) (hb : Based3 n s) :
    pos3 (fun u => s (shift m u)) ↔ pos3 s := by
  have hb' : Based3 n (fun u => s (shift m u)) := fun v v' hag =>
    hb _ _ fun k hk => by simp [shift, hag k hk]
  rw [pos3_iff hb', pos3_iff hb, rm_shift]
  exact rm_local s n 0 _ _ (by rw [Nat.zero_add]; exact hb) (fun _ h => absurd h (Nat.not_lt_zero _))

#print axioms based3_iff_shifts
#print axioms rm_shift
#print axioms pos3_shift
end Programme.«20261021-1639-ontological».Atlas.TernSymmetry
