import Programme.«20261025-1627-proof-complexity».OntoF2K4
import Programme.«20261025-1627-proof-complexity».OntoF3K9
import Programme.«20261025-0459-proof-complexity».OntoDeg1Lower

/-!
# Razborov's Question 7 as a Lean statement

`Hard p l D`: for all large `n`, onto-FPHP^{n+p^l}_n has no degree-`D` PC refutation
(`PPCRefutation p`). `Q7 p`: for every `D` some level `l` is `Hard` at `D`, i.e. the eventual
PC degree of onto-FPHP^{n+p^l}_n over `Z/p` is unbounded in `l`.
Blow-up (`ontoFPHP_lift`, `c = p`) makes `Hard` monotone in `l`, so the eventual degree
is nondecreasing in `l`; the known levels are recorded below.
-/

namespace Programme.«20261025-1627-proof-complexity».OntoQ7

open Programme.«20261025-0459-proof-complexity».OntoFPHP

/-- For all `n ≥ N`, onto-FPHP^{n+p^l}_n has no degree-`D` refutation over `Z/p`. -/
def Hard (p l D : Nat) : Prop :=
  ∃ N, ∀ n, N ≤ n → ¬ PPCRefutation p (ontoFPHP n (p ^ l)) D

/-- Razborov's Question 7 (positive form): the eventual degree is unbounded in `l`. -/
def Q7 (p : Nat) : Prop := ∀ D, ∃ l, Hard p l D

theorem hard_succ {p l D : Nat} (hp : 0 < p) (hD : 1 ≤ D) (h : Hard p l D) : Hard p (l + 1) D := by
  obtain ⟨N, hN⟩ := h
  refine ⟨p * N, fun n hn => ?_⟩
  have := Programme.«20261025-0459-proof-complexity».OntoBlowup.ontoFPHP_lift p p N (p ^ l) D hp (Nat.pow_pos hp) hD
    (hN N (Nat.le_refl N)) n hn
  rwa [Nat.pow_succ, Nat.mul_comm]

theorem hard_mono_l {p l l' D : Nat} (hp : 0 < p) (hD : 1 ≤ D) (hl : l ≤ l') (h : Hard p l D) :
    Hard p l' D := by
  induction hl with
  | refl => exact h
  | step _ ih => exact hard_succ hp hD ih

theorem hard_mono_D {p l D D' : Nat} (hD : D' ≤ D) (h : Hard p l D) : Hard p l D' := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn h' => hN n hn (Programme.«20261025-0459-proof-complexity».OntoPCLower.PPCDerivable.mono hD h')⟩

theorem hard_deg1 {p : Nat} (hp : 1 < p) : Hard p 1 1 :=
  ⟨1, fun n hn => Programme.«20261025-0459-proof-complexity».OntoDeg1Lower.ontoFPHP_no_deg1 p n (p ^ 1) hp hn ⟨1, by simp⟩⟩

theorem f2_l1_not_hard : ¬ Hard 2 1 2 := fun ⟨N, hN⟩ =>
  hN (N + 1) (by omega) ((Programme.«20261025-0459-proof-complexity».OntoLucas.f2_k2_exact (N + 1) 2 (by omega)).2 (Nat.le_refl 2))

theorem f3_l1_not_hard : ¬ Hard 3 1 3 := fun ⟨N, hN⟩ =>
  hN (N + 3) (by omega) ((Programme.«20261025-0459-proof-complexity».OntoLucas.f3_k3_exact (N + 3) 3 (by omega)).2 (Nat.le_refl 3))

theorem f2_l2_hard : Hard 2 2 3 :=
  ⟨5, fun n hn => by simpa using Programme.«20261025-1627-proof-complexity».OntoF2K4.f2_deg4 1 n 3 (by decide) (by omega) (Nat.le_refl 3)⟩

theorem f3_l2_hard : Hard 3 2 3 :=
  ⟨5, fun n hn => by simpa using Programme.«20261025-1627-proof-complexity».OntoF3K9.f3_deg4 1 n 3 (by decide) (by omega) (Nat.le_refl 3)⟩

/-- Summary: `Hard` is monotone in `l` (for `p > 0`, `D ≥ 1`), and over `Z/2`, `Z/3` level 1
needs degree `p` while every level `l ≥ 2` needs degree `≥ 4`. -/
theorem q7_facts :
    (∀ p l l' D, 0 < p → 1 ≤ D → l ≤ l' → Hard p l D → Hard p l' D) ∧
    ¬ Hard 2 1 2 ∧ ¬ Hard 3 1 3 ∧ (∀ l, 2 ≤ l → Hard 2 l 3 ∧ Hard 3 l 3) :=
  ⟨fun _ _ _ _ hp hD hl h => hard_mono_l hp hD hl h, f2_l1_not_hard, f3_l1_not_hard,
   fun _ hl => ⟨hard_mono_l (by decide) (by decide) hl f2_l2_hard,
                hard_mono_l (by decide) (by decide) hl f3_l2_hard⟩⟩

end Programme.«20261025-1627-proof-complexity».OntoQ7

#print axioms Programme.«20261025-1627-proof-complexity».OntoQ7.q7_facts
