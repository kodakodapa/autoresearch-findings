import Programme.«20261102-1249-proof-complexity».UniformC3.SubsetCount

namespace Programme.«20261102-1249-proof-complexity».UniformC3
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin
open Programme.«20261026-1402-proof-complexity».SymDesign
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_zero)
open Programme.«20261027-0607-proof-complexity».Peel (IsPrime)
open Programme.«20261025-0459-proof-complexity».OntoLucas (bin)

def rowSelections (m n : Nat) : List (Selection m n) :=
  (chooseRows m n).attach.map fun ⟨A,hA⟩ =>
    ⟨A,(chooseRows_prop m n A hA).1,(chooseRows_prop m n A hA).2.1,
      (chooseRows_prop m n A hA).2.2⟩

theorem sum_congr_mod {α : Type} (L : List α) (f g : α → Int) (p : Int)
    (h : ∀ a ∈ L, p ∣ f a-g a) : p ∣ (L.map f).sum-(L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have hh := Int.dvd_add h1 h2
    simp only [List.map_cons, List.sum_cons]
    have e : ∀ a b c d : Int, a+b-(c+d) = (a-c)+(b-d) := by intros; omega
    rw [e]
    exact hh

theorem bal_zero (p n k e : Nat) : Bal p n k (fun _ => 0) (fun _ => 0) e := by
  intro g _ _
  constructor
  · intro i _ _
    have h : rowS n k (fun _ => 0) g i = 0 := by
      apply rsum_zero
      intro t _
      split <;> rfl
    simp [h]
  · intro j _ _
    have h : colS n k (fun _ => 0) g j = 0 := by
      apply rsum_zero
      intro t _
      split <;> rfl
    simp [h]

theorem bal_sum {α : Type} (L : List α) (f : α → List Nat → Int)
    {p n k e : Nat} (h : ∀ a ∈ L, Bal p n k (f a) (fun _ => 0) e) :
    Bal p n k (fun g => (L.map (fun a => f a g)).sum) (fun _ => 0) e := by
  induction L with
  | nil => exact bal_zero p n k e
  | cons a L ih =>
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simpa only [List.map_cons, List.sum_cons, Int.zero_add] using Bal_add h1 h2

theorem sum_indicator_cast {α : Type} (L : List α) (P : α → Prop) [DecidablePred P] :
    (L.map (fun a => if P a then (1 : Int) else 0)).sum =
      (((L.map (fun a => if P a then (1 : Nat) else 0)).sum : Nat) : Int) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    split <;> push_cast <;> omega

theorem selection_count (n k : Nat) (g : List Nat) :
    ((rowSelections (n+k) n).map (fun A => if A.contains g then (1 : Int) else 0)).sum =
      (coverCount (n+k) n (g.map (· / n)) : Int) := by
  unfold rowSelections
  simp only [List.map_map, Function.comp_def, Selection.contains]
  change ((chooseRows (n+k) n).attach.map (fun a => if ∀ v ∈ g, v/n ∈ a.val then (1 : Int) else 0)).sum = _
  rw [List.attach_map_val (f := fun A : List Nat => if ∀ v ∈ g, v/n ∈ A then (1 : Int) else 0)]
  rw [sum_indicator_cast]
  congr 1
  unfold coverCount
  congr 1
  apply List.map_congr_left
  intro A _
  have hiff : (∀ v ∈ g, v/n ∈ A) ↔ covers (g.map (· / n)) A := by
    simp [covers]
  simp only [hiff]

def transferred {p : Nat} (H : IntegralLift p) (k : Nat) (g : List Nat) : Int :=
  ((rowSelections (2*p-1+k) (2*p-1)).map (fun A => embed H A g)).sum

theorem transferred_congr_count {p k : Nat} (hp : 1 < p) (H : IntegralLift p)
    {g : List Nat} (hg : CM (2*p-1) k g) (hl : g.length = p) :
    (p : Int) ∣ transferred H k g - (bin (2*p-1+k-p) (p-1) : Int) := by
  have h := sum_congr_mod (rowSelections (2*p-1+k) (2*p-1))
    (fun A => embed H A g) (fun A => if A.contains g then 1 else 0) (p : Int)
    (fun A _ => embed_unit hp H A hg hl)
  rw [selection_count] at h
  have hb : ∀ x ∈ g.map (· / (2*p-1)), x < 2*p-1+k := by
    intro x hx
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (CM_lt hg hv)
  rw [coverCount_eq _ _ _ (match_nodup_div hg) hb, List.length_map, hl,
    if_pos (by omega : p ≤ 2*p-1), show 2*p-1-p = p-1 by omega] at h
  exact h

theorem transferred_harmonic {p k : Nat} (hp : 1 < p) (H : IntegralLift p) :
    Bal 0 (2*p-1) k (transferred H k) (fun _ => 0) (p-1) :=
  bal_sum _ _ (fun A _ => embed_harmonic hp H A)

/-- Steps 2 and 3: the sole input is the square-board integral lift. -/
def rectangleFromSquare {p : Nat} (hp : IsPrime p) (H : IntegralLift p) (c : Nat) :
    RectangularLift p (c*p*p) where
  coeff := transferred H (c*p*p)
  unit := by
    intro g hg hl
    have h1 := transferred_congr_count hp.1 H hg hl
    have h2 := subset_multiplicity_congr hp c
    have he : 2*p-1+c*p*p-p = c*p*p+p-1 := by have := hp.1; omega
    rw [he] at h1
    have h := Int.dvd_add h1 h2
    have ee : ∀ a b : Int, (a-b)+(b-1)=a-1 := by intros; omega
    rwa [ee] at h
  harmonic := by
    intro g hg hl
    have h := transferred_harmonic hp.1 H g hg hl
    constructor
    · intro i hi hf
      have hh := h.1 i hi hf
      simpa using hh
    · intro j hj hf
      have hh := h.2 j hj hf
      simpa using hh

#print axioms rectangleFromSquare
end Programme.«20261102-1249-proof-complexity».UniformC3
