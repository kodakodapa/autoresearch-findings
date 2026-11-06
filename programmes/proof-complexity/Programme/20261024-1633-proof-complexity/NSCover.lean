import Programme.«20261024-1633-proof-complexity».NSLocal
import Programme.«20261024-1633-proof-complexity».NSTseitin

/-!
# Nullstellensatz refutations from local covers

`cover_ns`: suppose there are "centres" `v < n`, each with a variable list `W v` and an integer
function `ψ v` of the assignment depending only on `W v`, such that
* `∑_v ψ_v ≡ 1 (mod p)` on every Boolean assignment, and
* `p ∣ ψ_v(a)` whenever `a` satisfies every clause of `F` whose variables all lie in `W v`.
Then `F` has a Nullstellensatz refutation over `Z/p` of degree `max (|W v| + |C|)` over the
clauses `C` local to `W v`. The multiplier of clause `i` is `∑_v ψ_v · [i is the first falsified
clause local to W v]`, a local function, turned into a polynomial by `Work.NSLocal.local_ns_sum`.
-/

namespace Programme.«20261024-1633-proof-complexity».NSCover

open Classical Programme.«20261024-1110-proof-complexity».Haken
open Programme.«20261024-1633-proof-complexity».NS Programme.«20261024-1633-proof-complexity».NSLocal
open Programme.«20261024-1633-proof-complexity».NSTseitin (clause_eval_congr)

/-- Clause `i` of `F` is local to `W`: all its variables lie in `W`. -/
def Loc (F : CNF Nat) (W : List Nat) (i : Nat) : Bool :=
  (F.getD i []).all fun l => decide (l.var ∈ W)

/-- The first clause local to `W` falsified by `a`. -/
def first (F : CNF Nat) (W : List Nat) (a : Nat → Bool) : Option Nat :=
  (List.range F.length).find? fun j => Loc F W j && !Clause.eval a (F.getD j [])

theorem first_congr (F : CNF Nat) (W : List Nat) (a b : Nat → Bool) (h : ∀ x ∈ W, a x = b x) :
    first F W a = first F W b := by
  unfold first
  congr 1
  funext j
  by_cases hl : Loc F W j = true
  · rw [clause_eval_congr a b _ (fun l hl' => h _ (by
      unfold Loc at hl; exact of_decide_eq_true (List.all_eq_true.mp hl l hl')))]
  · simp [hl]

theorem sum_zero (l : List Nat) : (l.map fun _ => (0 : Int)).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; rfl

theorem sum_swap (l1 l2 : List Nat) (g : Nat → Nat → Int) :
    (l1.map fun i => (l2.map fun v => g v i).sum).sum =
      (l2.map fun v => (l1.map fun i => g v i).sum).sum := by
  induction l1 with
  | nil => simp only [List.map_nil, List.sum_nil]; exact (sum_zero l2).symm
  | cons x l1 ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    clear ih
    induction l2 with
    | nil => simp
    | cons y l2 ih2 => simp only [List.map_cons, List.sum_cons]; omega

theorem sum_single (N i0 : Nat) (hi : i0 < N) (f : Nat → Int) :
    ((List.range N).map fun i => if i = i0 then f i else 0).sum = f i0 := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases h : i0 = N
    · subst h
      have : ((List.range i0).map fun i => if i = i0 then f i else 0).sum = 0 := by
        rw [List.map_congr_left (g := fun _ => (0 : Int)) (fun i hi =>
          by rw [ite_eq_right (Nat.ne_of_lt (List.mem_range.mp hi))])]
        exact sum_zero _
      simp [this]
    · rw [ih (by omega)]; simp [Ne.symm h]

theorem dvd_sum_sub (l : List Nat) (p : Int) (f g : Nat → Int) (h : ∀ v ∈ l, p ∣ f v - g v) :
    p ∣ (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h x List.mem_cons_self
    have h2 := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    have : f x + (l.map f).sum - (g x + (l.map g).sum) =
        (f x - g x) + ((l.map f).sum - (l.map g).sum) := by omega
    rw [this]; exact Int.dvd_add h1 h2

theorem cover_ns (p n D : Nat) (F : CNF Nat) (W : Nat → List Nat)
    (ψ : Nat → (Nat → Bool) → Int)
    (hloc : ∀ v, v < n → ∀ a b : Nat → Bool, (∀ x ∈ W v, a x = b x) → ψ v a = ψ v b)
    (hzero : ∀ v, v < n → ∀ a : Nat → Bool,
      (∀ C ∈ F, (∀ l ∈ C, l.var ∈ W v) → Clause.eval a C = true) → (p : Int) ∣ ψ v a)
    (hsum : ∀ a : Nat → Bool, ((List.range n).map fun v => ψ v a).sum % (p : Int) = 1 % (p : Int))
    (hdeg : ∀ v, v < n → ∀ C ∈ F, (∀ l ∈ C, l.var ∈ W v) → (W v).length + C.length ≤ D)
    (hwid : ∀ C ∈ F, C.length ≤ D) :
    Nonempty (NSRefutation p F D) := by
  have hget : ∀ i, i < F.length → F.getD i [] ∈ F := by
    intro i hi; simp [List.getD, List.getElem?_eq_getElem hi]
  have hLoc : ∀ v i, Loc F (W v) i = true → ∀ l ∈ F.getD i [], l.var ∈ W v := by
    intro v i h l hl; unfold Loc at h; exact of_decide_eq_true (List.all_eq_true.mp h l hl)
  let term : Nat → Nat → (Nat → Bool) → Int := fun v i a =>
    if Loc F (W v) i = true ∧ first F (W v) a = some i then ψ v a else 0
  apply local_ns_sum p F D (fun i => (List.range n).map fun v =>
    (if Loc F (W v) i then W v else [], term v i))
  · intro i hi t ht a b h1 _
    simp only [List.mem_map, List.mem_range] at ht
    obtain ⟨v, hv, rfl⟩ := ht
    simp only [term]
    by_cases hl : Loc F (W v) i = true
    · simp only [hl, ite_true] at h1
      rw [first_congr F (W v) a b h1, hloc v hv a b h1]
    · simp [hl]
  · intro i hi t ht
    simp only [List.mem_map, List.mem_range] at ht
    obtain ⟨v, hv, rfl⟩ := ht
    by_cases hl : Loc F (W v) i = true
    · simp only [hl, ite_true]
      exact hdeg v hv _ (hget i hi) (hLoc v i hl)
    · simp only [hl]; simpa using hwid _ (hget i hi)
  · intro i hi; exact hwid _ (hget i hi)
  · intro a
    rw [← hsum a]
    simp only [List.map_map, Function.comp_def]
    have e1 : ((List.range F.length).map fun i =>
        ((List.range n).map fun v => term v i a).sum * (clausePoly (F.getD i [])).eval a).sum
        = ((List.range n).map fun v => ((List.range F.length).map fun i =>
            term v i a * (clausePoly (F.getD i [])).eval a).sum).sum := by
      rw [← sum_swap]
      congr 1; apply List.map_congr_left; intro i _
      generalize (clausePoly (F.getD i [])).eval a = x
      induction (List.range n) with
      | nil => simp
      | cons y l ih => simp only [List.map_cons, List.sum_cons, Int.add_mul, ih]
    rw [e1]
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    apply dvd_sum_sub
    intro v hv
    have hv := List.mem_range.mp hv
    cases hf : first F (W v) a with
    | some i0 =>
      have hmem := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
      have hi0 := List.mem_range.mp hmem
      have : ((List.range F.length).map fun i => term v i a * (clausePoly (F.getD i [])).eval a)
          = (List.range F.length).map fun i =>
            if i = i0 then ψ v a * (clausePoly (F.getD i [])).eval a else 0 := by
        apply List.map_congr_left; intro i _
        simp only [term, hf, Option.some.injEq]
        by_cases h : i = i0
        · subst h; simp [hp.1]
        · rw [ite_eq_right (fun h' => h h'.2.symm), ite_eq_right h, Int.zero_mul]
      rw [this, sum_single _ _ hi0, clausePoly_eval, hp.2]
      simp
    | none =>
      have hz : (p : Int) ∣ ψ v a := by
        apply hzero v hv a
        intro C hC hW
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hC
        have hn := List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
        have hl : Loc F (W v) i = true := by
          unfold Loc; apply List.all_eq_true.mpr
          intro l hl; apply decide_eq_true
          exact hW l (by simpa [List.getD, List.getElem?_eq_getElem hi] using hl)
        have e : F.getD i [] = F[i] := by simp [List.getD, List.getElem?_eq_getElem hi]
        rw [hl, e] at hn
        simpa using hn
      have : ((List.range F.length).map fun i => term v i a * (clausePoly (F.getD i [])).eval a)
          = (List.range F.length).map fun _ => (0 : Int) := by
        apply List.map_congr_left; intro i _; simp [term, hf]
      rw [this, sum_zero]
      obtain ⟨k, hk⟩ := hz
      exact ⟨-k, by rw [hk, Int.mul_neg]; omega⟩

end Programme.«20261024-1633-proof-complexity».NSCover

#print axioms Programme.«20261024-1633-proof-complexity».NSCover.cover_ns
