/-!
# Counting k-subsets: the positive side of the approximation method

`ksub V k` lists the `k`-element sublists of `V` (for duplicate-free `V`: the `k`-subsets);
`ksub_length`: there are `ch |V| k` of them (`ch` is Pascal's binomial coefficient).

`contain_count`: for duplicate-free `T ⊆ V` with `|T| ≤ k`, exactly `ch (|V|-|T|) (k-|T|)` of them
contain `T`. `pos_count`: if every set in `Ts` is duplicate-free, inside `V` and has `≥ ℓ+1`
elements, and `ℓ+1 ≤ k`, at most `|Ts| · ch (|V|-ℓ-1) (k-ℓ-1)` of the `k`-subsets contain some
member of `Ts` (the trim error on the positive test graphs).
-/

namespace Programme.«20261024-1633-proof-complexity».KSub

def ch : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _+1 => 0
  | n+1, k+1 => ch n (k+1) + ch n k

def ksub : List Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | [], _+1 => []
  | x :: V, k+1 => ksub V (k+1) ++ (ksub V k).map (x :: ·)

theorem ksub_length (V : List Nat) (k : Nat) : (ksub V k).length = ch V.length k := by
  induction V generalizing k with
  | nil => cases k <;> rfl
  | cons x V ih =>
    cases k with
    | zero => rfl
    | succ k => simp [ksub, ch, ih]

theorem mem_ksub {V : List Nat} {k : Nat} {K : List Nat} (h : K ∈ ksub V k) :
    K.Sublist V ∧ K.length = k := by
  induction V generalizing k K with
  | nil =>
    cases k with
    | zero => simp [ksub] at h; subst h; simp
    | succ k => simp [ksub] at h
  | cons x V ih =>
    cases k with
    | zero => simp [ksub] at h; subst h; simp
    | succ k =>
      simp only [ksub, List.mem_append, List.mem_map] at h
      rcases h with h | ⟨K', hK', rfl⟩
      · exact ⟨(ih h).1.cons x, (ih h).2⟩
      · exact ⟨(ih hK').1.cons_cons x, by simp [(ih hK').2]⟩

/-- `T ⊆ K` as a Boolean test. -/
def sub (T K : List Nat) : Bool := T.all fun i => decide (i ∈ K)

theorem sub_iff {T K : List Nat} : sub T K = true ↔ ∀ i ∈ T, i ∈ K := by simp [sub]

def cnt (V : List Nat) (k : Nat) (T : List Nat) : Nat := ((ksub V k).filter (sub T)).length

theorem len_le_of_sub {T V : List Nat} (hT : T.Nodup) (h : ∀ i ∈ T, i ∈ V) :
    T.length ≤ V.length := by
  induction T generalizing V with
  | nil => simp
  | cons a T ih =>
    have ha := h a (by simp)
    have hT' := List.nodup_cons.1 hT
    have h' : ∀ i ∈ T, i ∈ V.erase a := fun i hi =>
      (List.mem_erase_of_ne (fun (e : i = a) => hT'.1 (e ▸ hi))).2 (h i (by simp [hi]))
    have := ih hT'.2 h'
    rw [List.length_erase_of_mem ha] at this
    have := List.length_pos_of_mem ha
    simp; omega

theorem filter_zero {l : List (List Nat)} {p : List Nat → Bool} (h : ∀ K ∈ l, p K = false) :
    (l.filter p).length = 0 := by
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]; intro K hK; simp [h K hK]

theorem contain_count (V : List Nat) (hV : V.Nodup) (k : Nat) (T : List Nat) (hT : T.Nodup)
    (hTV : ∀ i ∈ T, i ∈ V) (hk : T.length ≤ k) :
    cnt V k T = ch (V.length - T.length) (k - T.length) := by
  induction V generalizing k T with
  | nil =>
    have : T = [] := by
      cases T with
      | nil => rfl
      | cons a T => exact absurd (hTV a (by simp)) (by simp)
    subst this
    cases k <;> rfl
  | cons x V ih =>
    have hxV : x ∉ V := (List.nodup_cons.1 hV).1
    have hV' : V.Nodup := (List.nodup_cons.1 hV).2
    cases k with
    | zero =>
      have : T = [] := List.length_eq_zero_iff.1 (by omega)
      subst this; rfl
    | succ k =>
      unfold cnt
      simp only [ksub, List.filter_append, List.length_append, List.filter_map, List.length_map]
      by_cases hx : x ∈ T
      · -- first part: no `K ⊆ V` contains `x`
        have h1 : ((ksub V (k+1)).filter (sub T)).length = 0 := by
          apply filter_zero; intro K hK
          cases hs : sub T K with
          | false => rfl
          | true => exact absurd ((mem_ksub hK).1.subset (sub_iff.1 hs x hx)) hxV
        have hcongr : ((ksub V k).filter (sub T ∘ (x :: ·))) = (ksub V k).filter (sub (T.erase x)) := by
          apply List.filter_congr; intro K _
          apply Bool.eq_iff_iff.2
          simp only [Function.comp_apply, sub_iff, List.mem_cons]
          constructor
          · intro h i hi
            have hi' := (List.Nodup.mem_erase_iff hT).1 hi
            rcases h i hi'.2 with h | h
            · exact absurd h hi'.1
            · exact h
          · intro h i hi
            by_cases hix : i = x
            · exact Or.inl hix
            · exact Or.inr (h i ((List.Nodup.mem_erase_iff hT).2 ⟨hix, hi⟩))
        have hlen : (T.erase x).length = T.length - 1 := List.length_erase_of_mem hx
        have hpos : 1 ≤ T.length := List.length_pos_of_mem hx
        have hsub : ∀ i ∈ T.erase x, i ∈ V := by
          intro i hi
          have hi' := (List.Nodup.mem_erase_iff hT).1 hi
          rcases List.mem_cons.1 (hTV i hi'.2) with h | h
          · exact absurd h hi'.1
          · exact h
        have := ih hV' k (T.erase x) (hT.erase x) hsub (by omega)
        unfold cnt at this
        rw [h1, hcongr, this, hlen]
        have e1 : V.length - (T.length - 1) = (x :: V).length - T.length := by simp; omega
        have e2 : k - (T.length - 1) = k + 1 - T.length := by omega
        rw [e1, e2]; omega
      · have hsub : ∀ i ∈ T, i ∈ V := by
          intro i hi
          rcases List.mem_cons.1 (hTV i hi) with h | h
          · exact absurd (h ▸ hi) hx
          · exact h
        have hcongr : ((ksub V k).filter (sub T ∘ (x :: ·))) = (ksub V k).filter (sub T) := by
          apply List.filter_congr; intro K _
          apply Bool.eq_iff_iff.2
          simp only [Function.comp_apply, sub_iff, List.mem_cons]
          constructor
          · intro h i hi
            rcases h i hi with h | h
            · exact absurd (h ▸ hi) hx
            · exact h
          · intro h i hi; exact Or.inr (h i hi)
        have hA := ih hV' (k+1) T hT hsub hk
        unfold cnt at hA
        rw [hcongr, hA]
        have htn := len_le_of_sub hT hsub
        by_cases hkt : T.length ≤ k
        · have hB := ih hV' k T hT hsub hkt
          unfold cnt at hB
          rw [hB]
          have e1 : (x :: V).length - T.length = (V.length - T.length) + 1 := by simp; omega
          have e2 : k + 1 - T.length = (k - T.length) + 1 := by omega
          rw [e1, e2]; simp [ch]
        · have hB : ((ksub V k).filter (sub T)).length = 0 := by
            apply filter_zero; intro K hK
            cases hs : sub T K with
            | false => rfl
            | true =>
              have := len_le_of_sub hT (sub_iff.1 hs)
              rw [(mem_ksub hK).2] at this; omega
          rw [hB]
          have e2 : k + 1 - T.length = 0 := by omega
          rw [e2]; cases (x :: V).length - T.length <;> cases V.length - T.length <;> rfl

theorem filter_mono {l : List (List Nat)} {p q : List Nat → Bool}
    (h : ∀ K ∈ l, p K = true → q K = true) : (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun K hK => h K (List.mem_cons_of_mem a hK))
    simp only [List.filter_cons]
    cases hp : p a <;> cases hq : q a
    · simpa using ih'
    · simp; omega
    · exact absurd (h a (by simp) hp) (by simp [hq])
    · simpa using ih'

/-- Union bound: positives containing some long member of `Ts`. -/
theorem pos_count (V : List Nat) (hV : V.Nodup) (k ℓ : Nat) (Ts : List (List Nat))
    (hTs : ∀ T ∈ Ts, T.Nodup ∧ (∀ i ∈ T, i ∈ V) ∧ ℓ + 1 ≤ T.length) (hk : ℓ + 1 ≤ k) :
    ((ksub V k).filter (fun K => Ts.any fun T => sub T K)).length
      ≤ Ts.length * ch (V.length - (ℓ + 1)) (k - (ℓ + 1)) := by
  induction Ts with
  | nil => simp
  | cons T Ts ih =>
    obtain ⟨hn, hs, hl⟩ := hTs T (by simp)
    have ih' := ih (fun T' h => hTs T' (List.mem_cons_of_mem T h))
    have htake : cnt V k (T.take (ℓ+1)) = ch (V.length - (ℓ + 1)) (k - (ℓ + 1)) := by
      have hlen : (T.take (ℓ+1)).length = ℓ + 1 := by simp; omega
      rw [contain_count V hV k _ (hn.sublist (List.take_sublist _ _))
        (fun i hi => hs i (List.mem_of_mem_take hi)) (by omega), hlen]
    have hsplit : ((ksub V k).filter (fun K => (T :: Ts).any fun T => sub T K)).length
        ≤ ((ksub V k).filter (sub T)).length
          + ((ksub V k).filter (fun K => Ts.any fun T => sub T K)).length := by
      generalize ksub V k = l
      induction l with
      | nil => simp
      | cons a l ih2 =>
        simp only [List.filter_cons, List.any_cons] at ih2 ⊢
        cases h1 : sub T a <;> cases h2 : Ts.any (fun T => sub T a) <;> simp <;> omega
    have hmono : ((ksub V k).filter (sub T)).length ≤ cnt V k (T.take (ℓ+1)) := by
      apply filter_mono; intro K _ h
      exact sub_iff.2 fun i hi => sub_iff.1 h i (List.mem_of_mem_take hi)
    rw [htake] at hmono
    simp only [List.length_cons, Nat.succ_mul]
    omega

-- sanity: C(7,3) = 35 subsets, 5 contain {0,1}
example : ch 7 3 = 35 := by decide
example : cnt (List.range 7) 3 [0, 1] = 5 := by decide

end Programme.«20261024-1633-proof-complexity».KSub

#print axioms Programme.«20261024-1633-proof-complexity».KSub.contain_count
#print axioms Programme.«20261024-1633-proof-complexity».KSub.pos_count
#print axioms Programme.«20261024-1633-proof-complexity».KSub.ksub_length
