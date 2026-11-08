import Peer.pr.FilteredLabels

namespace Work.ReproofK14
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC
open Peer.pr.MatchingLabels

theorem enc_inj {n i i' a b : Nat} (ha : a < n) (hb : b < n)
    (h : i * n + a = i' * n + b) : i = i' ∧ a = b := by
  rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
  · have : (i+1) * n ≤ i' * n := Nat.mul_le_mul_right n hlt
    rw [Nat.succ_mul] at this; omega
  · subst heq; omega
  · have : (i'+1) * n ≤ i * n := Nat.mul_le_mul_right n hgt
    rw [Nat.succ_mul] at this; omega

theorem cf_scale (a : Int) (L : List (Int × List Nat)) (u : List Nat) :
    cf (L.map fun b => (a*b.1,b.2)) u = a * cf L u := by
  induction L with
  | nil => simp [cf]
  | cons b L ih =>
    by_cases h : b.2.Perm u <;> simp [cf, h] at ih ⊢ <;> simp_all [Int.mul_add]

theorem perm1 (x y : Nat) : ([x] : List Nat).Perm [y] ↔ x = y := by
  constructor
  · intro h; simpa using List.singleton_perm.mp h
  · intro h; subst h; exact List.Perm.refl _

theorem cf_one (x y : Nat) : cf [((1 : Int), [x])] [y] = if x = y then 1 else 0 := by
  by_cases h : x = y <;> simp [cf, perm1, h]

/-- row label i' contributes to monomial (i,j) iff i' = i -/
theorem cf_row (n i' i j : Nat) (hj : j < n) : ∀ N, N ≤ n →
    cf ((List.range N).map fun j' => ((1 : Int), [i' * n + j'])) [i * n + j] =
      if i' = i ∧ j < N then 1 else 0 := by
  intro N
  induction N with
  | zero => intro _; simp [cf]
  | succ N ih =>
    intro hN
    rw [List.range_succ, List.map_append, cf_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil]
    rw [cf_one]
    have hiff : (i' * n + N = i * n + j) ↔ (i' = i ∧ N = j) :=
      ⟨fun h => by have := enc_inj (by omega) hj h; omega,
       fun ⟨a, b⟩ => by subst a; subst b; rfl⟩
    simp only [hiff]
    repeat' split
    all_goals omega

theorem cf_col (n j' i j : Nat) (hj : j' < n) (hjn : j < n) : ∀ M,
    cf ((List.range M).map fun i' => ((1 : Int), [i' * n + j'])) [i * n + j] =
      if j' = j ∧ i < M then 1 else 0 := by
  intro M
  induction M with
  | zero => simp [cf]
  | succ M ih =>
    rw [List.range_succ, List.map_append, cf_append, ih]
    simp only [List.map_cons, List.map_nil]
    rw [cf_one]
    have hiff : (M * n + j' = i * n + j) ↔ (M = i ∧ j' = j) :=
      ⟨fun h => by have := enc_inj hj hjn h; omega,
       fun ⟨a, b⟩ => by subst a; subst b; rfl⟩
    simp only [hiff]
    repeat' split
    all_goals omega

theorem labels_one (m n : Nat) : labels m n 1 =
    (List.range m).map (fun i => (⟨[], true, i⟩ : Label)) ++
    (List.range n).map (fun j => (⟨[], false, j⟩ : Label)) := by
  have hr : freeRow [] = fun _ => true := rfl
  have hc : freeCol [] = fun _ => true := rfl
  have hf (L : List Nat) : L.filter (fun _ => true) = L := List.filter_eq_self.mpr (by simp)
  simp [labels, matchings, rows, cols, hr, hc, hf]

theorem vc_cons (a : Int × Label) (v : Vector) (g : Label) :
    vectorCoeff (a :: v) g = (if a.2 = g then a.1 else 0) + vectorCoeff v g := by
  by_cases h : a.2 = g <;> simp [vectorCoeff, h]

theorem vc_append (v w : Vector) (g : Label) :
    vectorCoeff (v ++ w) g = vectorCoeff v g + vectorCoeff w g := by
  simp [vectorCoeff, List.filter_append]

theorem top_row (m n i : Nat) : (topLabel m n (⟨[], true, i⟩ : Label)).terms =
    (List.range n).map fun j => ((1 : Int), [i * n + j]) := by
  have hc : freeCol [] = fun _ => true := rfl
  have hf (L : List Nat) : L.filter (fun _ => true) = L := List.filter_eq_self.mpr (by simp)
  simp [topLabel, cols, hc, hf, mono]

theorem top_col (m n j : Nat) : (topLabel m n (⟨[], false, j⟩ : Label)).terms =
    (List.range m).map fun i => ((1 : Int), [i * n + j]) := by
  have hc : freeRow [] = fun _ => true := rfl
  have hf (L : List Nat) : L.filter (fun _ => true) = L := List.filter_eq_self.mpr (by simp)
  simp [topLabel, rows, hc, hf, mono]

/-- top coefficient at a single-edge monomial of a level-one vector -/
theorem top_one_coeff {m n : Nat} (v : Vector) (hv : valid m n 1 v) (i j : Nat)
    (hi : i < m) (hj : j < n) :
    coeff (top m n v) [i * n + j] =
      vectorCoeff v ⟨[], true, i⟩ + vectorCoeff v ⟨[], false, j⟩ := by
  induction v with
  | nil => simp [top, coeff, cf, vectorCoeff]
  | cons t v ih =>
    have hv' : valid m n 1 v := fun s hs => hv s (List.mem_cons_of_mem t hs)
    have ih := ih hv'
    have hT : top m n (t :: v) = ⟨((topLabel m n t.2).terms.map fun a => (t.1*a.1,a.2))
        ++ (top m n v).terms⟩ := by
      simp [top]
    have hc : coeff (top m n (t :: v)) [i * n + j] =
        t.1 * cf (topLabel m n t.2).terms [i * n + j] + coeff (top m n v) [i * n + j] := by
      rw [hT]; unfold coeff; simp only []; rw [cf_append, cf_scale]
    rw [hc, ih, vc_cons, vc_cons]
    have hg := hv t (by simp)
    rw [labels_one] at hg
    rcases List.mem_append.mp hg with h | h
    · obtain ⟨i', hi', hg⟩ := List.mem_map.mp h
      rw [← hg, top_row, cf_row n i' i j hj n (Nat.le_refl _)]
      by_cases h1 : i' = i <;> simp [h1, hj] <;> omega
    · obtain ⟨j', hj', hg⟩ := List.mem_map.mp h
      rw [← hg, top_col, cf_col n j' i j (List.mem_range.mp hj') hj m]
      by_cases h1 : j' = j <;> simp [h1, hi] <;> omega

theorem vc_zero {v : Vector} {g : Label} (h : ∀ t ∈ v, t.2 ≠ g) : vectorCoeff v g = 0 := by
  induction v with
  | nil => simp [vectorCoeff]
  | cons t v ih =>
    rw [vc_cons, ih (fun s hs => h s (List.mem_cons_of_mem t hs)), if_neg (h t (by simp))]; rfl

theorem vc_rows (a : Int) (i : Nat) : ∀ M,
    vectorCoeff ((List.range M).map fun i' => (a, (⟨[], true, i'⟩ : Label))) ⟨[], true, i⟩ =
      if i < M then a else 0 := by
  intro M
  induction M with
  | zero => simp [vectorCoeff]
  | succ M ih =>
    rw [List.range_succ, List.map_append, vc_append, ih]
    have e : vectorCoeff [(a, (⟨[], true, M⟩ : Label))] ⟨[], true, i⟩ =
        if M = i then a else 0 := by
      by_cases h : M = i <;> simp [vectorCoeff, h]
    simp only [List.map_cons, List.map_nil]
    rw [e]
    repeat' split
    all_goals omega

theorem vc_cols (a : Int) (j : Nat) : ∀ M,
    vectorCoeff ((List.range M).map fun i' => (a, (⟨[], false, i'⟩ : Label))) ⟨[], false, j⟩ =
      if j < M then a else 0 := by
  intro M
  induction M with
  | zero => simp [vectorCoeff]
  | succ M ih =>
    rw [List.range_succ, List.map_append, vc_append, ih]
    have e : vectorCoeff [(a, (⟨[], false, M⟩ : Label))] ⟨[], false, j⟩ =
        if M = j then a else 0 := by
      by_cases h : M = j <;> simp [vectorCoeff, h]
    simp only [List.map_cons, List.map_nil]
    rw [e]
    repeat' split
    all_goals omega

theorem z_one (m n : Nat) : z m n 1 [] =
    (List.range m).map (fun i => ((1 : Int), (⟨[], true, i⟩ : Label))) ++
    (List.range n).map (fun j => ((-1 : Int), (⟨[], false, j⟩ : Label))) := by
  have hr : freeRow [] = fun _ => true := rfl
  have hc : freeCol [] = fun _ => true := rfl
  have hf (L : List Nat) : L.filter (fun _ => true) = L := List.filter_eq_self.mpr (by simp)
  have ha (E : Matching) : (E.all fun _ => true) = true := by simp
  simp [z, matchings, rows, cols, hr, hc, hf, ordered, ha, List.filter_cons]

theorem spanning_one' (p m n : Nat) (hm : 0 < m) (hn : 0 < n) : Spanning p m n 1 := by
  intro v hk
  obtain ⟨hv, hker⟩ := hk
  let A : Nat → Int := fun i => vectorCoeff v ⟨[], true, i⟩
  let B : Nat → Int := fun j => vectorCoeff v ⟨[], false, j⟩
  have key : ∀ i j, i < m → j < n → (p : Int) ∣ A i + B j := by
    intro i j hi hj
    have h := hker [i * n + j]
    rw [top_one_coeff v hv i j hi hj] at h
    simpa [coeff, cf] using h
  refine ⟨[(A 0, z m n 1 [])], ?_, ?_⟩
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    simp [syzygies, matchings]
  · intro g
    have hcomb : combine [(A 0, z m n 1 [])] =
        (List.range m).map (fun i => (A 0, (⟨[], true, i⟩ : Label))) ++
        (List.range n).map (fun j => (-A 0, (⟨[], false, j⟩ : Label))) := by
      rw [z_one]; simp [combine, Function.comp_def]
    rw [hcomb]
    obtain ⟨b, r, k⟩ := g
    cases r
    · -- column labels
      by_cases hb : b = [] ∧ k < n
      · obtain ⟨rfl, hk⟩ := hb
        rw [vc_append, vc_cols (-A 0) k n]
        have hz : vectorCoeff ((List.range m).map fun i => (A 0, (⟨[], true, i⟩ : Label)))
            ⟨[], false, k⟩ = 0 := by
          apply vc_zero; intro t ht; obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht; simp
        rw [hz]
        have := key 0 k hm hk
        simp only [hk, if_true]
        change (p : Int) ∣ B k - (0 + -A 0)
        have e : B k - (0 + -A 0) = A 0 + B k := by omega
        rw [e]; exact this
      · have h1 : vectorCoeff v ⟨b, false, k⟩ = 0 := by
          apply vc_zero; intro t ht heq
          have hg := hv t ht
          rw [labels_one] at hg
          rw [heq] at hg
          rcases List.mem_append.mp hg with h | h
          · obtain ⟨i, _, h⟩ := List.mem_map.mp h; simp at h
          · obtain ⟨j, hj, h⟩ := List.mem_map.mp h
            simp at h; exact hb ⟨h.1, by rw [← h.2]; exact List.mem_range.mp hj⟩
        have h2 : vectorCoeff ((List.range m).map (fun i => (A 0, (⟨[], true, i⟩ : Label))) ++
            (List.range n).map (fun j => (-A 0, (⟨[], false, j⟩ : Label)))) ⟨b, false, k⟩ = 0 := by
          apply vc_zero; intro t ht heq
          rcases List.mem_append.mp ht with h | h
          · obtain ⟨i, _, rfl⟩ := List.mem_map.mp h; simp at heq
          · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
            simp at heq; exact hb ⟨heq.1, by rw [← heq.2]; exact List.mem_range.mp hj⟩
        rw [h1, h2]; simp
    · by_cases hb : b = [] ∧ k < m
      · obtain ⟨rfl, hk⟩ := hb
        rw [vc_append, vc_rows (A 0) k m]
        have hz : vectorCoeff ((List.range n).map fun j => (-A 0, (⟨[], false, j⟩ : Label)))
            ⟨[], true, k⟩ = 0 := by
          apply vc_zero; intro t ht; obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht; simp
        rw [hz]
        have h0 := key 0 0 hm hn
        have h1 := key k 0 hk hn
        simp only [hk, if_true]
        change (p : Int) ∣ A k - (A 0 + 0)
        have := Int.dvd_sub h1 h0
        rwa [show A k + B 0 - (A 0 + B 0) = A k - (A 0 + 0) by omega] at this
      · have h1 : vectorCoeff v ⟨b, true, k⟩ = 0 := by
          apply vc_zero; intro t ht heq
          have hg := hv t ht
          rw [labels_one] at hg
          rw [heq] at hg
          rcases List.mem_append.mp hg with h | h
          · obtain ⟨i, hi, h⟩ := List.mem_map.mp h
            simp at h; exact hb ⟨h.1, by rw [← h.2]; exact List.mem_range.mp hi⟩
          · obtain ⟨j, _, h⟩ := List.mem_map.mp h; simp at h
        have h2 : vectorCoeff ((List.range m).map (fun i => (A 0, (⟨[], true, i⟩ : Label))) ++
            (List.range n).map (fun j => (-A 0, (⟨[], false, j⟩ : Label)))) ⟨b, true, k⟩ = 0 := by
          apply vc_zero; intro t ht heq
          rcases List.mem_append.mp ht with h | h
          · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
            simp at heq; exact hb ⟨heq.1, by rw [← heq.2]; exact List.mem_range.mp hi⟩
          · obtain ⟨j, _, rfl⟩ := List.mem_map.mp h; simp at heq
        rw [h1, h2]; simp

theorem spanning_one {p m n : Nat} (hm : 0 < m) (hn : 0 < n) : Spanning p m n 1 :=
  spanning_one' p m n hm hn

end Work.ReproofK14
#print axioms Work.ReproofK14.spanning_one
