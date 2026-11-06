import Programme.«20261025-0459b-proof-complexity».VSwitch
import Programme.«20261024-1633-proof-complexity».CCApprox

/-!
# Approximating monotone real formulas without a weight bound

`vapprox`: every monotone integer formula `RC P f t` whose inputs have good approximators has an
approximator (entries `(S, v)`, `|S| ≤ 2L`) with at most `t (16L²)^L` rise events (merge lists
with `L` merges) and `t (4L²)^L` drop events (sets of `≥ L` vertices) such that
* (I+) on every `K` not containing a drop event, some entry `S ⊆ K` has `f (emb (posG K)) ≤ v`;
* (I−) on every colouring `c` fitting no rise event, every rainbow entry has `v ≤ f (emb (negG c))`.
Each binary gate takes the pairwise product of its children's entries and applies
`Work.VSwitch.vswitch` with `s = b = L`, `d = 4L`. No bound on the values is used.

`cc_vapprox`: the instance for clique–colouring via `CliqueColour.cc_interp`.
-/

namespace Programme.«20261025-0459b-proof-complexity».VApprox

open Programme.«20261025-0459b-proof-complexity».VSwitch
open Programme.«20261024-1633-proof-complexity».CPInterp
open Programme.«20261024-1633-proof-complexity».CP (val)
open Programme.«20261024-1633-proof-complexity».RealApprox (posG negG)

/-- Pairwise product of two approximators under a binary gate. -/
def prod (φ : Int → Int → Int) (A B : List (List Nat × Int)) : List (List Nat × Int) :=
  A.flatMap fun e₁ => B.map fun e₂ => (e₁.1 ++ e₂.1, φ e₁.2 e₂.2)

theorem mem_prod {φ : Int → Int → Int} {A B : List (List Nat × Int)} {e : List Nat × Int}
    (he : e ∈ prod φ A B) : ∃ e₁ ∈ A, ∃ e₂ ∈ B, e = (e₁.1 ++ e₂.1, φ e₁.2 e₂.2) := by
  unfold prod at he
  obtain ⟨e₁, h₁, he⟩ := List.mem_flatMap.1 he
  obtain ⟨e₂, h₂, rfl⟩ := List.mem_map.1 he
  exact ⟨e₁, h₁, e₂, h₂, rfl⟩

theorem prod_mem {φ : Int → Int → Int} {A B : List (List Nat × Int)} {e₁ e₂ : List Nat × Int}
    (h₁ : e₁ ∈ A) (h₂ : e₂ ∈ B) : (e₁.1 ++ e₂.1, φ e₁.2 e₂.2) ∈ prod φ A B :=
  List.mem_flatMap.2 ⟨e₁, h₁, List.mem_map.2 ⟨e₂, h₂, rfl⟩⟩

theorem rb_left {c : Nat → Nat} {S T : List Nat} (h : rb c (S ++ T)) : rb c S :=
  fun a ha b hb hab => h a (List.mem_append_left _ ha) b (List.mem_append_left _ hb) hab

theorem rb_right {c : Nat → Nat} {S T : List Nat} (h : rb c (S ++ T)) : rb c T :=
  fun a ha b hb hab => h a (List.mem_append_right _ ha) b (List.mem_append_right _ hb) hab

/-- The approximation invariant for a function `f` with event lists `Er`, `Ed`. -/
def Good {V : Type} (emb : (Nat → Nat → Bool) → V → Bool) (m L : Nat) (f : (V → Bool) → Int)
    (A : List (List Nat × Int)) (Er : List (List (Nat × Nat))) (Ed : List (List Nat)) : Prop :=
  (∀ e ∈ A, e.1.Nodup ∧ e.1.length ≤ 2 * L ∧ ∀ x ∈ e.1, x < m) ∧
  (∀ τ ∈ Er, Valid τ ∧ (∀ e ∈ τ, e.1 < m ∧ e.2 < m) ∧ τ.length = L) ∧
  (∀ R ∈ Ed, R.Nodup ∧ L ≤ R.length ∧ ∀ x ∈ R, x < m) ∧
  (∀ K : List Nat, (∃ e ∈ A, f (emb (posG K)) ≤ e.2 ∧ ∀ x ∈ e.1, x ∈ K) ∨
    ∃ R ∈ Ed, ∀ x ∈ R, x ∈ K) ∧
  (∀ c : Nat → Nat, (∀ e ∈ A, rb c e.1 → e.2 ≤ f (emb (negG c))) ∨ ∃ τ ∈ Er, cons c τ)

theorem vapprox {V : Type} (P : V → Bool) (m L : Nat)
    (emb : (Nat → Nat → Bool) → V → Bool) (inA : V → List (List Nat × Int))
    (hin : ∀ u, P u = true → Good emb m L (fun β => val β u) (inA u) [] []) :
    ∀ {f : (V → Bool) → Int} {t : Nat}, RC P f t →
    ∃ A Er Ed, Er.length ≤ t * (4 * L * (4 * L)) ^ L ∧ Ed.length ≤ t * (4 * L * L) ^ L ∧
      Good emb m L f A Er Ed := by
  intro f t hf
  induction hf with
  | const k =>
    refine ⟨[([], k)], [], [], by simp, by simp, ?_, by simp, by simp, ?_, ?_⟩
    · intro e he; rw [List.mem_singleton] at he; subst he; simp
    · intro K; exact Or.inl ⟨([], k), List.mem_singleton_self _, Int.le_refl _, by simp⟩
    · intro c; left; intro e he _; rw [List.mem_singleton] at he; subst he; exact Int.le_refl _
  | inp u hu => exact ⟨inA u, [], [], by simp, by simp, hin u hu⟩
  | @gate1 f s g hg _ ih =>
    obtain ⟨A, Er, Ed, hEr, hEd, h1, h2, h3, h4, h5⟩ := ih
    refine ⟨A.map fun e => (e.1, g e.2), Er, Ed, ?_, ?_, ?_, h2, h3, ?_, ?_⟩
    · exact Nat.le_trans hEr (Nat.mul_le_mul_right _ (by omega))
    · exact Nat.le_trans hEd (Nat.mul_le_mul_right _ (by omega))
    · intro e he; obtain ⟨e', he', rfl⟩ := List.mem_map.1 he; exact h1 e' he'
    · intro K
      rcases h4 K with ⟨e, he, hle, hK⟩ | h
      · exact Or.inl ⟨(e.1, g e.2), List.mem_map.2 ⟨e, he, rfl⟩, hg _ _ hle, hK⟩
      · exact Or.inr h
    · intro c
      rcases h5 c with h | h
      · left; intro e he hr
        obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
        exact hg _ _ (h e' he' hr)
      · exact Or.inr h
  | @gate2 f h s t g hg _ _ ih1 ih2 =>
    obtain ⟨A₁, Er₁, Ed₁, hEr₁, hEd₁, a1, a2, a3, a4, a5⟩ := ih1
    obtain ⟨A₂, Er₂, Ed₂, hEr₂, hEd₂, b1, b2, b3, b4, b5⟩ := ih2
    have hPr : ∀ e ∈ prod g A₁ A₂, e.1.length ≤ 4 * L ∧ ∀ x ∈ e.1, x < m := by
      intro e he
      obtain ⟨e₁, h₁, e₂, h₂, rfl⟩ := mem_prod he
      refine ⟨?_, ?_⟩
      · simp only [List.length_append]; have := (a1 e₁ h₁).2.1; have := (b1 e₂ h₂).2.1; omega
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact (a1 e₁ h₁).2.2 x hx
        · exact (b1 e₂ h₂).2.2 x hx
    obtain ⟨D, Er', Ed', _, hD, hEr', hEr'p, hEd', hEd'p, hpos, hneg⟩ :=
      vswitch m L L (4 * L) (prod g A₁ A₂) hPr
    refine ⟨D, Er₁ ++ Er₂ ++ Er', Ed₁ ++ Ed₂ ++ Ed', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, Nat.add_mul, Nat.one_mul]; omega
    · simp only [List.length_append, Nat.add_mul, Nat.one_mul]; omega
    · intro e he; exact ⟨(hD e he).1, by have := (hD e he).2.1; omega, (hD e he).2.2⟩
    · intro τ hτ
      rcases List.mem_append.1 hτ with hτ | hτ
      · rcases List.mem_append.1 hτ with hτ | hτ
        · exact a2 τ hτ
        · exact b2 τ hτ
      · exact hEr'p τ hτ
    · intro R hR
      rcases List.mem_append.1 hR with hR | hR
      · rcases List.mem_append.1 hR with hR | hR
        · exact a3 R hR
        · exact b3 R hR
      · exact hEd'p R hR
    · intro K
      rcases a4 K with ⟨e₁, h₁, hle₁, hK₁⟩ | ⟨R, hR, hRK⟩
      · rcases b4 K with ⟨e₂, h₂, hle₂, hK₂⟩ | ⟨R, hR, hRK⟩
        · rcases hpos K _ ⟨_, prod_mem h₁ h₂, hg _ _ _ _ hle₁ hle₂, fun x hx => by
              rcases List.mem_append.1 hx with hx | hx
              · exact hK₁ x hx
              · exact hK₂ x hx⟩ with h | ⟨R, hR, hRK⟩
          · exact Or.inl h
          · exact Or.inr ⟨R, List.mem_append_right _ hR, hRK⟩
        · exact Or.inr ⟨R, List.mem_append_left _ (List.mem_append_right _ hR), hRK⟩
      · exact Or.inr ⟨R, List.mem_append_left _ (List.mem_append_left _ hR), hRK⟩
    · intro c
      rcases a5 c with ha | ⟨τ, hτ, hc⟩
      · rcases b5 c with hb | ⟨τ, hτ, hc⟩
        · by_cases hev : ∃ τ ∈ Er', cons c τ
          · obtain ⟨τ, hτ, hc⟩ := hev
            exact Or.inr ⟨τ, List.mem_append_right _ hτ, hc⟩
          · left; intro e he hr
            rcases hneg c e.2 ⟨e, he, Int.le_refl _, hr⟩ with ⟨e', he', hle, hr'⟩ | h
            · obtain ⟨e₁, h₁, e₂, h₂, rfl⟩ := mem_prod he'
              exact Int.le_trans hle (hg _ _ _ _ (ha e₁ h₁ (rb_left hr')) (hb e₂ h₂ (rb_right hr')))
            · exact absurd h hev
        · exact Or.inr ⟨τ, List.mem_append_left _ (List.mem_append_right _ hτ), hc⟩
      · exact Or.inr ⟨τ, List.mem_append_left _ (List.mem_append_left _ hτ), hc⟩

open Programme.«20261024-1633-proof-complexity».CliqueColour
open Programme.«20261024-1633-proof-complexity».CCApprox (emb val_emb clique_pos colour_neg)
open Programme.«20261024-1633-proof-complexity».CP (Refutation)

/-- Input approximators: edge `(i,j)`, `i < j < m`, is the clique indicator of `{i,j}`. -/
def inA (m : Nat) : V → List (List Nat × Int)
  | .p i j => if i < j ∧ j < m then [([], 0), ([i, j], 1)] else [([], 0)]
  | _ => [([], 0)]

theorem hin (m L : Nat) (hL : 1 ≤ L) :
    ∀ u, shared isR isQ u = true → Good (emb m) m L (fun β => val β u) (inA m u) [] [] := by
  intro u hu
  cases u with
  | q _ _ => simp [shared, isR, isQ] at hu
  | r _ _ => simp [shared, isR, isQ] at hu
  | p i j =>
    by_cases h : i < j ∧ j < m
    · have e : inA m (.p i j) = [([], 0), ([i, j], 1)] := by simp [inA, h]
      rw [e]
      refine ⟨?_, by simp, by simp, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · simp
        · refine ⟨by simp; omega, by simp; omega, ?_⟩
          intro x hx; simp at hx; omega
      · intro K
        left
        simp only []
        rw [val_emb]
        by_cases g : posG K i j = true
        · refine ⟨([i, j], 1), by simp, by simp [g, h], ?_⟩
          simp only [posG, Bool.and_eq_true, decide_eq_true_eq] at g
          intro x hx; simp at hx; rcases hx with rfl | rfl; exact g.1; exact g.2
        · refine ⟨([], 0), by simp, by simp [g], by simp⟩
      · intro c
        left
        intro x hx hr
        simp only []
        rw [val_emb]
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · split <;> omega
        · have hne : c i ≠ c j := hr i (by simp) j (by simp) (by omega)
          have : negG c i j = true := by simp [negG, hne]
          simp [h, this]
    · have e : inA m (.p i j) = [([], 0)] := by simp [inA, h]
      rw [e]
      refine ⟨by simp, by simp, by simp, ?_, ?_⟩
      · intro K; left
        refine ⟨([], 0), by simp, ?_, by simp⟩
        simp only []
        rw [val_emb]; split
        · rename_i h'; exact absurd ⟨h'.1, h'.2.1⟩ h
        · exact Int.le_refl _
      · intro c; left
        intro x hx _
        rw [List.mem_singleton] at hx; subst hx
        simp only []
        rw [val_emb]; split <;> omega

/-- **Clique–colouring, value-free approximation.** For `L ≥ 1`, every tree-like CP refutation of
`CC m k` with `s` nodes (any coefficients) yields an approximator `A` (duplicate-free entries of
`≤ 2L` vertices `< m`), `≤ s(2k+5)(16L²)^L` rise events and `≤ s(2k+5)(4L²)^L` drop events with:
every duplicate-free `k`-list `K` of vertices `< m` containing no drop event has an entry `S ⊆ K` of
value `≥ 1`; for every colouring `c` with colours `< k-1` fitting no rise event, every entry
rainbow under `c` has value `≤ 0`. -/
theorem cc_vapprox (m k L : Nat) (hL : 1 ≤ L) (Rf : Refutation (CC m k)) :
    ∃ (A : List (List Nat × Int)) (Er : List (List (Nat × Nat))) (Ed : List (List Nat)),
      Er.length ≤ Rf.size * (2 * k + 5) * (4 * L * (4 * L)) ^ L ∧
      Ed.length ≤ Rf.size * (2 * k + 5) * (4 * L * L) ^ L ∧
      (∀ τ ∈ Er, Valid τ ∧ (∀ e ∈ τ, e.1 < m ∧ e.2 < m) ∧ τ.length = L) ∧
      (∀ R ∈ Ed, R.Nodup ∧ L ≤ R.length ∧ ∀ x ∈ R, x < m) ∧
      (∀ e ∈ A, e.1.Nodup ∧ e.1.length ≤ 2 * L ∧ ∀ x ∈ e.1, x < m) ∧
      (∀ K : List Nat, K.Nodup → K.length = k → (∀ x ∈ K, x < m) →
        (¬ ∃ R ∈ Ed, ∀ x ∈ R, x ∈ K) → ∃ e ∈ A, 1 ≤ e.2 ∧ ∀ x ∈ e.1, x ∈ K) ∧
      (∀ c : Nat → Nat, (∀ i, i < m → c i < k - 1) → (¬ ∃ τ ∈ Er, cons c τ) →
        ∀ e ∈ A, rb c e.1 → e.2 ≤ 0) := by
  obtain ⟨f, t, hrc, ht, _, hsep⟩ := cc_interp m k Rf
  obtain ⟨A, Er, Ed, hEr, hEd, g1, g2, g3, g4, g5⟩ :=
    vapprox (shared isR isQ) m L (emb m) (inA m) (hin m L hL) hrc
  refine ⟨A, Er, Ed, Nat.le_trans hEr (Nat.mul_le_mul_right _ ht),
    Nat.le_trans hEd (Nat.mul_le_mul_right _ ht), g2, g3, g1, ?_, ?_⟩
  · intro K hK hl hm hno
    rcases g4 K with ⟨e, he, hle, hK'⟩ | h
    · exact ⟨e, he, Int.le_trans ((hsep _).1 (clique_pos m k K hK hl hm)) hle, hK'⟩
    · exact absurd h hno
  · intro c hc hno e he hr
    rcases g5 c with h | h
    · exact Int.le_trans (h e he hr) ((hsep _).2 (colour_neg m k c hc))
    · exact absurd h hno

end Programme.«20261025-0459b-proof-complexity».VApprox
