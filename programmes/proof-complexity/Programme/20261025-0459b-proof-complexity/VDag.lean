import Programme.«20261025-0459b-proof-complexity».CCVal
import Programme.«20261025-0459b-proof-complexity».CPDagInterp

/-!
# DAG-like cutting planes for clique–colouring, arbitrary coefficients, `2^{Ω(m^{1/4})}`

* `vdag`: the value-free approximation of `Work.VApprox.vapprox`, run gate by gate over a monotone
  real circuit (`Work.CPDagInterp.MC`) instead of a formula. All gates share one list of rise events
  and one list of drop events; each binary gate adds at most `(16L²)^L` and `(4L²)^L` of them, so a
  circuit with `t` gates has at most `t (16L²)^L` and `t (4L²)^L`.
* `cc_vdag`: the clique–colouring instance via `Work.CPDagInterp.cc_interp_dag`.
* `count`: the counting of `Work.CCVal.cc_val`, stated for any `t`.
* `cc_dag`: for `L ≥ 1`, `32L² ≤ k-1`, `8L²k + L ≤ m`, every DAG-like CP refutation
  `Work.CPDag.DRefutation (CC m k)` with `s` lines has `2^(L-1) ≤ s (2k + 5)`.
-/

namespace Programme.«20261025-0459b-proof-complexity».VDag

open Programme.«20261025-0459b-proof-complexity».VSwitch Programme.«20261025-0459b-proof-complexity».VApprox Programme.«20261025-0459b-proof-complexity».CPDagInterp Programme.«20261025-0459b-proof-complexity».CPDag Programme.«20261025-0459b-proof-complexity».CCVal
open Programme.«20261024-1633-proof-complexity».CPInterp
open Programme.«20261024-1633-proof-complexity».CP (val)
open Programme.«20261024-1633-proof-complexity».RealApprox (posG negG)
open Programme.«20261024-1633-proof-complexity».KSub (ch)
open Programme.«20261024-1633-proof-complexity».Colour (ch2)

/-- `Good` survives enlarging the event lists by valid events. -/
theorem Good.lift {V : Type} {emb : (Nat → Nat → Bool) → V → Bool} {m L : Nat}
    {f : (V → Bool) → Int} {A : List (List Nat × Int)} {Er Er' : List (List (Nat × Nat))}
    {Ed Ed' : List (List Nat)} (g : Good emb m L f A Er Ed)
    (vEr : ∀ τ ∈ Er', Valid τ ∧ (∀ e ∈ τ, e.1 < m ∧ e.2 < m) ∧ τ.length = L)
    (vEd : ∀ R ∈ Ed', R.Nodup ∧ L ≤ R.length ∧ ∀ x ∈ R, x < m)
    (sEr : ∀ τ ∈ Er, τ ∈ Er') (sEd : ∀ R ∈ Ed, R ∈ Ed') : Good emb m L f A Er' Ed' := by
  obtain ⟨h1, _, _, h4, h5⟩ := g
  refine ⟨h1, vEr, vEd, ?_, ?_⟩
  · intro K
    rcases h4 K with h | ⟨R, hR, hK⟩
    · exact Or.inl h
    · exact Or.inr ⟨R, sEd R hR, hK⟩
  · intro c
    rcases h5 c with h | ⟨τ, hτ, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨τ, sEr τ hτ, hc⟩

/-- One binary gate on top of two good approximators with common event lists. -/
theorem gate2 {V : Type} (m L : Nat) (emb : (Nat → Nat → Bool) → V → Bool)
    {f h : (V → Bool) → Int} (g : Int → Int → Int)
    (hg : ∀ x x' y y', x ≤ x' → y ≤ y' → g x y ≤ g x' y')
    {A₁ A₂ : List (List Nat × Int)} {Er : List (List (Nat × Nat))} {Ed : List (List Nat)}
    (ga : Good emb m L f A₁ Er Ed) (gb : Good emb m L h A₂ Er Ed) :
    ∃ D Er' Ed', Er'.length ≤ (4 * L * (4 * L)) ^ L ∧ Ed'.length ≤ (4 * L * L) ^ L ∧
      Good emb m L (fun β => g (f β) (h β)) D (Er ++ Er') (Ed ++ Ed') := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := ga
  obtain ⟨b1, _, _, b4, b5⟩ := gb
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
  refine ⟨D, Er', Ed', hEr', by simpa using hEd', ?_, ?_, ?_, ?_, ?_⟩
  · intro e he; exact ⟨(hD e he).1, by have := (hD e he).2.1; omega, (hD e he).2.2⟩
  · intro τ hτ
    rcases List.mem_append.1 hτ with hτ | hτ
    · exact a2 τ hτ
    · exact hEr'p τ hτ
  · intro R hR
    rcases List.mem_append.1 hR with hR | hR
    · exact a3 R hR
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
      · exact Or.inr ⟨R, List.mem_append_left _ hR, hRK⟩
    · exact Or.inr ⟨R, List.mem_append_left _ hR, hRK⟩
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
      · exact Or.inr ⟨τ, List.mem_append_left _ hτ, hc⟩
    · exact Or.inr ⟨τ, List.mem_append_left _ hτ, hc⟩

/-- **Value-free approximation of a monotone real circuit.** -/
theorem vdag {V : Type} (P : V → Bool) (m L : Nat)
    (emb : (Nat → Nat → Bool) → V → Bool) (inA : V → List (List Nat × Int))
    (hin : ∀ u, P u = true → Good emb m L (fun β => val β u) (inA u) [] []) :
    ∀ {fs : List ((V → Bool) → Int)}, MC P fs →
    ∃ Er Ed, Er.length ≤ fs.length * (4 * L * (4 * L)) ^ L ∧
      Ed.length ≤ fs.length * (4 * L * L) ^ L ∧
      (∀ τ ∈ Er, Valid τ ∧ (∀ e ∈ τ, e.1 < m ∧ e.2 < m) ∧ τ.length = L) ∧
      (∀ R ∈ Ed, R.Nodup ∧ L ≤ R.length ∧ ∀ x ∈ R, x < m) ∧
      ∀ f ∈ fs, ∃ A, Good emb m L f A Er Ed
  | _, .nil => ⟨[], [], by simp, by simp, by simp, by simp, by simp⟩
  | _, @MC.cons _ _ fs f c j => by
    obtain ⟨Er, Ed, hEr, hEd, vEr, vEd, hg⟩ := vdag P m L emb inA hin c
    -- a new gate that adds no events
    have same : ∀ A, Good emb m L f A Er Ed → ∃ Er' Ed',
        Er'.length ≤ (f :: fs).length * (4 * L * (4 * L)) ^ L ∧
        Ed'.length ≤ (f :: fs).length * (4 * L * L) ^ L ∧
        (∀ τ ∈ Er', Valid τ ∧ (∀ e ∈ τ, e.1 < m ∧ e.2 < m) ∧ τ.length = L) ∧
        (∀ R ∈ Ed', R.Nodup ∧ L ≤ R.length ∧ ∀ x ∈ R, x < m) ∧
        ∀ f' ∈ f :: fs, ∃ A, Good emb m L f' A Er' Ed' := by
      intro A gA
      refine ⟨Er, Ed, ?_, ?_, vEr, vEd, ?_⟩
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
      · intro f' hf'
        rcases List.mem_cons.1 hf' with rfl | hf'
        · exact ⟨A, gA⟩
        · exact hg f' hf'
    cases j with
    | const k =>
      refine same [([], k)] ⟨?_, vEr, vEd, ?_, ?_⟩
      · intro e he; rw [List.mem_singleton] at he; subst he; simp
      · intro K; exact Or.inl ⟨([], k), List.mem_singleton_self _, Int.le_refl _, by simp⟩
      · intro c; left; intro e he _; rw [List.mem_singleton] at he; subst he; exact Int.le_refl _
    | inp u hu =>
      exact same (inA u) (Good.lift (hin u hu) vEr vEd (by simp) (by simp))
    | @gate1 f₁ g hgm h₁ =>
      obtain ⟨A, h1, h2, h3, h4, h5⟩ := hg f₁ h₁
      refine same (A.map fun e => (e.1, g e.2)) ⟨?_, h2, h3, ?_, ?_⟩
      · intro e he; obtain ⟨e', he', rfl⟩ := List.mem_map.1 he; exact h1 e' he'
      · intro K
        rcases h4 K with ⟨e, he, hle, hK⟩ | h
        · exact Or.inl ⟨(e.1, g e.2), List.mem_map.2 ⟨e, he, rfl⟩, hgm _ _ hle, hK⟩
        · exact Or.inr h
      · intro c
        rcases h5 c with h | h
        · left; intro e he hr
          obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
          exact hgm _ _ (h e' he' hr)
        · exact Or.inr h
    | @gate2 f₁ f₂ g hgm h₁ h₂ =>
      obtain ⟨A₁, ga⟩ := hg f₁ h₁
      obtain ⟨A₂, gb⟩ := hg f₂ h₂
      obtain ⟨D, Er', Ed', hEr', hEd', gD⟩ := gate2 m L emb g hgm ga gb
      have vEr2 := gD.2.1
      have vEd2 := gD.2.2.1
      refine ⟨Er ++ Er', Ed ++ Ed', ?_, ?_, vEr2, vEd2, ?_⟩
      · simp only [List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]; omega
      · simp only [List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]; omega
      · intro f' hf'
        rcases List.mem_cons.1 hf' with rfl | hf'
        · exact ⟨D, gD⟩
        · obtain ⟨A, gA⟩ := hg f' hf'
          exact ⟨A, Good.lift gA vEr2 vEd2 (fun τ h => List.mem_append_left _ h)
            (fun R h => List.mem_append_left _ h)⟩

open Programme.«20261024-1633-proof-complexity».CliqueColour
open Programme.«20261024-1633-proof-complexity».CCApprox (emb val_emb clique_pos colour_neg)

/-- **Clique–colouring, DAG-like CP, value-free approximation.** The conclusion of
`Work.VApprox.cc_vapprox`, for DAG-like refutations with `s` lines. -/
theorem cc_vdag (m k L : Nat) (hL : 1 ≤ L) (Rf : DRefutation (CC m k)) :
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
  obtain ⟨fs, hfs, hlen, f, hf, hsep⟩ := cc_interp_dag m k Rf
  obtain ⟨Er, Ed, hEr, hEd, _, _, hg⟩ :=
    vdag (shared isR isQ) m L (emb m) (inA m) (hin m L hL) hfs
  obtain ⟨A, g1, g2, g3, g4, g5⟩ := hg f hf
  refine ⟨A, Er, Ed, Nat.le_trans hEr (Nat.mul_le_mul_right _ hlen),
    Nat.le_trans hEd (Nat.mul_le_mul_right _ hlen), g2, g3, g1, ?_, ?_⟩
  · intro K hK hl hm hno
    rcases g4 K with ⟨e, he, hle, hK'⟩ | h
    · exact ⟨e, he, Int.le_trans ((hsep _).1 (clique_pos m k K hK hl hm)) hle, hK'⟩
    · exact absurd h hno
  · intro c hc hno e he hr
    rcases g5 c with h | h
    · exact Int.le_trans (h e he hr) ((hsep _).2 (colour_neg m k c hc))
    · exact absurd h hno

/-- The counting of `Work.CCVal.cc_val`, for an approximator with `t` in place of `s (2k+5)`. -/
theorem count (m k L t : Nat) (hL : 1 ≤ L) (hk : 32 * L ^ 2 ≤ k - 1) (hm : 8 * L ^ 2 * k + L ≤ m)
    (A : List (List Nat × Int)) (Er : List (List (Nat × Nat))) (Ed : List (List Nat))
    (hEr : Er.length ≤ t * (4 * L * (4 * L)) ^ L) (hEd : Ed.length ≤ t * (4 * L * L) ^ L)
    (gEr : ∀ τ ∈ Er, Valid τ ∧ (∀ e ∈ τ, e.1 < m ∧ e.2 < m) ∧ τ.length = L)
    (gEd : ∀ R ∈ Ed, R.Nodup ∧ L ≤ R.length ∧ ∀ x ∈ R, x < m)
    (gA : ∀ e ∈ A, e.1.Nodup ∧ e.1.length ≤ 2 * L ∧ ∀ x ∈ e.1, x < m)
    (gpos : ∀ K : List Nat, K.Nodup → K.length = k → (∀ x ∈ K, x < m) →
        (¬ ∃ R ∈ Ed, ∀ x ∈ R, x ∈ K) → ∃ e ∈ A, 1 ≤ e.2 ∧ ∀ x ∈ e.1, x ∈ K)
    (gneg : ∀ c : Nat → Nat, (∀ i, i < m → c i < k - 1) → (¬ ∃ τ ∈ Er, cons c τ) →
        ∀ e ∈ A, rb c e.1 → e.2 ≤ 0) :
    2 ^ (L - 1) ≤ t := by
  have hL2 : 1 ≤ L ^ 2 := Nat.pow_pos hL
  have hkL : L ≤ k := by
    have : L ≤ L ^ 2 := by rw [Nat.pow_two]; exact Nat.le_mul_of_pos_left _ hL
    omega
  have hkm : k ≤ m := by
    have : k ≤ 8 * L ^ 2 * k := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have e2 : 2 ^ L = 2 * 2 ^ (L - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  by_cases hall : ∀ K : List Nat, K.Nodup → K.length = k → (∀ x ∈ K, x < m) →
      ∃ R ∈ Ed, ∀ x ∈ R, x ∈ K
  · -- clique side: every k-set contains a member of `Ed`
    obtain ⟨l, rfl⟩ : ∃ l, L = l + 1 := ⟨L - 1, by omega⟩
    have h1 := Programme.«20261024-1633-proof-complexity».CCCount.pos_final m k l hkL Ed
      (fun T hT => ⟨(gEd T hT).1, (gEd T hT).2.1, (gEd T hT).2.2⟩) hall
    have h2 := Programme.«20261024-1633-proof-complexity».CCArith.pos_ratio m k l hkL
    have hch : 0 < ch m k :=
      Programme.«20261024-1633-proof-complexity».CCAssembly.ch_pos ch (fun n => by cases n <;> rfl)
        (fun _ _ => rfl) m k hkm
    -- (m-l)^L ≤ |Ed| k^L
    have h3 : (m - l) ^ (l + 1) * ch m k ≤ (Ed.length * k ^ (l + 1)) * ch m k := by
      calc (m - l) ^ (l + 1) * ch m k
          ≤ (m - l) ^ (l + 1) * (Ed.length * ch (m - (l + 1)) (k - (l + 1))) :=
            Nat.mul_le_mul_left _ h1
        _ = Ed.length * (ch (m - (l + 1)) (k - (l + 1)) * (m - l) ^ (l + 1)) := by
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ Ed.length * (ch m k * k ^ (l + 1)) := Nat.mul_le_mul_left _ h2
        _ = (Ed.length * k ^ (l + 1)) * ch m k := by
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have h4 := cancel hch h3
    generalize hX : 4 * (l + 1) ^ 2 * k = X
    have hXpos : 0 < X := by rw [← hX]; exact Nat.mul_pos (Nat.mul_pos (by omega) hL2) (by omega)
    have h5 : (2 * X) ^ (l + 1) ≤ (m - l) ^ (l + 1) := by
      apply Nat.pow_le_pow_left
      rw [← hX]
      have : 2 * (4 * (l + 1) ^ 2 * k) = 8 * (l + 1) ^ 2 * k := by
        simp only [← Nat.mul_assoc]
      omega
    have h6 : Ed.length * k ^ (l + 1) ≤ t * X ^ (l + 1) := by
      rw [← hX]
      calc Ed.length * k ^ (l + 1) ≤ t * (4 * (l + 1) * (l + 1)) ^ (l + 1) * k ^ (l + 1) :=
            Nat.mul_le_mul_right _ hEd
        _ = t * (4 * (l + 1) ^ 2 * k) ^ (l + 1) := by
            rw [Nat.mul_assoc t, ← Nat.mul_pow, Nat.pow_two, Nat.mul_assoc 4]
    have h7 : 2 ^ (l + 1) * X ^ (l + 1) ≤ t * X ^ (l + 1) := by
      rw [← Nat.mul_pow]; exact Nat.le_trans h5 (Nat.le_trans h4 h6)
    have h8 := cancel (Nat.pow_pos hXpos) h7
    simp only [Nat.add_sub_cancel] at e2 ⊢
    omega
  · -- colouring side: some k-clique avoids `Ed`, so an entry of value ≥ 1 exists
    obtain ⟨K, hK, hKl, hKm, hno⟩ : ∃ K : List Nat, K.Nodup ∧ K.length = k ∧
        (∀ x ∈ K, x < m) ∧ ¬ ∃ R ∈ Ed, ∀ x ∈ R, x ∈ K := by
      apply Classical.byContradiction
      intro hn
      apply hall
      intro K h1 h2 h3
      apply Classical.byContradiction
      intro h4
      exact hn ⟨K, h1, h2, h3, h4⟩
    obtain ⟨e, he, hv, _⟩ := gpos K hK hKl hKm hno
    have hq : 0 < k - 1 := by omega
    have h1 := neg_count (k - 1) m L hq e.1 (gA e he).1 (gA e he).2.1 (gA e he).2.2 Er gEr
      (fun c hc hr => by
        apply Classical.byContradiction
        intro hn
        have := gneg c hc hn e he hr
        omega)
    generalize hq' : k - 1 = q at h1 hk hq
    -- 2 C(2L,2) q^(m-1) ≤ q^m
    have hC : 2 * ch2 (2 * L) ≤ q := by
      have := ch2_le (2 * L)
      have e : 2 * L * (2 * L) = 4 * (L * L) := by rw [Nat.mul_mul_mul_comm]
      rw [Nat.pow_two] at hk
      omega
    have em : q ^ m = q * q ^ (m - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    have hc2 : 2 * (ch2 (2 * L) * q ^ (m - 1)) ≤ q ^ m := by
      rw [em, ← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hC
    have eL : q ^ m = q ^ L * q ^ (m - L) := by rw [← Nat.pow_add]; congr 1; omega
    have h2 : q ^ L * q ^ (m - L) ≤ (2 * Er.length) * q ^ (m - L) := by
      rw [← eL, Nat.mul_assoc]; omega
    have h3 := cancel (Nat.pow_pos hq) h2
    generalize hY : 4 * L * (4 * L) = Y at hEr
    have hYpos : 0 < Y := by rw [← hY]; exact Nat.mul_pos (by omega) (by omega)
    have h4 : 2 ^ L * Y ^ L ≤ (2 * t) * Y ^ L := by
      rw [← Nat.mul_pow]
      calc (2 * Y) ^ L ≤ q ^ L := by
            apply Nat.pow_le_pow_left
            rw [← hY]
            have : 4 * L * (4 * L) = 16 * (L * L) := by rw [Nat.mul_mul_mul_comm]
            rw [Nat.pow_two] at hk
            omega
        _ ≤ 2 * Er.length := h3
        _ ≤ 2 * (t * Y ^ L) := Nat.mul_le_mul_left _ hEr
        _ = (2 * t) * Y ^ L := by rw [Nat.mul_assoc]
    have h5 := cancel (Nat.pow_pos hYpos) h4
    omega


/-- **DAG-like cutting planes for clique–colouring, arbitrary coefficients.** For `L ≥ 1`,
`32L² ≤ k-1` and `8L²k + L ≤ m`, every DAG-like CP refutation of `CC m k` with `s` lines has
`2^(L-1) ≤ s (2k + 5)`. -/
theorem cc_dag (m k L : Nat) (hL : 1 ≤ L) (hk : 32 * L ^ 2 ≤ k - 1) (hm : 8 * L ^ 2 * k + L ≤ m)
    (Rf : DRefutation (CC m k)) : 2 ^ (L - 1) ≤ Rf.size * (2 * k + 5) := by
  obtain ⟨A, Er, Ed, hEr, hEd, gEr, gEd, gA, gpos, gneg⟩ := cc_vdag m k L hL Rf
  exact count m k L _ hL hk hm A Er Ed hEr hEd gEr gEd gA gpos gneg

end Programme.«20261025-0459b-proof-complexity».VDag

#print axioms Programme.«20261025-0459b-proof-complexity».VDag.cc_dag
