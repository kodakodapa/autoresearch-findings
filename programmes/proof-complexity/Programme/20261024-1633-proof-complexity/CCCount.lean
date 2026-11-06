import Programme.«20261024-1633-proof-complexity».KSub
import Programme.«20261024-1633-proof-complexity».Colour

/-!
# Final counting for the clique–colouring approximation bound

The two counts that close the approximation method once the error lists are known
(`Work.CCApprox.cc_approx`, th): vertices are `0..m-1`, graphs on them, colourings with `< q` colours.

* `pos_final`: if every duplicate-free `k`-list of vertices `< m` contains a set of `pe`
  (sets of size `≥ ℓ+1`), then `C(m,k) ≤ |pe| · C(m-ℓ-1, k-ℓ-1)`.
* `neg_final`: if every colouring making `S` rainbow hits an event of `ne` (core rainbow, none of
  its `p` petals rainbow; petals of size `≤ ℓ`, pairwise meeting inside the core), then
  `q^m ≤ C(|S|,2) q^(m-1) + |ne| · C(ℓ,2)^p q^(m-p)`.
-/

namespace Programme.«20261024-1633-proof-complexity».CCCount

open Programme.«20261024-1633-proof-complexity».KSub Programme.«20261024-1633-proof-complexity».Colour

/-- Positive side: all `k`-sets hit by `pe`. -/
theorem pos_final (m k ℓ : Nat) (hk : ℓ + 1 ≤ k) (pe : List (List Nat))
    (hpe : ∀ T ∈ pe, T.Nodup ∧ ℓ + 1 ≤ T.length ∧ ∀ x ∈ T, x < m)
    (hall : ∀ K : List Nat, K.Nodup → K.length = k → (∀ x ∈ K, x < m) →
      ∃ T ∈ pe, ∀ i ∈ T, i ∈ K) :
    ch m k ≤ pe.length * ch (m - (ℓ + 1)) (k - (ℓ + 1)) := by
  have hV : (List.range m).Nodup := List.nodup_range
  have h := pos_count (List.range m) hV k ℓ pe
    (fun T hT => ⟨(hpe T hT).1, fun i hi => List.mem_range.mpr ((hpe T hT).2.2 i hi),
      (hpe T hT).2.1⟩) hk
  rw [List.length_range] at h
  have hle : ((ksub (List.range m) k).filter (fun _ => true)).length ≤
      ((ksub (List.range m) k).filter (fun K => pe.any fun T => sub T K)).length := by
    apply filter_mono
    intro K hK _
    obtain ⟨hsub, hlen⟩ := mem_ksub hK
    obtain ⟨T, hT, hTK⟩ := hall K (hsub.nodup hV) hlen
      (fun x hx => List.mem_range.mp (hsub.subset hx))
    rw [List.any_eq_true]
    exact ⟨T, hT, sub_iff.mpr hTK⟩
  rw [List.filter_eq_self.mpr (fun _ _ => rfl), ksub_length, List.length_range] at hle
  omega

/-- `tot` only looks at colourings with colours `< q` on `W` that agree with the base off `W`. -/
theorem tot_mono_on (q : Nat) (W : List Nat) :
    ∀ (f g : (Nat → Nat) → Nat) (c : Nat → Nat),
      (∀ c', (∀ i ∈ W, c' i < q) → (∀ i, i ∉ W → c' i = c i) → f c' ≤ g c') →
      tot q W f c ≤ tot q W g c := by
  induction W with
  | nil => intro f g c h; exact h c (fun _ h => absurd h List.not_mem_nil) (fun _ _ => rfl)
  | cons u W ih =>
    intro f g c h
    simp only [tot]
    have key : ∀ r, r ≤ q → sm r (fun x => tot q W f (upd c u x)) ≤
        sm r (fun x => tot q W g (upd c u x)) := by
      intro r
      induction r with
      | zero => intro _; exact Nat.le_refl _
      | succ r ihr =>
        intro hr
        simp only [sm]
        apply Nat.add_le_add (ihr (by omega))
        apply ih f g (upd c u r)
        intro c' h1 h2
        apply h c'
        · intro i hi
          rw [List.mem_cons] at hi
          by_cases hiW : i ∈ W
          · exact h1 i hiW
          · rcases hi with rfl | hi
            · rw [h2 i hiW, upd_same]; omega
            · exact absurd hi hiW
        · intro i hi
          rw [List.mem_cons, not_or] at hi
          rw [h2 i hi.2, upd_ne c u r i hi.1]
    exact key q (Nat.le_refl q)

theorem rb_nil (c : Nat → Nat) : rb c [] := by
  intro a ha; exact absurd ha List.not_mem_nil

/-- Negative side: every colouring making `S` rainbow is caught by some event. -/
theorem neg_final (q ℓ p m : Nat) (hq : 0 < q) (S : List Nat) (hS : S.Nodup)
    (hSm : ∀ x ∈ S, x < m) (ne : List (List Nat × List (List Nat)))
    (hne : ∀ ev ∈ ne, ev.2.length = p ∧
      (∀ T ∈ ev.2, T.Nodup ∧ T.length ≤ ℓ ∧ ∀ x ∈ T, x < m) ∧
      ev.2.Pairwise (fun S T => ∀ x, x ∈ S → x ∈ T → x ∈ ev.1))
    (hit : ∀ c : Nat → Nat, (∀ i, i < m → c i < q) → rb c S →
      ∃ ev ∈ ne, rb c ev.1 ∧ ∀ T ∈ ev.2, ¬ rb c T) :
    q ^ m ≤ ch2 S.length * q ^ (m - 1) + ne.length * (ch2 ℓ ^ p * q ^ (m - p)) := by
  let V := List.range m
  have hV : V.Nodup := List.nodup_range
  have hVl : V.length = m := List.length_range
  let c0 : Nat → Nat := fun _ => 0
  let fS : (Nat → Nat) → Nat := fun c => if rb c [] ∧ ∀ S' ∈ [S], ¬ rb c S' then 1 else 0
  let fE : List Nat × List (List Nat) → (Nat → Nat) → Nat :=
    fun ev c => if rb c ev.1 ∧ ∀ T ∈ ev.2, ¬ rb c T then 1 else 0
  have hpt : tot q V (fun _ => 1) c0 ≤
      tot q V (fun c => fS c + (ne.map (fun ev => fE ev c)).sum) c0 := by
    apply tot_mono_on
    intro c' hc' _
    by_cases hr : rb c' S
    · obtain ⟨ev, hev, hP⟩ := hit c' (fun i hi => hc' i (List.mem_range.mpr hi)) hr
      have := le_sum_of_mem (fun ev => fE ev c') ne ev hev
      have h1 : fE ev c' = 1 := by simp only [fE]; rw [ite_eq_left hP]
      omega
    · have h1 : fS c' = 1 := by
        simp only [fS]
        rw [ite_eq_left ⟨rb_nil c', fun S' hS' => by
          rw [List.mem_singleton] at hS'; subst hS'; exact hr⟩]
      omega
  rw [tot_one, tot_add, tot_sum, hVl] at hpt
  have hA : tot q V fS c0 ≤ ch2 S.length * q ^ (m - 1) := by
    have := petal_count q S.length hq [] V [S] hV
      (fun S' hS' => by
        rw [List.mem_singleton] at hS'; subst hS'
        exact ⟨hS, Nat.le_refl _, fun x hx => List.mem_range.mpr (hSm x hx)⟩)
      (List.pairwise_singleton _ _) c0
    rw [hVl, List.length_singleton, Nat.pow_one] at this
    exact this
  have hB : (ne.map (fun ev => tot q V (fE ev) c0)).sum ≤ ne.length * (ch2 ℓ ^ p * q ^ (m - p)) := by
    apply sum_le
    intro ev hev
    obtain ⟨hl, hT, hpw⟩ := hne ev hev
    have := petal_count q ℓ hq ev.1 V ev.2 hV
      (fun T hT' => ⟨(hT T hT').1, (hT T hT').2.1,
        fun x hx => List.mem_range.mpr ((hT T hT').2.2 x hx)⟩) hpw c0
    rw [hl, hVl] at this
    exact this
  omega

end Programme.«20261024-1633-proof-complexity».CCCount

#print axioms Programme.«20261024-1633-proof-complexity».CCCount.pos_final
#print axioms Programme.«20261024-1633-proof-complexity».CCCount.neg_final
