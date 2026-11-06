/-!
# Block independence for counting Boolean assignments

`asg U` lists all `2^|U|` assignments on the coordinates `U` (false elsewhere).
`indep`: if events `E_j` depend only on `base ∪ R_j` (blocks `R_j` disjoint), and for every fixing
of the outside a `2^{-ℓ}` fraction of the assignments of `R_j` makes `E_j` true, then the number
of assignments on `base ++ R_1 ++ … ++ R_p` making no `E_j` true is `≤ 2^|U| (1-2^{-ℓ})^p`.
`fix_count`: fixing the values on `F ⊆ R` leaves a `2^{-|F|}` fraction.
-/

namespace Programme.«20261025-0459b-proof-complexity».Indep

def upd (a : Nat → Bool) (x : Nat) (v : Bool) : Nat → Bool := fun y => if y = x then v else a y

/-- Overwrite the coordinates in `R` in all ways. -/
def ext : List Nat → List (Nat → Bool) → List (Nat → Bool)
  | [], L => L
  | x :: R, L => ext R (L.flatMap fun a => [upd a x false, upd a x true])

def asg (U : List Nat) : List (Nat → Bool) := ext U [fun _ => false]

def cnt (L : List (Nat → Bool)) (P : (Nat → Bool) → Prop) [DecidablePred P] : Nat :=
  (L.filter fun a => decide (P a)).length

theorem ext_append (R : List Nat) : ∀ (L1 L2 : List (Nat → Bool)),
    ext R (L1 ++ L2) = ext R L1 ++ ext R L2 := by
  induction R with
  | nil => intro L1 L2; rfl
  | cons x R ih => intro L1 L2; simp only [ext, List.flatMap_append]; exact ih _ _

theorem ext_flat (R : List Nat) : ∀ L : List (Nat → Bool), ext R L = L.flatMap fun a => ext R [a]
  | [] => by induction R with
    | nil => rfl
    | cons x R ih => simpa [ext] using ih
  | a :: L => by
    rw [show a :: L = [a] ++ L from rfl, ext_append, ext_flat R L]; simp

theorem ext_app (A B : List Nat) (L : List (Nat → Bool)) : ext (A ++ B) L = ext B (ext A L) := by
  induction A generalizing L with
  | nil => rfl
  | cons x A ih => exact ih _

theorem ext_length (R : List Nat) : ∀ L : List (Nat → Bool), (ext R L).length = 2 ^ R.length * L.length := by
  induction R with
  | nil => intro L; simp [ext]
  | cons x R ih =>
    intro L; simp only [ext]; rw [ih]
    have : (L.flatMap fun a => [upd a x false, upd a x true]).length = 2 * L.length := by
      induction L with
      | nil => rfl
      | cons b L ihL => simp only [List.flatMap_cons, List.length_append, List.length_cons,
          List.length_nil] at *; omega
    rw [this, List.length_cons, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]

/-- Members of `ext R [a]` agree with `a` outside `R`. -/
theorem ext_out (R : List Nat) : ∀ (L : List (Nat → Bool)) (α : Nat → Bool), α ∈ ext R L →
    ∃ a ∈ L, ∀ y, y ∉ R → α y = a y := by
  induction R with
  | nil => intro L α h; exact ⟨α, h, fun _ _ => rfl⟩
  | cons x R ih =>
    intro L α h
    obtain ⟨b, hb, hα⟩ := ih _ α h
    simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hb
    obtain ⟨a, ha, hb⟩ := hb
    refine ⟨a, ha, fun y hy => ?_⟩
    have hyx : y ≠ x := fun e => hy (e ▸ List.mem_cons_self ..)
    have hyR : y ∉ R := fun e => hy (List.mem_cons_of_mem _ e)
    rw [hα y hyR]; rcases hb with rfl | rfl <;> simp [upd, hyx]

theorem cnt_append (L1 L2 : List (Nat → Bool)) (P : (Nat → Bool) → Prop) [DecidablePred P] :
    cnt (L1 ++ L2) P = cnt L1 P + cnt L2 P := by simp [cnt, List.filter_append]

theorem cnt_le_length (L : List (Nat → Bool)) (P : (Nat → Bool) → Prop) [DecidablePred P] :
    cnt L P ≤ L.length := List.length_filter_le _ _

theorem cnt_congr {L : List (Nat → Bool)} {P Q : (Nat → Bool) → Prop} [DecidablePred P]
    [DecidablePred Q] (h : ∀ a ∈ L, (P a ↔ Q a)) : cnt L P = cnt L Q := by
  unfold cnt; congr 1; apply List.filter_congr; intro a ha; simp [h a ha]

theorem cnt_mono {L : List (Nat → Bool)} {P Q : (Nat → Bool) → Prop} [DecidablePred P]
    [DecidablePred Q] (h : ∀ a ∈ L, P a → Q a) : cnt L P ≤ cnt L Q := by
  induction L with
  | nil => simp [cnt]
  | cons a L ih =>
    have ih' := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a (List.mem_cons_self ..)
    simp only [cnt, List.filter_cons] at *
    by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp, hq] at * <;> omega

theorem cnt_and {L : List (Nat → Bool)} {P Q : (Nat → Bool) → Prop} [DecidablePred P]
    [DecidablePred Q] : cnt L P = cnt L (fun a => P a ∧ Q a) + cnt L (fun a => P a ∧ ¬Q a) := by
  induction L with
  | nil => simp [cnt]
  | cons a L ih =>
    simp only [cnt, List.filter_cons] at *
    by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp, hq] at * <;> omega

/-- Counting over a flatMap, with a scaled per-fibre bound. -/
theorem cnt_flat (L : List (Nat → Bool)) (g : (Nat → Bool) → List (Nat → Bool))
    (P : (Nat → Bool) → Prop) [DecidablePred P] (Q : (Nat → Bool) → Prop) [DecidablePred Q]
    (K c : Nat) (hQ : ∀ a ∈ L, ∀ α ∈ g a, P α → Q a) (hc : ∀ a ∈ L, cnt (g a) P * K ≤ c) :
    cnt (L.flatMap g) P * K ≤ c * cnt L Q := by
  induction L with
  | nil => simp [cnt]
  | cons a L ih =>
    have ih' := ih (fun b hb => hQ b (List.mem_cons_of_mem _ hb))
      (fun b hb => hc b (List.mem_cons_of_mem _ hb))
    rw [List.flatMap_cons, cnt_append, Nat.add_mul]
    have ha := hc a (List.mem_cons_self ..)
    by_cases hq : Q a
    · have : cnt (a :: L) Q = cnt L Q + 1 := by simp [cnt, List.filter_cons, hq]
      rw [this, Nat.mul_add, Nat.mul_one]; omega
    · have h0 : cnt (g a) P = 0 := by
        unfold cnt; rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro α hα; simpa using fun hp => hq (hQ a (List.mem_cons_self ..) α hα hp)
      have : cnt (a :: L) Q = cnt L Q := by simp [cnt, List.filter_cons, hq]
      rw [this, h0, Nat.zero_mul, Nat.zero_add]; exact ih'

/-- A block event. -/
structure Blk where
  R : List Nat
  E : (Nat → Bool) → Prop
  dec : DecidablePred E

instance (b : Blk) : DecidablePred b.E := b.dec

def flat (bs : List Blk) : List Nat := bs.flatMap Blk.R

def none (bs : List Blk) (α : Nat → Bool) : Prop := ∀ b ∈ bs, ¬b.E α

instance (bs : List Blk) : DecidablePred (none bs) := by
  intro α; unfold none
  exact List.decidableBAll _ _

theorem indep_rev (ℓ : Nat) (base : List Nat) : ∀ bs : List Blk,
    (base ++ flat bs.reverse).Nodup →
    (∀ b ∈ bs, ∀ α β : Nat → Bool, (∀ y, (y ∈ base ∨ y ∈ b.R) → α y = β y) → (b.E α ↔ b.E β)) →
    (∀ b ∈ bs, ∀ a, 2 ^ b.R.length ≤ 2 ^ ℓ * cnt (ext b.R [a]) b.E) →
    cnt (asg (base ++ flat bs.reverse)) (none bs) * 2 ^ (ℓ * bs.length) ≤
      2 ^ (base ++ flat bs.reverse).length * (2 ^ ℓ - 1) ^ bs.length
  | [], _, _, _ => by
    simp only [List.reverse_nil, flat, List.flatMap_nil, List.append_nil, List.length_nil,
      Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
    have := cnt_le_length (asg base) (none [])
    rw [asg, ext_length] at this; simpa [asg, ext_length] using this
  | b :: bs, hnd, hdep, hfr => by
    have hfl : flat (b :: bs).reverse = flat bs.reverse ++ b.R := by
      simp [flat, List.reverse_cons, List.flatMap_append]
    rw [hfl] at hnd ⊢
    rw [← List.append_assoc] at hnd ⊢
    have hnd' : (base ++ flat bs.reverse).Nodup := (List.nodup_append.1 hnd).1
    have hdisj : ∀ y ∈ b.R, y ∉ base ++ flat bs.reverse := by
      intro y hy hy'
      have := (List.nodup_append.1 hnd).2.2
      exact this y hy' y hy rfl
    have ih := indep_rev ℓ base bs hnd' (fun c hc => hdep c (List.mem_cons_of_mem _ hc))
      (fun c hc => hfr c (List.mem_cons_of_mem _ hc))
    -- decompose the count over the last block
    have hsplit : asg (base ++ flat bs.reverse ++ b.R) =
        (asg (base ++ flat bs.reverse)).flatMap fun a => ext b.R [a] := by
      rw [asg, ext_app, ext_flat]; rfl
    rw [hsplit]
    -- each fibre: at most 2^|R| - 2^{|R|-ℓ}... in scaled form
    have hfib : ∀ a, cnt (ext b.R [a]) (fun α => ¬ b.E α) * 2 ^ ℓ ≤ 2 ^ b.R.length * (2 ^ ℓ - 1) := by
      intro a
      have h1 := hfr b (List.mem_cons_self ..) a
      have h2 : cnt (ext b.R [a]) b.E + cnt (ext b.R [a]) (fun α => ¬ b.E α) = 2 ^ b.R.length := by
        have := @cnt_and (ext b.R [a]) (fun _ => True) b.E _ _
        have hl := ext_length b.R [a]
        simp only [List.length_singleton, Nat.mul_one] at hl
        have e1 : cnt (ext b.R [a]) (fun _ => True) = 2 ^ b.R.length := by
          rw [← hl]; simp [cnt]
        rw [e1] at this
        rw [cnt_congr (P := b.E) (Q := fun a => True ∧ b.E a) (fun _ _ => by simp),
          cnt_congr (P := fun α => ¬ b.E α) (Q := fun a => True ∧ ¬ b.E a) (fun _ _ => by simp)]
        omega
      have hp : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
      rw [Nat.mul_sub, Nat.mul_one]
      have : cnt (ext b.R [a]) (fun α => ¬b.E α) * 2 ^ ℓ + cnt (ext b.R [a]) b.E * 2 ^ ℓ =
          2 ^ b.R.length * 2 ^ ℓ := by rw [← Nat.add_mul, Nat.add_comm, h2]
      rw [Nat.mul_comm (2 ^ ℓ)] at h1
      omega
    -- the other events are constant on fibres
    have hconst : ∀ a ∈ asg (base ++ flat bs.reverse), ∀ α ∈ ext b.R [a],
        none (b :: bs) α → none bs a := by
      intro a _ α hα hn c hc
      obtain ⟨a', ha', hag⟩ := ext_out b.R [a] α hα
      simp only [List.mem_singleton] at ha'; subst ha'
      have hcR : ∀ y ∈ c.R, y ∉ b.R := by
        intro y hy hyb
        apply hdisj y hyb
        simp only [List.mem_append]; right
        simp only [flat, List.mem_flatMap]; exact ⟨c, List.mem_reverse.2 hc, hy⟩
      have hbR : ∀ y ∈ base, y ∉ b.R := fun y hy hyb => hdisj y hyb (List.mem_append_left _ hy)
      have := hdep c (List.mem_cons_of_mem _ hc) α a' (fun y hy => by
        rcases hy with hy | hy
        · exact hag y (hbR y hy)
        · exact hag y (hcR y hy))
      exact fun he => hn c (List.mem_cons_of_mem _ hc) (this.2 he)
    have key := cnt_flat (asg (base ++ flat bs.reverse)) (fun a => ext b.R [a])
      (none (b :: bs)) (none bs) (2 ^ ℓ) (2 ^ b.R.length * (2 ^ ℓ - 1)) hconst
      (fun a _ => Nat.le_trans (Nat.mul_le_mul_right _ (cnt_mono (fun α _ h => h b
        (List.mem_cons_self ..)))) (hfib a))
    have hlen : (base ++ flat bs.reverse ++ b.R).length =
        (base ++ flat bs.reverse).length + b.R.length := List.length_append ..
    rw [hlen, List.length_cons, Nat.mul_succ, Nat.pow_add, Nat.pow_succ, Nat.pow_add]
    calc cnt _ (none (b :: bs)) * (2 ^ (ℓ * bs.length) * 2 ^ ℓ)
        = (cnt _ (none (b :: bs)) * 2 ^ ℓ) * 2 ^ (ℓ * bs.length) := by
          rw [Nat.mul_comm (2 ^ (ℓ * bs.length)), Nat.mul_assoc]
      _ ≤ (2 ^ b.R.length * (2 ^ ℓ - 1) * cnt (asg (base ++ flat bs.reverse)) (none bs)) *
          2 ^ (ℓ * bs.length) := Nat.mul_le_mul_right _ key
      _ = 2 ^ b.R.length * (2 ^ ℓ - 1) *
          (cnt (asg (base ++ flat bs.reverse)) (none bs) * 2 ^ (ℓ * bs.length)) := by
          rw [Nat.mul_assoc]
      _ ≤ 2 ^ b.R.length * (2 ^ ℓ - 1) *
          (2 ^ (base ++ flat bs.reverse).length * (2 ^ ℓ - 1) ^ bs.length) :=
          Nat.mul_le_mul_left _ ih
      _ = 2 ^ (base ++ flat bs.reverse).length * 2 ^ b.R.length *
          ((2 ^ ℓ - 1) ^ bs.length * (2 ^ ℓ - 1)) := by
          simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Fixing the values `v` on `D ⊆ R` leaves a `2^{-|D|}` fraction of the overwrites. -/
theorem fix_count (v : Nat → Bool) : ∀ (R D : List Nat) (a : Nat → Bool), R.Nodup → D.Nodup →
    (∀ y ∈ D, y ∈ R) → 2 ^ R.length ≤ 2 ^ D.length * cnt (ext R [a]) (fun α => ∀ y ∈ D, α y = v y)
  | [], D, a, _, _, hD => by
    have : D = [] := List.eq_nil_iff_forall_not_mem.2 (fun y hy => by simpa using hD y hy)
    subst this; simp [ext, cnt]
  | x :: R, D, a, hR, hDn, hD => by
    have hxR : x ∉ R := (List.nodup_cons.1 hR).1
    have hRn : R.Nodup := (List.nodup_cons.1 hR).2
    have hsp : ext (x :: R) [a] = ext R [upd a x false] ++ ext R [upd a x true] := by
      simp only [ext, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact ext_append R [upd a x false] [upd a x true]
    rw [hsp, cnt_append, List.length_cons, Nat.pow_succ]
    by_cases hx : x ∈ D
    · have hD' : ∀ y ∈ D.erase x, y ∈ R := by
        intro y hy
        rw [hDn.mem_erase_iff] at hy
        rcases List.mem_cons.1 (hD y hy.2) with h | h
        · exact absurd h hy.1
        · exact h
      have hl : (D.erase x).length + 1 = D.length := by
        have := List.length_erase_of_mem hx; have := List.length_pos_of_mem hx; omega
      have key : ∀ b : Bool, b = v x → 2 ^ R.length ≤ 2 ^ (D.erase x).length *
          cnt (ext R [upd a x b]) (fun α => ∀ y ∈ D, α y = v y) := by
        intro b hb
        have ih := fix_count v R (D.erase x) (upd a x b) hRn (hDn.erase x) hD'
        rw [cnt_congr (Q := fun α => ∀ y ∈ D.erase x, α y = v y)]; exact ih
        intro α hα
        obtain ⟨a', ha', hag⟩ := ext_out R _ α hα
        simp only [List.mem_singleton] at ha'; subst ha'
        have hαx : α x = v x := by rw [hag x hxR]; simp [upd, hb]
        constructor
        · intro h y hy; exact h y (List.mem_of_mem_erase hy)
        · intro h y hy
          by_cases hyx : y = x
          · subst hyx; exact hαx
          · exact h y ((hDn.mem_erase_iff).2 ⟨hyx, hy⟩)
      have hsum : 2 ^ R.length ≤ 2 ^ (D.erase x).length *
          (cnt (ext R [upd a x false]) (fun α => ∀ y ∈ D, α y = v y) +
            cnt (ext R [upd a x true]) (fun α => ∀ y ∈ D, α y = v y)) := by
        cases hv : v x
        · exact Nat.le_trans (key false hv.symm) (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
        · exact Nat.le_trans (key true hv.symm) (Nat.mul_le_mul_left _ (Nat.le_add_left _ _))
      rw [← hl, Nat.pow_succ, Nat.mul_right_comm]
      exact Nat.mul_le_mul_right 2 hsum
    · have hD' : ∀ y ∈ D, y ∈ R := by
        intro y hy
        rcases List.mem_cons.1 (hD y hy) with h | h
        · exact absurd (h ▸ hy) hx
        · exact h
      have h1 := fix_count v R D (upd a x false) hRn hDn hD'
      have h2 := fix_count v R D (upd a x true) hRn hDn hD'
      rw [Nat.mul_add]; omega

/-- **Block independence.** Events `b.E` depending only on `base ∪ b.R` (blocks disjoint), each
true on a `2^{-ℓ}` fraction of every fibre over `b.R`: at most `2^|U|(1-2^{-ℓ})^p` assignments on
`U = base ++ R_1 ++ … ++ R_p` make none of them true. -/
theorem indep (ℓ : Nat) (base : List Nat) (bs : List Blk) (hnd : (base ++ flat bs).Nodup)
    (hdep : ∀ b ∈ bs, ∀ α β : Nat → Bool, (∀ y, (y ∈ base ∨ y ∈ b.R) → α y = β y) →
      (b.E α ↔ b.E β))
    (hfr : ∀ b ∈ bs, ∀ a, 2 ^ b.R.length ≤ 2 ^ ℓ * cnt (ext b.R [a]) b.E) :
    cnt (asg (base ++ flat bs)) (none bs) * 2 ^ (ℓ * bs.length) ≤
      2 ^ (base ++ flat bs).length * (2 ^ ℓ - 1) ^ bs.length := by
  have h := indep_rev ℓ base bs.reverse (by simpa using hnd)
    (fun b hb => hdep b (List.mem_reverse.1 hb)) (fun b hb => hfr b (List.mem_reverse.1 hb))
  rw [List.reverse_reverse, List.length_reverse] at h
  rw [cnt_congr (Q := none bs.reverse) (fun α _ => by simp [none])]
  exact h

end Programme.«20261025-0459b-proof-complexity».Indep
