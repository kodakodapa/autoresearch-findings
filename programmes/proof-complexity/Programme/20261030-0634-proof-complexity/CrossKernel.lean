import Programme.«20261026-1402-proof-complexity».Ext1F2

set_option linter.deprecated false

namespace Programme.«20261030-0634-proof-complexity».CrossKernel
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (rsum_skip rsum_const)

/-- Symmetric pair operator for zero row and column sums. -/
def cross (F : Nat → Nat → Int) (a b i j : Nat) : Int := F a j + F i b

theorem cross_symm (F : Nat → Nat → Int) (a b i j : Nat) :
    cross F a b i j = cross F i j a b := Int.add_comm _ _

/-- An odd line length turns the cross operator into a right inverse modulo two. -/
theorem line (N b : Nat) (hN : N % 2 = 1) (hb : b < N)
    (G : Nat → Int) (t : Int) (hG : (2 : Int) ∣ rsum N G) :
    (2 : Int) ∣ rsum N (fun j => if j = b then 0 else G j + t) - G b := by
  have hs : rsum N (fun j => G j + t) = rsum N G + (N : Int) * t := by
    rw [rsum_add, rsum_const]
  rw [rsum_skip N b hb, hs]
  obtain ⟨q, hq⟩ := hG
  have hn : (N : Int) = 2 * (N / 2 : Nat) + 1 := by omega
  refine ⟨q + (N / 2 : Nat) * t - G b, ?_⟩
  rw [hn]
  grind

theorem cross_row (P N : Nat) (hN : N % 2 = 1)
    (F : Nat → Nat → Int) (hF : ∀ a < P, (2 : Int) ∣ rsum N (F a))
    (a b i : Nat) (ha : a < P) (hb : b < N) :
    (2 : Int) ∣ rsum N (fun j => if j = b then 0 else cross F a b i j) - F a b :=
  line N b hN hb (F a) (F i b) (hF a ha)

theorem cross_col (P N : Nat) (hP : P % 2 = 1)
    (F : Nat → Nat → Int) (hF : ∀ b < N, (2 : Int) ∣ rsum P (fun a => F a b))
    (a b j : Nat) (ha : a < P) (hb : b < N) :
    (2 : Int) ∣ rsum P (fun i => if i = a then 0 else cross F a b i j) - F a b := by
  have h := line P a hP ha (fun i => F i b) (F a j) (hF b hb)
  have he : (fun i => if i = a then 0 else cross F a b i j) =
      (fun i => if i = a then 0 else F i b + F a j) := by
    funext i; simp only [cross, Int.add_comm]
  rw [he]
  exact h

open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».Ext0 (canon_single isMatch_single)
open Programme.«20261026-1402-proof-complexity».Ext1 (canon_pair isMatch_pair canon_nil)
open Programme.«20261025-0459-proof-complexity».OntoSubst (var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt var_decode)
open Programme.«20261025-1627-proof-complexity».MomGen

def witness (n : Nat) (f : List Nat → Int) : List Nat → Int
  | [v, w] => f [var n (v / n) (w % n)] + f [var n (w / n) (v % n)]
  | _ => 0

theorem term (n k i j w : Nat) (f : List Nat → Int)
    (hi : i < n + k) (hj : j < n) (hw : w < (n+k)*n) :
    (if isMatch n [var n i j, w] then
      witness n f (canon ((n+k)*n) [var n i j,w]) else 0) =
    if i = w / n ∨ j = w % n then 0 else
      cross (fun a b => f [var n a b]) (w / n) (w % n) i j := by
  have hx := var_lt n k i j hi hj
  have hd := var_div n i j hj
  have hm := var_mod n i j hj
  by_cases he : var n i j = w
  · have hc : canon ((n+k)*n) [var n i j,w] = [w] := by
      have heq : canon ((n+k)*n) [var n i j,w] = canon ((n+k)*n) [w] :=
        canon_congr _ _ _ (fun z _ => by simp [he])
      rw [heq, canon_single _ _ hw]
    have h : i = w / n ∨ j = w % n := by left; rw [← he, hd]
    rw [if_pos h, hc]; split <;> rfl
  · by_cases h : i = w / n ∨ j = w % n
    · rw [if_pos h]
      have hbad : ¬ isMatch n [var n i j,w] = true := by
        rw [isMatch_pair n _ _ he, hd, hm]; omega
      rw [if_neg hbad]
    · rw [if_neg h]
      have hok : isMatch n [var n i j,w] = true := by
        rw [isMatch_pair n _ _ he, hd, hm]; omega
      rw [if_pos hok]
      rcases canon_pair _ _ _ hx hw he with hc | hc <;>
        rw [hc] <;> simp only [witness, hd, hm, cross]
      · exact Int.add_comm _ _

/-- Every zero-link edge input extends on a board with both sides odd. -/
theorem kernel (n k : Nat) (hn : n % 2 = 1) (hP : (n+k) % 2 = 1)
    (f : List Nat → Int) (hf : Bal 2 n k f (fun _ => 0) 0) :
    ∃ y, Bal 2 n k y f 1 := by
  let F := fun a b => f [var n a b]
  have hem : CM n k [] := ⟨canon_nil _, rfl⟩
  have hr : ∀ a < n+k, (2 : Int) ∣ rsum n (F a) := by
    intro a ha
    have h := (hf [] hem rfl).1 a ha (fun v hv => by simp at hv)
    simp only [Int.sub_zero] at h
    have he : rowS n k f [] a = rsum n (F a) := by
      unfold rowS lineS
      apply rsum_congr
      intro j hj
      rw [isMatch_single, if_pos rfl, canon_single _ _ (var_lt n k a j ha hj)]
    rwa [he] at h
  have hc : ∀ b < n, (2 : Int) ∣ rsum (n+k) (fun a => F a b) := by
    intro b hb
    have h := (hf [] hem rfl).2 b hb (fun v hv => by simp at hv)
    simp only [Int.sub_zero] at h
    have he : colS n k f [] b = rsum (n+k) (fun a => F a b) := by
      unfold colS lineS
      apply rsum_congr
      intro a ha
      rw [isMatch_single, if_pos rfl, canon_single _ _ (var_lt n k a b ha hb)]
    rwa [he] at h
  refine ⟨witness n f, ?_⟩
  intro g hg hl
  obtain ⟨w, rfl⟩ : ∃ w, g = [w] := by
    match g, hl with
    | [w], _ => exact ⟨w, rfl⟩
  have hw := CM_lt hg (List.mem_singleton_self w)
  have ha : w / n < n+k := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hw)
  have hb : w % n < n := Nat.mod_lt _ (by omega)
  have hfw : f [w] = F (w/n) (w%n) := by dsimp [F]; rw [var_decode]
  rw [hfw]
  constructor
  · intro i hi hfree
    have hia : i ≠ w/n := fun e => hfree w (by simp) e.symm
    unfold rowS lineS
    rw [rsum_congr n _ _ (fun j hj => term n k i j w f hi hj hw)]
    simp only [hia, false_or]
    exact cross_row (n+k) n hn F hr (w/n) (w%n) i ha hb
  · intro j hj hfree
    have hjb : j ≠ w%n := fun e => hfree w (by simp) e.symm
    unfold colS lineS
    rw [rsum_congr (n+k) _ _ (fun i hi => term n k i j w f hi hj hw)]
    simp only [hjb, or_false]
    exact cross_col (n+k) n hP F hc (w/n) (w%n) j ha hb

theorem kernel98 (f : List Nat → Int)
    (hf : Bal 2 9 8 f (fun _ => 0) 0) :
    ∃ y, Bal 2 9 8 y f 1 := kernel 9 8 (by decide) (by decide) f hf

#print axioms kernel
#print axioms kernel98
end Programme.«20261030-0634-proof-complexity».CrossKernel
