import Programme.«20261030-0634-proof-complexity».CrossKernel
import Programme.«20261030-0634-proof-complexity».LevelOneSplit

set_option linter.deprecated false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Programme.«20261030-0634-proof-complexity».Unit98
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt var_decode)
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».Ext0 (canon_single)
open Programme.«20261026-1402-proof-complexity».Ext1 (canon_pair isMatch_pair canon_nil)
open Programme.«20261026-1402-proof-complexity».Ext1F2 (Tour)

def bp (a : Nat) : Nat := if a < 11 then 0 else if a < 14 then 1 else 2
def bh (b : Nat) : Nat := b / 3
def localP (a : Nat) : Nat := if a < 11 then a else if a < 14 then a - 11 else a - 14
def E (a b : Nat) : Int := if bp a = bh b then 1 else 0
def W (a b i j : Nat) : Int :=
  if bp a = bh b ∧ bp i = bh j then
    if bp a = bp i then Tour (if bp a = 0 then 11 else 3) (localP a) (b % 3) (localP i) (j % 3)
    else 1
  else 0

theorem ws : ∀ a : Fin 17, ∀ b : Fin 9, ∀ i : Fin 17, ∀ j : Fin 9,
    W a b i j = W i j a b := by decide

theorem wr : ∀ a : Fin 17, ∀ b : Fin 9, ∀ i : Fin 17,
    i.val ≠ a.val → (2 : Int) ∣
    rsum 9 (fun j => if i.val = a.val ∨ j = b.val then 0 else W a b i j) - E a b := by decide

theorem wc : ∀ a : Fin 17, ∀ b : Fin 9, ∀ j : Fin 9,
    j.val ≠ b.val → (2 : Int) ∣
    rsum 17 (fun i => if i = a.val ∨ j.val = b.val then 0 else W a b i j) - E a b := by decide

def U : List Nat → Int
  | [v] => E (v / 9) (v % 9)
  | _ => 1

def Y : List Nat → Int
  | [v,w] => W (v / 9) (v % 9) (w / 9) (w % 9)
  | _ => 0

theorem term (i j w : Nat) (hi : i < 17) (hj : j < 9) (hw : w < 153) :
    (if isMatch 9 [var 9 i j, w] then Y (canon 153 [var 9 i j,w]) else 0) =
    if i = w / 9 ∨ j = w % 9 then 0 else W (w/9) (w%9) i j := by
  have hx := var_lt 9 8 i j hi hj
  have hd := var_div 9 i j hj
  have hm := var_mod 9 i j hj
  by_cases he : var 9 i j = w
  · have hc : canon 153 [var 9 i j,w] = [w] := by
      have heq : canon 153 [var 9 i j,w] = canon 153 [w] :=
        canon_congr _ _ _ (fun z _ => by simp [he])
      rw [heq, canon_single _ _ hw]
    have h : i = w / 9 ∨ j = w % 9 := by left; rw [← he, hd]
    rw [if_pos h, hc]; split <;> rfl
  · by_cases h : i = w / 9 ∨ j = w % 9
    · rw [if_pos h]
      have hbad : ¬ isMatch 9 [var 9 i j,w] = true := by
        rw [isMatch_pair 9 _ _ he, hd, hm]; omega
      rw [if_neg hbad]
    · rw [if_neg h]
      have hok : isMatch 9 [var 9 i j,w] = true := by
        rw [isMatch_pair 9 _ _ he, hd, hm]; omega
      rw [if_pos hok]
      rcases canon_pair _ _ _ hx hw he with hc | hc <;>
        rw [hc] <;> simp only [Y, hd, hm]
      · exact ws ⟨i,hi⟩ ⟨j,hj⟩ ⟨w/9,by omega⟩ ⟨w%9,by omega⟩

 theorem unit_extension : Bal 2 9 8 Y U 1 := by
  intro g hg hl
  obtain ⟨w, rfl⟩ : ∃ w, g = [w] := by
    match g, hl with
    | [w], _ => exact ⟨w, rfl⟩
  have hw := CM_lt hg (List.mem_singleton_self w)
  change w < 153 at hw
  constructor
  · intro i hi hf
    have hia : i ≠ w/9 := fun e => hf w (by simp) e.symm
    unfold rowS lineS
    rw [rsum_congr 9 _ _ (fun j hj => term i j w hi hj hw)]
    exact wr ⟨w/9, by omega⟩ ⟨w%9, by omega⟩ ⟨i,hi⟩ hia
  · intro j hj hf
    have hjb : j ≠ w%9 := fun e => hf w (by simp) e.symm
    unfold colS lineS
    rw [rsum_congr 17 _ _ (fun i hi => term i j w hi hj hw)]
    exact wc ⟨w/9, by omega⟩ ⟨w%9, by omega⟩ ⟨j,hj⟩ hjb

theorem er : ∀ a : Fin 17, (2 : Int) ∣ rsum 9 (E a) - 1 := by decide
theorem ec : ∀ b : Fin 9, (2 : Int) ∣ rsum 17 (fun a => E a b) - 1 := by decide

theorem unit_input : Bal 2 9 8 U (fun _ => 1) 0 := by
  intro g hg hl
  have hnil : g = [] := List.eq_nil_of_length_eq_zero hl
  subst g
  constructor
  · intro i hi _
    have he : rowS 9 8 U [] i = rsum 9 (E i) := by
      unfold rowS lineS
      apply rsum_congr
      intro j hj
      rw [Programme.«20261026-1402-proof-complexity».Ext0.isMatch_single,
        if_pos rfl, canon_single _ _ (var_lt 9 8 i j hi hj)]
      simp only [U, var_div 9 i j hj, var_mod 9 i j hj]
    rw [he]
    exact er ⟨i,hi⟩
  · intro j hj _
    have he : colS 9 8 U [] j = rsum 17 (fun i => E i j) := by
      unfold colS lineS
      apply rsum_congr
      intro i hi
      rw [Programme.«20261026-1402-proof-complexity».Ext0.isMatch_single,
        if_pos rfl, canon_single _ _ (var_lt 9 8 i j hi hj)]
      simp only [U, var_div 9 i j hj, var_mod 9 i j hj]
    rw [he]
    exact ec ⟨j,hj⟩

theorem ext1 : EXT 2 9 8 1 := by
  apply (Programme.«20261030-0634-proof-complexity».LevelOneSplit.ext1_iff_unit_kernel 2 9 8 U unit_input).mpr
  exact ⟨⟨Y, unit_extension⟩, Programme.«20261030-0634-proof-complexity».CrossKernel.kernel98⟩

#print axioms unit_extension
#print axioms unit_input
#print axioms ext1
end Programme.«20261030-0634-proof-complexity».Unit98
