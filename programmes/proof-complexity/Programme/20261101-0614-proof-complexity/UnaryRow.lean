import Programme.«20261101-0614-proof-complexity».UnaryIter

namespace Programme.«20261101-0614-proof-complexity».UnaryIter
open Programme.«20261031-2024-proof-complexity».NativeIter

def pos (x z : Nat) : Lit := ((x,z),true)
def minus (x z : Nat) : Lit := ((x,z),false)
def val (x z : Nat) (a : Assignment) : Rat := conjunction [pos x z] a
def total (x : Nat) (l : List Nat) (a : Assignment) : Rat :=
  (l.map fun z => val x z a).sum

def correction (x : Nat) (m : List Lit) : List Nat → Assignment → Rat
  | [], _ => 0
  | v::t, a => (t.map fun w => conjunction (m ++ [pos x v, pos x w]) a).sum +
      correction x (m ++ [minus x v]) t a

theorem cancel_one (r : Rat) : 1 + (-1 + r) = r := by
  rw [← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add]

theorem correction_identity (x : Nat) (m : List Lit) (l : List Nat) (a : Assignment) :
    correction x m l a = conjunction m a *
      (total x l a - 1 + conjunction (l.map (minus x)) a) := by
  induction l generalizing m with
  | nil => simp [correction, total, conjunction, Rat.sub_add_cancel, Rat.mul_zero]
  | cons v t ih =>
    simp only [correction, ih, conjunction_mul, total, List.map_cons, List.sum_cons]
    have hv : conjunction (minus x v :: t.map (minus x)) a =
        conjunction [minus x v] a * conjunction (t.map (minus x)) a :=
      conjunction_mul [minus x v] (t.map (minus x)) a
    rw [hv]
    have hpair (w : Nat) : conjunction [pos x v, pos x w] a =
        val x v a * val x w a := conjunction_mul [pos x v] [pos x w] a
    simp only [hpair, ← Rat.mul_assoc, sum_mul_left]
    cases h : a (x,v) <;>
      simp [val, conjunction, pos, minus, holds, h, Rat.add_comm,
        Rat.zero_add, Rat.mul_zero, Rat.zero_mul, Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_left_comm, cancel_one]

theorem correction_cone {F d} (x : Nat) (m : List Lit) (l : List Nat)
    (hm : Multiplier m) (hdis : ∀ v ∈ l, (x,v) ∉ m.map Prod.fst)
    (hsort : l.Pairwise (· < ·)) (hdeg : m.length + l.length ≤ d)
    (hp : ∀ v ∈ l, ∀ w ∈ l, v < w → [minus x v, minus x w] ∈ F) :
    Cone F d (correction x m l) := by
  induction l generalizing m with
  | nil => exact Cone.zero
  | cons v t ih =>
    obtain ⟨hv, ht⟩ := List.pairwise_cons.mp hsort
    have hfirst : Cone F d (fun a =>
        (t.map fun w => conjunction (m ++ [pos x v, pos x w]) a).sum) := by
      apply cone_sum
      intro w hw
      have he := Cone.equation [minus x v, minus x w] m 1
        (hp v (by simp) w (by simp [hw]) (hv w hw))
        (show Admitted d [minus x v, minus x w] m from ⟨hm, by
          have := List.length_pos_iff.mpr (show t ≠ [] from by intro h; simp [h] at hw)
          simp only [List.length_cons] at hdeg ⊢
          simp only [List.length_nil] at ⊢
          omega⟩)
      simpa [falsity, minus, pos, neg] using he
    have hm' : Multiplier (m ++ [minus x v]) := by
      simp only [Multiplier, List.map_append, List.map_cons, List.map_nil,
        List.nodup_append]
      refine ⟨hm, by simp, ?_⟩
      intro a ha b hb hab
      have hb' : b = (x,v) := by simpa [minus] using hb
      rw [hab, hb'] at ha
      exact hdis v (by simp) ha
    have hdis' : ∀ w ∈ t, (x,w) ∉ (m ++ [minus x v]).map Prod.fst := by
      intro w hw
      simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false, minus]
      intro h
      rcases h with h | h
      · exact hdis w (by simp [hw]) h
      · have := hv w hw
        have := Prod.mk.inj h
        omega
    exact Cone.add hfirst (ih _ hm' hdis' ht (by
      simp only [List.length_append, List.length_cons, List.length_nil] at *
      omega) (by intro z hz w hw hzw; exact hp z (by simp [hz]) w (by simp [hw]) hzw))

#print axioms correction_identity
#print axioms correction_cone

theorem row_mem (L x : Nat) (hx : x < L) : row L x ∈ cnf L := by
  simp only [cnf, raw, List.mem_eraseDups, List.mem_append]
  apply Or.inl; apply Or.inl; apply Or.inl
  exact List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx, by simp⟩

theorem pair_mem (L x v w : Nat) (hx : x < L) (hv : v < L)
    (hw : w < L) (hvw : v < w) : [minus x v, minus x w] ∈ cnf L := by
  simp only [cnf, raw, List.mem_eraseDups, List.mem_append]
  apply Or.inl; apply Or.inl; apply Or.inl
  apply List.mem_flatMap.mpr
  refine ⟨x, List.mem_range.mpr hx, ?_⟩
  apply List.mem_append.mpr; right
  apply List.mem_flatMap.mpr
  refine ⟨v, List.mem_range.mpr hv, List.mem_map.mpr ?_⟩
  exact ⟨w, List.mem_filter.mpr ⟨List.mem_range.mpr hw, by simpa using hvw⟩, rfl⟩

theorem row_linear (L x : Nat) (hx : x < L) :
    Cone (cnf L) L (fun a => total x (List.range L) a - 1) := by
  have h := correction_cone (F := cnf L) (d := L) x [] (List.range L)
    (by simp [Multiplier]) (by simp) (by
      exact List.pairwise_lt_range) (by simp)
    (by intro v hv w hw hvw
        exact pair_mem L x v w hx (List.mem_range.mp hv) (List.mem_range.mp hw) hvw)
  have he := Cone.equation (row L x) [] (-1) (row_mem L x hx)
    (show Admitted L (row L x) [] from ⟨by simp [Multiplier], by simp [row]⟩)
  have hid : correction x [] (List.range L) = (fun a =>
      total x (List.range L) a - 1 + conjunction ((List.range L).map (minus x)) a) := by
    funext a
    rw [correction_identity]
    simp [conjunction]
  rw [hid] at h
  have hf : falsity (row L x) = (List.range L).map (minus x) := by
    simp [falsity, row, minus, neg, List.map_map]
  have hsum := Cone.add h he
  have hh : (fun a =>
      (total x (List.range L) a - 1 + conjunction ((List.range L).map (minus x)) a) +
        -1 * conjunction ([] ++ falsity (row L x)) a) =
      (fun a => total x (List.range L) a - 1) := by
    funext a
    simp only [List.nil_append, hf, Rat.neg_mul, Rat.one_mul,
      Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]
  rw [hh] at hsum
  exact hsum

#print axioms row_linear
end Programme.«20261101-0614-proof-complexity».UnaryIter
