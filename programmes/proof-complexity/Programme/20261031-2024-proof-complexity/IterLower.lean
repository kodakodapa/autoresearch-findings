import Programme.«20261031-2024-proof-complexity».IterUpper

namespace Programme.«20261031-2024-proof-complexity».NativeIter

def witnessValue (x : Nat) : Nat := if x = 0 then 1 else x
def witness : Assignment := fun v => (witnessValue v.1).testBit v.2

theorem word_true_value (b x v : Nat) (hv : v < 2^b)
    (hx : witnessValue x < 2^b) (h : conjunction (word b x v) witness ≠ 0) :
    v = witnessValue x := by
  have hall : (word b x v).all (holds witness) = true := by
    cases hh : (word b x v).all (holds witness) <;> simp_all [conjunction]
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < b
  · have hh := List.all_eq_true.mp hall ((x,j), v.testBit j)
      (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
    have he : (witnessValue x).testBit j = v.testBit j := by
      simpa only [holds, witness, beq_iff_eq] using hh
    exact he.symm
  · have hp : 2^b ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega : v < 2^j),
      Nat.testBit_lt_two_pow (by omega : witnessValue x < 2^j)]

theorem eraseDups_of_nodup (l : List Lit) (h : l.Nodup) : l.eraseDups = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hn := List.nodup_cons.mp h
    rw [List.eraseDups_cons]
    have hf : l.filter (fun b => !(b == a)) = l := by
      apply List.filter_eq_self.mpr
      intro b hb
      have : b ≠ a := by intro he; subst b; exact hn.1 hb
      simpa using this
    rw [hf, ih hn.2]

theorem forbid_pair_length (b x z u v : Nat) (hxz : x ≠ z) :
    (forbid (word b x u ++ word b z v)).length = 2*b := by
  have hm := pair_multiplier b x z u v hxz
  have hn : (word b x u ++ word b z v).Nodup := by
    exact List.Pairwise.of_map Prod.fst (fun a c h he => h (congrArg Prod.fst he)) hm
  have hn' : ((word b x u ++ word b z v).map neg).Nodup := by
    apply List.Pairwise.map _ _ hn
    intro a c hac he
    apply hac
    have hh := congrArg neg he
    apply Prod.ext
    · exact (Prod.mk.inj hh).1
    · simpa [neg] using (Prod.mk.inj hh).2
  unfold forbid
  rw [eraseDups_of_nodup _ hn']
  simp only [List.length_map, List.length_append, word, List.length_range]
  omega

theorem witness_filtered (n b d : Nat) (hn : 2 ≤ n) (hnb : n ≤ 2^b)
    (hd : d < 2*b) : SatisfiesAt (cnfAt n b) d witness := by
  have hxv : ∀ x, x < n → witnessValue x < n := by
    intro x hx
    unfold witnessValue
    split <;> omega
  intro c hc hcd
  simp only [cnfAt, List.mem_eraseDups, List.mem_append] at hc
  rcases hc with hc | hc
  · obtain ⟨x, hx, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    obtain ⟨hv, hnv⟩ := List.mem_filter.mp hv
    rw [conjunction_forbid]
    by_cases he : conjunction (word b x v) witness = 0
    · exact he
    exfalso
    have hh := word_true_value b x v (List.mem_range.mp hv)
      (by have := hxv x (List.mem_range.mp hx); omega) he
    have := hxv x (List.mem_range.mp hx)
    simp only [decide_eq_true_eq] at hnv
    omega
  · obtain ⟨event, hevent, rfl⟩ := List.mem_map.mp hc
    obtain ⟨x, hx, hevent⟩ := List.mem_flatMap.mp hevent
    rcases List.mem_append.mp hevent with hevent | hevent
    · rcases List.mem_append.mp hevent with hevent | hevent
      · by_cases hx0 : x = 0
        · simp only [hx0, ↓reduceIte, List.mem_singleton] at hevent
          subst event
          rw [conjunction_forbid]
          by_cases he : conjunction (word b 0 0) witness = 0
          · exact he
          exfalso
          have hh := word_true_value b 0 0 (by omega)
            (by simpa [witnessValue] using (show 1 < 2^b by omega)) he
          simp [witnessValue] at hh
        · simp [hx0] at hevent
      · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hevent
        rw [conjunction_forbid]
        by_cases he : conjunction (word b x z) witness = 0
        · exact he
        exfalso
        have hzx : z < x := List.mem_range.mp hz
        have hxn := List.mem_range.mp hx
        have hh := word_true_value b x z (by omega)
          (by have := hxv x hxn; omega) he
        have hx0 : x ≠ 0 := by omega
        simp only [witnessValue, hx0, ↓reduceIte] at hh
        omega
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hevent
      obtain ⟨_, hxz⟩ := List.mem_filter.mp hz
      have hxz' : x < z := by simpa using hxz
      rw [forbid_pair_length b x z z z (by omega)] at hcd
      omega

theorem no_refutation_below_cnfAt (n b d : Nat) (hn : 2 ≤ n)
    (hnb : n ≤ 2^b) (hd : d < 2*b) : ¬ Refutes (cnfAt n b) d :=
  no_refutation_of_filtered_assignment (witness_filtered n b d hn hnb hd)

theorem native_capacity (n : Nat) (hn : 2 ≤ n) : n ≤ 2 ^ bits n := by
  have h := Nat.lt_log2_self (n := n-1)
  simp only [bits, show ¬n ≤ 1 by omega, ↓reduceIte]
  omega

theorem no_refutation_below_native_iter (n d : Nat) (hn : 2 ≤ n)
    (hd : d < 2 * bits n) : ¬ Refutes (cnf n) d :=
  no_refutation_below_cnfAt n (bits n) d hn (native_capacity n hn) hd

/-- Exact formal clause-product degree; the lower bound is an admission barrier. -/
theorem exact_native_iter (n : Nat) (hn : 2 ≤ n) :
    Refutes (cnf n) (2 * bits n) ∧
    ∀ d, d < 2 * bits n → ¬ Refutes (cnf n) d := by
  exact ⟨refutes_native_iter n hn, fun d hd => no_refutation_below_native_iter n d hn hd⟩

#print axioms exact_native_iter
#print axioms no_refutation_below_native_iter
#print axioms word_true_value
#print axioms no_refutation_below_cnfAt
end Programme.«20261031-2024-proof-complexity».NativeIter
