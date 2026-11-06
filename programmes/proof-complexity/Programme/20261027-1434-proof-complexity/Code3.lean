import Programme.«20261027-1434-proof-complexity».PeelBase

/-!
# Codes of canonical 3-matchings of `ontoFPHP 7 8`

A canonical 3-matching is a strictly descending list `[a, b, c]` of variables `< 105`. Its code is
the combinatorial rank `r3 a b c = C(a,3) + C(b,2) + c < C(105,3) = 187460`, which is injective
(`r3_inj`). `cd x y z` is the code of the set `{x, y, z}` (sorted by `srt`), and a guard value
for repeated or out-of-range entries. `cd_ind` expresses `[cd x y z = r3 a b c]` as a sum of six
indicator terms, one for each ordering of `a, b, c`.
-/

namespace Programme.«20261027-1434-proof-complexity».Code3

set_option linter.unusedVariables false

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261027-1434-proof-complexity».PeelBase

def C3 (a : Nat) : Nat := a * (a - 1) * (a - 2) / 6
def C2 (b : Nat) : Nat := b * (b - 1) / 2

def r3 (a b c : Nat) : Nat := C3 a + C2 b + c

theorem hA : ∀ a < 105, ∀ a' < a, C3 a' + C2 a' ≤ C3 a := by decide +kernel
theorem hB : ∀ b < 105, ∀ b' < b, C2 b' + b' ≤ C2 b := by decide +kernel
theorem hM : C3 104 + C2 104 ≤ 187460 := by decide +kernel

theorem r3_lt {a b c : Nat} (hcb : c < b) (hba : b < a) (ha : a < 105) : r3 a b c < 187460 := by
  have h1 := hB a ha b hba
  have h2 : C3 a + C2 a ≤ C3 104 + C2 104 := by
    rcases Nat.lt_or_ge a 104 with h | h
    · have := hA 104 (by omega) a h
      have h3 : C2 a ≤ C2 104 := by have := hB 104 (by omega) a h; omega
      omega
    · have : a = 104 := by omega
      subst this; omega
  unfold r3; have := hM; omega

theorem r3_inj {a b c a' b' c' : Nat} (hcb : c < b) (hba : b < a) (ha : a < 105)
    (hcb' : c' < b') (hba' : b' < a') (ha' : a' < 105) (h : r3 a b c = r3 a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  unfold r3 at h
  have ea : a = a' := by
    rcases Nat.lt_trichotomy a a' with hl | he | hl
    · have h1 := hB a ha b hba; have h2 := hA a' ha' a hl; omega
    · exact he
    · have h1 := hB a' ha' b' hba'; have h2 := hA a ha a' hl; omega
  subst ea
  have eb : b = b' := by
    rcases Nat.lt_trichotomy b b' with hl | he | hl
    · have := hB b' (by omega) b hl; omega
    · exact he
    · have := hB b (by omega) b' hl; omega
  subst eb
  exact ⟨rfl, rfl, by omega⟩

/-! ## Sorting three entries -/

def srt (x y z : Nat) : Nat × Nat × Nat :=
  if x < y then (if y < z then (z, y, x) else if x < z then (y, z, x) else (y, x, z))
  else (if x < z then (z, x, y) else if y < z then (x, z, y) else (x, y, z))

def ok3 (x y z : Nat) : Bool := x < 105 && y < 105 && z < 105 && x != y && y != z && x != z

/-- Code of the set `{x, y, z}`; `187460` (never a code) if the entries repeat or are too big. -/
def cd (x y z : Nat) : Nat :=
  if ok3 x y z then r3 (srt x y z).1 (srt x y z).2.1 (srt x y z).2.2 else 187460

def fc3 (x y z : Nat) : List Nat := [(srt x y z).1, (srt x y z).2.1, (srt x y z).2.2]

theorem srt_spec (x y z : Nat) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    (srt x y z).2.2 < (srt x y z).2.1 ∧ (srt x y z).2.1 < (srt x y z).1 ∧
    (∀ t, (t = (srt x y z).1 ∨ t = (srt x y z).2.1 ∨ t = (srt x y z).2.2) ↔ (t = x ∨ t = y ∨ t = z)) := by
  unfold srt
  split <;> (try split) <;> (try split) <;> simp only <;> refine ⟨by omega, by omega, fun t => by constructor <;> intro h <;> omega⟩

theorem srt_lt (x y z : Nat) (hx : x < 105) (hy : y < 105) (hz : z < 105) : (srt x y z).1 < 105 := by
  unfold srt; split <;> (try split) <;> (try split) <;> simp only <;> omega

/-- `[cd x y z = r3 a b c]` for a canonical triple `a > b > c`, as six ordered indicators. -/
def ind6 (a b c x y z : Nat) : Int :=
  (if x = a ∧ y = b ∧ z = c then 1 else 0) + (if x = a ∧ y = c ∧ z = b then 1 else 0) +
  (if x = b ∧ y = a ∧ z = c then 1 else 0) + (if x = b ∧ y = c ∧ z = a then 1 else 0) +
  (if x = c ∧ y = a ∧ z = b then 1 else 0) + (if x = c ∧ y = b ∧ z = a then 1 else 0)

theorem ind6_zero {a b c x y z : Nat}
    (h : ¬ ((a = x ∨ a = y ∨ a = z) ∧ (b = x ∨ b = y ∨ b = z) ∧ (c = x ∨ c = y ∨ c = z))) :
    ind6 a b c x y z = 0 := by
  have n1 : ¬ (x = a ∧ y = b ∧ z = c) := fun h' => h ⟨by omega, by omega, by omega⟩
  have n2 : ¬ (x = a ∧ y = c ∧ z = b) := fun h' => h ⟨by omega, by omega, by omega⟩
  have n3 : ¬ (x = b ∧ y = a ∧ z = c) := fun h' => h ⟨by omega, by omega, by omega⟩
  have n4 : ¬ (x = b ∧ y = c ∧ z = a) := fun h' => h ⟨by omega, by omega, by omega⟩
  have n5 : ¬ (x = c ∧ y = a ∧ z = b) := fun h' => h ⟨by omega, by omega, by omega⟩
  have n6 : ¬ (x = c ∧ y = b ∧ z = a) := fun h' => h ⟨by omega, by omega, by omega⟩
  simp only [ind6, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6]; rfl

theorem ind6_one {a b c x y z : Nat} (hcb : c < b) (hba : b < a)
    (ma : a = x ∨ a = y ∨ a = z) (mb : b = x ∨ b = y ∨ b = z) (mc : c = x ∨ c = y ∨ c = z) :
    ind6 a b c x y z = 1 := by
  have d1 : a ≠ b := by omega
  have d2 : b ≠ c := by omega
  have d3 : a ≠ c := by omega
  rcases ma with rfl | rfl | rfl <;> rcases mb with rfl | rfl | rfl <;> rcases mc with rfl | rfl | rfl <;>
    first | omega | simp [ind6, d1, d2, d3, d1.symm, d2.symm, d3.symm]

theorem cd_ind {a b c : Nat} (hcb : c < b) (hba : b < a) (ha : a < 105) (x y z : Nat) :
    (if cd x y z = r3 a b c then (1 : Int) else 0) = ind6 a b c x y z := by
  have hlt := r3_lt hcb hba ha
  unfold cd
  by_cases hok : ok3 x y z = true
  · simp only [hok, if_true]
    simp only [ok3, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hok
    obtain ⟨⟨⟨⟨⟨hx, hy⟩, hz⟩, hxy⟩, hyz⟩, hxz⟩ := hok
    obtain ⟨s1, s2, sm⟩ := srt_spec x y z hxy hyz hxz
    have s0 := srt_lt x y z hx hy hz
    by_cases he : r3 (srt x y z).1 (srt x y z).2.1 (srt x y z).2.2 = r3 a b c
    · obtain ⟨e1, e2, e3⟩ := r3_inj s1 s2 s0 hcb hba ha he
      rw [if_pos he]
      have ma := (sm a).mp (Or.inl e1.symm)
      have mb := (sm b).mp (Or.inr (Or.inl e2.symm))
      have mc := (sm c).mp (Or.inr (Or.inr e3.symm))
      exact (ind6_one hcb hba ma mb mc).symm
    · rw [if_neg he]
      have key : ¬ ((a = x ∨ a = y ∨ a = z) ∧ (b = x ∨ b = y ∨ b = z) ∧ (c = x ∨ c = y ∨ c = z)) := by
        rintro ⟨ma, mb, mc⟩
        apply he
        have ma' := (sm a).mpr ma; have mb' := (sm b).mpr mb; have mc' := (sm c).mpr mc
        have : (srt x y z).1 = a ∧ (srt x y z).2.1 = b ∧ (srt x y z).2.2 = c := by omega
        rw [this.1, this.2.1, this.2.2]
      exact (ind6_zero key).symm
  · simp only [Bool.not_eq_true] at hok
    simp only [hok, Bool.false_eq_true, if_false]
    rw [if_neg (by omega)]
    simp only [ok3, Bool.and_eq_false_iff, decide_eq_false_iff_not, bne_eq_false_iff_eq, Nat.not_lt] at hok
    refine (ind6_zero ?_).symm
    rintro ⟨ma, mb, mc⟩
    omega

/-! ## Canonical 3-matchings -/

theorem canon_three : ∀ (N a b c : Nat), c < b → b < a →
    canon N [a, b, c] = (if a < N then [a] else []) ++ (if b < N then [b] else []) ++ (if c < N then [c] else [])
  | 0, a, b, c, _, _ => by simp [canon]
  | N + 1, a, b, c, hcb, hba => by
    simp only [canon, List.mem_cons, List.not_mem_nil, or_false]
    rw [canon_three N a b c hcb hba]
    by_cases h1 : N = a
    · subst h1; simp [show b < N + 1 by omega, show c < N + 1 by omega, show b < N by omega, show c < N by omega]
    · by_cases h2 : N = b
      · subst h2
        simp [show ¬ a < N by omega, show ¬ a < N + 1 by omega, show c < N + 1 by omega, hcb]
      · by_cases h3 : N = c
        · subst h3
          simp [show ¬ a < N by omega, show ¬ a < N + 1 by omega, show ¬ b < N by omega,
            show ¬ b < N + 1 by omega]
        · simp only [h1, h2, h3, or_self, if_false]
          have e1 : (a < N + 1) = (a < N) := by apply propext; omega
          have e2 : (b < N + 1) = (b < N) := by apply propext; omega
          have e3 : (c < N + 1) = (c < N) := by apply propext; omega
          simp only [e1, e2, e3]

theorem canon_fc3 {x y z : Nat} (hx : x < 105) (hy : y < 105) (hz : z < 105) (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) : canon ((7 + 8) * 7) [x, y, z] = fc3 x y z := by
  obtain ⟨s1, s2, sm⟩ := srt_spec x y z hxy hyz hxz
  have s0 := srt_lt x y z hx hy hz
  rw [canon_congr _ [x, y, z] (fc3 x y z) (fun t _ => by
    simp only [fc3, List.mem_cons, List.not_mem_nil, or_false]; exact (sm t).symm)]
  unfold fc3
  rw [canon_three _ _ _ _ s1 s2]
  simp [show (srt x y z).1 < (7 + 8) * 7 by omega, show (srt x y z).2.1 < (7 + 8) * 7 by omega,
    show (srt x y z).2.2 < (7 + 8) * 7 by omega]

def code3 : List Nat → Nat
  | [a, b, c] => r3 a b c
  | _ => 0

theorem CM_three {m : List Nat} (hm : CM 7 8 m) (hl : m.length = 3) :
    ∃ a b c, m = [a, b, c] ∧ c < b ∧ b < a ∧ a < 105 ∧ isMatch 7 [a, b, c] = true := by
  match m, hl with
  | [x, y, z], _ =>
    have hx := CM_lt' hm (x := x) (by simp)
    have hy := CM_lt' hm (x := y) (by simp)
    have hz := CM_lt' hm (x := z) (by simp)
    have hnd := CM_nodup hm
    have hxy : x ≠ y := by intro h; subst h; simp at hnd
    have hxz : x ≠ z := by intro h; subst h; simp at hnd
    have hyz : y ≠ z := by intro h; subst h; simp at hnd
    have hc := canon_fc3 hx hy hz hxy hyz hxz
    rw [hm.1] at hc
    obtain ⟨s1, s2, -⟩ := srt_spec x y z hxy hyz hxz
    have s0 := srt_lt x y z hx hy hz
    simp only [fc3, List.cons.injEq, and_true] at hc
    obtain ⟨e1, e2, e3⟩ := hc
    refine ⟨x, y, z, rfl, by omega, by omega, hx, hm.2⟩

theorem code3_inj {m m' : List Nat} (hm : CM 7 8 m) (hl : m.length = 3) (hm' : CM 7 8 m')
    (hl' : m'.length = 3) (h : code3 m = code3 m') : m = m' := by
  obtain ⟨a, b, c, rfl, h1, h2, h3, -⟩ := CM_three hm hl
  obtain ⟨a', b', c', rfl, h1', h2', h3', -⟩ := CM_three hm' hl'
  obtain ⟨e1, e2, e3⟩ := r3_inj h1 h2 h3 h1' h2' h3' h
  subst e1; subst e2; subst e3; rfl

theorem code3_lt {m : List Nat} (hm : CM 7 8 m) (hl : m.length = 3) : code3 m < 187460 := by
  obtain ⟨a, b, c, rfl, h1, h2, h3, -⟩ := CM_three hm hl
  exact r3_lt h1 h2 h3

/-- The code of `canon [x, y, z]` for distinct variables is `cd x y z`. -/
theorem code3_canon {x y z : Nat} (hx : x < 105) (hy : y < 105) (hz : z < 105) (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) : code3 (canon ((7 + 8) * 7) [x, y, z]) = cd x y z := by
  rw [canon_fc3 hx hy hz hxy hyz hxz]
  have : ok3 x y z = true := by simp [ok3, hx, hy, hz, hxy, hyz, hxz]
  simp [fc3, code3, cd, this]

end Programme.«20261027-1434-proof-complexity».Code3
