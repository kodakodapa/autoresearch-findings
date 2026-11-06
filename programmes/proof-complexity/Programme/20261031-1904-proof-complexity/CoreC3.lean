import Programme.«20261029-1156-proof-complexity».StdPCCor
import Programme.«20261029-1156-proof-complexity».StdPCExact
import Programme.«20261027-0607-proof-complexity».VUnit
import Programme.«20261027-0607-proof-complexity».PeelV
import Programme.«20261025-0459-proof-complexity».OntoLucas
import Programme.«20261025-1627-proof-complexity».OntoF2K4
import Programme.«20261030-0634-proof-complexity».P3Top
import Programme.«20261028-0841-proof-complexity».L3.Q7
import Programme.«20261028-0841-proof-complexity».L3.Main
import Programme.«20261027-0607-proof-complexity».P7Main
import Programme.«20261027-0607-proof-complexity».CRTOnto
import Programme.«20261027-0607-proof-complexity».D5Main
import Programme.«20261029-1156-proof-complexity».StdPC
import Programme.«20261026-1402-proof-complexity».ExtLemma
import Programme.«20261026-1402-proof-complexity».RowCol
import Programme.«20261025-1627-proof-complexity».OntoQ7

/-! Canonical C3 vocabulary and restatements of the existing library results. -/
namespace Programme.«20261031-1904-proof-complexity».CoreC3

abbrev Poly := Programme.«20261024-1633-proof-complexity».NS.Poly
abbrev CubeDeg := Programme.«20261024-1633-proof-complexity».PCTseitin.CubeDeg
abbrev OntoFPHP := Programme.«20261025-0459-proof-complexity».OntoFPHP.ontoFPHP
abbrev PPCRefutation := Programme.«20261025-0459-proof-complexity».OntoFPHP.PPCRefutation
abbrev StdRefutes := Programme.«20261029-1156-proof-complexity».StdPC.Refutes
abbrev Bal := Programme.«20261026-1402-proof-complexity».ExtLemma.Bal
abbrev EXT := Programme.«20261026-1402-proof-complexity».ExtLemma.EXT
abbrev Hard := Programme.«20261025-1627-proof-complexity».OntoQ7.Hard
abbrev Q7 := Programme.«20261025-1627-proof-complexity».OntoQ7.Q7
abbrev IsPrime := Programme.«20261027-0607-proof-complexity».Peel.IsPrime

/-- The only second definition with a canonical concept's name in the library. -/
theorem rowCol_bal_eq : Programme.«20261026-1402-proof-complexity».RowCol.Bal = Bal := rfl

theorem pc_degree_exact {p c : Nat} (hp : IsPrime p) (hc : ¬ p ∣ c)
    (n : Nat) (hn : 2 * p - 3 ≤ n) (D : Nat) :
    PPCRefutation p (OntoFPHP n (p * c)) D ↔ p ≤ D :=
  Programme.«20261027-0607-proof-complexity».Lucas.pc_degree_exact hp hc n hn D

theorem separation {p q c : Nat} (hp : IsPrime p) (hq : IsPrime q)
    (hc : ¬ p ∣ c) (hqk : ¬ q ∣ p * c) (n : Nat) (hn : 2 * p - 3 ≤ n) :
    (∀ D, PPCRefutation p (OntoFPHP n (p * c)) D ↔ p ≤ D) ∧
      PPCRefutation q (OntoFPHP n (p * c)) 1 :=
  Programme.«20261027-0607-proof-complexity».Lucas.separation hp hq hc hqk n hn

theorem pc_degree_ge_p {p k : Nat} (hp : IsPrime p) (hk : p ∣ k)
    (n : Nat) (hn : 2 * p - 3 ≤ n) : ¬ PPCRefutation p (OntoFPHP n k) (p - 1) :=
  Programme.«20261027-0607-proof-complexity».Peel.pc_degree_ge_p hp hk n hn

theorem crt {a b D : Nat} (A : List (Poly Nat))
    (hab : ∃ x y : Int, x * a + y * b = 1) :
    PPCRefutation (a * b) A D ↔ PPCRefutation a A D ∧ PPCRefutation b A D :=
  Programme.«20261027-0607-proof-complexity».CRT.crt A hab

theorem composite_lower {m q k : Nat} (hq : IsPrime q) (hqm : q ∣ m)
    (hqk : q ∣ k) (n : Nat) (hn : 2 * q - 3 ≤ n) :
    ¬ PPCRefutation m (OntoFPHP n k) (q - 1) :=
  Programme.«20261027-0607-proof-complexity».CRTOnto.composite_lower hq hqm hqk n hn

theorem two_primes_exact {p q c : Nat} (hp : IsPrime p) (hq : IsPrime q)
    (hpq : p ≠ q) (hpc : ¬ p ∣ c) (hqc : ¬ q ∣ c) (n : Nat)
    (hnp : 2 * p - 3 ≤ n) (hnq : 2 * q - 3 ≤ n) (D : Nat) :
    PPCRefutation (p * q) (OntoFPHP n (p * q * c)) D ↔ p ≤ D ∧ q ≤ D :=
  Programme.«20261027-0607-proof-complexity».CRTOnto.two_primes_exact hp hq hpq hpc hqc n hnp hnq D

theorem no_deg5 (n : Nat) (hn : 9 ≤ n) : ¬ PPCRefutation 5 (OntoFPHP n 25) 5 :=
  Programme.«20261027-0607-proof-complexity».D5.no_deg5 n hn

theorem no_deg7 (n : Nat) (hn : 13 ≤ n) : ¬ PPCRefutation 7 (OntoFPHP n 49) 7 :=
  Programme.«20261027-0607-proof-complexity».P7.no_deg7 n hn

theorem no_deg4 (n : Nat) (hn : 7 ≤ n) : ¬ PPCRefutation 2 (OntoFPHP n 8) 4 :=
  Programme.«20261028-0841-proof-complexity».L3.Main.no_deg4 n hn

theorem hard_ge3 (l : Nat) (hl : 3 ≤ l) : Hard 2 l 4 :=
  Programme.«20261028-0841-proof-complexity».L3.Q7.hard_ge3 l hl

theorem no_deg3 (n : Nat) (hn : 5 ≤ n) : ¬ PPCRefutation 3 (OntoFPHP n 9) 3 :=
  Programme.«20261030-0634-proof-complexity».P3Top.no_deg3 n hn

theorem f2_k4_exact (n D : Nat) (hn : 5 ≤ n) : PPCRefutation 2 (OntoFPHP n 4) D ↔ 4 ≤ D :=
  Programme.«20261025-1627-proof-complexity».OntoF2K4.f2_k4_exact n D hn

theorem f3_k3_exact (n D : Nat) (hn : 3 ≤ n) : PPCRefutation 3 (OntoFPHP n 3) D ↔ 3 ≤ D :=
  Programme.«20261025-0459-proof-complexity».OntoLucas.f3_k3_exact n D hn

theorem no_refutation_of_unit {p k n0 : Nat} (hp : IsPrime p) (hk : p ∣ k)
    (hn0 : 2 * p - 1 ≤ n0) (T : List Nat → Int)
    (hT : ∀ e ≤ p - 1, Bal p n0 k T T e) (h1 : (p : Int) ∣ T [] - 1)
    (n : Nat) (hn : n0 ≤ n) : ¬ PPCRefutation p (OntoFPHP n k) p :=
  Programme.«20261027-0607-proof-complexity».VUnit.no_refutation_of_unit hp hk hn0 T hT h1 n hn

theorem no_deg_p_of_design {p k n0 : Nat} (hp : IsPrime p) (hk : p ∣ k)
    (hn0 : 2 * p - 1 ≤ n0) {T : List Nat → Int}
    (hT : ∀ e ≤ p - 1, Bal p n0 k T T e) (h1 : ¬ (p : Int) ∣ T [])
    (n : Nat) (hn : n0 ≤ n) : ¬ PPCRefutation p (OntoFPHP n k) p :=
  Programme.«20261027-0607-proof-complexity».PeelV.no_deg_p_of_design hp hk hn0 hT h1 n hn


theorem refutes_ppc {p D : Nat} {A : List (Poly Nat)} (hp : 1 < p)
    (h : StdRefutes p A D) : PPCRefutation p A D :=
  Programme.«20261029-1156-proof-complexity».StdPC.refutes_ppc hp h

theorem refutes_iff {p D : Nat} {A : List (Poly Nat)} (hp : 1 < p) :
    StdRefutes p A D ↔ PPCRefutation p A D :=
  Programme.«20261029-1156-proof-complexity».StdPCConv.refutes_iff hp

theorem std_pc_degree_exact {p c : Nat} (hp : IsPrime p) (hc : ¬ p ∣ c)
    (n : Nat) (hn : 2 * p - 3 ≤ n) (D : Nat) :
    StdRefutes p (OntoFPHP n (p * c)) D ↔ p ≤ D :=
  Programme.«20261029-1156-proof-complexity».StdPCExact.std_pc_degree_exact hp hc n hn D

theorem std_f2_k4_exact (n D : Nat) (hn : 5 ≤ n) :
    StdRefutes 2 (OntoFPHP n 4) D ↔ 4 ≤ D :=
  Programme.«20261029-1156-proof-complexity».StdPCExact.std_f2_k4_exact n D hn

theorem std_f3_k3_exact (n D : Nat) (hn : 3 ≤ n) :
    StdRefutes 3 (OntoFPHP n 3) D ↔ 3 ≤ D :=
  Programme.«20261029-1156-proof-complexity».StdPCExact.std_f3_k3_exact n D hn

theorem std_hard_ge3 (l : Nat) (hl : 3 ≤ l) :
    ∃ N, ∀ n, N ≤ n → ¬ StdRefutes 2 (OntoFPHP n (2 ^ l)) 4 :=
  Programme.«20261029-1156-proof-complexity».StdPCCor.std_hard_ge3 l hl

theorem std_hard_ge2 (l : Nat) (hl : 2 ≤ l) :
    (∃ N, ∀ n, N ≤ n → ¬ StdRefutes 2 (OntoFPHP n (2 ^ l)) 3) ∧
    (∃ N, ∀ n, N ≤ n → ¬ StdRefutes 3 (OntoFPHP n (3 ^ l)) 3) :=
  Programme.«20261029-1156-proof-complexity».StdPCCor.std_hard_ge2 l hl

theorem std_lower_p {p k : Nat} (hp : IsPrime p) (hk : p ∣ k)
    (n : Nat) (hn : 2 * p - 3 ≤ n) (D : Nat) (hD : D < p) :
    ¬ StdRefutes p (OntoFPHP n k) D :=
  Programme.«20261029-1156-proof-complexity».StdPCCor.std_lower_p hp hk n hn D hD

theorem shard_iff_hard {p l D : Nat} (hp : 1 < p) :
    Programme.«20261029-1156-proof-complexity».StdPCCor.SHard p l D ↔ Hard p l D := by
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun n hn h => hN n hn ((refutes_iff hp).mpr h)⟩
  · rintro ⟨N, hN⟩
    exact ⟨N, fun n hn h => hN n hn ((refutes_iff hp).mp h)⟩

theorem std_q7_iff {p : Nat} (hp : 1 < p) :
    (∀ D, ∃ l, Programme.«20261029-1156-proof-complexity».StdPCCor.SHard p l D) ↔ Q7 p := by
  constructor
  · intro h D
    obtain ⟨l, hl⟩ := h D
    exact ⟨l, (shard_iff_hard hp).mp hl⟩
  · intro h D
    obtain ⟨l, hl⟩ := h D
    exact ⟨l, (shard_iff_hard hp).mpr hl⟩

end Programme.«20261031-1904-proof-complexity».CoreC3

#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.rowCol_bal_eq
#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.pc_degree_exact
#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.separation
#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.pc_degree_ge_p
#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.crt
#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.composite_lower
#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.two_primes_exact
#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.no_deg5

#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.no_deg7

#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.no_deg4

#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.hard_ge3

#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.no_deg3

#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.f2_k4_exact

#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.f3_k3_exact

#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.no_refutation_of_unit
#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.no_deg_p_of_design

#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.refutes_ppc

#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.refutes_iff

#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.std_pc_degree_exact

#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.std_f2_k4_exact

#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.std_f3_k3_exact

#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.std_hard_ge3

#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.std_hard_ge2

#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.std_lower_p

#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.shard_iff_hard
#print axioms Programme.«20261031-1904-proof-complexity».CoreC3.std_q7_iff
