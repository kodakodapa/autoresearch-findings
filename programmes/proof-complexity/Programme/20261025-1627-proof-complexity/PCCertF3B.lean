import Programme.«20261025-1627-proof-complexity».PCCertF3

/-!
# `Z/3` certificates with stored packed rows

`Work.PCCertF3.Cert.mulI` recomputes the packed rows `bigOf e` of every entry `e` in the row list
of `s`; for dense rows the kernel then caches hundreds of thousands of large intermediate
vectors. Here a table `B` may store `bigOf e` for some entries. Each stored value is checked once
against `bigOf e` (`bigOkI`), and `mulB` uses the stored values. `checkB` implies
`Work.PCCertF3.Cert.check`, so `soundB` is a corollary of `Work.PCCertF3.Cert.sound`.
-/

namespace Programme.«20261025-1627-proof-complexity».PCCertF3

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».FinDiff Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-1627-proof-complexity».PCCertCore (rAll rAll_spec rAll_mono)

inductive VT where
  | lf : VT
  | nd : VT → Nat → V → VT → VT

def VT.find : VT → Nat → Option V
  | .lf, _ => none
  | .nd l k v r, i => match Nat.blt i k with
    | true => l.find i
    | false => match Nat.blt k i with
      | true => r.find i
      | false => some v

namespace Cert

/-- The stored packed row of `e`, or `bigOf e` if none is stored. -/
def bS (C : Cert) (B : VT) (e : Nat) : V :=
  match B.find e with
  | some v => v
  | none => C.bigOf e

def bigOkI (C : Cert) (B : VT) (e : Nat) : Bool :=
  match B.find e with
  | some v => decide (v = C.bigOf e)
  | none => true

def mulB (C : Cert) (B : VT) (s : Nat) : Bool :=
  (C.E s).rl.all (fun ec => decide (ec.1 < C.N)) &&
  isZ (shr (add3 (C.E s).bs (neg (sumL (C.E s).rl (fun ec => sclN ec.2 (unit (ec.1 + C.O)))))) C.O) &&
  isZ (msk (mkM C.W C.O C.nv) (add3 (C.bigOf s) (neg (sumL (C.E s).rl (fun ec => sclN ec.2 (C.bS B ec.1))))))

def checkB (D : Nat) (A : List (Poly Nat)) (C : Cert) (B : VT) : Bool :=
  decide (0 < C.N) && rAll (C.okI D) 0 C.N && C.axOk D A && rAll (C.bigOkI B) 0 C.N &&
  rAll (C.mulB B) 0 C.M && decide (C.O ≤ C.u0) &&
  ((C.E 0).bs.1.testBit C.u0 != (C.E 0).bs.2.testBit C.u0)

theorem bS_eq (C : Cert) (B : VT) (e : Nat) (h : C.bigOkI B e = true) : C.bS B e = C.bigOf e := by
  unfold bigOkI at h; unfold bS
  cases hf : B.find e with
  | none => rfl
  | some v => rw [hf] at h; exact of_decide_eq_true h

theorem sumL_congr' {α : Type} (L : List α) (f g : α → V) (h : ∀ a ∈ L, f a = g a) :
    sumL L f = sumL L g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    unfold sumL at *
    simp only [List.foldr_cons]
    rw [h a (List.mem_cons_self ..), ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem mulB_mulI (C : Cert) (B : VT) (hB : rAll (C.bigOkI B) 0 C.N = true) (s : Nat)
    (h : C.mulB B s = true) : C.mulI s = true := by
  unfold mulB at h; unfold mulI
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨h1, h2⟩, ?_⟩
  have e : sumL (C.E s).rl (fun ec => sclN ec.2 (C.bS B ec.1)) =
      sumL (C.E s).rl (fun ec => sclN ec.2 (C.bigOf ec.1)) :=
    sumL_congr' _ _ _ (fun ec he => by rw [C.bS_eq B ec.1 (rAll_spec hB ec.1 (h1 ec he))])
  rw [e] at h3
  exact h3

theorem checkB_check (D : Nat) (A : List (Poly Nat)) (C : Cert) (B : VT) (h : C.checkB D A B = true) :
    C.check D A = true := by
  unfold checkB at h; unfold check
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, rAll_mono (fun s hs => C.mulB_mulI B h3 s hs) h4⟩, h5⟩, h6⟩

theorem soundB (D : Nat) (A : List (Poly Nat)) (C : Cert) (B : VT) (h : C.checkB D A B = true) :
    ¬ PPCRefutation 3 A D :=
  sound D A C (checkB_check D A C B h)

end Cert

end Programme.«20261025-1627-proof-complexity».PCCertF3

#print axioms Programme.«20261025-1627-proof-complexity».PCCertF3.Cert.soundB
