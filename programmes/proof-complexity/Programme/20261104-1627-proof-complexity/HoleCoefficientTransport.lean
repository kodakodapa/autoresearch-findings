import Programme.«20261104-1627-proof-complexity».HoleCodeTransport
namespace Programme.«20261104-1627-proof-complexity».HoleCoefficientTransport
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261024-1633-proof-complexity».NS
 theorem map_perm_iff {f : Nat → Nat} (hf : Function.Injective f)
    (s t : List Nat) : (s.map f).Perm (t.map f) ↔ s.Perm t := by
  constructor
  · intro hp
    classical
    let g : Nat → Nat := fun y => if hy : ∃ x, f x = y then Classical.choose hy else 0
    have hg (x : Nat) : g (f x) = x := by
      have hx : ∃ z, f z = f x := ⟨x, rfl⟩
      simp only [g, dif_pos hx]
      exact hf (Classical.choose_spec hx)
    have h := hp.map g
    simpa [List.map_map, Function.comp_def, hg] using h
  · exact List.Perm.map f
 def rename (f : Nat → Nat) (P : Poly Nat) : Poly Nat :=
   ⟨P.terms.map fun t => (t.1, t.2.map f)⟩
 theorem coeff_rename {f : Nat → Nat} (hf : Function.Injective f)
    (P : Poly Nat) (u : List Nat) :
    coeff (rename f P) (u.map f) = coeff P u := by
  unfold coeff cf rename
  induction P.terms with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.filter_cons]
    simp only [map_perm_iff hf]
    split <;> simp_all
 theorem coeff_push {n h : Nat} (hn : 0 < n) (P : Poly Nat)
    (M : Matching) (hb : ∀ e ∈ M, e.2 < n) :
    coeff (rename (pushCode n h) P) (mono (n+1) (pushMatching h M)) =
      coeff P (mono n M) := by
  rw [mono_push hn h M hb]
  exact coeff_rename (Programme.«20261104-1627-proof-complexity».HoleCodeTransport.pushCode_injective hn) P _
end Programme.«20261104-1627-proof-complexity».HoleCoefficientTransport
#print axioms Programme.«20261104-1627-proof-complexity».HoleCoefficientTransport.coeff_push
