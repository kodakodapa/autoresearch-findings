import Programme.«20261025-0459-proof-complexity».OntoSubst

/-!
# Edge restriction of onto-FPHP

`gσ emap` sends variable `v` to the compact variable `e` when `emap[v] = e + 1` and to `false`
when `emap[v] = 0` (an edge deleted). `gAx emap n k` is onto-FPHP^{n+k}_n pulled through it: the
onto pigeonhole principle on the bipartite graph of kept edges. A degree-`D` refutation of
onto-FPHP gives one of `gAx` (`PPCDerivable.subst`), so a lower bound for the graph instance is
one for onto-FPHP.
-/

namespace Programme.«20261026-1402-proof-complexity».GraphSubst

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst

def gσ (emap : List Nat) : Nat → Lit := fun v =>
  match emap.getD v 0 with
  | 0 => .const false
  | e + 1 => .var e

def gAx (emap : List Nat) (n k : Nat) : List (Poly Nat) :=
  (ontoFPHP n k).map (Poly.subst (gσ emap))

theorem lower_of_graph (p n k D : Nat) (emap : List Nat) (hD : 1 ≤ D) (hnk : 0 < n + k)
    (h : ¬ PPCRefutation p (gAx emap n k) D) : ¬ PPCRefutation p (ontoFPHP n k) D := by
  intro hR
  apply h
  have hmem : ∀ P ∈ ontoFPHP n k, Poly.subst (gσ emap) P ∈ gAx emap n k :=
    fun P hP => List.mem_map.mpr ⟨P, hP, rfl⟩
  have hA : ∀ P ∈ ontoFPHP n k, P.deg ≤ D →
      PPCDerivable p (gAx emap n k) D (fun a => P.eval (pull (gσ emap) a)) := by
    intro P hP hd
    have := PPCDerivable.ax (p := p) _ (hmem P hP) (Nat.le_trans (subst_deg _ P) hd)
    exact PPCDerivable.congr _ _ this (fun a => ⟨0, by rw [subst_eval]; omega⟩)
  have h0 := (mem_pig (n := n) (k := k) (i := 0) hnk)
  have hz : PPCDerivable p (gAx emap n k) D (fun _ => 0) := by
    have hd : (sumOne (fun j => var n 0 j) n).deg ≤ D := by
      exact Nat.le_trans (sumOne_deg _ _) hD
    have := hA _ h0 hd
    exact PPCDerivable.congr _ _ (PPCDerivable.lin _ _ 0 0 this this) (fun a => ⟨0, by simp⟩)
  have := PPCDerivable.subst (gσ emap) hz hA hR
  exact this

end Programme.«20261026-1402-proof-complexity».GraphSubst

#print axioms Programme.«20261026-1402-proof-complexity».GraphSubst.lower_of_graph
