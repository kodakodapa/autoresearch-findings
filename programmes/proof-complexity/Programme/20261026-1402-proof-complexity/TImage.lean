import Programme.«20261026-1402-proof-complexity».Relabel
import Programme.«20261026-1402-proof-complexity».TExt

/-!
# Every pigeon/hole relabelling of `T` (K32) has a level-2 extension over `Z/2`

`T` is the indicator of 2-matchings inside the `3 × 3` block; K31 spans the zero-link part with
rectangle products and the `S_P × S_H` images of `T`. `t_image_ext` gives each image an extension.
-/

namespace Programme.«20261026-1402-proof-complexity».TImage

open Programme.«20261026-1402-proof-complexity».ExtLemma Programme.«20261026-1402-proof-complexity».Relabel

theorem t_image_ext {n k : Nat} (hn : 4 ≤ n) (hk : (2 : Int) ∣ k) (σ : Perm (n + k)) (τ : Perm n) :
    Bal 2 n k (relab σ τ (Programme.«20261026-1402-proof-complexity».TExt.Y n)) (relab σ τ (Programme.«20261026-1402-proof-complexity».TExt.T n)) 2 :=
  bal_relab σ τ (Programme.«20261026-1402-proof-complexity».TExt.t_ext hn hk)

end Programme.«20261026-1402-proof-complexity».TImage

#print axioms Programme.«20261026-1402-proof-complexity».TImage.t_image_ext
