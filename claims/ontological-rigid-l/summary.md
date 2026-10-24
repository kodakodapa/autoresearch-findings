## Setting

Gödel's lemma L says that a God-like being's property $G$ is positive, $P\,G$. In
Benzmüller's *Proofs Without Nominals* [@benzmueller2026nominals] (v4, sec:rigid), the
conjunction axiom Ax1Gen is read *rigidly*: it applies only to sets of properties given by
conditions formed in the object language $\mathcal L$, so Ax1GenR is a schema over
$\mathcal L$-conditions. v4 asks whether L follows under this reading with no condition on
positivity. The finding *Nominal-free proofs* on this site gives a detector-certified proof in
v4's module `Ax1GenRigidVariant2`; this one proves the statement over v4's semantics.

## Result

- **L under the rigid reading.** In every v4 $\mathcal L$-general model with nonempty
  individuals where the variant-2 axioms Ax2a, Ax2b, Ax4 and the instance of Ax1GenR for the
  set of globally positive properties $\{\psi \mid P\psi=\top\}$ hold at every world, $P\,G$
  holds at every world. The proof is a derivation in the certified deep calculus of the
  companion finding, so it holds by that calculus's soundness theorem, with the deep axioms
  matched clause by clause to the Lean module.
- **The schema reading is faithful.** In the full structure on any frame, actuality and
  positivity, if the rigid Ax1GenR holds for every set of properties then every deep instance
  $\mathrm{Ax1GenR}\,c$, for $c$ a rigid $\mathcal L$-condition (equations under connectives
  and carrier quantifiers), holds at every world.
- **The instance is needed.** Ax2a, Ax2b and Ax4 alone do not give $P\,G$: in a full S5 model
  with three worlds and one entity, where $P\varphi$ holds iff $\varphi$ holds of the entity at
  two or more worlds, they hold while $P\,G$ and the Ax1GenR instance fail at every world.

## Prior work

v4 derives L under the rigid reading in two ways: through a hybrid witness that its detector
flags, and from the rigidly positive properties under a proviso that it shows does not follow
from the axioms (`L_R_rigidpos`). The result here needs neither. The faithfulness lemma follows
the deep–shallow method of Benzmüller and Kirchner for other logics.

## Why it matters

This answers v4's rigid-reading question semantically and with no condition on positivity: the
one instance of the schema at the globally positive properties is enough, and without it the
other axioms do not suffice.

## Proved vs checked

The first two claims are Lean 4 theorems (core library, axioms propext, Classical.choice and
Quot.sound only), kernel-checked in the library build. The third is an explicit finite model,
checked by a script (`checks/K2-lr_instance_needed.py`, re-run at publication) and re-derived by
the run's skeptic, but not in Lean; its status is *derived*.
