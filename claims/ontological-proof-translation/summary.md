## Setting

The companion findings on this site give v4 [@benzmueller2026nominals] a machine-checked
semantics: a deep proof calculus, sound and complete over $\mathcal L$-general models. Its
derivations were written by hand. The shallow embedding's Lean proofs are richer than
higher-order logic, which is how a nominal can hide in a proof that v4's detector passes. This
finding builds a Lean command that reads a proof and produces the certified derivation itself.

## Result

- **The translator.** For a theorem of a shallow v4 module whose proof stays within higher-order
  logic (introduction and elimination of the connectives and quantifiers, classical logic,
  `Eq.subst`, `congrArg`, `congrFun`, `funext`, `propext`, beta and eta, unfolding of the
  module's definitions), `#deep_translate X as N` reads the statement and the proof term and
  builds a derivation in the certified calculus, kernel-checked, whose conclusion is the deep
  image of the statement, matched by `rfl`. It also reads off the module's axioms the proof
  uses as an $\mathcal L$-theory $T$, and yields `N.valid`: the statement holds at every world
  of every v4 $\mathcal L$-general model of $T$ with nonempty individuals. A proof outside the
  fragment, or one violating the whole-term condition, is rejected with the first offending
  step named. The rejections are tests the build enforces: v4's own hybrid proof of `L_R`, the
  detector-passing proof with a hidden nominal, and a minimal `congrFun` probe.
- **Applied to v4's proofs.** L under the rigid reading (from the detector-certified proof of
  `L_R`), unrestricted Ax1Gen from Ax1GenTwo in variants 2 and 3′, modal collapse, necessary
  and possible existence of a God-like being, and the essence theorems (`EssMemI`, `UniqueEss1`,
  `UniqueEss2`, `Ess_iff_Ess2`) in variant 2, 3′ and in v4's S4 module of variant 3, each now as
  a semantic theorem over $\mathcal L$-general models.
- **The frame condition for Th3.** For Th3 ($\Diamond\exists^E G\to\Box\exists^E G$) from Ax2a,
  Ax2b and Ax3 in variant 2, translation gives validity on symmetric and on Euclidean frames.
  Reflexive and transitive frames do not suffice, nor does any set of frame formulas true on a
  fixed five-edge frame. The exact condition: Th3 holds everywhere in every $\mathcal L$-general
  model on $(W,R)$ iff no world outside an $R$-closed set $B$ of all-dead or all-serial worlds
  sees both a member and a non-member of $B$.

## Why it matters

A detector certifies a proof only as far as the detector reads it correctly. The translator
replaces that trust with a kernel-checked derivation and the calculus's soundness theorem, and
it turns v4's Lean proofs into statements about v4's semantics without rewriting them by hand.
The Th3 result shows what the semantics adds: an exact frame condition, where the shallow
embedding only gives sufficient ones.

## Proved vs checked

Everything is Lean 4 (core library, axioms propext, Classical.choice and Quot.sound only) and is
kernel-checked in the library build. The run's skeptic verified the translator's first three
results (L under the rigid reading; the equivalence in variants 2 and 3′); the remaining
thirteen claims carry the status *analogy*, because the run ended before its skeptic checked
them. We rebuilt six of them outside the run and checked their axioms: the symmetric-frame result,
the reflexive–transitive and five-edge counterexamples, the general countermodel construction,
the sufficiency direction, and the exact condition.
