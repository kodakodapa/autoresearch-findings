## Setting

Benzmüller's *Proofs Without Nominals* [@benzmueller2026nominals] (v4) judges proofs in the
shallow embedding of higher-order modal logic against $\mathcal L$-*general models*: Henkin-style
models whose carriers are closed under the terms of the modal object language $\mathcal L$. Its
Proposition prop:lgeneral gives soundness over these models for proofs meeting a *whole-term*
condition; its Example ex:separating gives a sentence of $\mathcal L$,
$\mathsf A\exists p.(\mathsf{Atom}\,p\wedge p)$, that the embedding proves but the condition
excludes, formalised in its propositional part only. v4 leaves open whether its weaker *witness
criterion* alone implies the condition, and whether a separating model exists for any of its
axiom sets. This finding makes that semantics machine-checked.

## Result

- **A sound and complete calculus.** A deep natural-deduction calculus for the embedding's
  higher-order logic, with ∀E/∃I instances restricted to $\mathcal L$-terms and Leibniz
  substitution at every type of $\mathcal L$, is sound over v4's $\mathcal L$-general models
  with nonempty individuals, and complete: for every $\mathcal L$-theory $T$ and sentence
  $\varphi$, $\varphi$ holds in all such models of $T$ exactly when the calculus derives it from
  $T\cup\{\exists x.\top\}$. Löwenheim–Skolem and compactness follow: for theories containing
  $\exists x.\top$, a failure has a countermodel with countably many worlds and countable
  carriers, and every consequence follows from a finite sub-theory.
- **prop:lgeneral in deep form.** Leibniz with whole-term motives and $\mathcal L$-term sides
  derives the same sentences, and unrestricted Leibniz derives the separating sentence from any
  theory, so the motive clause is what keeps the calculus sound.
- **ex:separating at all types.** v4's flip model (total frame on $2^{\mathbb N}$, one
  individual, empty positivity) is $\mathcal L$-general at every type of $\mathcal L$ and refutes
  the separating sentence at every world. A model of variant 2 (Ax1Gen, Ax2a, Ax2b, Ax3, Ax4),
  with modal collapse and a God-like being, also refutes it at every world: a separating model
  for one of v4's axiom sets. With finitely many worlds the sentence always holds, so such a
  model needs infinitely many.
- **The equivalence, semantically.** In every $\mathcal L$-general model of variant 2 or 3′
  (Ax2a, Ax2b, $P\,E$, Ax4, $\exists x.\top$), Ax1GenTwo holds everywhere exactly when
  unrestricted Ax1Gen does, and then modal collapse and a God-like being follow (in variant 2
  with Ax3).
- **The witness criterion does not suffice in practice.** A Lean proof of the separating
  sentence in v4's own `Ax1GenTwoVariant2` module, which uses the nominal $\lambda u.\,u=w$ only
  as an argument of `congrFun`, passes v4's `hybrid_check.py` with no flags in both witness and
  whole-term mode. The sentence fails in the variant-2 model above, so the detector certifies a
  proof of a sentence that is not a consequence over $\mathcal L$-general models.

## Prior work

Soundness over $\mathcal L$-general models for whole-term proofs is v4's Proposition
prop:lgeneral, proved there in prose; here it is a Lean theorem about an explicit calculus. The
separating sentence is in substance the world-proposition axiom of Fine and Kaplan
[@fine1970propositional]: some true proposition entails every truth. Its failure in atomless
algebras is known for S5 with propositional quantifiers [@holliday2019note], finite-support
(Fraenkel–Mostowski) constructions of Henkin models are standard [@gabbay2011nominal], and
compactness and Löwenheim–Skolem for intensional general models follow Muskens's pattern
[@muskens2007intensional]. Existing completeness theorems for the embedding are relative to
Henkin models [@benzmueller2013quantified], whose domains contain every singleton, so they are
not $\mathcal L$-general. We found no statement of completeness over $\mathcal L$-general
models, of a separating model for one of v4's axiom sets, or of the detector result.

## Why it matters

The first four items settle, inside Lean, the semantic question v4 states as open, and they
give the detector-certified proofs on this site a meaning: a whole-term proof is true in every
$\mathcal L$-general model. The last item shows that the detector's implementation can miss a
nominal hidden in a motive, which is the case v4's open question asks about. It does not refute
Proposition prop:lgeneral, which holds; it shows that certifying proofs with the detector is
not yet a substitute for the semantic proof.

## Proved vs checked

Every claim except the detector result is a Lean 4 theorem (core library, axioms propext,
Classical.choice and Quot.sound only), kernel-checked in the library build. The detector result
is a Lean proof plus a run of v4's `hybrid_check.py` on it; the run's skeptic found it and we
reproduced it outside the run. Its status is *derived* because the detector run is a check, not
a Lean theorem.
