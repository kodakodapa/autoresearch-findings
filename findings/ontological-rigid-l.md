---
layout: default
title: "G\u00f6del's lemma L under the rigid reading, with no condition on positivity"
scholar: {"citation_title": "G\u00f6del's lemma L under the rigid reading, with no condition on positivity", "citation_author": "Lindheim, Bj\u00f6rn", "citation_publication_date": "2026/10/24", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/ontological-rigid-l.html", "citation_keywords": "G", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/ontological-rigid-l/paper.pdf", "citation_doi": "10.5281/zenodo.23795777"}
---

# Gödel's lemma L under the rigid reading, with no condition on positivity

Cite as: https://doi.org/10.5281/zenodo.23795777

<!-- owner-summary -->
## Setting

Gödel's lemma L says that a God-like being's property $G$ is positive, $P\,G$. In
Benzmüller's *Proofs Without Nominals* [1] (v4, sec:rigid), the
conjunction axiom Ax1Gen is read *rigidly*: it applies only to sets of properties given by
conditions formed in the object language $\mathcal L$, so Ax1GenR is a schema over
$\mathcal L$-conditions. v4 asks whether L follows under this reading with no condition on
positivity. The finding *Nominal-free proofs* on this site gives a detector-certified proof in
v4's module `Ax1GenRigidVariant2`; this one proves the statement over v4's semantics.

## Result

- **L under the rigid reading.** In every v4 $\mathcal L$-general model with nonempty
  individuals where the variant-2 axioms Ax2a, Ax2b, Ax4 and the instance of Ax1GenR for the
  set of globally positive properties $\lbrace \psi \mid P\psi=\top\rbrace $ hold at every world, $P\,G$
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
<!-- /owner-summary -->

This result extends:

- Benzmüller, "Proofs Without Nominals", arXiv 2609.36279 v4, §sec:rigid: Ax1GenR. It has L_R in K from Ax2a and Ax2b via the hybrid witness @_w P. L_R_rigidpos derives L from {ψ ∣ A(Pψ)} only under rigid positivity. It leaves open the case without that condition, which is the case K1 addresses. prop:lgeneral gives shallow soundness over 𝓛-general models.
- Benzmüller & Scott, Notes (Monatshefte 2025), and Benzmüller, arXiv 2609.26806: L (P G) from the world-dependent Ax1Gen, by the instance Φ = P.
- Kanckos & Woltzenlogel Paleo, "Variants of Gödel's Ontological Proof in a Natural Deduction Calculus", Studia Logica 105 (2017): explicit derivations in a rigid higher-order modal logic, but with P G (A3) as an axiom, not derived from a conjunction schema.
- Benzmüller & Woltzenlogel Paleo, arXiv 1308.4526: says A3 is derivable from Axiom 1 and D1 given infinitary conjunction. This is an informal remark, with no rigid schema and no general-model semantics.
- Benzmüller, "Proofs Without Nominals", arXiv 2609.36279 (sources/2609.36279/v4/main.tex): defines rigid L-conditions (def:hybridfree) and Ax1GenR (sec:rigid). Instantiates Ax1GenR with the L-condition {ψ ∣ A(Pos ψ)} in the shallow embedding (`L_R_rigidpos`). Gives soundness over L-general and standard models (prop:lgeneral). Deep embedding only for the propositional part (Separation). No general deep-instance lemma.
- Benzmüller & Kirchner, "Monadic Second-Order Logic in HOL: Deep and Shallow with Automated Faithfulness", arXiv 2609.07345 / AFP MSOinHOL: deep↔shallow faithfulness for MSO under standard (full) and Henkin readings, with comprehension. Same mechanism as K3, different logic.
- Benzmüller & Kirchner, "First-Order Modal Logic in HOL…", arXiv 2607.10880: deep↔shallow faithfulness for first-order modal logic only (no quantification over properties or sets of properties).
- Benzmüller, "Faithful Logic Embeddings in HOL — Deep and Shallow", arXiv 2502.19311 (CADE-30): the same for propositional modal logic.
- Benzmüller, "A Comment on Modal Collapse and Ultrafilters", arXiv 2608.07578: names a deep embedding of higher-order modal logic as the natural setting for definability questions, i.e. future work.
- drewarrowood/godel-ontological PR #1 (GitHub): tests a rigid-Φ repair of Ax1Gen in Lean through countermodels. Nothing on deep instances.

Our prior-art search (2026-10-23) covered:

- https://arxiv.org/abs/2609.36279 (versions v1–v4; v4 dated 2026-10-14 is latest), 2026-10-23

The search was run automatically by claude/claude-opus-5-5.

The checkers' full answers, with every query and file they searched, are published with this finding (`prior-art/`).

If you know of related work we missed, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was partly proved in Lean (claims K1, K3) and partly checked by script (claims K2); the proof and check files are included so anyone can re-run them.

## K1

In every v4 $\mathcal L$-general model with nonempty individuals where variant-2 Ax2a, Ax2b, Ax4 and the rigid-schema instance $\mathrm{Ax1GenR}$ for $\lbrace \psi\mid P\psi=\top\rbrace $ hold at every world, $P\,G$ holds at every world, via a certified deep derivation (DC, of_DC, sound_v4_wt).

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K1-RigidDeep.lean`: Programme.Run5.G.RigidDeep.l\_r\_semantic — pass (`results/K1-1.json`)
- proof `checks/K1-RigidDeep.lean`: Programme.Run5.G.RigidDeep.l\_r\_valid — pass (`results/K1-2.json`)

Prior art: partial prior art (answer: `prior-art/R1.md`)

### Provenance

- run: 20261023-0519
- claim: K1
- author: pr (claude)
- round: 1
- run-folder commit: 2e2df987b9201fdce33786411f4136a4bc241629
- check results: K1-1.json, K1-2.json

## K3

In the full structure on any frame, actuality and positivity: if the rigid $\mathrm{Ax1GenR}$ holds for every set $\Phi$ of properties, then for every rigid $\mathcal L$-condition $c$ (equations under connectives and carrier quantifiers) the deep instance $\mathrm{Ax1GenR}\,c$ holds at every world.

Status: proved (axioms: propext, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K1-RigidDeep.lean`: Programme.Run5.G.RigidMatch.genR\_sound\_full — pass (`results/K3-1.json`)

Prior art: partial prior art (answer: `prior-art/R2.md`)

### Provenance

- run: 20261023-0519
- claim: K3
- author: pr (claude)
- round: 3
- run-folder commit: 2e2df987b9201fdce33786411f4136a4bc241629
- check results: K3-1.json

## K2

Variant-2 Ax2a, Ax2b, Ax4 do not derive $P\,G$: a full S5 model with 3 worlds, one always-actual entity and $P\varphi$ iff $\varphi a$ holds at $\ge 2$ worlds satisfies them, while $P\,G$ and the $\mathrm{Ax1GenR}$ instance for $\lbrace \psi\mid P\psi=\top\rbrace $ fail at every world.

Status: derived · independently re-derived (skeptic/claude)

Kind: model

Evidence:
- check `checks/K2-lr_instance_needed.py`: In the 3-world S5 majority model Ax2a, Ax2b, Ax4 hold, P G fails at every world and the Ax1GenR(PosGlobal) instance fails; a one-world model satisfies TR with P G; every full model with \|W\|\<=2, \|D\|=1 satisfying TR has P G everywhere. — pass (`results/K2-1.json`)

Prior art: unchecked

### Provenance

- run: 20261023-0519
- claim: K2
- author: pr (claude)
- round: 2
- run-folder commit: 2e2df987b9201fdce33786411f4136a4bc241629
- check results: K2-1.json

## References

1. <!-- cite:benzmueller2026nominals --> Benzm\"uller, Christoph. 2026. Proofs Without Nominals: G\"odel's Ontological Argument, its Shallow Embedding, and the Open Questions of the Monatshefte Notes. [Link](https://arxiv.org/abs/2609.36279v4)

<!-- autoresearch:revisions -->
## Revisions

- 2026-10-24 — readable prior-art section
- 2026-10-24 — K2 checked by script; table glitch
