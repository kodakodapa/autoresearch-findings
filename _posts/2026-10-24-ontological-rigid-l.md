---
layout: post
title: "G\u00f6del's lemma L under the rigid reading, with no condition on positivity"
date: 2026-10-24
scholar: {"citation_title": "G\u00f6del's lemma L under the rigid reading, with no condition on positivity", "citation_author": "Kodakodapa", "citation_publication_date": "2026/10/24", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/ontological-rigid-l.html", "citation_keywords": "G", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/ontological-rigid-l/paper.pdf"}
---

## Summary

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
Quot.sound only), kernel-checked in the library build. The third rests on an explicit finite model
that the run checked by argument, not in Lean; its status is *derived*.
<!-- /owner-summary -->

This result extends Benzmüller, "Proofs Without Nominals", arXiv 2609.36279 v4, §sec:rigid: Ax1GenR. It has L_R in K from Ax2a and Ax2b via the hybrid witness @_w P. L_R_rigidpos derives L from {ψ | A(Pψ)} only under rigid positivity. It leaves open the case without that condition, which is the case K1 addresses. prop:lgeneral gives shallow soundness over 𝓛-general models; Benzmüller & Scott, Notes (Monatshefte 2025), and Benzmüller, arXiv 2609.26806: L (P G) from the world-dependent Ax1Gen, by the instance Φ = P; Kanckos & Woltzenlogel Paleo, "Variants of Gödel's Ontological Proof in a Natural Deduction Calculus", Studia Logica 105 (2017): explicit derivations in a rigid higher-order modal logic, but with P G (A3) as an axiom, not derived from a conjunction schema; Benzmüller & Woltzenlogel Paleo, arXiv 1308.4526: says A3 is derivable from Axiom 1 and D1 given infinitary conjunction. This is an informal remark, with no rigid schema and no general-model semantics; Benzmüller, "Proofs Without Nominals", arXiv 2609.36279 (sources/2609.36279/v4/main.tex): defines rigid L-conditions (def:hybridfree) and Ax1GenR (sec:rigid). Instantiates Ax1GenR with the L-condition {ψ | A(Pos ψ)} in the shallow embedding (`L_R_rigidpos`). Gives soundness over L-general and standard models (prop:lgeneral). Deep embedding only for the propositional part (Separation). No general deep-instance lemma; Benzmüller & Kirchner, "Monadic Second-Order Logic in HOL: Deep and Shallow with Automated Faithfulness", arXiv 2609.07345 / AFP MSOinHOL: deep↔shallow faithfulness for MSO under standard (full) and Henkin readings, with comprehension. Same mechanism as K3, different logic; Benzmüller & Kirchner, "First-Order Modal Logic in HOL…", arXiv 2607.10880: deep↔shallow faithfulness for first-order modal logic only (no quantification over properties or sets of properties); Benzmüller, "Faithful Logic Embeddings in HOL — Deep and Shallow", arXiv 2502.19311 (CADE-30): the same for propositional modal logic; Benzmüller, "A Comment on Modal Collapse and Ultrafilters", arXiv 2608.07578: names a deep embedding of higher-order modal logic as the natural setting for definability questions, i.e. future work; drewarrowood/godel-ontological PR #1 (GitHub): tests a rigid-Φ repair of Ax1Gen in Lean through countermodels. Nothing on deep instances. Our prior-art search (2026-10-23) covered:

- sources/2609.36279/v4/main.tex (sec:rigid, sec:criterion, def:lgeneral, prop:lgeneral, sec:criterion-open, open questions), read 2026-10-23
- sources/2609.26806/v1 and v3 (main.tex, lean.tex, tab-frames.tex), grep for Ax1Gen/rigid/general model, 2026-10-23
- https://arxiv.org/abs/2609.36279 (versions v1–v4; v4 dated 2026-10-14 is latest), 2026-10-23
- WebSearch: "\"Ax1Gen\" rigid positive properties God-like positive ontological argument", 2026-10-23
- WebSearch: "Gödel ontological \"any number of summands\" conjunction positive properties \"positivity of being God-like\" derived without axiom", 2026-10-23
- WebSearch: "Kanckos Paleo rigid higher-order modal logic ontological proof natural deduction God-like positive", 2026-10-23
- WebSearch: "ontological argument \"general models\" deep embedding derivation \"positive\" God-like rigid conjunction axiom Lean 2026", 2026-10-23
- Results seen in search listings only, not opened: arXiv 2608.07578, 2001.04701, 1308.4526, 1910.08955, 2605.27246; Springer 10.1007/s00605-025-02078-x, 10.1007/s11787-026-00409-6; GitHub drewarrowood/godel-ontological, alozanoroble/godel-ontological-lean
- Local: sources/2609.36279/v4/main.tex (sec:criterion, def:hybridfree, prop:sound, sec:rigid, def:lgeneral, prop:lgeneral, ex:separating), anc/OpenQuestions/README.md, anc/OpenQuestions/lean/OpenQuestions/Ax1GenRigidVariant2.lean, 2026-10-23
- Local: sources/2609.26806/v1 and v3 (grep for Ax1Gen/Ax1GenR in main.tex, lean.tex, anc/Notes), 2026-10-23
- Web search (search-engine results only; no pages opened): "deep embedding shallow embedding higher-order modal logic faithfulness comprehension instance ontological argument", 2026-10-23
- Web search: "rigid set of properties conjunction axiom Gödel ontological argument Ax1Gen rigid", 2026-10-23
- Web search: "Henkin general models higher-order modal logic comprehension schema standard model full structure deep shallow agreement Benzmüller", 2026-10-23
- Result URLs seen: https://arxiv.org/html/2609.36279v2 ; https://arxiv.org/html/2608.07578 ; https://arxiv.org/pdf/2607.10880 ; https://arxiv.org/abs/2609.07345 ; https://isa-afp.org/browser_info/current/AFP/MSOinHOL/outline.pdf ; https://arxiv.org/pdf/2502.19311 ; https://isa-afp.org/browser_info/current/AFP/FaithfulPMLinHOL/outline.pdf ; https://github.com/drewarrowood/godel-ontological/pull/1 ; https://link.springer.com/article/10.1007/s00605-025-02078-x ; https://www.researchgate.net/publication/38338872_Higher-Order_Semantics_and_Extensionality ; https://philarchive.org/archive/MUSHOM (all 2026-10-23)

The search was run automatically by claude/claude-opus-5-5.

If you know of related work we missed, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was partly proved in Lean (claims K1, K3) and partly checked by script (claims K2); the proof and check files are included so anyone can re-run them.

**K1.** In every v4 $\mathcal L$-general model with nonempty individuals where variant-2 Ax2a, Ax2b, Ax4 and the rigid-schema instance $\mathrm{Ax1GenR}$ for $\{\psi\mid P\psi=\top\}$ hold at every world, $P\,G$ holds at every world, via a certified deep derivation (DC, of_DC, sound_v4_wt).

- Status: proved (axioms: propext, Classical.choice, Quot.sound)
- Machine-checked: no check scripts.
- Prior art: partial prior art

**K3.** In the full structure on any frame, actuality and positivity: if the rigid $\mathrm{Ax1GenR}$ holds for every set $\Phi$ of properties, then for every rigid $\mathcal L$-condition $c$ (equations under connectives and carrier quantifiers) the deep instance $\mathrm{Ax1GenR}\,c$ holds at every world.

- Status: proved (axioms: propext, Quot.sound)
- Machine-checked: no check scripts.
- Prior art: partial prior art

**K2.** Variant-2 Ax2a, Ax2b, Ax4 do not derive $P\,G$: a full S5 model with 3 worlds, one always-actual entity and $P\varphi$ iff $\varphi a$ holds at $\ge 2$ worlds satisfies them, while $P\,G$ and the $\mathrm{Ax1GenR}$ instance for $\{\psi\mid P\psi=\top\}$ fail at every world.

- Status: derived · independently re-derived (sk/claude)
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: unchecked

## How to verify

Run each script in `claims/ontological-rigid-l/checks/` with `python -I <script>`; it passes if it
exits with status 0. The results recorded in the original run are in
`claims/ontological-rigid-l/results/`; the full claim text is in `claims/ontological-rigid-l/claim.md`.

## Provenance

- run: 20261023-0519
- claims: K1, K3, K2
- run-folder commit: 2e2df987b9201fdce33786411f4136a4bc241629
- K1 author: pr (claude)
- K3 author: pr (claude)
- K2 author: pr (claude)

## References

1. <!-- cite:benzmueller2026nominals --> Benzm\"uller, Christoph. 2026. Proofs Without Nominals: G\"odel's Ontological Argument, its Shallow Embedding, and the Open Questions of the Monatshefte Notes. [Link](https://arxiv.org/abs/2609.36279v4)
