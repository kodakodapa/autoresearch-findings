---
layout: post
title: "From Lean proofs to certified derivations in the ontological embedding"
date: 2026-10-24
scholar: {"citation_title": "From Lean proofs to certified derivations in the ontological embedding", "citation_author": "Kodakodapa", "citation_publication_date": "2026/10/24", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/ontological-proof-translation.html", "citation_keywords": "H", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/ontological-proof-translation/paper.pdf"}
---

## Summary

<!-- owner-summary -->
## Setting

The companion findings on this site give v4 [1] a machine-checked
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
<!-- /owner-summary -->

This result extends:

- C. Benzmüller, "Proofs Without Nominals …", arXiv 2609.36279 v4 (https://arxiv.org/abs/2609.36279):.
- C. Benzmüller, "Gödel's and Scott's Variants … in Lean 4 and TPTP THF", arXiv 2609.26806 v3 (https://arxiv.org/abs/2609.26806): the port the developments build on. It points to 2609.36279 for nominals and the open questions, and has no general-model results.
- C. Benzmüller, "A Comment on Modal Collapse and Ultrafilters", arXiv 2608.07578 (https://arxiv.org/pdf/2608.07578): rigidity of positivity as the driver of collapse. It is background for K1's proviso question and does not address general models.

Our prior-art search (2026-10-23) covered:

- WebFetch: https://arxiv.org/a/benzmuller_c_1 (author listing, 2026 papers), 2026-10-23
- Web pages other than the arXiv listing were seen through search-result summaries only. The Springer and LLP papers were not opened.

The search was run automatically by claude/claude-opus-5-5.

The checkers' full answers, with every query and file they searched, are published with this finding (`prior-art/`).

If you know of related work we missed, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the proof and check files are included so anyone can re-run them.

**K1.** Let $T$ be the $\mathcal L$-sentences Ax1GenR at PosGlobal, Ax4, Ax2a, Ax2b of OpenQuestions.Ax1GenRigidVariant2, read off RigidHF.L_R_hf by the translator. Then $P\,G$ (run 4's Run3.K1.Pos Run3.K1.God) holds at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals.

- Status: proved (axioms: propext, Classical.choice, Quot.sound)
- Machine-checked: no check scripts.
- Prior art: partial prior art

**K3.** Let $T$ be the $\mathcal L$-sentences Ax1GenTwo, $\exists x.\top$, Ax4, Ax3, Ax2a, Ax2b of OpenQuestions.Ax1GenTwoVariant2, read off the module by the translator. Then unrestricted Ax1Gen holds at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals (ValidV4).

- Status: proved (axioms: propext, Classical.choice, Quot.sound)
- Machine-checked: no check scripts.
- Prior art: partial prior art

**K4.** Let $T$ be the $\mathcal L$-sentences Ax1GenTwo, $\exists x.\top$, Ax4, Ax3, Ax2a, Ax2b of OpenQuestions.Ax1GenTwoVariant3Plain, read off the module by the translator. Then unrestricted Ax1Gen holds at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals (ValidV4).

- Status: proved (axioms: propext, Classical.choice, Quot.sound)
- Machine-checked: no check scripts.
- Prior art: partial prior art

**K5.** Let $T$ be the $\mathcal L$-sentences Ax4, Ax3, Ax1GenTwo, Ax2a, Ax2b, $\exists x.\top$ of OpenQuestions.Ax1GenTwoVariant2, read off its proof of MC_Two_unconditional. Then $\forall p{:}\sigma.\,p\to\Box p$ holds at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals.

- Status: analogy: a resemblance, not an established result
- Machine-checked: no check scripts.
- Prior art: unchecked

**K6.** Let $T$ be the $\mathcal L$-sentences Ax4, Ax3, Ax1GenTwo, Ax2a, $\exists x.\top$ of OpenQuestions.Ax1GenTwoVariant2, read off its proofs. Then $\Box\exists^E x.G\,x$ and $\neg\Box\neg\exists^E x.G\,x$ hold at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals.

- Status: analogy: a resemblance, not an established result
- Machine-checked: no check scripts.
- Prior art: unchecked

**K7.** Let $T$ be the $\mathcal L$-sentences Ax3, Ax2a, Ax2b of OpenQuestions.Ax1GenTwoVariant2, read off its proof of Th3. Then $\neg\Box\neg\exists^E x.G\,x\to\Box\exists^E x.G\,x$ holds at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals and symmetric $R$.

- Status: analogy: a resemblance, not an established result
- Machine-checked: no check scripts.
- Prior art: unchecked

**K8.** Let $T$ be the $\mathcal L$-sentences Ax1Gen, Ax2a, Ax2b, Ax4, $\exists x.\top$ of OpenQuestions.GoedelVariantHOML3inS4oneFile (variant 3), read off its proof of MC_K. Then $\forall p{:}\sigma.\,p\to\Box p$ holds at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals.

- Status: analogy: a resemblance, not an established result
- Machine-checked: no check scripts.
- Prior art: unchecked

**K9.** Let $T$ be the $\mathcal L$-sentences Ax1Gen, Ax2a, Ax4, $\exists x.\top$ of OpenQuestions.GoedelVariantHOML3inS4oneFile. In every v4 $\mathcal L$-general model of $T$ with nonempty individuals, on any frame, $\Box\exists^E x.G\,x$ and $\neg\Box\neg\exists^E x.G\,x$ hold at every world.

- Status: analogy: a resemblance, not an established result
- Machine-checked: no check scripts.
- Prior art: unchecked

**K10.** For the $\mathcal L$-sentences $T$ = Ax3, Ax2a, Ax2b and $\varphi$ = Th3 of K7 (Th3K): $\varphi$ is not valid in all v4 $\mathcal L$-general models of $T$ with nonempty individuals whose $R$ is reflexive and transitive; hence also not without frame condition.

- Status: analogy: a resemblance, not an established result
- Machine-checked: no check scripts.
- Prior art: unchecked

**K11.** Let $T$ be Ax4, Ax3, Ax2a, Ax1GenTwo, $\exists x.\top$ of OpenQuestions.Ax1GenTwoVariant3Plain (plus Ax2b for UniqueEss). Then EssMemI_K_unconditional, UniqueEss1_K_unconditional, UniqueEss2_K_unconditional hold at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals.

- Status: analogy: a resemblance, not an established result
- Machine-checked: no check scripts.
- Prior art: unchecked

**K12.** Let $T$ be the $\mathcal L$-sentences Ax3, Ax2a, Ax2b of OpenQuestions.Ax1GenTwoVariant2. Then $\neg\Box\neg\exists^E x.G\,x\to\Box\exists^E x.G\,x$ holds at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals and Euclidean $R$.

- Status: analogy: a resemblance, not an established result
- Machine-checked: no check scripts.
- Prior art: unchecked

**K13.** Let $T$ be Ax1Gen, Ax2a, Ax3, Ax4, $\exists x.\top$ of OpenQuestions.GoedelVariantHOML3inS4oneFile (plus Ax2b for UniqueEss). Then EssMemI_K, UniqueEss1_K, UniqueEss2_K, Ess_iff_Ess2_K hold at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals.

- Status: analogy: a resemblance, not an established result
- Machine-checked: no check scripts.
- Prior art: unchecked

**K14.** Let $T$ = Ax3, Ax2b, Ax2a of OpenQuestions.Ax1GenTwoVariant2 (K7's Th3K) and $\varphi$ = Th3. For every list $F_s$ of frame formulas true on F4 $=\lbrace 01,03,31,12,21\rbrace $, $\varphi$ is not valid in all v4 $\mathcal L$-general models of $T$ with nonempty individuals whose $R$ satisfies $F_s$.

- Status: analogy: a resemblance, not an established result
- Machine-checked: no check scripts.
- Prior art: unchecked

**K15.** For $T$ = Ax3, Ax2b, Ax2a, $\varphi$ = Th3 of Ax1GenTwoVariant2: on any frame $(W,R)$ with $B$ $R$-closed, uniform (all members have successors or none), $b\in B$, $u\notin B$, $Rwb$, $Rwu$, some v4 $\mathcal L$-general model of $T$ on $(W,R)$, nonempty individuals, refutes $\varphi$.

- Status: analogy: a resemblance, not an established result
- Machine-checked: no check scripts.
- Prior art: unchecked

**K16.** Let $T$ = Ax3, Ax2b, Ax2a of OpenQuestions.Ax1GenTwoVariant2. On any frame $(W,R)$ with $Q_L$ (no world outside an $R$-closed $B$ sees a member and a non-member of $B$), $\Diamond\exists^E G\to\Box\exists^E G$ holds everywhere in every v4 $\mathcal L$-general model of $T$ with nonempty individuals.

- Status: analogy: a resemblance, not an established result
- Machine-checked: no check scripts.
- Prior art: unchecked

**K17.** Let $T$ = Ax3, Ax2b, Ax2a of OpenQuestions.Ax1GenTwoVariant2. On any frame $(W,R)$, Th3 holds everywhere in every v4 $\mathcal L$-general model of $T$ with nonempty individuals iff no world outside an $R$-closed set $B$ of all-dead or all-serial worlds sees a member and a non-member of $B$.

- Status: analogy: a resemblance, not an established result
- Machine-checked: no check scripts.
- Prior art: unchecked

## How to verify

Run each script in `claims/ontological-proof-translation/checks/` with `python -I <script>`; it passes if it
exits with status 0. The results recorded in the original run are in
`claims/ontological-proof-translation/results/`; the full claim text is in `claims/ontological-proof-translation/claim.md`.

## Provenance

- run: 20261023-0556
- claims: K1, K3, K4, K5, K6, K7, K8, K9, K10, K11, K12, K13, K14, K15, K16, K17
- run-folder commit: ade4f20858f2a3b683193e13de0d89273d57c4c9
- K1 author: pr (claude)
- K3 author: pr (claude)
- K4 author: pr (claude)
- K5 author: pr (claude)
- K6 author: pr (claude)
- K7 author: pr (claude)
- K8 author: pr (claude)
- K9 author: pr (claude)
- K10 author: pr (claude)
- K11 author: pr (claude)
- K12 author: pr (claude)
- K13 author: pr (claude)
- K14 author: pr (claude)
- K15 author: pr (claude)
- K16 author: pr (claude)
- K17 author: pr (claude)

## References

1. <!-- cite:benzmueller2026nominals --> Benzm\"uller, Christoph. 2026. Proofs Without Nominals: G\"odel's Ontological Argument, its Shallow Embedding, and the Open Questions of the Monatshefte Notes. [Link](https://arxiv.org/abs/2609.36279v4)

<!-- autoresearch:revisions -->
## Revisions

- 2026-10-24 — readable prior-art section
