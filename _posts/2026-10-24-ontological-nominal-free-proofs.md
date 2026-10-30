---
layout: post
title: "Nominal-free proofs of the theorems Benzm\u00fcller's detector flags"
date: 2026-10-24
scholar: {"citation_title": "Nominal-free proofs of the theorems Benzm\u00fcller's detector flags", "citation_author": "Lindheim, Bj\u00f6rn", "citation_publication_date": "2026/10/24", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/ontological-nominal-free-proofs.html", "citation_keywords": "*", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/ontological-nominal-free-proofs/paper.pdf", "citation_doi": "10.5281/zenodo.23795772"}
---

## Summary

Cite as: https://doi.org/10.5281/zenodo.23795772

<!-- owner-summary -->
## Setting

Benzmüller and Scott's *Notes* prove variants of Gödel's ontological argument in a shallow
embedding of higher-order modal logic in classical higher-order logic [1].
Benzmüller's *Proofs Without Nominals* [2] (v4) points out that the
embedding's quantifiers also range over *nominals*, properties like $\lambda u.\,u = w$ that pick
out a single world. A proof that substitutes one proves a theorem of the embedding but not
necessarily of the modal object language $\mathcal L$. v4 ships a detector that flags such
"hybrid" proofs in two modes (witness and whole-term), and lists the theorems of its Lean
modules it could only prove with a flagged step, among them two of its stated open questions:
whether the equivalence of the restricted conjunction axiom Ax1GenTwo with the unrestricted
Ax1Gen has a nominal-free proof in variants 2 and 3′, and whether Gödel's lemma L follows under
the rigid reading Ax1GenR with no condition on positivity.

## Result

For each flagged theorem below we give a new proof of the *identical* statement, from the same
module's definitions, that v4's own detector passes in both modes (full names):

- **The equivalence question:** `Ax1Gen_of_Two` and `Two_equivalent`, with `P_of_conj`,
  `loc_of_conj` and the related lemmas, in `Ax1GenTwoVariant2` and `Ax1GenTwoVariant3Plain`
  (logic K).
- **The rigid question:** `L_R` in `Ax1GenRigidVariant2`, from Ax2a, Ax2b and Ax4 only, with
  witness `PosGlobal` and no condition on positivity.
- **Further flagged theorems:** modal collapse and Th5 in `Ax1GenBoxVariant3` (the reflexivity
  hypothesis unused); fourteen theorems of `GoedelVariantHOML3inS4oneFile` without `Rrefl` or
  `Rtrans`; the one-conjunct theorems of `Ax1GenOneVariant3`; collapse and the existence
  theorems of `Ax1GenTwoVariant3` and `Ax1GenTwoVariant3Th4`; `AllExist` and `MC_OneWorld` of
  `Ax1GenTwoVariant3Plain`; and collapse in its possibilist and Anderson-quantifier versions.
- **A model:** on two worlds with one always-actual entity and a universal frame, Ax1, Ax2a,
  Ax2b, Ax3, both forms of Ax4, Ax1Gen with its Two, One and Box restrictions, and Th4 hold, and necessary
  existence holds at both worlds, so `NoNecExist` fails there; and an
  abstract Henkin lemma describing what Ax1GenR forces over admitted rigid families.

## What is new

v4 already has nominal-free proofs of two of the lemmas listed first (`ae_Two` and
`G_ex_Two_unconditional`, under those names), and frame-free `_K` versions of most theorems of
`GoedelVariantHOML3inS4oneFile`; what this finding adds there are proofs under the original names
that the detector passes, and nominal-free routes to `EssSupp`, `EssDetermined` and `AllExist`.
The new results are the equivalence lemmas, which v4 proves only through the nominal arguments
`OneWorld` and `R_Id` and lists as open, and `L_R` with no condition on positivity, also listed
as open. v4's text and its Lean module disagree on whether the detector flags the witness of its
own `L_R` proof; ours passes either way.

## Why it matters

v4 asks whether these results are theorems of the modal logic or only of its embedding. A
detector-certified proof answers that for every proof the detector reads correctly. The
companion findings on this site make the answer semantic: a complete calculus over v4's
$\mathcal L$-general models, the equivalence and L under the rigid reading proved in every such
model, and a hole in the detector that shows why the semantic proofs are needed.

## Proved vs checked

Every proof is Lean 4 (core library, axioms propext, Classical.choice and Quot.sound only),
built in v4's own modules, and was run through v4's `hybrid_check.py` in witness and whole-term
mode with full-name matching. One further claim of the run (a Henkin-model version of the
equivalence over eleven listed closure terms) was disputed by the run's skeptic and is left out.
<!-- /owner-summary -->

This result extends:

- C. Benzmüller, "Proofs Without Nominals", arXiv 2609.36279v4, https://arxiv.org/abs/2609.36279: gives detector-certified proofs `ae_Two` and `G_ex_Two_unconditional` of the same statements as `ae_Two_nominal` and `G_ex_Two_unconditional_nominal`, in both modules. `only_top_and_empty_domain(_False)` follows directly from `ae_Two`, though v4 proves it only through the flagged `OneWorld`. v4 proves Ax1Gen_of_Two, Two_equivalent, P_of_conj and loc_of_conj only through the nominal steps OneWorld/R_Id (flagged), and lists their hybrid-free status as open (sec:plain, sec:open).
- C. Benzmüller, "Proofs Without Nominals", arXiv 2609.36279 v4 (sources/2609.36279/v4): proves every statement in K3–K8 and K12 under the same names, but with nominal or actuality witnesses that its detector flags (audit/report.txt). It states that the hybrid-free versions are open for the Ax1GenOne variant 3 and for dropping (†) (§sec:one, §sec:open). Example ex:separating and Separation.lean give a flip-invariant separating model for the empty theory, which is the same technique K11 uses, applied to a different theory.
- C. Benzmüller, "Gödel's and Scott's Variants … in Lean 4 and TPTP THF", arXiv 2609.26806: the Lean port of the Notes. It does not cover the Ax1Gen readings in variant 3 or detector certificates.
- alozanoroble/godel-ontological-lean and drewarrowood/godel-ontological (GitHub): Lean formalisations of the variants. Neither addresses nominal-free proofs.
- Benzmüller, Proofs Without Nominals, arXiv 2609.36279 v4 (https://arxiv.org/abs/2609.36279):.
- Benzmüller & Scott, Notes on Gödel's and Scott's variants, Monatshefte 2025 (https://link.springer.com/article/10.1007/s00605-025-02078-x): T1, positive properties are possibly exemplified (special case of K13's first half).
- R. Koons, Sobel on Gödel's Ontological Proof (https://robkoons.net/uploads/1/3/5/2/135276253/art_koons__sobelongodel_sontologicalproof_l.pdf): the standard argument that a positive property is possibly instantiated.
- alozanoroble/godel-ontological-lean (https://github.com/alozanoroble/godel-ontological-lean): Lean 4 frame-condition table for Gödel, Scott, Anderson, Fitting and Hájek. It does not cover variant 3's essence lemmas.

Our prior-art search (2026-10-22) covered:

- https://arxiv.org/abs/2609.36279: version history (v1–v4, v4 is the latest, 2026-10-14). Fetched 2026-10-22.
- These were search-engine results only. External pages beyond the summaries were not opened.
- I used only search-result summaries for the web hits and did not open the pages.

The search was run automatically by claude/claude-opus-5-5.

The checkers' full answers, with every query and file they searched, are published with this finding (`prior-art/`).

If you know of related work we missed, please open an issue.

We believe this result is new. Our prior-art search (2026-10-22) covered:

- I worked only from search-result summaries for the web results. I did not open those pages.

The search was run automatically by claude/claude-opus-5-5.

The checkers' full answers, with every query and file they searched, are published with this finding (`prior-art/`).

We found no earlier statement of it, but we can't be certain. If you know of prior work, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the proof and check files are included so anyone can re-run them.

**K1.** `In v4's Ax1GenTwoVariant2 (logic K), Ax1Gen_of_Two, Two_equivalent, P_of_conj, loc_of_conj, ae_Two_nominal, G_ex_Two_unconditional_nominal and only_top_and_empty_domain(_False) have proofs of the identical statements that v4's detector passes in witness and whole-term mode.`

- Status: proved (axioms: Ax1GenTwo, Ax2a, Ax2b, Ax3, Ax4, P, R, e, eNonempty, existsAt, i, propext, Classical.choice, Quot.sound)
- Machine-checked: 2 of 2 check scripts passed.
- Prior art: partial prior art

**K2.** `In v4's Ax1GenTwoVariant3Plain (logic K), Ax1Gen_of_Two, Two_equivalent, P_of_conj, loc_of_conj, ae_Two_nominal, G_ex_Two_unconditional_nominal and only_top_and_empty_domain(_False) have proofs of the identical statements that v4's detector passes in witness and whole-term mode.`

- Status: proved (axioms: Ax1GenTwo, Ax2a, Ax2b, Ax3, Ax4, P, R, e, eNonempty, existsAt, i, propext, Classical.choice, Quot.sound)
- Machine-checked: 2 of 2 check scripts passed.
- Prior art: partial prior art

**K3.** `In v4's Ax1GenBoxVariant3, MC_S4, Th5_S4 and Ax1Gen_of_refl have proofs of the identical statements that v4's detector passes (witness and whole-term, full names); the reflexivity hypothesis is not used.`

- Status: proved (axioms: Ax1GenBox, Ax2a, Ax2b, Ax3, Ax4, P, R, e, eNonempty, existsAt, i, propext, Classical.choice, Quot.sound)
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

**K4.** `In v4's GoedelVariantHOML3inS4oneFile, AllExist, Th3, Th5, MC, MCdual, Triv, UniqueEss1/2/3, EssMem, EssMemI, EssSupp, EssDetermined and Ess_iff_Ess2 have proofs of the identical statements that v4's detector passes (witness and whole-term, full names), using neither Rrefl nor Rtrans.`

- Status: proved (axioms: Ax1Gen, Ax2a, Ax3, Ax4, P, R, e, eNonempty, existsAt, i, propext, Classical.choice, Quot.sound)
- Machine-checked: 2 of 2 check scripts passed.
- Prior art: partial prior art

**K5.** `In v4's Ax1GenOneVariant3 (logic K), MC_unconditional, MC_One, AllActual_of_PBot, NotPBot/PTop/G_ex/Th4_One_deriv, E_top_of_PBot, AllExist_One, One_gives_S, One_gives_Box, Box_gives_One have proofs of the identical statements that v4's detector passes (full names).`

- Status: proved (axioms: Ax1GenOne, Ax2a, Ax2b, Ax3, Ax4, P, R, e, eNonempty, existsAt, i, propext, Classical.choice, Quot.sound)
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

**K6.** `In v4's Ax1GenTwoVariant3PlainPoss and Ax1GenTwoVariant3PlainAndersonQuant, MC_unconditional has a proof of the identical statement that v4's detector passes (witness and whole-term, full names).`

- Status: proved (axioms: Ax1GenTwo, Ax2a, Ax2b, Ax3, Ax4, P, R, e, eNonempty, i, propext, Classical.choice, Quot.sound)
- Machine-checked: 2 of 2 check scripts passed.
- Prior art: partial prior art

**K7.** In v4's Ax1GenTwoVariant3 (logic K), MC_unconditional, MC_Two, L_Two_hybrid, G_ex_Two_actual_hybrid and Th4_Two_actual_hybrid have proofs of the identical statements that v4's detector passes (witness and whole-term, full names), via a hybrid-free lemma that every $\sigma$ is constant.

- Status: proved (axioms: Ax1GenTwo, Ax2a, Ax2b, Ax3, Ax4, P, R, e, eNonempty, existsAt, i, propext, Classical.choice, Quot.sound)
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

**K8.** `In v4's Ax1GenTwoVariant3Th4, G_ex_Two_hybrid and AllExist_Two have proofs of the identical statements that v4's detector passes (witness and whole-term, full names), with no frame condition.`

- Status: proved (axioms: Ax1GenTwo, Ax2a, Ax2b, Ax3, Ax4, P, R, Th4, e, eNonempty, existsAt, i, propext, Classical.choice, Quot.sound)
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

**K11.** On worlds Bool, one always-actual entity, universal $R$, $P\varphi w:=\varphi()w$, swap-invariant domains closed under all terms of an $\mathcal L$-datatype: Ax1, Ax2a, Ax2b, Ax3, both Ax4, Ax1Gen(Two/One/Box), Th4 hold, $E$ holds at both worlds, so NoNecExist fails.

- Status: proved (axioms: propext, Classical.choice, Quot.sound)
- Machine-checked: no check scripts.
- Prior art: partial prior art

**K12.** `In v4's Ax1GenTwoVariant3Plain (logic K), AllExist and MC_OneWorld have proofs of the identical statements that v4's detector passes (witness and whole-term, full names).`

- Status: proved (axioms: Ax1GenTwo, Ax2a, Ax3, Ax4, P, R, e, eNonempty, existsAt, i, propext, Classical.choice, Quot.sound)
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

**K13.** Abstract Henkin variant 2, exclusive Ax2a, Ax2b, Ax4, Ax1GenR over admitted rigid families $\mathcal F$, any actuality: each $\Phi\in\mathcal F$ positive at $w$ is realised by an actual entity at an $R$-successor; if $G$ is admitted and $\neg PG\,w$, no $\Phi\in\mathcal F$ equals admitted $P_w$.

- Status: proved (axioms: propext, Classical.choice, Quot.sound)
- Machine-checked: no check scripts.
- Prior art: partial prior art

**K14.** In v4's Ax1GenRigidVariant2 (logic K), L_R ($\mathrm{Ax1GenR}\to\lfloor PG\rfloor$) has a proof of the identical statement that v4's detector passes (witness and whole-term, full names), with witness PosGlobal, from Ax2a, Ax2b, Ax4 only, with no condition on positivity.

- Status: proved (axioms: Ax2a, Ax2b, Ax4, P, R, e, existsAt, i, propext, Classical.choice, Quot.sound)
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

## How to verify

Run each script in `claims/ontological-nominal-free-proofs/checks/` with `python -I <script>`; it passes if it
exits with status 0. The results recorded in the original run are in
`claims/ontological-nominal-free-proofs/results/`; the full claim text is in `claims/ontological-nominal-free-proofs/claim.md`.

## Provenance

- run: 20261022-1314
- claims: K1, K2, K3, K4, K5, K6, K7, K8, K11, K12, K13, K14
- run-folder commit: 7e239585d6c77726d88783754d4bfa7d3c3bf197
- K1 author: pr (claude)
- K2 author: pr (claude)
- K3 author: pr (claude)
- K4 author: pr (claude)
- K5 author: pr (claude)
- K6 author: pr (claude)
- K7 author: pr (claude)
- K8 author: pr (claude)
- K11 author: pr (claude)
- K12 author: pr (claude)
- K13 author: pr (claude)
- K14 author: pr (claude)

## References

1. <!-- cite:benzmueller2025notes --> Benzm\"uller, Christoph and Scott, Dana S.. 2025. Notes on G\"odel's and Scott's variants of the ontological argument. Monatshefte f\"ur Mathematik. [Link](https://link.springer.com/article/10.1007/s00605-025-02078-x)
2. <!-- cite:benzmueller2026nominals --> Benzm\"uller, Christoph. 2026. Proofs Without Nominals: G\"odel's Ontological Argument, its Shallow Embedding, and the Open Questions of the Monatshefte Notes. [Link](https://arxiv.org/abs/2609.36279v4)

<!-- autoresearch:revisions -->
## Revisions

- 2026-10-24 — readable prior-art section
