---
layout: default
title: "Nominal-free proofs of the theorems Benzm\u00fcller's detector flags"
scholar: {"citation_title": "Nominal-free proofs of the theorems Benzm\u00fcller's detector flags", "citation_author": "Kodakodapa", "citation_publication_date": "2026/10/24", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/ontological-nominal-free-proofs.html", "citation_keywords": "*", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/ontological-nominal-free-proofs/paper.pdf"}
---

# Nominal-free proofs of the theorems Benzmüller's detector flags

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

This result extends C. Benzmüller, "Proofs Without Nominals", arXiv 2609.36279v4, https://arxiv.org/abs/2609.36279: gives detector-certified proofs `ae_Two` and `G_ex_Two_unconditional` of the same statements as `ae_Two_nominal` and `G_ex_Two_unconditional_nominal`, in both modules. `only_top_and_empty_domain(_False)` follows directly from `ae_Two`, though v4 proves it only through the flagged `OneWorld`. v4 proves Ax1Gen_of_Two, Two_equivalent, P_of_conj and loc_of_conj only through the nominal steps OneWorld/R_Id (flagged), and lists their hybrid-free status as open (sec:plain, sec:open); C. Benzmüller, "Proofs Without Nominals", arXiv 2609.36279 v4 (sources/2609.36279/v4): proves every statement in K3–K8 and K12 under the same names, but with nominal or actuality witnesses that its detector flags (audit/report.txt). It states that the hybrid-free versions are open for the Ax1GenOne variant 3 and for dropping (†) (§sec:one, §sec:open). Example ex:separating and Separation.lean give a flip-invariant separating model for the empty theory, which is the same technique K11 uses, applied to a different theory; C. Benzmüller, "Gödel's and Scott's Variants … in Lean 4 and TPTP THF", arXiv 2609.26806: the Lean port of the Notes. It does not cover the Ax1Gen readings in variant 3 or detector certificates; alozanoroble/godel-ontological-lean and drewarrowood/godel-ontological (GitHub): Lean formalisations of the variants. Neither addresses nominal-free proofs; Benzmüller, Proofs Without Nominals, arXiv 2609.36279 v4 (https://arxiv.org/abs/2609.36279):; Benzmüller & Scott, Notes on Gödel's and Scott's variants, Monatshefte 2025 (https://link.springer.com/article/10.1007/s00605-025-02078-x): T1, positive properties are possibly exemplified (special case of K13's first half); R. Koons, Sobel on Gödel's Ontological Proof (https://robkoons.net/uploads/1/3/5/2/135276253/art_koons__sobelongodel_sontologicalproof_l.pdf): the standard argument that a positive property is possibly instantiated; alozanoroble/godel-ontological-lean (https://github.com/alozanoroble/godel-ontological-lean): Lean 4 frame-condition table for Gödel, Scott, Anderson, Fitting and Hájek. It does not cover variant 3's essence lemmas. Our prior-art search (2026-10-22) covered:

- sources/2609.36279/v4/main.tex: §"Ax1GenTwo: at least two different conjuncts" (around Corollary cor:gextwo), §"Variant 3: where the non-emptiness clause belongs" (sec:plain), §"What stays open" (sec:open), Appendix "The detector" (app:detector). Read 2026-10-22.
- sources/2609.36279/v4/anc/OpenQuestions/lean/OpenQuestions/Ax1GenTwoVariant2.lean and Ax1GenTwoVariant3Plain.lean. Read 2026-10-22.
- sources/2609.36279/v4/anc/OpenQuestions/audit/report.txt, census-openquestions.txt, alt/alt-report-filtered.txt, alt/alt-axioms.txt. Read 2026-10-22.
- https://arxiv.org/abs/2609.36279: version history (v1–v4, v4 is the latest, 2026-10-14). Fetched 2026-10-22.
- WebSearch: "Benzmüller "Proofs Without Nominals" Ax1GenTwo hybrid-free equivalence Ax1Gen", 2026-10-22.
- WebSearch: "Gödel ontological argument conjunction axiom "at least two" conjuncts nominal accessibility identity Lean formalisation", 2026-10-22. It returned arXiv 2609.26806, the alozanoroble and drewarrowood repositories, and Odifreddi & Gomes (Logica Universalis). None of them treats a hybrid-free Ax1GenTwo⇔Ax1Gen equivalence.
- sources/2609.26806 (Lean/THF port): checked only to identify it. It predates the Ax1GenTwo emendation and has no bearing on the claim.
- sources/2609.36279/v4/main.tex: §sec:criterion (def:hybridfree, prop:sound), §sec:v3 (thm:nonecexist, thm:v3), §sec:ax1gentwo (prop:v3two, thm:v3-two), §sec:plain (thm:plain, fig:emended), §sec:one, §sec:box, §sec:boxtwo, §sec:criterion-open (def:lgeneral, prop:lgeneral, ex:separating), §sec:open. Read 2026-10-22.
- sources/2609.36279/v4/anc/OpenQuestions/audit/report.txt (per-module detector output). Read 2026-10-22.
- sources/2609.36279/v4/anc/OpenQuestions/lean/OpenQuestions/{Ax1GenBoxVariant3, Ax1GenOneVariant3, Ax1GenTwoVariant3, Ax1GenTwoVariant3Th4, Ax1GenTwoVariant3Plain, Ax1GenTwoVariant3PlainPoss, Ax1GenTwoVariant3PlainAndersonQuant, Ax1GenTwoVariant3Model}.lean and lean/Separation.lean. Read 2026-10-22.
- sources/2609.36279/v4/anc/OpenQuestions/alternatives/README.md. Read 2026-10-22.
- sources/2609.26806 (v1, v3): grepped for the theorem names (none present). 2026-10-22.
- Web search: "Gödel ontological argument variant 3 modal collapse "one world" nominal hybrid-free proof Lean". 2026-10-22.
- Web search: ""Proofs Without Nominals" Benzmüller ontological" (https://arxiv.org/abs/2609.36279). 2026-10-22.
- Web search: "Gödel ontological argument necessary existence essence every world single world collapse higher-order modal logic general models propositional quantification". 2026-10-22.
- These were search-engine results only. External pages beyond the summaries were not opened.
- sources/2609.36279/v4/main.tex: `sec:v3`, `thm:nonecexist`, `thm:v3`, `lem:serial`, `lem:reach`, `thm:uniqueess-k`, `sec:rigid`, `def:lgeneral`, `prop:lgeneral`, `sec:open` (read 2026-10-22)
- sources/2609.36279/v4/anc/OpenQuestions/lean/OpenQuestions/GoedelVariantHOML3inS4oneFile.lean, full K-section and EssSupp/EssDetermined (2026-10-22)
- sources/2609.36279/v4/anc/OpenQuestions/lean/OpenQuestions/Ax1GenRigidVariant2.lean: `P_succ`, `L_R`, `L_R_rigidpos`, `RigidPos_of_link` (2026-10-22)
- sources/2609.26806/v3/anc/Notes/*.lean, grep for Th1/T1 and exemplification (2026-10-22)
- Web search, "Gödel ontological argument variant essence modal logic K without reflexivity modal collapse Lean formalisation 2026" (2026-10-22)
- Web search, "ontological argument Henkin general models rigid sets of properties conjunction axiom positive properties possibly exemplified" (2026-10-22)
- Web search, "Benzmüller Proofs Without Nominals arXiv" (2026-10-22): https://arxiv.org/abs/2609.36279
- I used only search-result summaries for the web hits and did not open the pages.

The search was run automatically by claude/claude-opus-5-5.

If you know of related work we missed, please open an issue.

We believe this result is new. Our prior-art search (2026-10-22) covered:

- sources/2609.36279/v4/main.tex (§sec:rigid, lines ~1373–1410), read 2026-10-22
- sources/2609.36279/v4/anc/OpenQuestions/lean/OpenQuestions/Ax1GenRigidVariant2.lean, read 2026-10-22
- sources/2609.36279/v4/anc/OpenQuestions/audit/census-openquestions.txt (grep for L_R, PosGlobal), read 2026-10-22
- sources/2609.26806/v1, v3 (grep for Ax1GenR / PosGlobal / RigidPos: no hits), 2026-10-22
- Web search: "Gödel ontological argument generalised conjunction axiom rigid set of properties "positive" Ax1Gen", 2026-10-22. Results: https://arxiv.org/html/2609.36279v1, https://link.springer.com/article/10.1007/s00605-025-02078-x, https://arxiv.org/html/2609.26806, https://arxiv.org/html/2608.07578, https://link.springer.com/article/10.1007/s11787-026-00409-6, https://www.researchgate.net/publication/402244958
- Web search: "Benzmüller "Proofs Without Nominals" ontological argument rigid positivity", 2026-10-22. Results: https://arxiv.org/abs/2609.36279, https://arxiv.org/pdf/1910.08955, https://arxiv.org/pdf/2608.07578, https://arxiv.org/pdf/2202.06264
- I worked only from search-result summaries for the web results. I did not open those pages.

The search was run automatically by claude/claude-opus-5-5.

We found no earlier statement of it, but we can't be certain. If you know of prior work, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the proof and check files are included so anyone can re-run them.

## K1

`In v4's Ax1GenTwoVariant2 (logic K), Ax1Gen_of_Two, Two_equivalent, P_of_conj, loc_of_conj, ae_Two_nominal, G_ex_Two_unconditional_nominal and only_top_and_empty_domain(_False) have proofs of the identical statements that v4's detector passes in witness and whole-term mode.`

Status: proved (axioms: Ax1GenTwo, Ax2a, Ax2b, Ax3, Ax4, P, R, e, eNonempty, existsAt, i, propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K1-TwoV2.lean`: Programme.F.TwoV2.Ax1Gen\_of\_Two\_hf — pass (`results/K1-1.json`)
- proof `checks/K1-TwoV2.lean`: Programme.F.TwoV2.Two\_equivalent\_hf — pass (`results/K1-2.json`)
- proof `checks/K1-TwoV2.lean`: Programme.F.TwoV2.loc\_of\_conj\_hf — pass (`results/K1-3.json`)
- proof `checks/K1-TwoV2.lean`: Programme.F.TwoV2.P\_of\_conj\_hf — pass (`results/K1-4.json`)
- proof `checks/K1-TwoV2.lean`: Programme.F.TwoV2.ae\_Two\_nominal\_hf — pass (`results/K1-5.json`)
- proof `checks/K1-TwoV2.lean`: Programme.F.TwoV2.G\_ex\_Two\_unconditional\_nominal\_hf — pass (`results/K1-6.json`)
- proof `checks/K1-TwoV2.lean`: Programme.F.TwoV2.only\_top\_and\_empty\_domain\_False\_hf — pass (`results/K1-7.json`)
- proof `checks/K1-TwoV2.lean`: Programme.F.TwoV2.only\_top\_and\_empty\_domain\_hf — pass (`results/K1-8.json`)
- check `checks/K1-hybrid_TwoV2.py`: The embedded Lean file compiles against /library with no sorry, and `python /library/tools/hybrid_check.py --path <tmp> Programme.F.TwoV2 <8 names>` exits 0: no theorem hybrid, inheriting or whole-term flagged. — pass (`results/K1-11.json`)
- check `checks/K1-hybrid_TwoV2.py`: Strict full-name certification (the skeptic): compiles the embedded, sha-pinned Lean file against /library with no error/sorry; runs v4's HybridAudit (#hybrid\_audit and #hybrid\_all) on the module and asserts that no named theorem appears, by FULLY QUALIFIED name, as hybrid, inheriting or EXTRA, that whole-term mode reports and that there is no sorryAx; negative control: a re-export of the library's hybrid `Two_equivalent` in the same namespace IS flagged, so the matcher is live. — pass (`results/K1-11.json`)

Prior art: partial prior art (answer: `prior-art/R2.md`)

### Provenance

- run: 20261022-1314
- claim: K1
- author: pr (claude)
- round: 1
- run-folder commit: 7e239585d6c77726d88783754d4bfa7d3c3bf197
- check results: K1-1.json, K1-11.json, K1-2.json, K1-3.json, K1-4.json, K1-5.json, K1-6.json, K1-7.json, K1-8.json

## K2

`In v4's Ax1GenTwoVariant3Plain (logic K), Ax1Gen_of_Two, Two_equivalent, P_of_conj, loc_of_conj, ae_Two_nominal, G_ex_Two_unconditional_nominal and only_top_and_empty_domain(_False) have proofs of the identical statements that v4's detector passes in witness and whole-term mode.`

Status: proved (axioms: Ax1GenTwo, Ax2a, Ax2b, Ax3, Ax4, P, R, e, eNonempty, existsAt, i, propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K2-TwoV3Plain.lean`: Programme.F.TwoV3Plain.Ax1Gen\_of\_Two\_hf — pass (`results/K2-1.json`)
- proof `checks/K2-TwoV3Plain.lean`: Programme.F.TwoV3Plain.Two\_equivalent\_hf — pass (`results/K2-2.json`)
- proof `checks/K2-TwoV3Plain.lean`: Programme.F.TwoV3Plain.loc\_of\_conj\_hf — pass (`results/K2-3.json`)
- proof `checks/K2-TwoV3Plain.lean`: Programme.F.TwoV3Plain.P\_of\_conj\_hf — pass (`results/K2-4.json`)
- proof `checks/K2-TwoV3Plain.lean`: Programme.F.TwoV3Plain.ae\_Two\_nominal\_hf — pass (`results/K2-5.json`)
- proof `checks/K2-TwoV3Plain.lean`: Programme.F.TwoV3Plain.G\_ex\_Two\_unconditional\_nominal\_hf — pass (`results/K2-6.json`)
- proof `checks/K2-TwoV3Plain.lean`: Programme.F.TwoV3Plain.only\_top\_and\_empty\_domain\_False\_hf — pass (`results/K2-7.json`)
- proof `checks/K2-TwoV3Plain.lean`: Programme.F.TwoV3Plain.only\_top\_and\_empty\_domain\_hf — pass (`results/K2-8.json`)
- check `checks/K2-hybrid_TwoV3Plain.py`: The embedded Lean file compiles against /library with no sorry, and `python /library/tools/hybrid_check.py --path <tmp> Programme.F.TwoV3Plain <8 names>` exits 0: no theorem hybrid, inheriting or whole-term flagged. — pass (`results/K2-11.json`)
- check `checks/K2-hybrid_TwoV3Plain.py`: Strict full-name certification (the skeptic): compiles the embedded, sha-pinned Lean file against /library with no error/sorry; runs v4's HybridAudit (#hybrid\_audit and #hybrid\_all) on the module and asserts that no named theorem appears, by FULLY QUALIFIED name, as hybrid, inheriting or EXTRA, that whole-term mode reports and that there is no sorryAx; negative control: a re-export of the library's hybrid `Two_equivalent` in the same namespace IS flagged, so the matcher is live. — pass (`results/K2-11.json`)

Prior art: partial prior art (answer: `prior-art/R2.md`)

### Provenance

- run: 20261022-1314
- claim: K2
- author: pr (claude)
- round: 1
- run-folder commit: 7e239585d6c77726d88783754d4bfa7d3c3bf197
- check results: K2-1.json, K2-11.json, K2-2.json, K2-3.json, K2-4.json, K2-5.json, K2-6.json, K2-7.json, K2-8.json

## K3

`In v4's Ax1GenBoxVariant3, MC_S4, Th5_S4 and Ax1Gen_of_refl have proofs of the identical statements that v4's detector passes (witness and whole-term, full names); the reflexivity hypothesis is not used.`

Status: proved (axioms: Ax1GenBox, Ax2a, Ax2b, Ax3, Ax4, P, R, e, eNonempty, existsAt, i, propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K3-BoxV3.lean`: Programme.F.BoxV3.MC\_S4\_hf — pass (`results/K3-1.json`)
- proof `checks/K3-BoxV3.lean`: Programme.F.BoxV3.Ax1Gen\_of\_refl\_hf — pass (`results/K3-2.json`)
- proof `checks/K3-BoxV3.lean`: Programme.F.BoxV3.Th5\_S4\_hf — pass (`results/K3-3.json`)
- check `checks/K3-hybrid_BoxV3.py`: Strict full-name certification (the skeptic): compiles the embedded, sha-pinned Lean file against /library with no error/sorry; runs v4's HybridAudit (#hybrid\_audit and #hybrid\_all) on the module and asserts that no named theorem appears, by FULLY QUALIFIED name, as hybrid, inheriting or EXTRA, that whole-term mode reports and that there is no sorryAx; negative control: a re-export of the library's hybrid `MC_S4` in the same namespace IS flagged, so the matcher is live. — pass (`results/K3-4.json`)

Prior art: partial prior art (answer: `prior-art/R3.md`)

### Provenance

- run: 20261022-1314
- claim: K3
- author: pr (claude)
- round: 2
- run-folder commit: 7e239585d6c77726d88783754d4bfa7d3c3bf197
- check results: K3-1.json, K3-2.json, K3-3.json, K3-4.json

## K4

`In v4's GoedelVariantHOML3inS4oneFile, AllExist, Th3, Th5, MC, MCdual, Triv, UniqueEss1/2/3, EssMem, EssMemI, EssSupp, EssDetermined and Ess_iff_Ess2 have proofs of the identical statements that v4's detector passes (witness and whole-term, full names), using neither Rrefl nor Rtrans.`

Status: proved (axioms: Ax1Gen, Ax2a, Ax3, Ax4, P, R, e, eNonempty, existsAt, i, propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K4-HOML3.lean`: Programme.F.HOML3.AllExist\_hf — pass (`results/K4-16.json`)
- proof `checks/K4-HOML3.lean`: Programme.F.HOML3.Th3\_hf — pass (`results/K4-17.json`)
- proof `checks/K4-HOML3.lean`: Programme.F.HOML3.Th5\_hf — pass (`results/K4-18.json`)
- proof `checks/K4-HOML3.lean`: Programme.F.HOML3.MC\_hf — pass (`results/K4-19.json`)
- proof `checks/K4-HOML3.lean`: Programme.F.HOML3.MCdual\_hf — pass (`results/K4-20.json`)
- proof `checks/K4-HOML3.lean`: Programme.F.HOML3.Triv\_hf — pass (`results/K4-21.json`)
- proof `checks/K4-HOML3.lean`: Programme.F.HOML3.UniqueEss1\_hf — pass (`results/K4-22.json`)
- proof `checks/K4-HOML3.lean`: Programme.F.HOML3.UniqueEss2\_hf — pass (`results/K4-23.json`)
- proof `checks/K4-HOML3.lean`: Programme.F.HOML3.UniqueEss3\_hf — pass (`results/K4-24.json`)
- proof `checks/K4-HOML3.lean`: Programme.F.HOML3.EssMemI\_hf — pass (`results/K4-25.json`)
- proof `checks/K4-HOML3.lean`: Programme.F.HOML3.EssMem\_hf — pass (`results/K4-26.json`)
- proof `checks/K4-HOML3.lean`: Programme.F.HOML3.Ess\_iff\_Ess2\_hf — pass (`results/K4-27.json`)
- proof `checks/K4-HOML3.lean`: Programme.F.HOML3.EssSupp\_hf — pass (`results/K4-28.json`)
- proof `checks/K4-HOML3.lean`: Programme.F.HOML3.EssDetermined\_hf — pass (`results/K4-29.json`)
- check `checks/K4-hybrid_HOML3.py`: Strict full-name certification (the skeptic): compiles the embedded, sha-pinned Lean file against /library with no error/sorry; runs v4's HybridAudit (#hybrid\_audit and #hybrid\_all) on the module and asserts that no named theorem appears, by FULLY QUALIFIED name, as hybrid, inheriting or EXTRA, that whole-term mode reports and that there is no sorryAx; negative control: a re-export of the library's hybrid `Th3` in the same namespace IS flagged, so the matcher is live. — pass (`results/K4-30.json`)
- check `checks/K4-hybrid_HOML3.py`: Compiles the embedded sha-pinned file against /library (no error/sorry); v4's HybridAudit (witness + whole-term) flags none of the 14 theorems by full name (0 hybrid/inheriting/EXTRA); the transitive constant closure of every proof avoids all F\_WORKLIST names of the module incl. ACTUAL-only AllExist and AllExistI; negative control (re-export of Th3) is flagged. — pass (`results/K4-30.json`)

Prior art: partial prior art (answer: `prior-art/R4.md`)

### Provenance

- run: 20261022-1314
- claim: K4
- author: pr (claude)
- round: 5
- run-folder commit: 7e239585d6c77726d88783754d4bfa7d3c3bf197
- check results: K4-16.json, K4-17.json, K4-18.json, K4-19.json, K4-20.json, K4-21.json, K4-22.json, K4-23.json, K4-24.json, K4-25.json, K4-26.json, K4-27.json, K4-28.json, K4-29.json, K4-30.json

## K5

`In v4's Ax1GenOneVariant3 (logic K), MC_unconditional, MC_One, AllActual_of_PBot, NotPBot/PTop/G_ex/Th4_One_deriv, E_top_of_PBot, AllExist_One, One_gives_S, One_gives_Box, Box_gives_One have proofs of the identical statements that v4's detector passes (full names).`

Status: proved (axioms: Ax1GenOne, Ax2a, Ax2b, Ax3, Ax4, P, R, e, eNonempty, existsAt, i, propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K5-OneV3.lean`: Programme.F.OneV3.MC\_unconditional\_hf — pass (`results/K5-1.json`)
- proof `checks/K5-OneV3.lean`: Programme.F.OneV3.MC\_One\_hf — pass (`results/K5-2.json`)
- proof `checks/K5-OneV3.lean`: Programme.F.OneV3.AllActual\_of\_PBot\_hf — pass (`results/K5-3.json`)
- proof `checks/K5-OneV3.lean`: Programme.F.OneV3.NotPBot\_One\_deriv\_hf — pass (`results/K5-4.json`)
- proof `checks/K5-OneV3.lean`: Programme.F.OneV3.PTop\_One\_deriv\_hf — pass (`results/K5-5.json`)
- proof `checks/K5-OneV3.lean`: Programme.F.OneV3.E\_top\_of\_PBot\_hf — pass (`results/K5-6.json`)
- proof `checks/K5-OneV3.lean`: Programme.F.OneV3.G\_ex\_One\_deriv\_hf — pass (`results/K5-7.json`)
- proof `checks/K5-OneV3.lean`: Programme.F.OneV3.Th4\_One\_deriv\_hf — pass (`results/K5-8.json`)
- proof `checks/K5-OneV3.lean`: Programme.F.OneV3.AllExist\_One\_hf — pass (`results/K5-9.json`)
- proof `checks/K5-OneV3.lean`: Programme.F.OneV3.One\_gives\_S\_hf — pass (`results/K5-10.json`)
- proof `checks/K5-OneV3.lean`: Programme.F.OneV3.One\_gives\_Box\_hf — pass (`results/K5-11.json`)
- proof `checks/K5-OneV3.lean`: Programme.F.OneV3.Box\_gives\_One\_hf — pass (`results/K5-12.json`)
- check `checks/K5-hybrid_OneV3.py`: Strict full-name certification (the skeptic): compiles the embedded, sha-pinned Lean file against /library with no error/sorry; runs v4's HybridAudit (#hybrid\_audit and #hybrid\_all) on the module and asserts that no named theorem appears, by FULLY QUALIFIED name, as hybrid, inheriting or EXTRA, that whole-term mode reports and that there is no sorryAx; negative control: a re-export of the library's hybrid `MC_unconditional` in the same namespace IS flagged, so the matcher is live. — pass (`results/K5-13.json`)

Prior art: partial prior art (answer: `prior-art/R3.md`)

### Provenance

- run: 20261022-1314
- claim: K5
- author: pr (claude)
- round: 2
- run-folder commit: 7e239585d6c77726d88783754d4bfa7d3c3bf197
- check results: K5-1.json, K5-10.json, K5-11.json, K5-12.json, K5-13.json, K5-2.json, K5-3.json, K5-4.json, K5-5.json, K5-6.json, K5-7.json, K5-8.json, K5-9.json

## K6

`In v4's Ax1GenTwoVariant3PlainPoss and Ax1GenTwoVariant3PlainAndersonQuant, MC_unconditional has a proof of the identical statement that v4's detector passes (witness and whole-term, full names).`

Status: proved (axioms: Ax1GenTwo, Ax2a, Ax2b, Ax3, Ax4, P, R, e, eNonempty, i, propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K6-TwoV3PlainPoss.lean`: Programme.F.TwoV3PlainPoss.MC\_unconditional\_hf — pass (`results/K6-1.json`)
- check `checks/K6-hybrid_TwoV3PlainPoss.py`: Strict full-name certification (the skeptic): compiles the embedded, sha-pinned Lean file against /library with no error/sorry; runs v4's HybridAudit (#hybrid\_audit and #hybrid\_all) on the module and asserts that no named theorem appears, by FULLY QUALIFIED name, as hybrid, inheriting or EXTRA, that whole-term mode reports and that there is no sorryAx; negative control: a re-export of the library's hybrid `MC_unconditional` in the same namespace IS flagged, so the matcher is live. — pass (`results/K6-2.json`)
- proof `checks/K6-TwoV3PlainAndersonQuant.lean`: Programme.F.TwoV3PlainAndersonQuant.MC\_unconditional\_hf — pass (`results/K6-3.json`)
- check `checks/K6-hybrid_TwoV3PlainAndersonQuant.py`: Strict full-name certification (the skeptic): compiles the embedded, sha-pinned Lean file against /library with no error/sorry; runs v4's HybridAudit (#hybrid\_audit and #hybrid\_all) on the module and asserts that no named theorem appears, by FULLY QUALIFIED name, as hybrid, inheriting or EXTRA, that whole-term mode reports and that there is no sorryAx; negative control: a re-export of the library's hybrid `MC_unconditional` in the same namespace IS flagged, so the matcher is live. — pass (`results/K6-4.json`)

Prior art: partial prior art (answer: `prior-art/R3.md`)

### Provenance

- run: 20261022-1314
- claim: K6
- author: pr (claude)
- round: 2
- run-folder commit: 7e239585d6c77726d88783754d4bfa7d3c3bf197
- check results: K6-1.json, K6-2.json, K6-3.json, K6-4.json

## K7

In v4's Ax1GenTwoVariant3 (logic K), MC_unconditional, MC_Two, L_Two_hybrid, G_ex_Two_actual_hybrid and Th4_Two_actual_hybrid have proofs of the identical statements that v4's detector passes (witness and whole-term, full names), via a hybrid-free lemma that every $\sigma$ is constant.

Status: proved (axioms: Ax1GenTwo, Ax2a, Ax2b, Ax3, Ax4, P, R, e, eNonempty, existsAt, i, propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K7-TwoV3.lean`: Programme.F.TwoV3.MC\_unconditional\_hf — pass (`results/K7-1.json`)
- proof `checks/K7-TwoV3.lean`: Programme.F.TwoV3.MC\_Two\_hf — pass (`results/K7-2.json`)
- proof `checks/K7-TwoV3.lean`: Programme.F.TwoV3.L\_Two\_hybrid\_hf — pass (`results/K7-3.json`)
- proof `checks/K7-TwoV3.lean`: Programme.F.TwoV3.G\_ex\_Two\_actual\_hybrid\_hf — pass (`results/K7-4.json`)
- proof `checks/K7-TwoV3.lean`: Programme.F.TwoV3.Th4\_Two\_actual\_hybrid\_hf — pass (`results/K7-5.json`)
- check `checks/K7-hybrid_TwoV3.py`: Strict full-name certification (the skeptic): compiles the embedded, sha-pinned Lean file against /library with no error/sorry; runs v4's HybridAudit (#hybrid\_audit and #hybrid\_all) on the module and asserts that no named theorem appears, by FULLY QUALIFIED name, as hybrid, inheriting or EXTRA, that whole-term mode reports and that there is no sorryAx; negative control: a re-export of the library's hybrid `MC_unconditional` in the same namespace IS flagged, so the matcher is live. — pass (`results/K7-6.json`)

Prior art: partial prior art (answer: `prior-art/R3.md`)

### Provenance

- run: 20261022-1314
- claim: K7
- author: pr (claude)
- round: 2
- run-folder commit: 7e239585d6c77726d88783754d4bfa7d3c3bf197
- check results: K7-1.json, K7-2.json, K7-3.json, K7-4.json, K7-5.json, K7-6.json

## K8

`In v4's Ax1GenTwoVariant3Th4, G_ex_Two_hybrid and AllExist_Two have proofs of the identical statements that v4's detector passes (witness and whole-term, full names), with no frame condition.`

Status: proved (axioms: Ax1GenTwo, Ax2a, Ax2b, Ax3, Ax4, P, R, Th4, e, eNonempty, existsAt, i, propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K8-TwoV3Th4.lean`: Programme.F.TwoV3Th4.G\_ex\_Two\_hybrid\_hf — pass (`results/K8-1.json`)
- proof `checks/K8-TwoV3Th4.lean`: Programme.F.TwoV3Th4.AllExist\_Two\_hf — pass (`results/K8-2.json`)
- check `checks/K8-hybrid_TwoV3Th4.py`: Strict full-name certification (the skeptic): compiles the embedded, sha-pinned Lean file against /library with no error/sorry; runs v4's HybridAudit (#hybrid\_audit and #hybrid\_all) on the module and asserts that no named theorem appears, by FULLY QUALIFIED name, as hybrid, inheriting or EXTRA, that whole-term mode reports and that there is no sorryAx; negative control: a re-export of the library's hybrid `G_ex_Two_hybrid` in the same namespace IS flagged, so the matcher is live. — pass (`results/K8-3.json`)

Prior art: partial prior art (answer: `prior-art/R3.md`)

### Provenance

- run: 20261022-1314
- claim: K8
- author: pr (claude)
- round: 2
- run-folder commit: 7e239585d6c77726d88783754d4bfa7d3c3bf197
- check results: K8-1.json, K8-2.json, K8-3.json

## K11

On worlds Bool, one always-actual entity, universal $R$, $P\varphi w:=\varphi()w$, swap-invariant domains closed under all terms of an $\mathcal L$-datatype: Ax1, Ax2a, Ax2b, Ax3, both Ax4, Ax1Gen(Two/One/Box), Th4 hold, $E$ holds at both worlds, so NoNecExist fails.

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K11-NoNecModel.lean`: Programme.F.NoNecModel.nonec\_model — pass (`results/K11-1.json`)

Prior art: partial prior art (answer: `prior-art/R3.md`)

### Provenance

- run: 20261022-1314
- claim: K11
- author: pr (claude)
- round: 3
- run-folder commit: 7e239585d6c77726d88783754d4bfa7d3c3bf197
- check results: K11-1.json

## K12

`In v4's Ax1GenTwoVariant3Plain (logic K), AllExist and MC_OneWorld have proofs of the identical statements that v4's detector passes (witness and whole-term, full names).`

Status: proved (axioms: Ax1GenTwo, Ax2a, Ax3, Ax4, P, R, e, eNonempty, existsAt, i, propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K12-V3PlainExtra.lean`: Programme.F.V3PlainExtra.AllExist\_hf — pass (`results/K12-1.json`)
- proof `checks/K12-V3PlainExtra.lean`: Programme.F.V3PlainExtra.MC\_OneWorld\_hf — pass (`results/K12-2.json`)
- check `checks/K12-hybrid_V3PlainExtra.py`: Strict full-name certification: compiles the embedded, sha-pinned Lean file against /library with no error/sorry; runs v4's HybridAudit (#hybrid\_audit and #hybrid\_all) on the module and asserts that neither theorem appears, by fully qualified name, as hybrid, inheriting or EXTRA, that whole-term mode reports and that there is no sorryAx; negative control: a re-export of the library's inheriting `Two_equivalent` in the same namespace IS flagged. — pass (`results/K12-3.json`)

Prior art: partial prior art (answer: `prior-art/R3.md`)

### Provenance

- run: 20261022-1314
- claim: K12
- author: pr (claude)
- round: 3
- run-folder commit: 7e239585d6c77726d88783754d4bfa7d3c3bf197
- check results: K12-1.json, K12-2.json, K12-3.json

## K13

Abstract Henkin variant 2, exclusive Ax2a, Ax2b, Ax4, Ax1GenR over admitted rigid families $\mathcal F$, any actuality: each $\Phi\in\mathcal F$ positive at $w$ is realised by an actual entity at an $R$-successor; if $G$ is admitted and $\neg PG\,w$, no $\Phi\in\mathcal F$ equals admitted $P_w$.

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K13-RigidLemma.lean`: Programme.F.RigidLemma.realised — pass (`results/K13-1.json`)
- proof `checks/K13-RigidLemma.lean`: Programme.F.RigidLemma.no\_god\_succ — pass (`results/K13-2.json`)
- proof `checks/K13-RigidLemma.lean`: Programme.F.RigidLemma.pos\_type\_omitted — pass (`results/K13-3.json`)
- proof `checks/K13-RigidLemma.lean`: Programme.F.RigidLemma.pos\_type\_omitted\_of\_pred — pass (`results/K13-4.json`)

Prior art: partial prior art (answer: `prior-art/R4.md`)

### Provenance

- run: 20261022-1314
- claim: K13
- author: pr (claude)
- round: 5
- run-folder commit: 7e239585d6c77726d88783754d4bfa7d3c3bf197
- check results: K13-1.json, K13-2.json, K13-3.json, K13-4.json

## K14

In v4's Ax1GenRigidVariant2 (logic K), L_R ($\mathrm{Ax1GenR}\to\lfloor PG\rfloor$) has a proof of the identical statement that v4's detector passes (witness and whole-term, full names), with witness PosGlobal, from Ax2a, Ax2b, Ax4 only, with no condition on positivity.

Status: proved (axioms: Ax2a, Ax2b, Ax4, P, R, e, existsAt, i, propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K14-RigidHF.lean`: Programme.F.RigidHF.L\_R\_hf — pass (`results/K14-1.json`)
- proof `checks/K14-RigidHF.lean`: Programme.F.RigidHF.guard\_pos\_hf — pass (`results/K14-2.json`)
- check `checks/K14-hybrid_RigidHF.py`: Compiles the embedded sha-pinned file against /library (no error/sorry); v4's HybridAudit (witness + whole-term) flags neither theorem by full name (0 hybrid/inheriting/EXTRA); proof closure avoids L\_R, RigidPos, RigidPos\_of\_link, pos\_link, Link, L\_R\_rigidpos; negative control (re-export of L\_R) is flagged. — pass (`results/K14-3.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R5.md`)

### Provenance

- run: 20261022-1314
- claim: K14
- author: pr (claude)
- round: 6
- run-folder commit: 7e239585d6c77726d88783754d4bfa7d3c3bf197
- check results: K14-1.json, K14-2.json, K14-3.json

## References

1. <!-- cite:benzmueller2025notes --> Benzm\"uller, Christoph and Scott, Dana S.. 2025. Notes on G\"odel's and Scott's variants of the ontological argument. Monatshefte f\"ur Mathematik. [Link](https://link.springer.com/article/10.1007/s00605-025-02078-x)
2. <!-- cite:benzmueller2026nominals --> Benzm\"uller, Christoph. 2026. Proofs Without Nominals: G\"odel's Ontological Argument, its Shallow Embedding, and the Open Questions of the Monatshefte Notes. [Link](https://arxiv.org/abs/2609.36279v4)
