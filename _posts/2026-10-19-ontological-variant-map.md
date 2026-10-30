---
layout: post
title: "A certified map of variants of G\u00f6del's ontological argument"
date: 2026-10-19
scholar: {"citation_title": "A certified map of variants of G\u00f6del's ontological argument", "citation_author": "Lindheim, Bj\u00f6rn", "citation_publication_date": "2026/10/19", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/ontological-variant-map.html", "citation_keywords": "C009", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/ontological-variant-map/paper.pdf"}
---

## Summary

<!-- owner-summary -->
## Setting

Gödel's ontological argument, in Scott's version, uses a second-order predicate $P$ ("positive")
and five axioms: A1 (exactly one of a property and its negation is positive; split here into
A1a, "not both", and A1b, "at least one"), A2 (positivity is closed under necessary entailment),
A3 ($P(G)$, where $G$, "God-like", means having every positive property), A4 (positive
properties are necessarily positive) and A5 (necessary existence is positive). The conclusion is
that a God-like being exists, $\exists x\,G(x)$, and necessarily exists, $\Box\exists x\,G(x)$.
A well-known side effect is *modal collapse*: everything true is necessarily true.

Many variants and weakenings are studied, mostly one variant at a time with an automated
theorem prover [1, 2, 3, 4]. This finding maps the space systematically. We take every subset
of each variant's axioms and the nine frame classes K, D, T, B, K4, KB, KD45, S4 and S5. We
vary the semantics: all intensional properties, rigid properties or extensional properties
(Fitting [5]), and constant or varying (actualist) domains. Cell by cell we
decide whether the axioms are consistent, whether they prove the conclusion and whether they
force collapse.

## Result

- **Scott, all properties** (constant or varying domains): the God-like being exists exactly
  when the subset contains A1a, A2, A3 and A5 and the frames are B, KB or S5; necessary
  existence also holds on KD45. Collapse holds exactly when the subset contains A1a, A2 and A5,
  on the same frames. A1b and A4 are never needed. With A1, A2 and A5 alone, every symmetric
  frame is forced to consist of isolated worlds.
- **Scott, rigid properties:** with constant domains no consistent cell forces collapse, and the
  conclusion holds on every frame exactly when the subset contains A1, A2 and A3, or A1, A3 and
  A5 (with Scott's essence). With varying domains existence needs A1a, A2, A3 and A5 on
  reflexive frames (T, B, S4, S5), or A4 as well on KB; with A4 added, necessary existence holds
  on every frame.
- **Anderson's variant** (with $H = P(G_A)$): existence needs A1a, A2 and H on B, KB or S5, and
  on KD45 only with A4 or A1b, and only with constant domains. A5 follows from A2 and H. Adding A1b, the
  direction Anderson removed, brings collapse back on B and S5, and on KB only together with A4.
- **Fitting's extensional variant** ($H = P(G)$, $N = P(NE)$): with constant domains no cell forces
  collapse, and the conclusion holds exactly for supersets of {A1a, A2, H} or {A1a, H, N}. With
  varying domains existence needs all of {A1a, A2, H, N} and reflexive frames (T, B, S4, S5);
  necessary existence also holds on KD45.
- **Benzmüller's simplified variant** (no positive empty property, closure under entailment,
  closure under arbitrary meets): every cell is consistent and none collapses; the conclusion
  holds exactly for the full axiom set with closure under local entailment, and never with
  closure under necessary entailment alone.

## Why it matters

Each of these variants has been studied before, and many single cells of the map are known: the
dependence of collapse on symmetry, the sufficiency of KB, the redundancy of A5 in Anderson's
variant, the absence of collapse in Anderson's, Fitting's and the simplified variant
[1, 2, 6, 3].
What we did not find is the complete picture: for each variant, exactly which axiom subsets and
frame conditions give the conclusion or collapse, and the minimal sets. The map shows, for
example, that in Scott's version neither A1b nor A4 ever matters, and that with rigid
properties and constant domains collapse disappears altogether.

## Proved vs checked

Every positive cell is proved in Lean 4 (core library, standard axioms only) in a shallow
embedding of higher-order modal logic on arbitrary Kripke frames of the class. Every negative
cell has an explicit finite countermodel, re-evaluated by a script. The tables cover the stated
axiom sets, semantic choices and nine frame classes; other variants (other definitions of
essence, other conjunction principles) are outside the map. We did not include the variants with
Gödel's binary conjunction axiom: that it fails on infinite domains is known
[7].
<!-- /owner-summary -->

This result extends the single cells and per-proof axiom dependencies of Scott's and Gödel's variants established with other provers (Benzmüller & Scott 2025; Benzmüller 2026); the analysis of Anderson's variant and the redundancy of its axioms (Benzmüller, Weber & Woltzenlogel Paleo 2017); Fitting's and Anderson's collapse-free variants (Fitting 2002; Benzmüller & Fuenmayor 2019); Benzmüller's simplified variant (2020). Our prior-art search (2026-10-19) covered:

- Benzmüller & Scott, "Notes on Gödel's and Scott's variants of the ontological argument", Monatshefte für Mathematik (2025), and its Isabelle/HOL development (AFP entry Notes_On_Goedels_Ontological_Argument, theory outline): per-theorem dependencies; modal collapse for Gödel variants 2 and 3 needs "only symmetry"; Scott's T3 and MC use Rsymm; Scott's variant fails in K only in the last step; UniqueEss lemmas (an essence of x is necessarily had only by x).
- Benzmüller, "Gödel's and Scott's Variants of the Ontological Argument in Lean 4 and TPTP THF" (arXiv 2609.26806, Oct 2026): Lean port with `#print axioms` dependency tables (Table 4) over S5, S4 and K embeddings, actualist/possibilist/mixed quantifiers; Th4 of Gödel variant 2 does not need Ax4; Scott's T3 and MC depend on symmetry alone; Gödel's 1970 axioms inconsistent in K.
- Benzmüller, "Proofs Without Nominals: Gödel's Ontological Argument, its Shallow Embedding, and the Open Questions of the Monatshefte Notes" (arXiv 2609.36279, 2026): the conjunction axiom must be emended (two or more conjuncts); collapse in K under the original axiom; in variant 3 an essence of x can only be "being x".
- Benzmüller & Woltzenlogel Paleo, automating Gödel's proof (2014–2016, incl. arXiv 1308.4526): KB suffices; Scott's axioms imply collapse; Gödel's original inconsistent.
- Benzmüller & Fuenmayor, positive properties, ultrafilters and modal collapse (arXiv 1910.08955): Anderson and Fitting variants avoid collapse.
- Benzmüller, "A (simplified) supreme being necessarily exists" (arXiv 2001.04701; KR 2020): simplified axioms valid in K and T without collapse.
- github.com/drewarrowood/godel-ontological (Lean 4): Scott with frame hypotheses; Symmetric gives local T3, S4 countermodel; rigid (world-independent) positivity makes A4 free but admits a countermodel to global T3; Russell-cut table (dropping A5 or A3).
- Fitting, Types, Tableaus and Gödel's God (2002); Sobel, Logic and Theism (2004); Anderson (1990); Wikipedia "Gödel's ontological proof" and "Modal collapse".
- Benzmüller, "A Comment on Modal Collapse and Ultrafilters in Gödel's Ontological Argument" (arXiv 2608.07578, 2026), replying to Odifreddi & Gomes, Logica Universalis (2026).
- Benzmüller, Weber & Woltzenlogel Paleo, "Computer-Assisted Analysis of the Anderson–Hájek Ontological Controversy" (Logica Universalis 2017; summary version read).
- Anderson & Gettings, "Gödel's Ontological Proof Revisited", in Gödel '96 (abstract only).

If you know of related work we missed, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was checked by scripts that run Lean proofs; the proof and check files are included so anyone can re-run them.

**K2.** Full-property constant-domain embedding, Scott essence: A1, A2, A5 imply $R\,w\,v \leftrightarrow v = w$ and modal collapse on every symmetric frame; adding A3 gives $\exists x\,G(x)$ and $\Box\exists x\,G(x)$ there, and $\Box\exists x\,G(x)$ on euclidean frames. A4 is not used.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

**K7.** Constant domain, rigid properties, Scott/Gödel essence, all 32 subsets × 9 classes certified: no consistent cell forces collapse; $\exists x\,G(x)$ and $\Box\exists x\,G(x)$ hold iff the subset contains A1,A2,A3, or A1,A3,A5 with Scott essence, on every frame.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

**K9.** Constant-domain full-property Anderson slice: $\exists x\,G_A(x)$ holds iff the subset contains A1a, A2, H and the class is B, KB, S5, or KD45 with A4; $\Box\exists x\,G_A(x)$ iff it contains A1a, A2, H on B, KB, KD45, S5. A5 is derivable from A2 and H.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

**K13.** Constant-domain extensional Fitting, all subsets of A1a,A1b,A2,H,N × nine frame classes: all 288 cells are consistent and permit noncollapse; both existence conclusions hold exactly for supersets of $\lbrace A1a,A2,H\rbrace $ or $\lbrace A1a,H,N\rbrace $. A1b is unnecessary.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

**K15.** Varying-domain (actualist) full-property Anderson, 32 subsets × 9 classes: as in constant domains except $\exists^E x\,G_A(x)$ on KD45 with A4 now fails; a 3-world KD45 model satisfies all five axioms, but its God-like being does not exist at the root.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

**K16.** Varying-domain (actualist) extensional Fitting, 32 subsets of A1a,A1b,A2,H,N × 9 classes: $\exists^E x\,G(x)$ holds iff the subset contains $\lbrace A1a,A2,H,N\rbrace $ on T, B, S4, S5; $\Box\exists^E x\,G(x)$ also on KD45. K13's sets $\lbrace A1a,A2,H\rbrace $ and $\lbrace A1a,H,N\rbrace $ fail in S5.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

**K18.** Varying-domain rigid Scott, 64 subsets of A1a,A1b,A2..A5 × 9 classes: A1b is never needed; $\exists^E G$ iff ⊇{A1a,A2,A3,A5} on T,B,S4,S5 or +A4 on KB; $\Box\exists^E G$ iff ⊇{A1a,A2,A3,A5} on T,B,S4,S5,KD45 or +A4 on any frame.

- Status: derived · author check only
- Machine-checked: 2 of 2 check scripts passed.
- Prior art: partial prior art

**K21.** Anderson $G_A$, full properties, 64 subsets of A1a,A1b,A2,H,A4,A5 × 9 classes × constant/varying domains: collapse iff ⊇{A1a,A1b,A2,H} on B,S5, or +A4 on KB; $\exists G_A$ on KD45 needs A4 or A1b and constant domains; otherwise as K9/K15.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

**K22.** Full-property Scott, constant or varying domains, 64 subsets of A1a,A1b,A2–A5 × 2 essences × 9 classes: A1b is never needed; $\exists G$ iff ⊇{A1a,A2,A3,A5} on B,KB,S5 (box also KD45); collapse iff ⊇{A1a,A2,A5} there; Gödel essence with {A1a,A2,A5} has no model.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

**K24.** Constant-domain full-property simplified AllMeet slice (216 cells): every cell is consistent and permits noncollapse; $\exists G$ and $\Box\exists G$ hold exactly for all three axioms with local/either closure. Every other cell has a finite countermodel.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

**K28.** Varying-domain full-property simplified slices: AllMeet has exactly K24’s 216-cell outcomes; binary closure has 216 consistent, noncollapsing cells refuting $\exists^E G$ and $\Box\exists^E G$, even with A1w. Positive AllMeet cells require all axioms and local/either closure.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

## Discussion

The map is a refinement of work that is largely known, not a new argument. Its value is
completeness: for each variant, every subset of the axioms and every listed frame class is decided
with a certificate, so the minimal sets and the frame boundaries can be read off rather than
inferred from separate studies. Several entries agree with results already established with
other provers [1, 2, 6], which we take
as a check on our encoding rather than as findings.

The map covers only the stated choices: a shallow embedding of higher-order modal logic, Scott's
and Gödel's definitions of essence, the listed variants, nine frame classes and two kinds of
domain. Other definitions of essence, other readings of positivity (for example world-relative
and rigid mixtures), Gödel's conjunction axiom in all slices [7], and
logics beyond these frame classes are outside it. A cell decided here can therefore change under
a different encoding, and claims of minimality hold relative to the listed axioms.

What a reader can take away is where the strength of each variant sits: in Scott's version the
weight lies on A1a, A2, A3 and A5 together with symmetry, while A1b and A4 are idle; in
Anderson's version the dropped complement direction is exactly the switch for collapse; and in
the rigid and simplified readings, existence holds without collapse. Natural next steps are the
open cells the run left (mixed conjunction principles in some slices) and other definitions of
essence.

## How to verify

Run each script in `claims/ontological-variant-map/checks/` with `python -I <script>`; it passes if it
exits with status 0. The results recorded in the original run are in
`claims/ontological-variant-map/results/`; the full claim text is in `claims/ontological-variant-map/claim.md`.

## Provenance

- run: 20261018-1933
- claims: K2, K7, K9, K13, K15, K16, K18, K21, K22, K24, K28
- run-folder commit: 338871c09385f72bc0f657c9a639ef6a3c825566
- K2 author: r1 (claude)
- K7 author: r1 (claude)
- K9 author: r1 (claude)
- K13 author: r2 (codex)
- K15 author: r1 (claude)
- K16 author: r1 (claude)
- K18 author: r1 (claude)
- K21 author: r1 (claude)
- K22 author: r1 (claude)
- K24 author: r2 (codex)
- K28 author: r2 (codex)

## References

1. <!-- cite:benzmueller2025notes --> Benzm\"uller, Christoph and Scott, Dana S.. 2025. Notes on G\"odel's and Scott's variants of the ontological argument. Monatshefte f\"ur Mathematik. [Link](https://link.springer.com/article/10.1007/s00605-025-02078-x)
2. <!-- cite:benzmueller2026lean --> Benzm\"uller, Christoph. 2026. G\"odel's and Scott's Variants of the Ontological Argument in Lean 4 and TPTP THF. [Link](https://arxiv.org/abs/2609.26806)
3. <!-- cite:benzmueller2020simplified --> Benzm\"uller, Christoph. 2020. A (Simplified) Supreme Being Necessarily Exists, says the Computer: Computationally Explored Variants of G\"odel's Ontological Argument. Proceedings of KR 2020. [Link](https://arxiv.org/abs/2001.04701)
4. <!-- cite:benzmueller2019ultrafilters --> Benzm\"uller, Christoph and Fuenmayor, David. 2019. Computer-supported Analysis of Positive Properties, Ultrafilters and Modal Collapse in Variants of G\"odel's Ontological Argument. [Link](https://arxiv.org/abs/1910.08955)
5. <!-- cite:fitting2002types --> Fitting, Melvin. 2002. Types, Tableaus, and G\"odel's God. Kluwer
6. <!-- cite:benzmueller2017hajek --> Benzm\"uller, Christoph and Weber, Leon and Woltzenlogel Paleo, Bruno. 2017. Computer-Assisted Analysis of the Anderson--H\'ajek Ontological Controversy. Logica Universalis
7. <!-- cite:benzmueller2026ultrafilters --> Benzm\"uller, Christoph. 2026. A Comment on Modal Collapse and Ultrafilters in G\"odel's Ontological Argument. [Link](https://arxiv.org/abs/2608.07578)

<!-- autoresearch:revisions -->
## Revisions

- 2026-10-21 — Production note: Lean proofs run inside check scripts are now described as such, separately from harness-built proofs
