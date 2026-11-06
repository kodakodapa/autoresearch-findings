---
layout: post
title: "Polynomial calculus degree at least 5 over F2 for the onto functional pigeonhole principle with surplus 8"
date: 2026-11-06
scholar: {"citation_title": "Polynomial calculus degree at least 5 over F2 for the onto functional pigeonhole principle with surplus 8", "citation_author": "Lindheim, Bj\u00f6rn", "citation_publication_date": "2026/11/06", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/pc-degree-5-onto-fphp-surplus-8.html", "citation_keywords": "C3", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/pc-degree-5-onto-fphp-surplus-8/paper.pdf", "citation_doi": "10.5281/zenodo.24008746"}
---

## Summary

Cite as: https://doi.org/10.5281/zenodo.23996615 (all versions; this version: https://doi.org/10.5281/zenodo.24008746)

<!-- owner-summary -->
## Setting

The onto functional pigeonhole principle $\mathrm{onto\text{-}FPHP}^{n+k}\_n$ says that $n+k$
pigeons can be mapped one-to-one onto $n$ holes; it is false for every $k\ge1$. In Boolean
variables $x\_{ij}$ (pigeon $i$ in hole $j$) its axioms are $\sum\_j x\_{ij}-1$,
$\sum\_i x\_{ij}-1$, $x\_{ij}x\_{i'j}$ and $x\_{ij}x\_{ij'}$, the linear encoding used for this family
[1, 2]. These results are for the linear encoding only: translating the CNF clause by clause instead turns each pigeon clause into a polynomial of degree $n$ [2], so degree bounds below $n$ say nothing about that encoding. A polynomial calculus (PC) refutation over
$\mathbb F\_2$ derives $1$ from the axioms and the Boolean axioms $x^2-x$ by linear combinations
and multiplication by a variable; its degree is the largest degree of a line.

Over $\mathbb F\_2$, with surplus $k=2^\ell$, the PC degree is exactly 2 at $k=2$ and exactly 4 at
$k=4$ (companion results in the same library). This finding is about $k=8$.

## Result

For every $n\ge7$, $\mathrm{onto\text{-}FPHP}^{n+8}\_n$ has no PC refutation over $\mathbb F\_2$ of
degree 4. Its PC degree is therefore at least 5, while the general bound for surplus divisible
by $p^2$ (companion finding) gives only 3 at $p=2$. So at $p=2$ the third level is strictly
harder than the second for every $n\ge7$.

The proof combines a general argument with a finite certificate of 95,550 steps, each checked by
the Lean kernel.

## Why it matters

Razborov's Question 7 asks whether PC degree for surplus $p^\ell$ stays bounded in characteristic
$p$ [2]. Riis and Sitharam's Theorem 33 gives degree at least 7 for $k=8$ once
$N\ge196$ [3], which is stronger than this result for large $n$. The range
$7\le n<196$ is not covered by that theorem. This result covers it, and it is machine-checked.

## Proved vs checked

The result is proved in Lean 4 for every $n\ge7$; the certificate is part of the proof, not a
separate check up to a bound. The proof uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. A second agent in the run checked the certificate
independently, with its own program written from the Lean definitions, not from the author's
code. That is an independent check of the certificate, not an independent Lean re-proof. No
person has reviewed the proof. The same library also states the result for standard (syntactic)
PC (`std_no_deg4_k8`).
<!-- /owner-summary -->

This result extends:

- Riis-Sitharam, ECCC TR97-048, Theorem 33: PC degree >= 2^l - 1 for onto-PHP^{N+p^l}_N over characteristic p once N >= (21+3p^2)(2^l - 2) - p (same family; proof not checked by us; at l = 2 this is >= 3 against our >= p+1 from n = 2p-1; at p = 2, l = 3 it is >= 7 for N >= 196 against our >= 5 for n >= 7).
- Beame-Riis 1998, Theorem 8.1 and Lemma 8.7: Nullstellensatz degree between 2^l - 1 and p^l - 1 (multiplier degree) for the same family; Section 10 lists polynomial-calculus lower bounds as open.
- Riis 1993, as Theorem 8 of Razborov's survey: degree-d PC refutations when C(m,d) and C(n,d) differ mod p, which gives the matching upper bound p for k = pc, p not dividing c (via Lucas).
- Razborov, Proof complexity of pigeonhole principles (2001), Question 7: the fixed-p, fixed-l bounded-degree question for onto-FPHP^{n+p^l}_n.
- Miksa-Nordstrom (JACM 2024): general PC degree method; onto-FPHP with m = n+1 easy (Riis); the case of characteristic dividing the surplus not covered.

Our prior-art search (2026-11-05) covered:

- Riis, Sitharam, Non-constant degree lower bounds imply linear degree lower bounds, ECCC TR97-048 (1997), pp. 36-38 and 45-46 (Theorem 33, Propositions 27 and 28), opened 2026-10-29
- Beame, Riis, More on the relative strength of counting principles, DIMACS Series 39 (1998), homes.cs.washington.edu/~beame/papers/riis.pdf: Theorem 8.1, Lemma 8.7, Section 10, opened 2026-10-27 and 2026-11-01
- Razborov, Proof complexity of pigeonhole principles, DLT 2001 (LNCS 2295), people.cs.uchicago.edu/~razborov/files/php_survey.pdf: Theorem 8, Question 7, footnote 5, opened 2026-10-27 and 2026-10-29
- Riis, BRICS Report RS-99-29, opened 2026-10-29
- Miksa, Nordstrom, A generalized method for proving polynomial calculus degree lower bounds (CCC 2015; JACM 2024; arXiv 1505.01358), opened 2026-10-27
- de Rezende et al., Theory of Computing 21(6) (2025), opened 2026-10-29
- Lauria et al., Theory of Computing 21(4) (2025), opened 2026-10-27

The checkers' full answers, with every query and file they searched, are published with this finding (`prior-art/`).

If you know of related work we missed, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the verification steps below build the published programme library.

Promoted declaring sources are included under `checks/library/`.

**K18.** Lean `Work.L3.Main.no_deg4`: for every $n\ge7$, `ontoFPHP n 8` (onto-FPHP$^{n+8}\_n$, functional encoding) has no degree-4 `PPCRefutation 2` (polynomial calculus over $\mathbb Z/2$, line degree 4). Unconditional.

- Status: proved (axioms: propext, Classical.choice, Quot.sound)
- Machine-checked: no check scripts.
- Prior art: partial prior art

## Discussion

The upper bound from Riis's criterion is 8 [4, 2], so for
$k=8$ the degree lies between 5 and 8 for $n\ge7$. This is one case, not a growth result in
$\ell$. We have not checked the proof of Theorem 33 and cite it for comparison only.

## How to verify

Lean toolchain: `leanprover/lean4:v4.35.0`. [Programme library at the recorded commit](https://github.com/kodakodapa/autoresearch-findings/tree/2abad0979eeb03ede3a77490f45a4f381119ff02/programmes/proof-complexity). Install elan, then pin the library subtree while keeping the finding checks:

```sh
git clone https://github.com/kodakodapa/autoresearch-findings.git
cd autoresearch-findings
git checkout 2abad0979eeb03ede3a77490f45a4f381119ff02 -- programmes/proof-complexity
cd programmes/proof-complexity && lake build
AR_LIBRARY=$PWD python -I ../../claims/pc-degree-5-onto-fphp-surplus-8/checks/lean-K18.py
```

`checks/run-copies/`: the author's working copies from the run; they import the run's private `Work` package and are not built standalone.

## Provenance

- run: 20261028-0841
- claims: K18
- run-folder commit: 19b6167239a90c29b4a3f0ff0f64c79016faf2f8
- K18 author: pr (claude)

## References

1. <!-- cite:beame1998counting --> Beame, Paul and Riis, Søren. 1998. More on the relative strength of counting principles. Proof Complexity and Feasible Arithmetics. [Link](https://homes.cs.washington.edu/~beame/papers/riis.pdf)
2. <!-- cite:razborov2001php --> Razborov, Alexander A.. 2002. Proof complexity of pigeonhole principles. Developments in Language Theory (DLT 2001). [Link](https://people.cs.uchicago.edu/~razborov/files/php_survey.pdf)
3. <!-- cite:riis1997nonconstant --> Riis, Søren and Sitharam, Meera. 1997. Non-constant degree lower bounds imply linear degree lower bounds. [Link](https://eccc.weizmann.ac.il/report/1997/048/)
4. <!-- cite:riis1993independence --> Riis, Søren. 1993. Independence in Bounded Arithmetic

<!-- autoresearch:revisions -->
## Revisions

- 2026-11-06 — Math rendering on the site; paper lists only cited references
- 2026-11-06 — Library published buildable; verification steps; run copies labelled
- 2026-11-06 — Verification steps; stale run copies removed; encoding stated
