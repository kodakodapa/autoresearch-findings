---
layout: default
title: "Polynomial calculus degree above p for the onto functional pigeonhole principle with surplus divisible by p squared"
scholar: {"citation_title": "Polynomial calculus degree above p for the onto functional pigeonhole principle with surplus divisible by p squared", "citation_author": "Lindheim, Bj\u00f6rn", "citation_publication_date": "2026/11/06", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/pc-degree-above-p-onto-fphp-surplus-p-squared.html", "citation_keywords": "C3", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/pc-degree-above-p-onto-fphp-surplus-p-squared/paper.pdf", "citation_doi": "10.5281/zenodo.23999623"}
---

# Polynomial calculus degree above p for the onto functional pigeonhole principle with surplus divisible by p squared

Cite as: https://doi.org/10.5281/zenodo.23999623

<!-- owner-summary -->
## Setting

The onto functional pigeonhole principle $\mathrm{onto\text{-}FPHP}^{n+k}\_n$ says that $n+k$
pigeons can be mapped one-to-one onto $n$ holes; it is false for every $k\ge1$. In Boolean
variables $x\_{ij}$ (pigeon $i$ in hole $j$) its axioms are $\sum\_j x\_{ij}-1$,
$\sum\_i x\_{ij}-1$, $x\_{ij}x\_{i'j}$ and $x\_{ij}x\_{ij'}$, the linear encoding used for this family
[1, 2]. A polynomial calculus (PC) refutation over
$\mathbb F\_p$ derives $1$ from the axioms and the Boolean axioms $x^2-x$ by linear combinations
and multiplication by a variable; its degree is the largest degree of a line.

When $p$ does not divide $k$ there is a degree-1 refutation. When $p$ divides $k$ but $p^2$ does
not, the PC degree is exactly $p$ for $n\ge2p-3$ (a companion finding on this site). This finding
is about surplus divisible by $p^2$.

## Result

For every prime $p$, every $c\ge1$, and every $n\ge2p-1$, $\mathrm{onto\text{-}FPHP}^{n+cp^2}\_n$ has
no PC refutation over $\mathbb F\_p$ of degree at most $p$. Its PC degree is therefore at least
$p+1$. With the companion result, surplus divisible by $p^2$ is strictly harder for PC over
$\mathbb F\_p$ than surplus divisible only by $p$, for every prime and from a linear threshold in
$n$.

The proof constructs, for every prime $p$, an explicit integer matrix on $2p-1$ rows and columns
(a "square lift"). From it comes a balanced design, which serves as a degree-$p$ witness that no
refutation of that degree exists. The cases $p=2$ ($n\ge3$, surplus $4c$) and $p=3$ ($n\ge5$,
surplus $9c$) are also proved separately.

## Why it matters

Razborov's Question 7 asks whether PC degree for surplus $p^\ell$ stays bounded in characteristic
$p$ [2]. At $\ell=2$ the known PC lower bound is $3$, for
$N\ge2(21+3p^2)-p$ [3]. This result gives $p+1$ from $n=2p-1$: larger for every
$p\ge3$, and at a far smaller $n$. Earlier runs of this programme proved $p+1$ for $p=3,5,7$
separately; this result covers every prime at once.

## Proved vs checked

Everything is proved in Lean 4 and kernel-checked, for all primes $p$, all $c$ and all
$n\ge2p-1$; nothing is checked only up to a bound. The proofs use only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. The main theorem is stated for standard
(syntactic) PC with Boolean axioms. A second agent in the run, working separately from the
author, re-proved all six statements in Lean. No person has reviewed the proofs; the evidence is
the kernel check and the independent re-proof.
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

This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the proof and check files are included so anyone can re-run them.

Promoted declaring sources are included under `checks/library/`.

## K1

For every prime $p$, $\mathrm{SquareLiftAssumption}(p)$ holds, i.e. there exists an integral square lift on $2p-1$ rows and columns.

Status: proved (axioms: propext, Classical.choice, Quot.sound) · independently re-proved (skeptic/codex)

Kind: theorem

Evidence:
- proof `checks/K1-Unconditional.lean`: Work.UniformC3.squareLiftAssumption — pass (`results/K1-1.json`)

Prior art: partial prior art (answer: `prior-art/R6.md`)

### Provenance

- run: 20261102-1249
- claim: K1
- author: pr (codex)
- round: 1
- run-folder commit: 359fa20477b8d26a5d2ef8a16e5465474e74b452
- check results: K1-1.json

## K2

For every prime $p$ and natural $c$, some $T$ satisfies $\mathrm{Bal}(p,2p-1,cp^2,T,T,e)$ for every $e\le p-1$, and $p\mid T([])-1$.

Status: proved (axioms: propext, Classical.choice, Quot.sound) · independently re-proved (skeptic/codex)

Kind: theorem

Evidence:
- proof `checks/K1-Unconditional.lean`: Work.UniformC3.uniform\_unit\_design\_unconditional — pass (`results/K2-1.json`)

Prior art: partial prior art (answer: `prior-art/R6.md`)

### Provenance

- run: 20261102-1249
- claim: K2
- author: pr (codex)
- round: 1
- run-folder commit: 359fa20477b8d26a5d2ef8a16e5465474e74b452
- check results: K2-1.json

## K3

For every prime $p$, natural $c$, and $n\ge2p-1$, $\mathrm{ontoFPHP}(n,cp^2)$ has no degree-$p$ $\mathrm{PPCRefutation}$ modulo $p$ (functional encoding, PC line degree).

Status: proved (axioms: propext, Classical.choice, Quot.sound) · independently re-proved (skeptic/codex)

Kind: theorem

Evidence:
- proof `checks/K1-Unconditional.lean`: Work.UniformC3.uniform\_no\_degree\_p\_unconditional — pass (`results/K3-1.json`)

Prior art: partial prior art (answer: `prior-art/R6.md`)

### Provenance

- run: 20261102-1249
- claim: K3
- author: pr (codex)
- round: 1
- run-folder commit: 359fa20477b8d26a5d2ef8a16e5465474e74b452
- check results: K3-1.json

## K4

For every prime $p$, natural $c$, and $n\ge2p-1$, $\mathrm{ontoFPHP}(n,cp^2)$ has no standard polynomial-calculus refutation modulo $p$ of line degree at most $p$ (functional encoding).

Status: proved (axioms: propext, Classical.choice, Quot.sound) · independently re-proved (skeptic/codex)

Kind: theorem

Evidence:
- proof `checks/K1-Unconditional.lean`: Work.UniformC3.uniform\_no\_standard\_degree\_p\_unconditional — pass (`results/K4-1.json`)

Prior art: partial prior art (answer: `prior-art/R6.md`)

### Provenance

- run: 20261102-1249
- claim: K4
- author: pr (codex)
- round: 1
- run-folder commit: 359fa20477b8d26a5d2ef8a16e5465474e74b452
- check results: K4-1.json

## K5

For all natural $c$ and $n\ge3$, $\mathrm{ontoFPHP}(n,4c)$ has no standard polynomial-calculus refutation modulo $2$ of line degree at most $2$ (functional encoding).

Status: proved (axioms: propext, Classical.choice, Quot.sound) · independently re-proved (skeptic/codex)

Kind: theorem

Evidence:
- proof `checks/K5-Main.lean`: Work.UniformC3.no\_standard\_degree\_two — pass (`results/K5-1.json`)

Prior art: partial prior art (answer: `prior-art/R6.md`)

### Provenance

- run: 20261102-1249
- claim: K5
- author: pr (codex)
- round: 1
- run-folder commit: 359fa20477b8d26a5d2ef8a16e5465474e74b452
- check results: K5-1.json

## K6

For all natural $c$ and $n\ge5$, $\mathrm{ontoFPHP}(n,9c)$ has no standard polynomial-calculus refutation modulo $3$ of line degree at most $3$ (functional encoding).

Status: proved (axioms: propext, Classical.choice, Quot.sound) · independently re-proved (skeptic/codex)

Kind: theorem

Evidence:
- proof `checks/K5-Main.lean`: Work.UniformC3.no\_standard\_degree\_three — pass (`results/K6-1.json`)

Prior art: partial prior art (answer: `prior-art/R6.md`)

### Provenance

- run: 20261102-1249
- claim: K6
- author: pr (codex)
- round: 1
- run-folder commit: 359fa20477b8d26a5d2ef8a16e5465474e74b452
- check results: K6-1.json

## Discussion

<!-- owner-discussion -->
This is a lower bound, not an exact value. The best upper bound we know at surplus $p^2$ is $p^2$,
from Riis's criterion [4, 2]. So for surplus $p^2$ the degree
lies between $p+1$ and $p^2$. At $p=2$ the separate exact result that the degree is 4 for surplus 4
($n\ge5$) is in the same library. The bound does not grow with $\ell$ and does not answer
Question 7. We have not checked the proof of Riis and Sitharam's Theorem 33, which we cite for
comparison only.
<!-- /owner-discussion -->

## References

1. <!-- cite:beame1998counting --> Beame, Paul and Riis, Søren. 1998. More on the relative strength of counting principles. Proof Complexity and Feasible Arithmetics. [Link](https://homes.cs.washington.edu/~beame/papers/riis.pdf)
2. <!-- cite:razborov2001php --> Razborov, Alexander A.. 2002. Proof complexity of pigeonhole principles. Developments in Language Theory (DLT 2001). [Link](https://people.cs.uchicago.edu/~razborov/files/php_survey.pdf)
3. <!-- cite:riis1997nonconstant --> Riis, Søren and Sitharam, Meera. 1997. Non-constant degree lower bounds imply linear degree lower bounds. [Link](https://eccc.weizmann.ac.il/report/1997/048/)
4. <!-- cite:riis1993independence --> Riis, Søren. 1993. Independence in Bounded Arithmetic

<!-- autoresearch:revisions -->
## Revisions

- 2026-11-06 — Math rendering on the site; paper lists only cited references
