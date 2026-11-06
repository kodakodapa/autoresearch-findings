---
layout: post
title: "Exact polynomial calculus degree p for the onto functional pigeonhole principle with surplus divisible by p"
date: 2026-11-06
scholar: {"citation_title": "Exact polynomial calculus degree p for the onto functional pigeonhole principle with surplus divisible by p", "citation_author": "Lindheim, Bj\u00f6rn", "citation_publication_date": "2026/11/06", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/exact-pc-degree-onto-fphp-first-level.html", "citation_keywords": "C3", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/exact-pc-degree-onto-fphp-first-level/paper.pdf", "citation_doi": "10.5281/zenodo.23996565"}
---

## Summary

Cite as: https://doi.org/10.5281/zenodo.23996565

<!-- owner-summary -->
## Setting

The onto functional pigeonhole principle $\mathrm{onto\text{-}FPHP}^{n+k}_n$ says that $n+k$
pigeons can be mapped one-to-one onto $n$ holes. It is false for every $k\ge1$. As a system of
polynomial equations in Boolean variables $x_{ij}$ (pigeon $i$ sits in hole $j$) it has the
axioms $\sum_j x_{ij}-1$ (each pigeon sits in a hole), $\sum_i x_{ij}-1$ (each hole holds exactly
one pigeon), $x_{ij}x_{i'j}$ (no two pigeons share a hole) and $x_{ij}x_{ij'}$ (no pigeon sits in
two holes). This is the linear encoding used in the literature on this family
[1, 2].

A polynomial calculus (PC) refutation over the field $\mathbb F_p$ derives the polynomial $1$
from the axioms and the Boolean axioms $x^2-x$, using linear combinations and multiplication by a
variable. Its degree is the largest degree of a line. The PC degree of the principle is the least
degree of a refutation. When $p$ does not divide $k$, summing the pigeon axioms and subtracting
the hole axioms gives the constant $-k$, a degree-1 refutation. The question is what happens when
$p$ divides $k$.

## Result

For every prime $p$, every $c$ not divisible by $p$, and every $n\ge 2p-3$, the PC degree of
$\mathrm{onto\text{-}FPHP}^{n+pc}_n$ over $\mathbb F_p$ is exactly $p$: there is a refutation of
degree $p$, and none of degree $p-1$. More generally, whenever $p$ divides $k$ and $n\ge2p-3$,
there is no refutation of degree $p-1$. The same formula therefore has PC degree $p$ over
$\mathbb F_p$ and PC degree $1$ over $\mathbb F_q$ for every prime $q$ not dividing $pc$.

## Why it matters

Razborov's survey asks (Question 7) whether $\mathrm{onto\text{-}FPHP}^{n+p^\ell}_n$ has
bounded-degree PC refutations in characteristic $p$ [2]. The upper bound $p$ at
the first level comes from Riis's criterion [3]. The known lower bounds are
for the weaker Nullstellensatz system [1] and, for PC, a bound that grows with
$\ell$ for large $n$ [4]. This result fixes the degree exactly at the first
level (surplus divisible by $p$ but not by $p^2$), for every prime, from a small linear threshold
in $n$.

## Proved vs checked

Everything is proved in Lean 4 and kernel-checked, for all primes $p$ and all $n\ge2p-3$; nothing
is checked only up to a bound. The proofs use only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. A second agent in the run, working separately from the
author, re-proved each of the three statements in Lean. No person has reviewed the proofs; the
evidence is the kernel check and the independent re-proof.

The Lean statements are for the library's formulation of PC, in which lines are functions on
the Boolean cube. A later theorem of the same library shows that a refutation of degree $D$ in
standard (syntactic) PC over $\mathbb F_p$ exists exactly when one exists in the library's
formulation, so the result holds verbatim for standard PC (`std_pc_degree_exact`).
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

**K13.** `Work.Lucas.pc_degree_exact`: for every prime $p$ (`IsPrime p`), every $c$ with $p\nmid c$, every $n\ge2p-3$ and every $D$: `ontoFPHP n (p*c)` has a degree-$D$ `PPCRefutation p` iff $p\le D$ (PC degree over $\mathbb Z/p$ of onto-FPHP$^{n+pc}_n$ is exactly $p$).

- Status: proved (axioms: propext, Classical.choice, Quot.sound) · independently re-proved (skeptic/codex)
- Machine-checked: no check scripts.
- Prior art: partial prior art

**K14.** `Work.Peel.pc_degree_ge_p`: for every prime $p$ (`IsPrime p`), every $k$ with $p\mid k$ and every $n\ge2p-3$, `ontoFPHP n k` (onto-FPHP$^{n+k}_n$, functional encoding) has no `PPCRefutation p` of degree $p-1$ (polynomial calculus over $\mathbb Z/p$).

- Status: proved (axioms: propext, Classical.choice, Quot.sound) · independently re-proved (skeptic/codex)
- Machine-checked: no check scripts.
- Prior art: partial prior art

**K15.** `Work.Lucas.separation`: for primes $p,q$, $p\nmid c$, $q\nmid pc$, $n\ge2p-3$: `ontoFPHP n (p*c)` has a degree-$D$ `PPCRefutation p` iff $p\le D$, and has a degree-1 `PPCRefutation q`.

- Status: proved (axioms: propext, Classical.choice, Quot.sound) · independently re-proved (skeptic/codex)
- Machine-checked: no check scripts.
- Prior art: partial prior art

## Discussion

The degree here is a constant, $p$. The result says nothing about growth with $\ell$, which is
what Question 7 is about. Riis and Sitharam's Theorem 33 gives degree at least $2^\ell-1$ for
surplus $p^\ell$ once $N\ge(21+3p^2)(2^\ell-2)-p$ [4]. At $\ell=1$ that bound
is 1, and surplus $pc$ with $c>1$ is outside its family. We have not checked the proof of
Theorem 33. Below $n=2p-3$ the degree is not determined here. The Nullstellensatz degree of
Beame and Riis [1] is multiplier degree, one less than the line degree used here.

## How to verify
Promoted declaring sources are included under `checks/library/`; publication checks import their library modules and inspect each theorem with `#print axioms`.

Run each script in `claims/exact-pc-degree-onto-fphp-first-level/checks/` with `python -I <script>`; it passes if it
exits with status 0. The results recorded in the original run are in
`claims/exact-pc-degree-onto-fphp-first-level/results/`; the full claim text is in `claims/exact-pc-degree-onto-fphp-first-level/claim.md`.

## Provenance

- run: 20261027-0607
- claims: K13, K14, K15
- run-folder commit: 908b30496168c757d5eba6ba4ba761dbab7933b8
- K13 author: th (claude)
- K14 author: th (claude)
- K15 author: th (claude)

## References

1. <!-- cite:beame1998counting --> Beame, Paul and Riis, Søren. 1998. More on the relative strength of counting principles. Proof Complexity and Feasible Arithmetics. [Link](https://homes.cs.washington.edu/~beame/papers/riis.pdf)
2. <!-- cite:razborov2001php --> Razborov, Alexander A.. 2002. Proof complexity of pigeonhole principles. Developments in Language Theory (DLT 2001). [Link](https://people.cs.uchicago.edu/~razborov/files/php_survey.pdf)
3. <!-- cite:riis1993independence --> Riis, Søren. 1993. Independence in Bounded Arithmetic
4. <!-- cite:riis1997nonconstant --> Riis, Søren and Sitharam, Meera. 1997. Non-constant degree lower bounds imply linear degree lower bounds. [Link](https://eccc.weizmann.ac.il/report/1997/048/)
