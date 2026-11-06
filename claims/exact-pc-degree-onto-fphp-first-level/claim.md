# Exact polynomial calculus degree p for the onto functional pigeonhole principle with surplus divisible by p

Cite as: https://doi.org/10.5281/zenodo.23996564 (all versions; this version: https://doi.org/10.5281/zenodo.24012206)

<!-- owner-summary -->
## Setting

The onto functional pigeonhole principle $\mathrm{onto\text{-}FPHP}^{n+k}_n$ says that $n+k$
pigeons can be mapped one-to-one onto $n$ holes. It is false for every $k\ge1$. As a system of
polynomial equations in Boolean variables $x_{ij}$ (pigeon $i$ sits in hole $j$) it has the
axioms $\sum_j x_{ij}-1$ (each pigeon sits in a hole), $\sum_i x_{ij}-1$ (each hole holds exactly
one pigeon), $x_{ij}x_{i'j}$ (no two pigeons share a hole) and $x_{ij}x_{ij'}$ (no pigeon sits in
two holes). This is the linear encoding used in the literature on this family
[1, 2]. These results are for the linear encoding only: translating the CNF clause by clause instead turns each pigeon clause into a polynomial of degree $n$ [2], so degree bounds below $n$ say nothing about that encoding.

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

This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the verification steps below build the published programme library.

Promoted declaring sources are included under `checks/library/`.

## K13

`Work.Lucas.pc_degree_exact`: for every prime $p$ (`IsPrime p`), every $c$ with $p\nmid c$, every $n\ge2p-3$ and every $D$: `ontoFPHP n (p*c)` has a degree-$D$ `PPCRefutation p` iff $p\le D$ (PC degree over $\mathbb Z/p$ of onto-FPHP$^{n+pc}_n$ is exactly $p$).

Status: proved (axioms: propext, Classical.choice, Quot.sound) · independently re-proved (skeptic/codex)

Kind: theorem

Evidence:
- proof `checks/run-copies/K13-Lucas.lean`: Work.Lucas.pc\_degree\_exact — pass (`results/K13-2.json`)
- reasoning: Lower bound: K14 (no degree $p-1$) plus monotonicity of PPCDerivable in the degree. Upper bound: library OntoLucas.ontoFPHP\_upper at $t=p$, whose unit hypothesis is $\binom{n+pc}{p}-\binom np\equiv c\not\equiv0$ mod $p$; proved by $p\mid\binom pr$ for $0<r<p$, Pascal's rule and telescoping in $c$. Convention: PC line degree, functional encoding. This agrees with Beame-Riis Lemma 8.7: their NS degree $p^l-1$ counts multiplier degree, and the products have degree $p^l$, which is line degree $p$ at $l=1$.

Prior art: partial prior art (answer: `prior-art/R13.md`)

### Provenance

- run: 20261027-0607
- claim: K13
- author: th (claude)
- round: 3
- run-folder commit: 908b30496168c757d5eba6ba4ba761dbab7933b8
- check results: K13-2.json

## K14

`Work.Peel.pc_degree_ge_p`: for every prime $p$ (`IsPrime p`), every $k$ with $p\mid k$ and every $n\ge2p-3$, `ontoFPHP n k` (onto-FPHP$^{n+k}_n$, functional encoding) has no `PPCRefutation p` of degree $p-1$ (polynomial calculus over $\mathbb Z/p$).

Status: proved (axioms: propext, Classical.choice, Quot.sound) · independently re-proved (skeptic/codex)

Kind: theorem

Evidence:
- proof `checks/run-copies/K14-Peel.lean`: Work.Peel.pc\_degree\_ge\_p — pass (`results/K14-2.json`)
- reasoning: Paper proof (mirrors the Lean chain). Library criterion K4: if $\mathrm{EXT}_p(n_0,k,d)$ holds for all $d\le p-2$ then no degree-$(p-1)$ refutation for any $n\ge n_0$. EXT at level $d$ is proved by peeling: the flag lemma (K8) turns a balanced $f$ into a tower of links; at level 0 subtract a symmetric window, and at level $j$ subtract a block-product window ($j$ rectangles $\times$ unit blocks $\times$ a symmetric degree-$(d-j+1)$ design on a rest block), which equals $(d-j+1)!\cdot RP$ on $j$-matchings. The residual has zero links, so S\_j (K10) puts it in the span of rectangle products. Every factorial used is at most $(p-1)!$, a unit mod prime $p$; the blocks fit when $2d+1\le n$, i.e. $n\ge2p-3$. ExtLin.EXT\_of\_span (K5) closes the step.

Prior art: partial prior art (answer: `prior-art/R13.md`)

### Provenance

- run: 20261027-0607
- claim: K14
- author: th (claude)
- round: 3
- run-folder commit: 908b30496168c757d5eba6ba4ba761dbab7933b8
- check results: K14-2.json

## K15

`Work.Lucas.separation`: for primes $p,q$, $p\nmid c$, $q\nmid pc$, $n\ge2p-3$: `ontoFPHP n (p*c)` has a degree-$D$ `PPCRefutation p` iff $p\le D$, and has a degree-1 `PPCRefutation q`.

Status: proved (axioms: propext, Classical.choice, Quot.sound) · independently re-proved (skeptic/codex)

Kind: theorem

Evidence:
- proof `checks/run-copies/K13-Lucas.lean`: Work.Lucas.separation — pass (`results/K15-2.json`)
- reasoning: Over $\mathbb F_p$: K13. Over $\mathbb F_q$ with $q\nmid pc$: library OntoFPHP.ontoFPHP\_deg1 needs a unit $k^{-1}$ mod $q$, supplied by Bezout. The gap is $p$ versus 1 and is constant in $n$ for fixed $p$, so this separates characteristics along the parameter $p$, not asymptotically in $n$.

Prior art: partial prior art (answer: `prior-art/R13.md`)

### Provenance

- run: 20261027-0607
- claim: K15
- author: th (claude)
- round: 3
- run-folder commit: 908b30496168c757d5eba6ba4ba761dbab7933b8
- check results: K15-2.json

## Discussion

<!-- owner-discussion -->
The degree here is a constant, $p$. The result says nothing about growth with $\ell$, which is
what Question 7 is about. Riis and Sitharam's Theorem 33 gives degree at least $2^\ell-1$ for
surplus $p^\ell$ once $N\ge(21+3p^2)(2^\ell-2)-p$ [4]. At $\ell=1$ that bound
is 1, and surplus $pc$ with $c>1$ is outside its family. We have not checked the proof of
Theorem 33. Below $n=2p-3$ the degree is not determined here. The Nullstellensatz degree of
Beame and Riis [1] is multiplier degree, one less than the line degree used here.
<!-- /owner-discussion -->

## References

1. <!-- cite:beame1998counting --> Beame, Paul and Riis, Søren. 1998. More on the relative strength of counting principles. Proof Complexity and Feasible Arithmetics. [Link](https://homes.cs.washington.edu/~beame/papers/riis.pdf)
2. <!-- cite:razborov2001php --> Razborov, Alexander A.. 2002. Proof complexity of pigeonhole principles. Developments in Language Theory (DLT 2001). [Link](https://people.cs.uchicago.edu/~razborov/files/php_survey.pdf)
3. <!-- cite:riis1993independence --> Riis, Søren. 1993. Independence in Bounded Arithmetic
4. <!-- cite:riis1997nonconstant --> Riis, Søren and Sitharam, Meera. 1997. Non-constant degree lower bounds imply linear degree lower bounds. [Link](https://eccc.weizmann.ac.il/report/1997/048/)

<!-- programme verification -->
## How to verify

Lean toolchain: `leanprover/lean4:v4.35.0`. [Programme library at the recorded commit](https://github.com/kodakodapa/autoresearch-findings/tree/2abad0979eeb03ede3a77490f45a4f381119ff02/programmes/proof-complexity). Install elan, then pin the library subtree while keeping the finding checks:

```sh
git clone https://github.com/kodakodapa/autoresearch-findings.git
cd autoresearch-findings
git checkout 2abad0979eeb03ede3a77490f45a4f381119ff02 -- programmes/proof-complexity
cd programmes/proof-complexity && lake build
AR_LIBRARY=$PWD python -I ../../claims/exact-pc-degree-onto-fphp-first-level/checks/lean-K13.py
AR_LIBRARY=$PWD python -I ../../claims/exact-pc-degree-onto-fphp-first-level/checks/lean-K14.py
AR_LIBRARY=$PWD python -I ../../claims/exact-pc-degree-onto-fphp-first-level/checks/lean-K15.py
```

`checks/run-copies/`: the author's working copies from the run; they import the run's private `Work` package and are not built standalone.
<!-- /programme verification -->

<!-- autoresearch:revisions -->
## Revisions

- 2026-11-06 — Math rendering on the site; paper lists only cited references
- 2026-11-06 — Library published buildable; verification steps; run copies labelled
- 2026-11-06 — Verification steps; stale run copies removed; encoding stated
