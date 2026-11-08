---
layout: post
title: "Exact polynomial calculus degree p for the onto functional pigeonhole principle with surplus divisible by p"
date: 2026-11-06
scholar: {"citation_title": "Exact polynomial calculus degree p for the onto functional pigeonhole principle with surplus divisible by p", "citation_author": "Lindheim, Bj\u00f6rn", "citation_publication_date": "2026/11/06", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/exact-pc-degree-onto-fphp-first-level.html", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/exact-pc-degree-onto-fphp-first-level/paper.pdf", "citation_doi": "10.5281/zenodo.24017401"}
---

## Summary

Cite as: https://doi.org/10.5281/zenodo.23996564 (all versions; this version: https://doi.org/10.5281/zenodo.24017401)

<!-- owner-summary -->
## Setting

The onto functional pigeonhole principle $\mathrm{onto\text{-}FPHP}^{n+k}\_n$ says that $n+k$
pigeons can be mapped one-to-one onto $n$ holes. It is false for every $k\ge1$. As a system of
polynomial equations in Boolean variables $x\_{ij}$ (pigeon $i$ sits in hole $j$) it has the
axioms $\sum\_j x\_{ij}-1$ (each pigeon sits in a hole), $\sum\_i x\_{ij}-1$ (each hole holds exactly
one pigeon), $x\_{ij}x\_{i'j}$ (no two pigeons share a hole) and $x\_{ij}x\_{ij'}$ (no pigeon sits in
two holes). This is the linear encoding used in the literature on this family
[1, 2]. These results are for the linear encoding only: translating the CNF clause by clause instead turns each pigeon clause into a polynomial of degree $n$ [2], so degree bounds below $n$ say nothing about that encoding.

A polynomial calculus (PC) refutation over the field $\mathbb F\_p$ derives the polynomial $1$
from the axioms and the Boolean axioms $x^2-x$, using linear combinations and multiplication by a
variable. Its degree is the largest degree of a line. The PC degree of the principle is the least
degree of a refutation. When $p$ does not divide $k$, summing the pigeon axioms and subtracting
the hole axioms gives the constant $-k$, a degree-1 refutation. The question is what happens when
$p$ divides $k$.

## Result

For every prime $p$, every $c$ not divisible by $p$, and every $n\ge 2p-3$, the PC degree of
$\mathrm{onto\text{-}FPHP}^{n+pc}\_n$ over $\mathbb F\_p$ is exactly $p$: there is a refutation of
degree $p$, and none of degree $p-1$. More generally, whenever $p$ divides $k$ and $n\ge2p-3$,
there is no refutation of degree $p-1$. The same formula therefore has PC degree $p$ over
$\mathbb F\_p$ and PC degree $1$ over $\mathbb F\_q$ for every prime $q$ not dividing $pc$.

## Why it matters

Razborov's survey asks (Question 7) whether $\mathrm{onto\text{-}FPHP}^{n+p^\ell}\_n$ has
bounded-degree PC refutations in characteristic $p$ [2]. The upper bound $p$ at
the first level comes from Riis's criterion [3]. The known lower bounds are
for the weaker Nullstellensatz system [1] and, for PC, a bound that grows with
$\ell$ for large $n$ [4]. This result fixes the degree exactly at the first
level (surplus divisible by $p$ but not by $p^2$), for every prime, from a small linear threshold
in $n$.

## Proved vs checked

Everything is proved in Lean 4 and kernel-checked, for all primes $p$ and all $n\ge2p-3$; nothing
is checked only up to a bound. The proofs use only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. A second agent in the run re-proved each of the three statements in Lean, but
its re-proofs reuse some of the author's lemmas (one to nine per proof, listed with each claim), so
they are not fully independent. No person has reviewed the proofs; the evidence is the kernel check.

The Lean statements are for the library's formulation of PC, in which lines are functions on
the Boolean cube. A later theorem of the same library shows that a refutation of degree $D$ in
standard (syntactic) PC over $\mathbb F\_p$ exists exactly when one exists in the library's
formulation, so the result holds verbatim for standard PC (`Programme.«20261029-1156-proof-complexity».StdPCExact.std_pc_degree_exact` in the published library; this finding's own checks do not re-check it).
<!-- /owner-summary -->

This result extends:

- Riis-Sitharam, ECCC TR97-048, Theorem 33: PC degree >= 2^l - 1 for onto-PHP^{N+p^l}_N over characteristic p once N >= (21+3p^2)(2^l - 2) - p (same family; proof not checked by us; at l = 2 this is >= 3 against our >= p+1 from n = 2p-1; at p = 2, l = 3 it is >= 7 for N >= 196 against our >= 5 for n >= 7).
- Beame-Riis 1998, Theorem 8.1 and Lemma 8.7: Nullstellensatz degree between 2^l - 1 and p^l - 1 (multiplier degree) for the same family; Section 10 lists polynomial-calculus lower bounds as open.
- Riis 1993, as Theorem 8 of Razborov's survey: degree-d PC refutations when C(m,d) and C(n,d) differ mod p, which gives the matching upper bound p for k = pc, p not dividing c (via Lucas).
- Razborov, Proof complexity of pigeonhole principles (2001), Question 7: the fixed-p, fixed-l bounded-degree question for onto-FPHP^{n+p^l}_n.
- Miksa-Nordstrom (JACM 2024): general PC degree method; onto-FPHP with m = n+1 easy (Riis); the case of characteristic dividing the surplus not covered.
- BGIP 2001: proves linear PC degree for Tseitin mod p over characteristic q containing a primitive root of unity of order p (Thm 15) and for MOD_p^n over F_q, q not dividing p (Cor 20: "requires degree > delta n"). This is the cross-characteristic regime. Our results concern the same-characteristic regime p ∣ k, so there is no overlap. The paper does not treat onto-PHP.
- Alekhnovich-Razborov 2003: "immunity" method giving linear PC degree bounds for mod_p Tseitin over characteristic different from p, for flow tautologies and for random k-CNF in characteristic 2 (abstract only). No PHP or onto-PHP result. The method is relevant only as possible technique.
- Impagliazzo-Pudlak-Sgall 1999: simpler proof of Razborov's ceil(n/2)+1 PC lower bound for (injective, non-onto) PHP^m_n over any field, plus an upper bound in large characteristic (abstract). This is a different principle: without the onto and functional axioms the bound is independent of p. It does not transfer to the exact degree p or p+1 for onto-FPHP.
- BIKPRS 1996/97: Nullstellensatz lower bounds for Count_q over Z_m with q not dividing m (Thm 3.2) and over Q (Thm 4.6), plus the PC-to-NS simulation (Thm 5.4). This is Nullstellensatz and Count, not PC degree for onto-FPHP, and the paper excludes the case q ∣ m.
- Grigoriev FOCS 1998 (snippet only, not opened): Nullstellensatz degree for Tseitin mod p over other characteristics. It is a predecessor of BGIP; NS, not PC, and a different principle.
- Filmus-Lauria-Mikša-Nordström-Vinyals 2025: PC space and separations. It mentions the functional PHP only for space limits, not for characteristic-dependent degree.
- Ken 2022/2024: restates Razborov's injPHP bound "no PC-refutation ... with degree <= m/2" (Thm 24) and extends it to NS over finite rings (Cor 25). Onto-PHP appears only in reductions (Props 12, 15), and no degree bound for it is proved.
- Reduction transfer: none of the opened sources gives a low-degree reduction from Count_q, Tseitin mod q or Mod_q (q != p) to onto-FPHP^{n+k}_n with p ∣ k over F_p. Since the cross-characteristic lower bounds need q != p, they do not yield results 1-3 directly.

Our prior-art search (2026-11-06) covered:

- Riis, Sitharam, Non-constant degree lower bounds imply linear degree lower bounds, ECCC TR97-048 (1997), pp. 36-38 and 45-46 (Theorem 33, Propositions 27 and 28), opened 2026-10-29
- Beame, Riis, More on the relative strength of counting principles, DIMACS Series 39 (1998), homes.cs.washington.edu/~beame/papers/riis.pdf: Theorem 8.1, Lemma 8.7, Section 10, opened 2026-10-27 and 2026-11-01
- Razborov, Proof complexity of pigeonhole principles, DLT 2001 (LNCS 2295), people.cs.uchicago.edu/~razborov/files/php_survey.pdf: Theorem 8, Question 7, footnote 5, opened 2026-10-27 and 2026-10-29
- Riis, BRICS Report RS-99-29, opened 2026-10-29
- Miksa, Nordstrom, A generalized method for proving polynomial calculus degree lower bounds (CCC 2015; JACM 2024; arXiv 1505.01358), opened 2026-10-27
- de Rezende et al., Theory of Computing 21(6) (2025), opened 2026-10-29
- Lauria et al., Theory of Computing 21(4) (2025), opened 2026-10-27
- Buss, Grigoriev, Impagliazzo, Pitassi, "Linear gaps between degrees for the polynomial calculus modulo distinct primes", JCSS 62(2):267-289, 2001 (STOC 1999). Opened: journal final PDF, https://mathweb.ucsd.edu/~sbuss/ResearchWeb/lineargaps/journalfinal.pdf
- Alekhnovich, Razborov, "Lower bounds for polynomial calculus: non-binomial case", Proc. Steklov Inst. Math. 242 (2003) 18-35 (FOCS 2001). Opened: abstract only, https://mathnet.ru/eng/tm403 (full text not opened).
- Impagliazzo, Pudlak, Sgall, "Lower bounds for the polynomial calculus and the Groebner basis algorithm", Computational Complexity 8(2):127-144, 1999 (ECCC TR97-042). Opened: ECCC abstract only, https://eccc.weizmann.ac.il/report/1997/042/
- Buss, Impagliazzo, Krajicek, Pudlak, Razborov, Sgall, "Proof complexity in algebraic systems and bounded depth Frege systems with modular counting", Computational Complexity 6(3):256-298, 1996/97. Opened: full PDF, https://mathweb.ucsd.edu/~sbuss/ResearchWeb/nullstellensatz/token.pdf
- Grigoriev, "Tseitin's tautologies and lower bounds for Nullstellensatz proofs", FOCS 1998, pp. 648-652. Snippet only, not opened (dblp/researchr entries).
- Mikša, Nordström, "A generalized method for proving polynomial calculus degree lower bounds", CCC 2015 (arXiv 1505.01358). Already credited. Seen in search results; not re-opened here.
- Filmus, Lauria, Mikša, Nordström, Vinyals, "Towards an understanding of polynomial calculus: new separations and lower bounds", Theory of Computing 21(4), 2025 (ICALP 2013). Opened: abstract page, https://zesty2.cs.uchicago.edu/articles/v021a004
- Eitetsu Ken, "On some Sigma_0^B-formulae generalizing counting principles over V^0", arXiv 2203.10237 (2022; a journal version appears to be Arch. Math. Logic 2024, https://link.springer.com/article/10.1007/s00153-024-00938-1). Opened: ar5iv HTML and Springer page, first ~100k characters of each.
- Web searches for 2000-2026 papers on PC degree of onto-PHP or Count where the characteristic divides the surplus: no further hits beyond the items above.

Prior-art answer recorded by the owner (basis stated in the file); published in `prior-art/`.

If you know of related work we missed, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the verification steps below build the published programme library.

The declaring Lean sources are in `checks/library/`.

**K13.** `Work.Lucas.pc_degree_exact`: for every prime $p$ (`IsPrime p`), every $c$ with $p\nmid c$, every $n\ge2p-3$ and every $D$: `ontoFPHP n (p*c)` has a degree-$D$ `PPCRefutation p` iff $p\le D$ (PC degree over $\mathbb Z/p$ of onto-FPHP$^{n+pc}\_n$ is exactly $p$).

Lean: `Programme.«20261027-0607-proof-complexity».Lucas.pc_degree_exact`

- Status: proved (axioms: propext, Classical.choice, Quot.sound) · second-agent re-proof (skeptic/codex)
- Machine-checked: `checks/lean-K13.py` (library theorem `Programme.«20261027-0607-proof-complexity».Lucas.pc_degree_exact`)
- Second-agent re-proofs: 1, published in `claims/exact-pc-degree-onto-fphp-first-level/checks/reproofs/`.
- reproof `checks/reproofs/K13-ExactReproof.lean` by the skeptic (codex): `Work.Lucas.pc_degree_exact` — pass (`checks/reproofs/K13-ExactReproof.json`); second-agent re-proof; uses 2 lemmas from the author's package; re-proof by a second agent; imports the run's private packages (not rebuildable from this repo)
- Re-checked at publication on 2026-11-08: pass (`results/publication/lean-K13.json`)
- Prior art: partial prior art

**K14.** `Work.Peel.pc_degree_ge_p`: for every prime $p$ (`IsPrime p`), every $k$ with $p\mid k$ and every $n\ge2p-3$, `ontoFPHP n k` (onto-FPHP$^{n+k}\_n$, functional encoding) has no `PPCRefutation p` of degree $p-1$ (polynomial calculus over $\mathbb Z/p$).

Lean: `Programme.«20261027-0607-proof-complexity».Peel.pc_degree_ge_p`

- Status: proved (axioms: propext, Classical.choice, Quot.sound) · second-agent re-proof (skeptic/codex)
- Machine-checked: `checks/lean-K14.py` (library theorem `Programme.«20261027-0607-proof-complexity».Peel.pc_degree_ge_p`)
- Second-agent re-proofs: 1, published in `claims/exact-pc-degree-onto-fphp-first-level/checks/reproofs/`.
- reproof `checks/reproofs/K14-LowerReproof.lean` by the skeptic (codex): `Work.Peel.pc_degree_ge_p` — pass (`checks/reproofs/K14-LowerReproof.json`); second-agent re-proof; uses 9 lemmas from the author's package; re-proof by a second agent; imports the run's private packages (not rebuildable from this repo)
- Re-checked at publication on 2026-11-08: pass (`results/publication/lean-K14.json`)
- Prior art: partial prior art

**K15.** `Work.Lucas.separation`: for primes $p,q$, $p\nmid c$, $q\nmid pc$, $n\ge2p-3$: `ontoFPHP n (p*c)` has a degree-$D$ `PPCRefutation p` iff $p\le D$, and has a degree-1 `PPCRefutation q`.

Lean: `Programme.«20261027-0607-proof-complexity».Lucas.separation`

- Status: proved (axioms: propext, Classical.choice, Quot.sound) · second-agent re-proof (skeptic/codex)
- Machine-checked: `checks/lean-K15.py` (library theorem `Programme.«20261027-0607-proof-complexity».Lucas.separation`)
- Second-agent re-proofs: 1, published in `claims/exact-pc-degree-onto-fphp-first-level/checks/reproofs/`.
- reproof `checks/reproofs/K15-SeparationReproof.lean` by the skeptic (codex): `Work.Lucas.separation` — pass (`checks/reproofs/K15-SeparationReproof.json`); second-agent re-proof; uses 1 lemmas from the author's package; re-proof by a second agent; imports the run's private packages (not rebuildable from this repo)
- Re-checked at publication on 2026-11-08: pass (`results/publication/lean-K15.json`)
- Prior art: partial prior art

## Discussion

The degree here is a constant, $p$. The result says nothing about growth with $\ell$, which is
what Question 7 is about. Riis and Sitharam's Theorem 33 gives degree at least $2^\ell-1$ for
surplus $p^\ell$ once $N\ge(21+3p^2)(2^\ell-2)-p$ [4]. At $\ell=1$ that bound
is 1, and surplus $pc$ with $c>1$ is outside its family. We have not checked the proof of
Theorem 33. Below $n=2p-3$ the degree is not determined here. The Nullstellensatz degree of
Beame and Riis [1] is multiplier degree, one less than the line degree used here.

## How to verify

Lean toolchain: `leanprover/lean4:v4.35.0`. [Programme library at the recorded commit](https://github.com/kodakodapa/autoresearch-findings/tree/ad1259e5894f224a3d1eda62a1914da4b4dd699e/programmes/proof-complexity). Install elan and open a new shell after installing elan, then pin the library subtree while keeping the finding checks:

```sh
git clone https://github.com/kodakodapa/autoresearch-findings.git
cd autoresearch-findings
git checkout ad1259e5894f224a3d1eda62a1914da4b4dd699e -- programmes/proof-complexity
cd programmes/proof-complexity && lake build 'Programme.«20261027-0607-proof-complexity».Lucas' 'Programme.«20261027-0607-proof-complexity».Peel'
AR_LIBRARY=$PWD python -I ../../claims/exact-pc-degree-onto-fphp-first-level/checks/lean-K13.py
AR_LIBRARY=$PWD python -I ../../claims/exact-pc-degree-onto-fphp-first-level/checks/lean-K14.py
AR_LIBRARY=$PWD python -I ../../claims/exact-pc-degree-onto-fphp-first-level/checks/lean-K15.py
```

A full `lake build` builds the whole library. The named targets build only the claim modules and their dependencies. Indicative measurements from the 2026-11-06 reproduction on 2 cores / 7.8 GB: K13–K15 90 s; K1–K6 440 s; K18 87 min (90 certificate modules). Peak memory was 4.7 GB for one Lean process. Build times depend on hardware and cached dependencies.

`checks/run-copies/`: the author's working copies from the run; they import the run's private `Work` package and are not built standalone.

The output of the checks re-run at publication is in `claims/exact-pc-degree-onto-fphp-first-level/results/publication/`.

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

<!-- autoresearch:revisions -->
## Revisions

- 2026-11-06 — Math rendering on the site; paper lists only cited references
- 2026-11-06 — Library published buildable; verification steps; run copies labelled
- 2026-11-06 — Verification steps; stale run copies removed; encoding stated
- 2026-11-06 — Publication re-checks and reproofs published; prior art extended; texts corrected
- 2026-11-06 — Library theorem names and checked statements shown; reproof wording corrected; build cost
- 2026-11-08 — Prior-art wording; library names; monotonicity
