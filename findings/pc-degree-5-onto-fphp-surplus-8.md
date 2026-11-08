---
layout: default
title: "Polynomial calculus degree at least 5 over F2 for the onto functional pigeonhole principle with surplus 8"
scholar: {"citation_title": "Polynomial calculus degree at least 5 over F2 for the onto functional pigeonhole principle with surplus 8", "citation_author": "Lindheim, Bj\u00f6rn", "citation_publication_date": "2026/11/06", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/pc-degree-5-onto-fphp-surplus-8.html", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/pc-degree-5-onto-fphp-surplus-8/paper.pdf", "citation_doi": "10.5281/zenodo.24017445"}
---

# Polynomial calculus degree at least 5 over F2 for the onto functional pigeonhole principle with surplus 8

Cite as: https://doi.org/10.5281/zenodo.23996615 (all versions; this version: https://doi.org/10.5281/zenodo.24017445)

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

The proof combines a general reduction with finite certificates: small ones for levels 0–2 and,
for level 3, one of 95,550 steps that the Lean kernel checks in 2,154 pieces, plus 60 coverage checks.

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

The Lean theorem excludes refutations of degree exactly 4; smaller degrees are excluded by monotonicity in
the degree bound, stated in the library as `Programme.«maintenance-20261108».DegreeMono.no_deg_le4` (and `deg_ge5`).
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

## K18

Lean `Work.L3.Main.no_deg4`: for every $n\ge7$, `ontoFPHP n 8` (onto-FPHP$^{n+8}\_n$, functional encoding) has no degree-4 `PPCRefutation 2` (polynomial calculus over $\mathbb Z/2$, line degree 4). Unconditional.

Lean: `Programme.«20261028-0841-proof-complexity».L3.Main.no_deg4`

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- library check `checks/lean-K18.py` (library theorem `Programme.«20261028-0841-proof-complexity».L3.Main.no_deg4`)
- proof `checks/run-copies/K18-Main.lean`: Work.L3.Main.no\_deg4 — pass (`results/K18-4.json`)

Re-checked at publication on 2026-11-08: pass (`results/publication/lean-K18.json`)

<details>
<summary>Lean statement as checked</summary>

<pre>Programme.«20261028-0841-proof-complexity».L3.Main.no_deg4 : ∀ (n : Nat),
  7 ≤ n →
    ¬Programme.«20261025-0459-proof-complexity».OntoFPHP.PPCRefutation 2
        (Programme.«20261025-0459-proof-complexity».OntoFPHP.ontoFPHP n 8) 4</pre>
</details>

Prior art: partial prior art (answer: `prior-art/R11.md`)

### Provenance

- run: 20261028-0841
- claim: K18
- author: pr (claude)
- run-folder commit: 19b6167239a90c29b4a3f0ff0f64c79016faf2f8
- check results: K18-4.json

## Discussion

<!-- owner-discussion -->
The upper bound from Riis's criterion is 8 [4, 2], so for
$k=8$ the degree lies between 5 and 8 for $n\ge7$. This is one case, not a growth result in
$\ell$. We have not checked the proof of Theorem 33 and cite it for comparison only.
<!-- /owner-discussion -->

## References

1. <!-- cite:beame1998counting --> Beame, Paul and Riis, Søren. 1998. More on the relative strength of counting principles. Proof Complexity and Feasible Arithmetics. [Link](https://homes.cs.washington.edu/~beame/papers/riis.pdf)
2. <!-- cite:razborov2001php --> Razborov, Alexander A.. 2002. Proof complexity of pigeonhole principles. Developments in Language Theory (DLT 2001). [Link](https://people.cs.uchicago.edu/~razborov/files/php_survey.pdf)
3. <!-- cite:riis1997nonconstant --> Riis, Søren and Sitharam, Meera. 1997. Non-constant degree lower bounds imply linear degree lower bounds. [Link](https://eccc.weizmann.ac.il/report/1997/048/)
4. <!-- cite:riis1993independence --> Riis, Søren. 1993. Independence in Bounded Arithmetic

<!-- programme verification -->
## How to verify

Lean toolchain: `leanprover/lean4:v4.35.0`. [Programme library at the recorded commit](https://github.com/kodakodapa/autoresearch-findings/tree/ad1259e5894f224a3d1eda62a1914da4b4dd699e/programmes/proof-complexity). Install elan and open a new shell after installing elan, then pin the library subtree while keeping the finding checks:

```sh
git clone https://github.com/kodakodapa/autoresearch-findings.git
cd autoresearch-findings
git checkout ad1259e5894f224a3d1eda62a1914da4b4dd699e -- programmes/proof-complexity
cd programmes/proof-complexity && lake build 'Programme.«20261028-0841-proof-complexity».L3.Main'
AR_LIBRARY=$PWD python -I ../../claims/pc-degree-5-onto-fphp-surplus-8/checks/lean-K18.py
```

A full `lake build` builds the whole library. The named targets build only the claim modules and their dependencies. Indicative measurements from the 2026-11-06 reproduction on 2 cores / 7.8 GB: K13–K15 90 s; K1–K6 440 s; K18 87 min (90 certificate modules). Peak memory was 4.7 GB for one Lean process. Build times depend on hardware and cached dependencies.

`checks/run-copies/`: the author's working copies from the run; they import the run's private `Work` package and are not built standalone.
<!-- /programme verification -->

<!-- autoresearch:revisions -->
## Revisions

- 2026-11-06 — Math rendering on the site; paper lists only cited references
- 2026-11-06 — Library published buildable; verification steps; run copies labelled
- 2026-11-06 — Verification steps; stale run copies removed; encoding stated
- 2026-11-06 — Publication re-checks and reproofs published; prior art extended; texts corrected
- 2026-11-06 — Library theorem names and checked statements shown; reproof wording corrected; build cost
- 2026-11-08 — Certificate wording; degree-monotonicity theorems named (degree >= 5)
