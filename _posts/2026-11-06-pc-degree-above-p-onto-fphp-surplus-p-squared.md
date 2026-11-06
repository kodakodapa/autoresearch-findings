---
layout: post
title: "Polynomial calculus degree above p for the onto functional pigeonhole principle with surplus divisible by p squared"
date: 2026-11-06
scholar: {"citation_title": "Polynomial calculus degree above p for the onto functional pigeonhole principle with surplus divisible by p squared", "citation_author": "Lindheim, Bj\u00f6rn", "citation_publication_date": "2026/11/06", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/pc-degree-above-p-onto-fphp-surplus-p-squared.html", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/pc-degree-above-p-onto-fphp-surplus-p-squared/paper.pdf", "citation_doi": "10.5281/zenodo.24013408"}
---

## Summary

Cite as: https://doi.org/10.5281/zenodo.23996585 (all versions; this version: https://doi.org/10.5281/zenodo.24013408)

<!-- owner-summary -->
## Setting

The onto functional pigeonhole principle $\mathrm{onto\text{-}FPHP}^{n+k}\_n$ says that $n+k$
pigeons can be mapped one-to-one onto $n$ holes; it is false for every $k\ge1$. In Boolean
variables $x\_{ij}$ (pigeon $i$ in hole $j$) its axioms are $\sum\_j x\_{ij}-1$,
$\sum\_i x\_{ij}-1$, $x\_{ij}x\_{i'j}$ and $x\_{ij}x\_{ij'}$, the linear encoding used for this family
[1, 2]. These results are for the linear encoding only: translating the CNF clause by clause instead turns each pigeon clause into a polynomial of degree $n$ [2], so degree bounds below $n$ say nothing about that encoding. A polynomial calculus (PC) refutation over
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

**K1.** For every prime $p$, $\mathrm{SquareLiftAssumption}(p)$ holds, i.e. there exists an integral square lift on $2p-1$ rows and columns.

- Status: proved (axioms: propext, Classical.choice, Quot.sound) · independently re-proved (skeptic/codex)
- Machine-checked: no check scripts.
- Second-agent re-proofs: 1, published in `claims/pc-degree-above-p-onto-fphp-surplus-p-squared/checks/reproofs/`.
- reproof `checks/reproofs/K1-Reproof.lean` by the skeptic (codex): `Work.UniformC3.squareLiftAssumption` — pass (`checks/reproofs/K1-Reproof.json`)
- Re-checked at publication on 2026-11-06: pass (`results/publication/lean-K1.json`)
- Prior art: partial prior art

**K2.** For every prime $p$ and natural $c$, some $T$ satisfies $\mathrm{Bal}(p,2p-1,cp^2,T,T,e)$ for every $e\le p-1$, and $p\mid T([])-1$.

- Status: proved (axioms: propext, Classical.choice, Quot.sound) · independently re-proved (skeptic/codex)
- Machine-checked: no check scripts.
- Second-agent re-proofs: 1, published in `claims/pc-degree-above-p-onto-fphp-surplus-p-squared/checks/reproofs/`.
- reproof `checks/reproofs/K2-Reproof.lean` by the skeptic (codex): `Work.UniformC3.uniform_unit_design_unconditional` — pass (`checks/reproofs/K2-Reproof.json`)
- Re-checked at publication on 2026-11-06: pass (`results/publication/lean-K2.json`)
- Prior art: partial prior art

**K3.** For every prime $p$, natural $c$, and $n\ge2p-1$, $\mathrm{ontoFPHP}(n,cp^2)$ has no degree-$p$ $\mathrm{PPCRefutation}$ modulo $p$ (functional encoding, PC line degree).

- Status: proved (axioms: propext, Classical.choice, Quot.sound) · independently re-proved (skeptic/codex)
- Machine-checked: no check scripts.
- Second-agent re-proofs: 1, published in `claims/pc-degree-above-p-onto-fphp-surplus-p-squared/checks/reproofs/`.
- reproof `checks/reproofs/K3-Reproof.lean` by the skeptic (codex): `Work.UniformC3.uniform_no_degree_p_unconditional` — pass (`checks/reproofs/K3-Reproof.json`)
- Re-checked at publication on 2026-11-06: pass (`results/publication/lean-K3.json`)
- Prior art: partial prior art

**K4.** For every prime $p$, natural $c$, and $n\ge2p-1$, $\mathrm{ontoFPHP}(n,cp^2)$ has no standard polynomial-calculus refutation modulo $p$ of line degree at most $p$ (functional encoding).

- Status: proved (axioms: propext, Classical.choice, Quot.sound) · independently re-proved (skeptic/codex)
- Machine-checked: no check scripts.
- Second-agent re-proofs: 1, published in `claims/pc-degree-above-p-onto-fphp-surplus-p-squared/checks/reproofs/`.
- reproof `checks/reproofs/K4-Reproof.lean` by the skeptic (codex): `Work.UniformC3.uniform_no_standard_degree_p_unconditional` — pass (`checks/reproofs/K4-Reproof.json`)
- Re-checked at publication on 2026-11-06: pass (`results/publication/lean-K4.json`)
- Prior art: partial prior art

**K5.** For all natural $c$ and $n\ge3$, $\mathrm{ontoFPHP}(n,4c)$ has no standard polynomial-calculus refutation modulo $2$ of line degree at most $2$ (functional encoding).

- Status: proved (axioms: propext, Classical.choice, Quot.sound) · independently re-proved (skeptic/codex)
- Machine-checked: no check scripts.
- Second-agent re-proofs: 1, published in `claims/pc-degree-above-p-onto-fphp-surplus-p-squared/checks/reproofs/`.
- reproof `checks/reproofs/K5-Reproof.lean` by the skeptic (codex): `Work.UniformC3.no_standard_degree_two` — pass (`checks/reproofs/K5-Reproof.json`)
- Re-checked at publication on 2026-11-06: pass (`results/publication/lean-K5.json`)
- Prior art: partial prior art

**K6.** For all natural $c$ and $n\ge5$, $\mathrm{ontoFPHP}(n,9c)$ has no standard polynomial-calculus refutation modulo $3$ of line degree at most $3$ (functional encoding).

- Status: proved (axioms: propext, Classical.choice, Quot.sound) · independently re-proved (skeptic/codex)
- Machine-checked: no check scripts.
- Second-agent re-proofs: 1, published in `claims/pc-degree-above-p-onto-fphp-surplus-p-squared/checks/reproofs/`.
- reproof `checks/reproofs/K6-Reproof.lean` by the skeptic (codex): `Work.UniformC3.no_standard_degree_three` — pass (`checks/reproofs/K6-Reproof.json`)
- Re-checked at publication on 2026-11-06: pass (`results/publication/lean-K6.json`)
- Prior art: partial prior art

## Discussion

This is a lower bound, not an exact value. The best upper bound we know at surplus $p^2$ is $p^2$,
from Riis's criterion [4, 2]. So for surplus $p^2$ the degree
lies between $p+1$ and $p^2$. At $p=2$ the separate exact result that the degree is 4 for surplus 4
($n\ge5$) is in the same library. The bound does not grow with $\ell$ and does not answer
Question 7. We have not checked the proof of Riis and Sitharam's Theorem 33, which we cite for
comparison only.

## How to verify

Lean toolchain: `leanprover/lean4:v4.35.0`. [Programme library at the recorded commit](https://github.com/kodakodapa/autoresearch-findings/tree/2abad0979eeb03ede3a77490f45a4f381119ff02/programmes/proof-complexity). Install elan, then pin the library subtree while keeping the finding checks:

```sh
git clone https://github.com/kodakodapa/autoresearch-findings.git
cd autoresearch-findings
git checkout 2abad0979eeb03ede3a77490f45a4f381119ff02 -- programmes/proof-complexity
cd programmes/proof-complexity && lake build
AR_LIBRARY=$PWD python -I ../../claims/pc-degree-above-p-onto-fphp-surplus-p-squared/checks/lean-K1.py
AR_LIBRARY=$PWD python -I ../../claims/pc-degree-above-p-onto-fphp-surplus-p-squared/checks/lean-K2.py
AR_LIBRARY=$PWD python -I ../../claims/pc-degree-above-p-onto-fphp-surplus-p-squared/checks/lean-K3.py
AR_LIBRARY=$PWD python -I ../../claims/pc-degree-above-p-onto-fphp-surplus-p-squared/checks/lean-K4.py
AR_LIBRARY=$PWD python -I ../../claims/pc-degree-above-p-onto-fphp-surplus-p-squared/checks/lean-K5.py
AR_LIBRARY=$PWD python -I ../../claims/pc-degree-above-p-onto-fphp-surplus-p-squared/checks/lean-K6.py
```

`checks/run-copies/`: the author's working copies from the run; they import the run's private `Work` package and are not built standalone.

The output of the checks re-run at publication is in `claims/pc-degree-above-p-onto-fphp-surplus-p-squared/results/publication/`.

## Provenance

- run: 20261102-1249
- claims: K1, K2, K3, K4, K5, K6
- run-folder commit: 359fa20477b8d26a5d2ef8a16e5465474e74b452
- K1 author: pr (codex)
- K2 author: pr (codex)
- K3 author: pr (codex)
- K4 author: pr (codex)
- K5 author: pr (codex)
- K6 author: pr (codex)

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
- 2026-11-06 — Publication re-checks and reproofs published; prior art extended; texts corrected
