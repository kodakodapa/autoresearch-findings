# Polynomial calculus degree above 4 over F3 for the onto functional pigeonhole principle with surplus divisible by 9, conditional on a spanning statement

<!-- owner-summary -->
## Setting

The onto functional pigeonhole principle $\mathrm{onto\text{-}FPHP}^{n+k}_n$ says that $n+k$
pigeons can be mapped one-to-one onto $n$ holes; it is false for every $k\ge1$. In Boolean
variables $x_{ij}$ (pigeon $i$ in hole $j$) its axioms are $\sum_j x_{ij}-1$,
$\sum_i x_{ij}-1$, $x_{ij}x_{i'j}$ and $x_{ij}x_{ij'}$, the linear encoding used for this family
[1, 2]. These results are for the linear encoding only. A polynomial
calculus (PC) refutation over $\mathbb F_3$ derives $1$ from the axioms and the Boolean axioms
$x^2-x$ by linear combinations and multiplication by a variable; its degree is the largest degree of
a line.

The proof works with *matching labels*: for each partial matching $M$ of $d-1$ edges, one label per
free pigeon and one per free hole. An integer vector over labels lies in the *kernel* $\mathrm{Kernel}(p,m,n,d)$
when its top-degree extension sum vanishes modulo $p$. *Spanning*$(p,m,n,d)$ says that every kernel vector
is, modulo $p$, an integer combination of an explicit list of generators (row–row, column–column,
row–column and anchored syzygies) on the $m\times n$ board.

## Result

For $9\mid k$ and $n\ge7$: if Spanning$(3,n+k,n,r)$ holds for $r=2,3,4$, then
$\mathrm{onto\text{-}FPHP}^{n+k}_n$ has no standard PC refutation over $\mathbb F_3$ of any degree
$d\le4$. Spanning holds at level 1 on every board. On the smallest board the theorem uses,
$16\times7$ ($n=7$, $k=9$), exact computations over $\mathbb F_3$ show that Spanning holds at level 2
(kernel dimension 343, equal to the generators' rank) and at level 3 (kernel dimension 24,780, equal to
the generators' rank; two independent programs agree). Level 4 is undecided.

## Why it matters

Razborov's Question 7 concerns the PC degree for surplus $p^\ell$ in characteristic $p$
[2]. This finding isolates what a degree-4 lower bound for surplus divisible by 9 over
$\mathbb F_3$ needs, for all $n$: a single, finite-looking linear-algebra statement per board, Spanning,
which is now known to be satisfiable at levels 2 and 3 on the first board. A uniform proof of Spanning
for all boards would make the theorem unconditional.

## Proved vs checked

The conditional theorem and the level-1 statement are proved in Lean 4 and kernel-checked, with only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`. A second agent in the run re-proved
them in Lean. The level-2 and level-3 statements on the $16\times7$ board are exact rank computations
over $\mathbb F_3$ (measured, not Lean theorems); the computations implement the same label and
generator definitions as the Lean library, but that correspondence is by reimplementation, not proof.
No person has reviewed the proofs.
<!-- /owner-summary -->

This result extends:

- Riis-Sitharam, ECCC TR97-048, Theorem 33: PC degree >= 2^l - 1 for onto-PHP^{N+p^l}_N over characteristic p once N >= (21+3p^2)(2^l - 2) - p (same family; proof not checked by us; at l = 2 this is >= 3 against our >= p+1 from n = 2p-1; at p = 2, l = 3 it is >= 7 for N >= 196 against our >= 5 for n >= 7).
- Beame-Riis 1998, Theorem 8.1 and Lemma 8.7: Nullstellensatz degree between 2^l - 1 and p^l - 1 (multiplier degree) for the same family; Section 10 lists polynomial-calculus lower bounds as open.
- Riis 1993, as Theorem 8 of Razborov's survey: degree-d PC refutations when C(m,d) and C(n,d) differ mod p, which gives the matching upper bound p for k = pc, p not dividing c (the congruence C(n+pc,p) − C(n,p) is congruent to c mod p, proved directly in our Lean).
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

Our prior-art search (2026-11-08) covered:

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

This result was found by AI research agents (the autoresearch harness). It was partly proved in Lean (claims K14, K100) and partly checked by script (claims K119, K120); the verification steps below build the published programme library.

The declaring Lean sources are in `checks/library/`.

## K14

For every natural modulus $p$ and positive natural dimensions $m,n$, $\mathrm{Spanning}(p,m,n,1)$ holds for the concrete raw matching-label vectors and enumerated syzygies.

Lean: `Programme.«20261104-1627-proof-complexity».MatchingLabels.spanning_one`

Status: proved (axioms: propext, Classical.choice, Quot.sound) · second-agent re-proof (skeptic/codex)

Kind: theorem

Evidence:
- library check `checks/lean-K14.py` (library theorem `Programme.«20261104-1627-proof-complexity».MatchingLabels.spanning_one`)
- proof `checks/run-copies/K14-RectangularOne.lean`: Work.MatchingLabels.spanning\_one — pass (`results/K14-1.json`)
- reproof `checks/reproofs/K14-ReproofK14.lean` by the skeptic (codex): `Work.MatchingLabels.spanning_one` — pass (`checks/reproofs/K14-ReproofK14.json`); second-agent re-proof; uses 0 lemmas from the author's package; re-proof by a second agent; imports the run's private packages (not rebuildable from this repo)

Re-checked at publication on 2026-11-08: pass (`results/publication/lean-K14.json`)

<details>
<summary>Lean statement as checked</summary>

<pre>@Programme.«20261104-1627-proof-complexity».MatchingLabels.spanning_one : ∀ {p m n : Nat},
  0 &lt; m → 0 &lt; n → Programme.«20261104-1627-proof-complexity».MatchingLabels.Spanning p m n 1</pre>
</details>

Prior art: partial prior art (answer: `prior-art/R49.md`)

### Provenance

- run: 20261104-1627
- claim: K14
- author: pr (codex)
- run-folder commit: ec49de5e279909aace60ec48cf1d9c3545b6502c
- check results: K14-1.json

## K100

If $9\mid k$, $n\ge7$, and $\mathrm{Spanning}(3,n+k,n,r)$ for $r=2,3,4$, the degree-four StepSix invariant exists and StdPC has no refutation of $\mathrm{ontoFPHP}(n,k)$ at any degree $d\le4$.

Lean: `Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.nodrop`, `Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.invariant`, `Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.no_stdpc`, `Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.no_ppc`, `Programme.«20261104-1627-proof-complexity».RemainingSpanning.invariant`, `Programme.«20261104-1627-proof-complexity».RemainingSpanning.no_stdpc_le`

Status: proved (axioms: propext, Classical.choice, Quot.sound) · second-agent re-proof (researcher/codex, skeptic/codex)

Kind: theorem

Evidence:
- library check `checks/lean-K100.py` (library theorem `Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.nodrop`, `Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.invariant`, `Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.no_stdpc`, `Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.no_ppc`, `Programme.«20261104-1627-proof-complexity».RemainingSpanning.invariant`, `Programme.«20261104-1627-proof-complexity».RemainingSpanning.no_stdpc_le`)
- proof `checks/run-copies/K100-ConcreteDegreeFour.lean`: Work.ConcreteDegreeFour.nodrop — pass (`results/K100-1.json`)
- proof `checks/run-copies/K100-ConcreteDegreeFour.lean`: Work.ConcreteDegreeFour.invariant — pass (`results/K100-2.json`)
- proof `checks/run-copies/K100-ConcreteDegreeFour.lean`: Work.ConcreteDegreeFour.no\_stdpc — pass (`results/K100-3.json`)
- proof `checks/run-copies/K100-ConcreteDegreeFour.lean`: Work.ConcreteDegreeFour.no\_ppc — pass (`results/K100-4.json`)
- proof `checks/run-copies/K100-RemainingSpanning.lean`: Work.RemainingSpanning.invariant — pass (`results/K100-5.json`)
- proof `checks/run-copies/K100-RemainingSpanning.lean`: Work.RemainingSpanning.no\_stdpc\_le — pass (`results/K100-6.json`)
- reproof `checks/reproofs/K100-K100Reproof.lean` by the researcher (codex): `Work.RemainingSpanning.no_stdpc_le` — pass (`checks/reproofs/K100-K100Reproof.json`); second-agent re-proof; uses 8 lemmas from the author's package; re-proof by a second agent; imports the run's private packages (not rebuildable from this repo)
- reproof `checks/reproofs/K100-ReproofK100.lean` by the skeptic (codex): `Work.RemainingSpanning.no_stdpc_le` — pass (`checks/reproofs/K100-ReproofK100.json`); second-agent re-proof; uses 4 lemmas from the author's package; re-proof by a second agent; imports the run's private packages (not rebuildable from this repo)

Re-checked at publication on 2026-11-08: pass (`results/publication/lean-K100.json`)

<details>
<summary>Lean statement as checked</summary>

<pre>@Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.nodrop : ∀ {n k D : Nat},
  9 ∣ k →
    7 ≤ n →
      0 &lt; D →
        D ≤ 4 →
          (∀ (r : Nat),
              0 &lt; r → r ≤ 4 → Programme.«20261104-1627-proof-complexity».MatchingLabels.Spanning 3 (n + k) n r) →
            Programme.«20261025-1627-proof-complexity».NoDrop.NoDrop 3
              (Programme.«20261025-0459-proof-complexity».OntoFPHP.ontoFPHP n k) D
@Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.invariant : {n k : Nat} →
  9 ∣ k →
    7 ≤ n →
      (∀ (r : Nat), 0 &lt; r → r ≤ 4 → Programme.«20261104-1627-proof-complexity».MatchingLabels.Spanning 3 (n + k) n r) →
        Programme.«20261102-0635-proof-complexity».StepSix.Invariant 3 4
          (Programme.«20261025-0459-proof-complexity».OntoFPHP.ontoFPHP n k)
@Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.no_stdpc : ∀ {n k : Nat},
  9 ∣ k →
    7 ≤ n →
      (∀ (r : Nat), 0 &lt; r → r ≤ 4 → Programme.«20261104-1627-proof-complexity».MatchingLabels.Spanning 3 (n + k) n r) →
        ¬Programme.«20261029-1156-proof-complexity».StdPC.Refutes 3
            (Programme.«20261025-0459-proof-complexity».OntoFPHP.ontoFPHP n k) 4
@Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.no_ppc : ∀ {n k : Nat},
  9 ∣ k →
    7 ≤ n →
      (∀ (r : Nat), 0 &lt; r → r ≤ 4 → Programme.«20261104-1627-proof-complexity».MatchingLabels.Spanning 3 (n + k) n r) →
        ¬Programme.«20261025-0459-proof-complexity».OntoFPHP.PPCRefutation 3
            (Programme.«20261025-0459-proof-complexity».OntoFPHP.ontoFPHP n k) 4
@Programme.«20261104-1627-proof-complexity».RemainingSpanning.invariant : {n k : Nat} →
  9 ∣ k →
    7 ≤ n →
      Programme.«20261104-1627-proof-complexity».MatchingLabels.Spanning 3 (n + k) n 2 →
        Programme.«20261104-1627-proof-complexity».MatchingLabels.Spanning 3 (n + k) n 3 →
          Programme.«20261104-1627-proof-complexity».MatchingLabels.Spanning 3 (n + k) n 4 →
            Programme.«20261102-0635-proof-complexity».StepSix.Invariant 3 4
              (Programme.«20261025-0459-proof-complexity».OntoFPHP.ontoFPHP n k)
@Programme.«20261104-1627-proof-complexity».RemainingSpanning.no_stdpc_le : ∀ {n k d : Nat},
  9 ∣ k →
    7 ≤ n →
      Programme.«20261104-1627-proof-complexity».MatchingLabels.Spanning 3 (n + k) n 2 →
        Programme.«20261104-1627-proof-complexity».MatchingLabels.Spanning 3 (n + k) n 3 →
          Programme.«20261104-1627-proof-complexity».MatchingLabels.Spanning 3 (n + k) n 4 →
            d ≤ 4 →
              ¬Programme.«20261029-1156-proof-complexity».StdPC.Refutes 3
                  (Programme.«20261025-0459-proof-complexity».OntoFPHP.ontoFPHP n k) d</pre>
</details>

Prior art: partial prior art (answer: `prior-art/R49.md`)

### Provenance

- run: 20261104-1627
- claim: K100
- author: th (codex)
- run-folder commit: ec49de5e279909aace60ec48cf1d9c3545b6502c
- check results: K100-1.json, K100-2.json, K100-3.json, K100-4.json, K100-5.json, K100-6.json

## K119

For $m=16..16$, $n=7$ and $r=2$, the full-space generator rank over $\mathbb F_3$ is $343$, equal to the top-map kernel dimension, in the implemented canonical matching-label encoding.

Status: measured · range 16..16 · author check only

Kind: model

Evidence:
- check `checks/run-copies/K119-spanning_16_7_two.py`: Exact top rank 2009 and generator rank 343 in 2352 label coordinates; every enumerated generator has zero top; prints an ar-table. — pass (`results/K119-1.json`)

Re-checked at publication on 2026-11-08: pass (`results/publication/run-copies-K119-spanning_16_7_two.json`)

Prior art: partial prior art (answer: `prior-art/R49.md`)

### Provenance

- run: 20261104-1627
- claim: K119
- author: r1 (codex)
- run-folder commit: ec49de5e279909aace60ec48cf1d9c3545b6502c
- check results: K119-1.json

## K120

For $m=16..16$, $n=7$ and $r=3$, exact full-space computations over $\mathbb F_3$ give top rank $70980$ and generator rank $24780$, equal to the kernel dimension in $95760$ matching-label coordinates.

Status: derived · author check only

Kind: model

Evidence:
- job `checks/run-copies/K120-spanning_16_7_three.py` (run detached by the runner): Exact full-space top rank 70980, kernel dimension and generator rank 24780; all generators have zero top; prints ar-table. — pass (`results/job-R44.json`, log `results/job-R44.log`)
- reasoning: Independent job R43 reports identical ranks and counts; its script and job belong to the prover, so that job is cited in body/refs rather than as own job evidence.

Re-checked at publication on 2026-11-08: pass (`results/publication/run-copies-K120-spanning_16_7_three.json`)

Prior art: partial prior art (answer: `prior-art/R49.md`)

### Provenance

- run: 20261104-1627
- claim: K120
- author: r1 (codex)
- run-folder commit: ec49de5e279909aace60ec48cf1d9c3545b6502c
- check results: job-R44.json

## Discussion

<!-- owner-discussion -->
The theorem is conditional, and the condition is only checked on one board at levels 2 and 3. For the
statement for all $n\ge7$, Spanning must hold on every board $(n+k)\times n$, which no finite
computation can settle; the run proved lifting lemmas toward a uniform argument, but that argument is
not complete. Level 4 on the $16\times7$ board was not decided: the computation reached 86% of the
984,593 generators before its time limit. We have not checked the proof of Riis and Sitharam's
Theorem 33 [3], which we cite for comparison only.
<!-- /owner-discussion -->

## References

1. <!-- cite:beame1998counting --> Beame, Paul and Riis, Søren. 1998. More on the relative strength of counting principles. Proof Complexity and Feasible Arithmetics. [Link](https://homes.cs.washington.edu/~beame/papers/riis.pdf)
2. <!-- cite:razborov2001php --> Razborov, Alexander A.. 2002. Proof complexity of pigeonhole principles. Developments in Language Theory (DLT 2001). [Link](https://people.cs.uchicago.edu/~razborov/files/php_survey.pdf)
3. <!-- cite:riis1997nonconstant --> Riis, Søren and Sitharam, Meera. 1997. Non-constant degree lower bounds imply linear degree lower bounds. [Link](https://eccc.weizmann.ac.il/report/1997/048/)

<!-- programme verification -->
## How to verify

Lean toolchain: `leanprover/lean4:v4.35.0`. [Programme library at the recorded commit](https://github.com/kodakodapa/autoresearch-findings/tree/ad1259e5894f224a3d1eda62a1914da4b4dd699e/programmes/proof-complexity). Install elan and open a new shell after installing elan, then pin the library subtree while keeping the finding checks:

```sh
git clone https://github.com/kodakodapa/autoresearch-findings.git
cd autoresearch-findings
git checkout ad1259e5894f224a3d1eda62a1914da4b4dd699e -- programmes/proof-complexity
cd programmes/proof-complexity && lake build 'Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour' 'Programme.«20261104-1627-proof-complexity».RectangularOne' 'Programme.«20261104-1627-proof-complexity».RemainingSpanning'
AR_LIBRARY=$PWD python -I ../../claims/conditional-pc-degree-four-onto-fphp-surplus-9/checks/lean-K100.py
AR_LIBRARY=$PWD python -I ../../claims/conditional-pc-degree-four-onto-fphp-surplus-9/checks/lean-K14.py
```

A full `lake build` builds the whole library. The named targets build only the claim modules and their dependencies. Indicative measurements from the 2026-11-06 reproduction on 2 cores / 7.8 GB: K13–K15 90 s; K1–K6 440 s; K18 87 min (90 certificate modules). Peak memory was 4.7 GB for one Lean process. Build times depend on hardware and cached dependencies.

`checks/run-copies/`: the author's working copies from the run; they import the run's private `Work` package and are not built standalone.
<!-- /programme verification -->
