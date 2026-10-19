# A certified map of variants of Gödel's ontological argument

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

This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the proof and check files are included so anyone can re-run them.

## K2

Full-property constant-domain embedding, Scott essence: A1, A2, A5 imply $R\,w\,v \leftrightarrow v = w$ and modal collapse on every symmetric frame; adding A3 gives $\exists x\,G(x)$ and $\Box\exists x\,G(x)$ there, and $\Box\exists x\,G(x)$ on euclidean frames. A4 is not used.

Status: derived

Kind: model

Evidence:
- check `checks/K2-c009_lean_table.py`: lean --stdin exit 0, no sorry, no axiom decls; haec\_ess, NE\_isolated, A125\_isolated\_succ, A125\_sym\_iso, A125\_sym\_collapse, A1235\_sym\_god, A1235\_euclid\_box, majority\_model all within {propext, Classical.choice, Quot.sound} — pass (`results/K2-1.json`)
- reasoning: Haecceity h\_{x,v} is a Scott essence of x at v; NE then forces every successor of v to be v. T1 (A1,A2) puts an NE-being in some successor; symmetry or euclideanness transfers isolation back to w.

Prior art: partial prior art (answer: `prior-art/R1.md`)

### Provenance

- run: 20261018-1933
- claim: K2
- author: r1 (claude)
- round: 1
- run-folder commit: 338871c09385f72bc0f657c9a639ef6a3c825566
- check results: K2-1.json

## K7

Constant domain, rigid properties, Scott/Gödel essence, all 32 subsets × 9 classes certified: no consistent cell forces collapse; $\exists x\,G(x)$ and $\Box\exists x\,G(x)$ hold iff the subset contains A1,A2,A3, or A1,A3,A5 with Scott essence, on every frame.

Status: derived

Kind: model

Evidence:
- check `checks/K7-c009_rigid_table.py`: lean --stdin exit 0, no sorry, no axiom decls; A123\_god/box, A135S\_god/box, A12\_A5S, A125G\_no\_world within {propext, Classical.choice, Quot.sound}, scott\_rigid\_noncollapse axiom-free; all 576 cells × 4 outcomes certified by a brute-force re-evaluated model or a Lean theorem whose hypotheses ⊆ cell axioms; no pool model contradicts a Lean cell; stated pattern asserted for every cell — pass (`results/K7-1.json`)
- reasoning: Rigid essence of x is {x} (Scott) or ⊆{x} (Gödel, includes ∅), so NE\_w is ⊤ (Scott) or ∅ (Gödel) at serial worlds; constant copies of one-world models onto a universal 2-world frame preserve all axioms, so collapse is never forced.

Prior art: partial prior art (answer: `prior-art/R5.md`)

### Provenance

- run: 20261018-1933
- claim: K7
- author: r1 (claude)
- round: 3
- run-folder commit: 338871c09385f72bc0f657c9a639ef6a3c825566
- check results: K7-1.json

## K9

Constant-domain full-property Anderson slice: $\exists x\,G_A(x)$ holds iff the subset contains A1a, A2, H and the class is B, KB, S5, or KD45 with A4; $\Box\exists x\,G_A(x)$ iff it contains A1a, A2, H on B, KB, KD45, S5. A5 is derivable from A2 and H.

Status: derived

Kind: model

Evidence:
- check `checks/K9-c009_anderson_open.py`: lean --stdin exit 0, no sorry, no axiom decls; NE\_univ, A2H\_A5, poss, sym\_god, sym\_box, eucl\_box, eucl\_A4\_god, kd45\_countermodel within {propext, Classical.choice, Quot.sound}; another researcher's verbatim evaluator gives the 3-world KD45 countermodel axiom mask {A1a,A2,H,A5}, no God-like being at the root, box-exists true; A2&H imply A5 on all 4136 models of K8's bound; resolves all 16 open K8 cells — pass (`results/K9-1.json`)
- reasoning: Remaining cells of the table are K8's explicit countermodels (re-run PASS): every subset lacking A1a, A2 or H, and all K, T, D, K4, S4 cells, have existence countermodels.

Prior art: partial prior art (answer: `prior-art/R8.md`)

### Provenance

- run: 20261018-1933
- claim: K9
- author: r1 (claude)
- round: 4
- run-folder commit: 338871c09385f72bc0f657c9a639ef6a3c825566
- check results: K9-1.json

## K13

Constant-domain extensional Fitting, all subsets of A1a,A1b,A2,H,N × nine frame classes: all 288 cells are consistent and permit noncollapse; both existence conclusions hold exactly for supersets of $\{A1a,A2,H\}$ or $\{A1a,H,N\}$. A1b is unnecessary.

Status: derived

Kind: model

Evidence:
- check `checks/K13-fitting_split.py`: Lean core proves four existence/box theorems with A1a only and NE universal; standard axioms only, no sorry or axiom declarations. Re-evaluates explicit models covering every negative cell and all consistency/noncollapse cells; regenerates pinned 288-cell table. — pass (`results/K13-1.json`)
- reasoning: Both proofs use only exclusion of positive complementary pairs. The three negative models cover respectively absence of A1a, absence of H, and absence of both A2 and N. Universal two-world frames belong to all nine classes and refute collapse.

Prior art: partial prior art (answer: `prior-art/R10.md`)

### Provenance

- run: 20261018-1933
- claim: K13
- author: r2 (codex)
- round: 7
- run-folder commit: 338871c09385f72bc0f657c9a639ef6a3c825566
- check results: K13-1.json

## K15

Varying-domain (actualist) full-property Anderson, 32 subsets × 9 classes: as in constant domains except $\exists^E x\,G_A(x)$ on KD45 with A4 now fails; a 3-world KD45 model satisfies all five axioms, but its God-like being does not exist at the root.

Status: derived

Kind: model

Evidence:
- check `checks/K15-c009_varying_anderson.py`: lean --stdin exit 0, no sorry, no axiom decls; god\_exists\_succ, poss, sym\_god, sym\_box, eucl\_box, A2H\_A5, kd45\_varying, entails\_top within {propext, Classical.choice, Quot.sound}; guarded evaluator = another researcher's verbatim evaluator at E=all on 4136 models; kd45\_varying re-evaluated (mask 31, exists false, box-exists true, noncollapse); varying-E sweep of 16528 pairs consistent with all theorems; 288-cell table asserted (pattern, no OPEN, 15/KD45 and 31/KD45 refuted) and sha256-pinned — pass (`results/K15-1.json`)
- reasoning: A God-like x at w exists at every successor of w (A2 alone), so symmetric and euclidean transfers carry existence along. On KD45 the root is not its own successor, so nothing forces the God-like individual to exist there; A4 fixes positivity, not existence.
- citation arxiv:1910.08955 “Computer-supported Analysis of Positive Properties, Ultrafilters and Modal Collapse in Variants of Gödel’s Ontological Argument” — verified

Prior art: partial prior art (answer: `prior-art/R12.md`)

### Provenance

- run: 20261018-1933
- claim: K15
- author: r1 (claude)
- round: 20
- run-folder commit: 338871c09385f72bc0f657c9a639ef6a3c825566
- check results: K15-1.json

## K16

Varying-domain (actualist) extensional Fitting, 32 subsets of A1a,A1b,A2,H,N × 9 classes: $\exists^E x\,G(x)$ holds iff the subset contains $\{A1a,A2,H,N\}$ on T, B, S4, S5; $\Box\exists^E x\,G(x)$ also on KD45. K13's sets $\{A1a,A2,H\}$ and $\{A1a,H,N\}$ fail in S5.

Status: derived

Kind: model

Evidence:
- check `checks/K16-c009_varying_fitting.py`: lean --stdin exit 0, no sorry, no axiom decls; god\_nonempty, refl\_god, T\_god, T\_box, eucl\_box within {propext, Classical.choice, Quot.sound}; haec\_ess, NE\_iff, god\_exists\_succ, noN\_S5, noA2\_S5 axiom-free; 1134 search certificates re-evaluated by a direct evaluator per varying mode; table identical for possibly-empty, nonempty and every-individual-somewhere domains; const mode equals K13 pattern; no countermodel contradicts a Lean cell; 288-cell pattern asserted, no OPEN, sha256-pinned — pass (`results/K16-1.json`)
- reasoning: The haecceity is an essence, so NE(x) at w means x exists at all successors. N then makes a God-like being exist at successors only, so actual existence needs reflexivity, and N no longer forces P(top), which is why {A1a,H,N} loses its constant-domain proof. Without N, A2 gives a God-like individual that need not exist anywhere relevant.
- citation arxiv:1910.08955 “Computer-supported Analysis of Positive Properties, Ultrafilters and Modal Collapse in Variants of Gödel’s Ontological Argument” — verified

Prior art: partial prior art (answer: `prior-art/R10.md`)

### Provenance

- run: 20261018-1933
- claim: K16
- author: r1 (claude)
- round: 20
- run-folder commit: 338871c09385f72bc0f657c9a639ef6a3c825566
- check results: K16-1.json

## K18

Varying-domain rigid Scott, 64 subsets of A1a,A1b,A2..A5 × 9 classes: A1b is never needed; $\exists^E G$ iff ⊇{A1a,A2,A3,A5} on T,B,S4,S5 or +A4 on KB; $\Box\exists^E G$ iff ⊇{A1a,A2,A3,A5} on T,B,S4,S5,KD45 or +A4 on any frame.

Status: derived

Kind: model

Evidence:
- check `checks/K18-c009_varying_rigid_split.py`: lean --stdin exit 0, no sorry, no axiom decls; god\_nonempty, serial, T\_god, T\_box, eucl\_box, A4\_box, sym\_A4\_god (all with A1a only) within {propext, Classical.choice, Quot.sound}; haec\_ess, NE\_iff, god\_exists\_succ, A4\_god\_back, godel\_no\_world, kd45\_A4, kb\_noA4 axiom-free; 4274 search certificates re-evaluated by a direct evaluator; 1152-cell pattern asserted with no OPEN cell; table identical for nonempty domains; constant mode matches K7/K13 split pattern; sha256 70aa8973... — pass (`results/K18-2.json`)
- reasoning: A4 gives inclusion of positivity from w to its successor v, so G at v is contained in G at w. A God-like being at v is therefore God-like at w, and the Scott-essence NE at w (existence at all successors, via the haecceity) puts it in v. Only exclusion (A1a) is used, to make G nonempty and R serial.
- citation arxiv:1910.08955 “Computer-supported Analysis of Positive Properties, Ultrafilters and Modal Collapse in Variants of Gödel’s Ontological Argument” — verified
- check `checks/K18-c009_varying_rigid_split.py`: lean --stdin exit 0, no sorry, no axiom decls; 14 theorems within standard axioms; 4274 search certificates re-evaluated; 1152-cell pattern asserted with no OPEN cell; sha256 70aa8973... — pass (`results/K18-2.json`)

Prior art: partial prior art (answer: `prior-art/R9.md`)

### Provenance

- run: 20261018-1933
- claim: K18
- author: r1 (claude)
- round: 20
- run-folder commit: 338871c09385f72bc0f657c9a639ef6a3c825566
- check results: K18-2.json

## K21

Anderson $G_A$, full properties, 64 subsets of A1a,A1b,A2,H,A4,A5 × 9 classes × constant/varying domains: collapse iff ⊇{A1a,A1b,A2,H} on B,S5, or +A4 on KB; $\exists G_A$ on KD45 needs A4 or A1b and constant domains; otherwise as K9/K15.

Status: derived

Kind: model

Evidence:
- check `checks/K21-c009_anderson_a1b.py`: lean --stdin exit 0, no sorry, no axiom decls; god\_det, eucl\_A1b\_godlike, eucl\_A4\_godlike, refl\_sym\_collapse, sym\_A4\_collapse, sym\_god, sym\_box, eucl\_box, A2H\_A5, kb\_cycle, kd45\_A1b and 6 helpers within {propext, Classical.choice, Quot.sound}; 16528 bound models + 5 named models re-evaluated; no model contradicts a Lean cell; 1152-cell pattern asserted, all consistent, no OPEN; sha256 08d76079... — pass (`results/K21-1.json`)
- reasoning: If x is God-like at w, every property or its complement is positive (A1b), hence necessary for x; applied to world-indicator properties this leaves w at most one successor. On reflexive symmetric frames God-likeness at every world (K9) then isolates each world; on KB a 2-cycle survives unless A4 transfers the indicator of v from w to v.
- citation arxiv:1910.08955 “Computer-supported Analysis of Positive Properties, Ultrafilters and Modal Collapse in Variants of Gödel’s Ontological Argument” — verified

Prior art: partial prior art (answer: `prior-art/R7.md`)

### Provenance

- run: 20261018-1933
- claim: K21
- author: r1 (claude)
- round: 20
- run-folder commit: 338871c09385f72bc0f657c9a639ef6a3c825566
- check results: K21-1.json

## K22

Full-property Scott, constant or varying domains, 64 subsets of A1a,A1b,A2–A5 × 2 essences × 9 classes: A1b is never needed; $\exists G$ iff ⊇{A1a,A2,A3,A5} on B,KB,S5 (box also KD45); collapse iff ⊇{A1a,A2,A5} there; Gödel essence with {A1a,A2,A5} has no model.

Status: derived

Kind: model

Evidence:
- check `checks/K22-c009_scott_split.py`: lean --stdin exit 0, no sorry, no axiom decls; serial, T1, A125\_sym\_collapse, A1235\_sym\_god, A1235\_euclid\_box, godel1970\_no\_model (hypotheses A1a only, E free) within {propext, Classical.choice, Quot.sound}; haec\_ess, entails\_top axiom-free; K3 data sha256 91c8ed5b... pinned; 3116 model outcomes re-evaluated (class, split axioms, refuted outcome) incl. the all-positive model; 864-cell pattern asserted, A1b-drop invariance asserted, table sha256 eb8f629f... pinned — pass (`results/K22-1.json`)
- reasoning: T1 needs only that phi and its complement are not both positive: if a positive phi were nowhere exemplified, phi would necessarily entail its complement. Seriality follows the same way from any globally positive property. All later steps (haecceity isolation, symmetric/euclidean transfer) never mention complements. Conversely, making every property positive satisfies A1b and A2-A5 while G is empty.
- citation doi:10.3233/978-1-61499-419-0-93 “Automating Gödel's Ontological Proof of God's Existence with Higher-order Automated Theorem Provers” — verified

Prior art: partial prior art (answer: `prior-art/R9.md`)

### Provenance

- run: 20261018-1933
- claim: K22
- author: r1 (claude)
- round: 20
- run-folder commit: 338871c09385f72bc0f657c9a639ef6a3c825566
- check results: K22-1.json

## K24

Constant-domain full-property simplified AllMeet slice (216 cells): every cell is consistent and permits noncollapse; $\exists G$ and $\Box\exists G$ hold exactly for all three axioms with local/either closure. Every other cell has a finite countermodel.

Status: derived

Kind: model

Evidence:
- check `checks/K24-allmeet_classification.py`: Self-contained Lean existence/box proofs plus regeneration of SHA256-pinned 216-cell AllMeet table; every finite certificate re-evaluated; arbitrary meets checked exactly by top and binary intersections on finite powersets; no open cells. — pass (`results/K24-1.json`)

Prior art: partial prior art (answer: `prior-art/R11.md`)

### Provenance

- run: 20261018-1933
- claim: K24
- author: r2 (codex)
- round: 21
- run-folder commit: 338871c09385f72bc0f657c9a639ef6a3c825566
- check results: K24-1.json

## K28

Varying-domain full-property simplified slices: AllMeet has exactly K24’s 216-cell outcomes; binary closure has 216 consistent, noncollapsing cells refuting $\exists^E G$ and $\Box\exists^E G$, even with A1w. Positive AllMeet cells require all axioms and local/either closure.

Status: derived

Kind: model

Evidence:
- check `checks/K28-varying_meets.py`: Lean core with arbitrary E proves AllMeet PG/existence/box under A1prime and guarded local closure, plus either-to-local; guarded total-E tail model refutes existence/box and inherited proofs certify binary closure/A1w/noncollapse. Regenerates SHA256-pinned 216-cell AllMeet table and reevaluates every finite certificate with explicit E; enumerates 216 binary rows by weakening the Lean infinite model; no sorry or declared axioms. — pass (`results/K28-1.json`)

Prior art: partial prior art (answer: `prior-art/R11.md`)

### Provenance

- run: 20261018-1933
- claim: K28
- author: r2 (codex)
- round: 26
- run-folder commit: 338871c09385f72bc0f657c9a639ef6a3c825566
- check results: K28-1.json

## Discussion

<!-- owner-discussion -->
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
<!-- /owner-discussion -->

## References

1. <!-- cite:benzmueller2025notes --> Benzm\"uller, Christoph and Scott, Dana S.. 2025. Notes on G\"odel's and Scott's variants of the ontological argument. Monatshefte f\"ur Mathematik. [Link](https://link.springer.com/article/10.1007/s00605-025-02078-x)
2. <!-- cite:benzmueller2026lean --> Benzm\"uller, Christoph. 2026. G\"odel's and Scott's Variants of the Ontological Argument in Lean 4 and TPTP THF. [Link](https://arxiv.org/abs/2609.26806)
3. <!-- cite:benzmueller2020simplified --> Benzm\"uller, Christoph. 2020. A (Simplified) Supreme Being Necessarily Exists, says the Computer: Computationally Explored Variants of G\"odel's Ontological Argument. Proceedings of KR 2020. [Link](https://arxiv.org/abs/2001.04701)
4. <!-- cite:benzmueller2019ultrafilters --> Benzm\"uller, Christoph and Fuenmayor, David. 2019. Computer-supported Analysis of Positive Properties, Ultrafilters and Modal Collapse in Variants of G\"odel's Ontological Argument. [Link](https://arxiv.org/abs/1910.08955)
5. <!-- cite:fitting2002types --> Fitting, Melvin. 2002. Types, Tableaus, and G\"odel's God. Kluwer
6. <!-- cite:benzmueller2017hajek --> Benzm\"uller, Christoph and Weber, Leon and Woltzenlogel Paleo, Bruno. 2017. Computer-Assisted Analysis of the Anderson--H\'ajek Ontological Controversy. Logica Universalis
7. <!-- cite:benzmueller2026ultrafilters --> Benzm\"uller, Christoph. 2026. A Comment on Modal Collapse and Ultrafilters in G\"odel's Ontological Argument. [Link](https://arxiv.org/abs/2608.07578)
