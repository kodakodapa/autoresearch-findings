## Setting

Gödel's ontological argument, in Scott's version, uses a second-order predicate $P$ ("positive")
and five axioms: A1 (exactly one of a property and its negation is positive; split here into
A1a, "not both", and A1b, "at least one"), A2 (positivity is closed under necessary entailment),
A3 ($P(G)$, where $G$, "God-like", means having every positive property), A4 (positive
properties are necessarily positive) and A5 (necessary existence is positive). The conclusion is
that a God-like being exists, $\exists x\,G(x)$, and necessarily exists, $\Box\exists x\,G(x)$.
A well-known side effect is *modal collapse*: everything true is necessarily true.

Many variants and weakenings are studied, mostly one variant at a time with an automated
theorem prover [@benzmueller2025notes; @benzmueller2026lean; @benzmueller2020simplified;
@benzmueller2019ultrafilters]. This finding maps the space systematically. We take every subset
of each variant's axioms and the nine frame classes K, D, T, B, K4, KB, KD45, S4 and S5. We
vary the semantics: all intensional properties, rigid properties or extensional properties
(Fitting [@fitting2002types]), and constant or varying (actualist) domains. Cell by cell we
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
[@benzmueller2025notes; @benzmueller2026lean; @benzmueller2017hajek; @benzmueller2020simplified].
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
[@benzmueller2026ultrafilters].

## Discussion

The map is a refinement of work that is largely known, not a new argument. Its value is
completeness: for each variant, every subset of the axioms and every listed frame class is decided
with a certificate, so the minimal sets and the frame boundaries can be read off rather than
inferred from separate studies. Several entries agree with results already established with
other provers [@benzmueller2025notes; @benzmueller2026lean; @benzmueller2017hajek], which we take
as a check on our encoding rather than as findings.

The map covers only the stated choices: a shallow embedding of higher-order modal logic, Scott's
and Gödel's definitions of essence, the listed variants, nine frame classes and two kinds of
domain. Other definitions of essence, other readings of positivity (for example world-relative
and rigid mixtures), Gödel's conjunction axiom in all slices [@benzmueller2026ultrafilters], and
logics beyond these frame classes are outside it. A cell decided here can therefore change under
a different encoding, and claims of minimality hold relative to the listed axioms.

What a reader can take away is where the strength of each variant sits: in Scott's version the
weight lies on A1a, A2, A3 and A5 together with symmetry, while A1b and A4 are idle; in
Anderson's version the dropped complement direction is exactly the switch for collapse; and in
the rigid and simplified readings, existence holds without collapse. Natural next steps are the
open cells the run left (mixed conjunction principles in some slices) and other definitions of
essence.
