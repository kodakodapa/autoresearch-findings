---
layout: post
title: "Unexploitable modal agents that cooperate with themselves: a census"
date: 2026-10-21
scholar: {"citation_title": "Unexploitable modal agents that cooperate with themselves: a census", "citation_author": "Kodakodapa", "citation_publication_date": "2026/10/21", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/only-one-fairbot-census.html", "citation_keywords": "C046", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/only-one-fairbot-census/paper.pdf"}
---

## Summary

<!-- owner-summary -->
## Setting

Two programs play a one-shot prisoner's dilemma, and each can read the other's source code.
Following Barasz et al. [1], a *modal agent* decides by asking what can be proved
about the opponent, written with the provability box $\Box$ of the logic GL: $p$ means "the
opponent cooperates with me" and $q$ "the opponent cooperates with DefectBot". FairBot is
$\Box p$: it cooperates exactly when it can prove that the opponent cooperates with it. An agent
is *unexploitable* if no modal opponent ever ends up defecting while the agent cooperates, and
*self-cooperating* if two copies cooperate. We take guarded formulas (every atom under a box)
built from $p$, $q$, $\bot$, $\neg$, $\wedge$, $\vee$, $\Box$, measure size as the number of
nodes, and call two agents behaviourally equal when they make the same moves against every
opponent. Agents using only $p$ are the rank-0 agents of Barasz et al.

A LessWrong post [2] asked whether every rank-0 agent that is unexploitable and
self-cooperating is FairBot. A comment there shows that the answer is yes up to modal depth 1 and
no from depth 2, with examples such as $\Box\Box p$, FairBot over PA+1 and $\Box^k p$.

## Result

- **Rank 0.** Among rank-0 agents of size at most 15 there are exactly 5031 classes that are
  unexploitable and self-cooperating (4374 of them also cooperate with FairBot and CooperateBot).
  Only $\Box p$ itself is FairBot; every other class is told apart from FairBot by an explicit
  opponent.
- **With $q$.** Allowing $q$, up to size 14 there are 26449 such classes (16756 up to behaviour);
  387 of them behave exactly like FairBot against every opponent, and each of the others is told
  apart from FairBot by an explicit opponent.
- **Why some different formulas are FairBot.** Two agents behave identically against every
  opponent exactly when they have the same moves against DefectBot and agree on every input the
  opponent can actually produce: until the agent first cooperates, the opponent's move against it
  equals its move against DefectBot. So, for example, $\Box(p \vee (q \wedge \Box\bot))$ is
  behaviourally FairBot.
- **A small example that is not FairBot.** $\neg\Box\bot \wedge \Box(p \vee \Box\bot)$ (size 9)
  is unexploitable and cooperates with itself and with CooperateBot, yet mutually defects with
  FairBot; it is the agent WaitFairBot$_1$ of Barasz et al. Every smaller rank-0 agent that is
  unexploitable and self-cooperating cooperates with FairBot.

## Why it matters

The LessWrong question was answered with a few examples. These counts make the answer
quantitative: among small agents, FairBot is one of thousands of unexploitable self-cooperators,
and for each one there is a concrete opponent that tells it apart from FairBot. The criterion for
behavioural equality explains which syntactically different agents are nevertheless FairBot.

## Proved vs checked

The equality criterion and the FairBot-equivalence of $\Box(p \vee (q \wedge \Box\bot))$ are
proved in Lean 4, in the height semantics of closed GL fixed points; the link to provability in
arithmetic is Solovay's theorem [3], cited, not formalised (see also
[4]). The counts are exhaustive computations up to the stated sizes, with every
separating opponent recorded and re-solved by the checks. The minimality statement for the size-9
agent is an exhaustive search over smaller rank-0 agents.
<!-- /owner-summary -->

This result extends Barasz et al. (arXiv 1401.5577): modal agents, unexploitability, rank, and WaitFairBot_K; "Is there only one FairBot?" (LessWrong, 2026), with Zac Hatfield-Dodds's comment answering it to modal depth 1 and giving examples. Our prior-art search (2026-10-21) covered:

- Barasz, LaVictoire, Christiano, Fallenstein, Herreshoff, Yudkowsky, "Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic" (arXiv 1401.5577): unexploitability (Section 2), rank and Theorem 4.10 (Section 4), WaitFairBot_K and the obstacle theorem (Section 5).
- LessWrong, "Is there only one FairBot?" (transhumanist_atom_understander, 29 Aug 2026) and comments: Zac Hatfield-Dodds shows the uniqueness conjecture holds up to modal depth 1 for rank-0 agents and fails from depth 2 (Box Box p; FairBot over PA+1 = Box(p or Box False); Box^k p for k >= 3); PrudentBot separates Box Box p from FairBot; the author notes Box Box p is not provably unexploitable in PA. No enumeration or counts.
- LessWrong / Alignment Forum wiki "Modal combat": DefectBot, CooperateBot, FairBot, PrudentBot, CliqueBot, TrollBot; no uniqueness result, no enumeration.
- LaVictoire et al. 2014 (MIPC); comment thread on "Robust Cooperation in the Prisoner's Dilemma" (LessWrong, on instability of FairBot equilibria); Hobson, "Yet More Modal Combat" (2021); Critch, parametric bounded Löb (arXiv 1602.04184); Critch, Dennis & Russell (arXiv 2208.07006); MIRI provability repository (github.com/machine-intelligence/provability, a modal-agent evaluator, no published census).
- Out of scope by direction: probabilistic blends (Oesterheld arXiv 2211.05057; Cooper et al. arXiv 2412.14570).
- Web searches for deterministic blends, behavioural distance and classifications of modal agents (2026-10-20/21); none means not found in this search.

If you know of related work we missed, please open an issue.

We believe this result is new. Our prior-art search (2026-10-21) covered:

- Barasz, LaVictoire, Christiano, Fallenstein, Herreshoff, Yudkowsky, "Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic" (arXiv 1401.5577): unexploitability (Section 2), rank and Theorem 4.10 (Section 4), WaitFairBot_K and the obstacle theorem (Section 5).
- LessWrong, "Is there only one FairBot?" (transhumanist_atom_understander, 29 Aug 2026) and comments: Zac Hatfield-Dodds shows the uniqueness conjecture holds up to modal depth 1 for rank-0 agents and fails from depth 2 (Box Box p; FairBot over PA+1 = Box(p or Box False); Box^k p for k >= 3); PrudentBot separates Box Box p from FairBot; the author notes Box Box p is not provably unexploitable in PA. No enumeration or counts.
- LessWrong / Alignment Forum wiki "Modal combat": DefectBot, CooperateBot, FairBot, PrudentBot, CliqueBot, TrollBot; no uniqueness result, no enumeration.
- LaVictoire et al. 2014 (MIPC); comment thread on "Robust Cooperation in the Prisoner's Dilemma" (LessWrong, on instability of FairBot equilibria); Hobson, "Yet More Modal Combat" (2021); Critch, parametric bounded Löb (arXiv 1602.04184); Critch, Dennis & Russell (arXiv 2208.07006); MIRI provability repository (github.com/machine-intelligence/provability, a modal-agent evaluator, no published census).
- Out of scope by direction: probabilistic blends (Oesterheld arXiv 2211.05057; Cooper et al. arXiv 2412.14570).
- Web searches for deterministic blends, behavioural distance and classifications of modal agents (2026-10-20/21); none means not found in this search.

We found no earlier statement of it, but we can't be certain. If you know of prior work, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was partly checked by scripts that run Lean proofs (claims K11, K18) and partly checked by script (claims K51, K53, K2); the proof and check files are included so anyone can re-run them.

**K51.** In rank-0 $L$ (atom $p$, guarded, size $\le15$) exactly 5031 classes are unexploitable and self-cooperating, 4374 of them cooperating with FairBot and CooperateBot; only $\Box p$ is FairBot, every other one is separated from it by an explicit opponent.

- Status: derived · author check only
- Machine-checked: 2 of 2 check scripts passed.
- Prior art: partial prior art

**K53.** In $L$ with atoms $p,q$ (guarded, size $\le14$), 26449 machine classes (16756 behaviour classes) are unexploitable and self-cooperating; 387 of them behave as FairBot, and each other one gets a different outcome than FairBot against an explicit opponent.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

**K11.** $X=\Box(p\vee(q\wedge\Box\bot))$ (size 7) has the same moves as FairBot $\Box p$ at every height against every modal opponent, since an opponent's height-0 move against any agent equals its move against DefectBot.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K18.** For causal agents $A,A'$ in height semantics: they make the same moves in every game against every causal opponent iff their DefectBot traces are equal and they agree on all realizable words ($p=q$ up to the first cooperation of $A$ or its DefectBot trace).

- Status: derived · author check only
- Machine-checked: 2 of 2 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K2.** $A=\neg\Box\bot\wedge\Box(p\vee\Box\bot)$ (size 9) is unexploitable by every modal opponent, cooperates with its copy and with CooperateBot, yet mutually defects with FairBot; every rank-0 unexploitable self-cooperator of size $\le 8$ cooperates with FairBot.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

## Discussion

The counts depend on the agent language and the size measure; they say how common
non-FairBot unexploitable self-cooperators are among small formulas, not in any absolute sense.
"Unexploitable" is about what actually happens in play (truth in the standard model, as in Barasz
et al.), not about what Peano arithmetic can prove about the agent; the LessWrong discussion
points out that the two differ. Open questions: how the counts grow with size, and whether the
non-FairBot classes fall into a small number of families.

## How to verify

Run each script in `claims/only-one-fairbot-census/checks/` with `python -I <script>`; it passes if it
exits with status 0. The results recorded in the original run are in
`claims/only-one-fairbot-census/results/`; the full claim text is in `claims/only-one-fairbot-census/claim.md`.

## Provenance

- run: 20261020-1600
- claims: K51, K53, K11, K18, K2
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- K51 author: r1 (claude)
- K53 author: r1 (claude)
- K11 author: r1 (claude)
- K18 author: r1 (claude)
- K2 author: r1 (claude)

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:onlyonefairbot2026 --> transhumanist\_atom\_understander. 2026. Is there only one FairBot?. [Link](https://www.lesswrong.com/posts/auAq7Rcstop3FBEob/is-there-only-one-fairbot)
3. <!-- cite:solovay1976provability --> Solovay, Robert M.. 1976. Provability Interpretations of Modal Logic. Israel Journal of Mathematics
4. <!-- cite:boolos1993logic --> Boolos, George. 1993. The Logic of Provability. Cambridge University Press

<!-- autoresearch:revisions -->
## Revisions

- 2026-10-21 — Production note: Lean proofs run inside check scripts are now described as such, separately from harness-built proofs
