---
layout: post
title: "An unexploitable modal agent that defects against itself"
date: 2026-10-18
---

<!-- owner-summary -->
## Setting

Two programs play a one-shot prisoner's dilemma, and each can read the other's source code.
Following Barasz et al. [1], a *modal agent* decides by asking what can be proved about the
opponent in Peano arithmetic, written with the provability box $\Box$ of the logic GL. FairBot,
$\Box p$, cooperates exactly when it can prove that the opponent cooperates with it
($p$); CooperateBot always cooperates; DefectBot always defects. An agent is *unexploitable* if
no modal opponent ever gets it to cooperate while the opponent defects. We consider agents
built from $p$, from $q$ ("the opponent cooperates with DefectBot"), $\bot$, $\neg$, $\wedge$,
$\vee$ and $\Box$, with every atom under a box, and measure size as the number of nodes in the
formula.

## Result

The agent $W = \Box(\Box\Box\bot \vee (p \wedge (q \vee \neg\Box q)))$ is unexploitable,
cooperates with FairBot and with CooperateBot, yet defects against an exact copy of itself. An
exhaustive search shows that no agent of size 11 or less has this combination of properties, and
$W$ (size 12) is one of the three smallest. It is the first member of an infinite family
$W_n = \Box(\Box^n\bot \vee (p \wedge (q \vee \neg\Box q)))$, $n \ge 2$, all with the same four
properties, with exact laws for how $W_n$ plays against graded FairBots $\Box^k p$, graded
PrudentBots and other members of the family.

## Why it matters

Every unexploitable agent in the literature we checked (FairBot, PrudentBot, CliqueBot)
cooperates with its own copy. $W_n$ shows that unexploitability, cooperation with FairBot and
generosity towards CooperateBot do not force self-cooperation: the delayed "gate"
$\Box^n\bot$ lets the agent tolerate FairBot's failure to prove anything about DefectBot, while
two copies of $W_n$ never reach mutual cooperation.

## Proved vs checked

The properties of $W_n$ and its laws against graded FairBots, graded PrudentBots and other
$W_m$ are proved for all indices in Lean 4 (height semantics of closed GL fixed points; the link
to provability in arithmetic is Solovay's theorem [2], cited, not formalised; see also [3]). The minimality of size
12 is an exhaustive computation over all agents up to size 12 in the stated language.
<!-- /owner-summary -->

We believe this result is new. Our prior-art search (2026-10-17) covered:

- Barasz et al. 2014, Robust Cooperation in the Prisoner's Dilemma (arXiv 1401.5577), full text: agents CB, DB, CliqueBot, FairBot, PrudentBot, TrollBot, JustBot, WaitFairBot_K; Theorems 3.2, 4.8, 4.10 and the obstacles section.
- LaVictoire et al. 2014, Program Equilibrium in the Prisoner's Dilemma via Löb's Theorem (intelligence.org/files/ProgramEquilibrium.pdf).
- LessWrong post "Robust Cooperation in the Prisoner's Dilemma" and its comments (orthonormal, cousin_it, Will_Sawin, Karl, dankane).
- Arbital / LessWrong wiki "Modal combat".
- Garrabrant, "Prisoners' Dilemma with Costs to Modeling" (Alignment Forum).
- Mennen, "Modal Combat for games other than the prisoner's dilemma" (agentfoundations.org item 1304).
- github.com/machine-intelligence/provability (Haskell solver and combat code; the agents folder contents were not visible).

We found no earlier statement of it, but we can't be certain. If you know of prior work, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the proof and check files are included so anyone can re-run them.

**K6.** In L (atoms p,q boxed; F,~,&,\|,[]; size=nodes), the smallest agent that cooperates with FairBot and CooperateBot, defects against itself and is unexploitable has size 12; W=\[]([][]F\|(p&(q\|~[]q))) is one, unexploitable by every opponent; none of size <=11.

- Status: derived
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K9.** For every n>=2, the agent W_n=\[]([]^n F\|(p&(q\|~[]q))) of size n+10 is unexploitable by every modal opponent, mutually cooperates with FairBot and CooperateBot, and defects against itself (both copies defect above height n+1); W_0, W_1 fail with FairBot. Lean-proved.

- Status: derived
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K11.** For all n>=0, k>=1, j,m>=0 (height semantics of closed GL fixed points): W_n and F_k cooperate at every height iff k<n; W_n and P_j iff 2<=n<j; W_n and W_m both defect from height n+m+3. Hence all W_n (n>=2) are distinct. Lean-proved.

- Status: derived
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

## How to verify

Run each script in `claims/wn-gate-family/checks/` with `python -I <script>`; it passes if it
exits with status 0. The results recorded in the original run are in
`claims/wn-gate-family/results/`; the full claim text is in `claims/wn-gate-family/claim.md`.

## Provenance

- run: 20261017-1126
- claims: K6, K9, K11
- run-folder commit: 662166ecff0651902cc5fcb04bf747c62d795af2
- K6 author: r1 (claude)
- K9 author: r1 (claude)
- K11 author: r1 (claude)

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:solovay1976provability --> Solovay, Robert M.. 1976. Provability Interpretations of Modal Logic. Israel Journal of Mathematics
3. <!-- cite:boolos1993logic --> Boolos, George. 1993. The Logic of Provability. Cambridge University Press

<!-- autoresearch:revisions -->
## Revisions

- 2026-10-18 — Escaped claim statements, compiled PDF, references, per-finding paper, website layout
