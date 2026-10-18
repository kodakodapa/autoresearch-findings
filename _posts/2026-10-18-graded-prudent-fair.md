---
layout: post
title: "When graded PrudentBots cooperate with graded FairBots"
date: 2026-10-18
---

## Summary

<!-- owner-summary -->
## Setting

Two programs play a one-shot prisoner's dilemma, and each can read the other's source code. A
*modal agent* [1] decides by asking what Peano arithmetic (PA) can prove about
the opponent, written with the provability box $\Box$ of the logic GL. Here $p$ means "the
opponent cooperates with me" and $q$ means "the opponent cooperates with DefectBot", the agent
that always defects. FairBot, $\Box p$, cooperates exactly when it can prove that the opponent
cooperates with it. PrudentBot adds a safety test: it also requires a proof, in the stronger
system PA+1, that the opponent would not cooperate with DefectBot, so it does not reward an
opponent that cooperates with everyone.

We study two graded families. The graded FairBot $F_k = \Box^k p$ ($k \ge 1$) asks for $k$
nested layers of provability; $F_1$ is FairBot. The graded PrudentBot
$P_j = \Box p \wedge \Box(\neg\Box^j\bot \rightarrow \neg q)$ ($j \ge 0$) runs its safety test
in PA+$j$, since $\neg\Box^{j}\bot$ expresses the consistency of PA+$(j-1)$; $P_1$ is
PrudentBot.

## Result

$P_j$ and $F_k$ cooperate with each other exactly when $k \le j$; when $k > j$, both defect.
In words: a PrudentBot that runs its safety test in a stronger system can afford to cooperate
with FairBots that demand more nested proof, and the exchange rate is one for one. Every $P_j$
still defects against CooperateBot, so the extra cooperation costs nothing in safety.

## Why it matters

Barasz et al. remark that PrudentBot's safety test may use a stronger system than PA+1 and
that this widens the set of agents it cooperates with, and online discussion of the paper
looked at specific pairs of such variants. Here the relation is pinned down exactly for the
two graded families, for all indices: the boundary of cooperation is the single inequality
$k \le j$.

## Proved vs checked

Proved for all $j \ge 0$ and $k \ge 1$ in Lean 4, in the height semantics of closed GL fixed
points (on the chain of heights, both agents cooperate at every height when $k \le j$; when
$k > j$ both defect above height $j + k$). The link to provability in PA is Solovay's theorem
[2] (see also [3]), cited, not formalised, and the reading
in the standard model assumes PA is sound.
<!-- /owner-summary -->

This result extends # Prior-art answer for R4 (K8: P_j / F_k threshold law)

Verdict: partial prior art.

- Barasz et al. 2014, remark after Theorem 3.2: PrudentBot's DefectBot check may use PA+n for larger n, which widens the set of agents it cooperates with without losing safety. That is the idea behind graded PrudentBots, stated informally.
- LessWrong comments on the Barasz et al. post (orthonormal, cousin_it) discuss indexed variants "Prudent(m,n)Bot" with specific pairs, e.g. Prudent(0,100)Bot cooperating with Prudent(0,1)Bot and Prudent(99,1000)Bot, and cousin_it noting that a PrudentBot using PA and PA+1 does not cooperate with one using PA+1 and PA+2.
- Not found: a general threshold law for P_j against graded FairBots F_k (cooperate iff k <= j, both defect above j+k), or a proof of it.
- Suggested wording: the graded family was discussed informally (Barasz et al. remark; LessWrong comments); the general law and its Lean proof were not found.

## Sources searched (owner, web search, 2026-10-17)
- Barasz et al. 2014, Robust Cooperation in the Prisoner's Dilemma (arXiv 1401.5577), full text: agents CB, DB, CliqueBot, FairBot, PrudentBot, TrollBot, JustBot, WaitFairBot_K; Theorems 3.2, 4.8, 4.10 and the obstacles section.
- LaVictoire et al. 2014, Program Equilibrium in the Prisoner's Dilemma via Löb's Theorem (intelligence.org/files/ProgramEquilibrium.pdf).
- LessWrong post "Robust Cooperation in the Prisoner's Dilemma" and its comments (orthonormal, cousin_it, Will_Sawin, Karl, dankane).
- Arbital / LessWrong wiki "Modal combat".
- Garrabrant, "Prisoners' Dilemma with Costs to Modeling" (Alignment Forum).
- Mennen, "Modal Combat for games other than the prisoner's dilemma" (agentfoundations.org item 1304).
- github.com/machine-intelligence/provability (Haskell solver and combat code; the agents folder contents were not visible).
Not searched: Critch's parametric bounded Löb paper, theses, the contents of the Haskell agents folder, non-English sources. A "none" verdict means "not found in this search", nothing more. Our prior-art search (2026-10-17) covered:

- Barasz et al. 2014, Robust Cooperation in the Prisoner's Dilemma (arXiv 1401.5577), full text: agents CB, DB, CliqueBot, FairBot, PrudentBot, TrollBot, JustBot, WaitFairBot_K; Theorems 3.2, 4.8, 4.10 and the obstacles section.
- LaVictoire et al. 2014, Program Equilibrium in the Prisoner's Dilemma via Löb's Theorem (intelligence.org/files/ProgramEquilibrium.pdf).
- LessWrong post "Robust Cooperation in the Prisoner's Dilemma" and its comments (orthonormal, cousin_it, Will_Sawin, Karl, dankane).
- Arbital / LessWrong wiki "Modal combat".
- Garrabrant, "Prisoners' Dilemma with Costs to Modeling" (Alignment Forum).
- Mennen, "Modal Combat for games other than the prisoner's dilemma" (agentfoundations.org item 1304).
- github.com/machine-intelligence/provability (Haskell solver and combat code; the agents folder contents were not visible).

If you know of related work we missed, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the proof and check files are included so anyone can re-run them.

**K8.** For all j>=0, k>=1 (height-chain semantics of closed GL fixed points): P_j=[]p&\[](~[]^jF->~q) and F_k=[]^k p cooperate at every height iff k<=j; if j<k both defect above height j+k. Lean-proved; P_j defects vs CB.

- Status: derived
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

## How to verify

Run each script in `claims/graded-prudent-fair/checks/` with `python -I <script>`; it passes if it
exits with status 0. The results recorded in the original run are in
`claims/graded-prudent-fair/results/`; the full claim text is in `claims/graded-prudent-fair/claim.md`.

## Provenance

- run: 20261017-1126
- claims: K8
- run-folder commit: 662166ecff0651902cc5fcb04bf747c62d795af2
- K8 author: r1 (claude)

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:solovay1976provability --> Solovay, Robert M.. 1976. Provability Interpretations of Modal Logic. Israel Journal of Mathematics
3. <!-- cite:boolos1993logic --> Boolos, George. 1993. The Logic of Provability. Cambridge University Press
