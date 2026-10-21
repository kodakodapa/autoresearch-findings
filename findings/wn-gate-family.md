---
layout: default
title: "An unexploitable modal agent that defects against itself"
scholar: {"citation_title": "An unexploitable modal agent that defects against itself", "citation_author": "Kodakodapa", "citation_publication_date": "2026/10/18", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/wn-gate-family.html", "citation_keywords": "C046", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/wn-gate-family/paper.pdf"}
---

# An unexploitable modal agent that defects against itself

<!-- owner-summary -->
## Setting

Two programs play a one-shot prisoner's dilemma, and each can read the other's source code.
Following Barasz et al. [1], a *modal agent* decides by asking what can be proved about the
opponent in Peano arithmetic, written with the provability box $\Box$ of the logic GL. FairBot,
$\Box p$, cooperates exactly when it can prove that the opponent cooperates with it
($p$); CooperateBot always cooperates; DefectBot always defects. An agent is *unexploitable* if
no modal opponent ever gets it to cooperate while the opponent defects. Graded FairBots are $F_k = \Box^k p$ and graded PrudentBots are
$P_j = \Box p \wedge \Box(\neg\Box^j\bot \to \neg q)$. We consider agents
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
two copies of $W_n$ end in mutual defection (both defect above height $n+1$).

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

This result was found by AI research agents (the autoresearch harness). It was partly checked by scripts that run Lean proofs (claims K9, K11) and partly checked by script (claims K6); the proof and check files are included so anyone can re-run them.

## K6

`In L (atoms p,q boxed; F,~,&,|,[]; size=nodes), the smallest agent that cooperates with FairBot and CooperateBot, defects against itself and is unexploitable has size 12; W=[]([][]F|(p&(q|~[]q))) is one, unexploitable by every opponent; none of size <=11.`

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K6-c046_combo12.py`: census counts to size 12; S=0,FBc=1,CBc=1 counts per size 4..12 = 2,2,4,8,19,46,120,357,900; none \<=11 and exactly 3 of size 12 unexploited by all 2815 size\<=9 classes; W's self/FB/CB/DB outcomes and zero exploiters by an independent height-table solver; GLS certificates for W vs W, FB, CB with flipped-candidate controls — pass (`results/K6-1.json`)
- reasoning: W at the tail implies p at every height \>=2 (box over lower heights), so any opponent cooperates at the tail whenever W does: W is unexploitable by every modal agent, not only census agents. The 3 size-12 agents all have such a gate.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R3.md`)

### Provenance

- run: 20261017-1126
- claim: K6
- author: r1 (claude)
- round: 3
- run-folder commit: 662166ecff0651902cc5fcb04bf747c62d795af2
- check results: K6-1.json

## K9

`For every n>=2, the agent W_n=[]([]^n F|(p&(q|~[]q))) of size n+10 is unexploitable by every modal opponent, mutually cooperates with FairBot and CooperateBot, and defects against itself (both copies defect above height n+1); W_0, W_1 fail with FairBot. Lean-proved.`

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K9-c046_wn_lean.py`: embedded Lean 4 theorems w\_gate, w\_unexploitable, w\_db, w\_cb, w\_self, w\_self\_db, w\_fb compile with no sorryAx; three false variants rejected; height tables n\<=12 and 3000 random opponent traces agree; size(W\_n)=n+10 — pass (`results/K9-1.json`)
- reasoning: Closed GL fixed points are letter-free and so decided by height on finite linear frames (Boolos, Logic of Provability ch. 7); w\_gate quantifies over arbitrary opponent traces, hence over all modal opponents.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R5.md`)

### Provenance

- run: 20261017-1126
- claim: K9
- author: r1 (claude)
- round: 5
- run-folder commit: 662166ecff0651902cc5fcb04bf747c62d795af2
- check results: K9-1.json

## K11

`For all n>=0, k>=1, j,m>=0 (height semantics of closed GL fixed points): W_n and F_k cooperate at every height iff k<n; W_n and P_j iff 2<=n<j; W_n and W_m both defect from height n+m+3. Hence all W_n (n>=2) are distinct. Lean-proved.`

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K11-c046_wpairs_lean.py`: embedded Lean 4 theorems w\_fk, pj\_db, w\_pj, w\_wm compile with no sorryAx; four false variants rejected with proof errors; height tables n\<=12, k,j,m\<=14 (heights 0..79) agree with all theorems and K10's n=2..5 predicates — pass (`results/K11-1.json`)
- reasoning: Closed GL fixed points are letter-free and decided by height on finite linear frames (Boolos, Logic of Provability ch. 7). F\_n coops with W\_m iff m\>n, so F\_n separates W\_n from W\_{n+1}.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R1.md`)

### Provenance

- run: 20261017-1126
- claim: K11
- author: r1 (claude)
- round: 6
- run-folder commit: 662166ecff0651902cc5fcb04bf747c62d795af2
- check results: K11-1.json

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:solovay1976provability --> Solovay, Robert M.. 1976. Provability Interpretations of Modal Logic. Israel Journal of Mathematics
3. <!-- cite:boolos1993logic --> Boolos, George. 1993. The Logic of Provability. Cambridge University Press

<!-- autoresearch:revisions -->
## Revisions

- 2026-10-18 — Escaped claim statements, compiled PDF, references, per-finding paper, website layout
- 2026-10-21 — Production note corrected (K6 is checked by script); summary wording and definitions fixed
