---
layout: post
title: "Round robins of modal agents in the Stag Hunt"
date: 2026-10-21
scholar: {"citation_title": "Round robins of modal agents in the Stag Hunt", "citation_author": "Kodakodapa", "citation_publication_date": "2026/10/21", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/staghunt-round-robin.html", "citation_keywords": "C046", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/staghunt-round-robin/paper.pdf"}
---

## Summary

<!-- owner-summary -->
## Setting

In the Stag Hunt both players do best by hunting stag together; hunting stag alone pays nothing,
and hare is a safe middle option. We write the payoffs as stag/stag $a$, stag against hare $s$,
hare against stag $t$, hare/hare $d$, with $a > t > d > s$. The players are modal agents in the
sense of Barasz et al. [1]: programs that decide by what can be proved about the
opponent, with $p$ = "the opponent hunts stag against me" and $q$ = "the opponent hunts stag
against HareBot". FairBot $\Box p$ hunts stag exactly when it can prove the opponent does. We take
all 7,561 behaviourally distinct guarded agents of size at most 10 and let every agent play every
agent, itself included, with equal weight (a round robin).

## Result

- **FairBot never wins.** Normalising $a = 1$, $s = 0$, the triangle of strict Stag Hunts
  $0 < d < t < 1$ splits into exactly six regions, each won by a single agent, and FairBot wins
  none of them. The agent $A_3 = \Box(p \vee \Box^3\neg(p \vee q))$ wins on 44.6% of the area,
  including every game with payoffs $(4, 0, t, 2)$ for $2 < t < 4$ and the game $(3, 0, 2, 1)$.
  At $(4, 0, 3, 2)$ it scores 23,411 against FairBot's 21,719.
- **Why it beats FairBot.** $A_3$ reaches stag/stag with 4,444 of the 4,459 agents that hunt stag
  against StagBot and with none of the others; it gains on the first group and loses on the
  second, for a net gain of 1,692 points over FairBot at $(4, 0, 3, 2)$.
- **Families behind the winners.** For every $k$, $A_k = \Box(p \vee \Box^k\neg(p \vee q))$ hunts
  stag against HareBot (and is left alone there), coordinates with StagBot, with every $A_m$ and
  with every $F_j = \Box(\Box^j\bot \vee p)$ (FairBot over a stronger system); the lenient FairBots $R_k = \Box(p \vee \Box^k p)$ are safe and
  coordinate with $\neg\Box^j\bot$ exactly when $j \le k$.
- **The winner depends on the size bound.** In the same census the score of $R_k$ rises strictly
  with $k$ up to $k = 8$ and that of $A_k$ up to $k = 5$, so longer members of both families score
  higher than the census winners. The specific winners above are therefore artefacts of the size
  bound; what holds across the families is that lenient agents beat FairBot in this round robin.

## Why it matters

Round robins are a natural way to compare programs that read each other's code, and FairBot is
often taken as the reference cooperative agent. In the Stag Hunt, where cooperating with a
defector costs less than in the prisoner's dilemma, agents that are more willing to hunt stag do
better than FairBot against a broad population, and exact payoff breakpoints show where each
agent takes over.

## Proved vs checked

The laws for $A_k$ and $R_k$ are proved for all indices in Lean 4, in the height semantics of
closed GL fixed points; the link to provability in arithmetic is Solovay's theorem
[2], cited, not formalised (see also [3]). Scores, regions
and breakpoints are exact rational computations over the stated census.
<!-- /owner-summary -->

We believe this result is new. Our prior-art search (2026-10-21) covered:

- Barasz, LaVictoire et al., arXiv 1401.5577.
- LessWrong / Alignment Forum wiki "Modal combat" and "Is there only one FairBot?" (2026).
- Mennen, "Modal combat for games other than the prisoner's dilemma" (2017).
- Todorov, ten Napel & Müller, "Parametric Open Source Games", arXiv 2606.27068.
- Tennenholtz (2004), program equilibrium (background).
- Web searches for modal agents in the Stag Hunt and for tournaments of modal agents (2026-10-21); none means not found in this search.

We found no earlier statement of it, but we can't be certain. If you know of prior work, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was partly checked by scripts that run Lean proofs (claims K8, K3) and partly checked by script (claims K15, K6, K14, K5, K7, K4, K17, K18); the proof and check files are included so anyone can re-run them.

**K15.** Normalising $a=1,s=0$, the strict Stag Hunt triangle $0<d<t<1$ splits into exactly 6 census (size $\le10$) round-robin winner regions, each one agent; $A_3$ wins on 44.6% of the area and $R_6=\Box(p\lor\Box^6p)$ near $t,d\to1$; FairBot nowhere.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K6.** In the 7,561-class guarded-language census of size $\le10$, $A_3=\Box(p\lor\Box^3\neg(p\lor q))$ uniquely maximizes round-robin score $21950+487t$ for every $2<t<4$, with payoffs $(SS,SH,HS,HH)=(4,0,t,2)$.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K14.** At $(SS,SH,HS,HH)=(3,0,2,1)$, $A_3=\Box(p\lor\Box^3\neg(p\lor q))$ uniquely maximizes the equally weighted round robin over the 7561 guarded size-$\le10$ census classes, scoring 16393 versus FairBot's 14158.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K5.** For $(SS,SH,HS,HH)=(4,0,3,h)$ and $0<h<4$, the size-$\le10$ modal census has six winner intervals, separated by $116/1423$, $15/22$, $2537/1001$, $4079/1071$, and $463/116$.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K7.** In L up to size 10 with Stag Hunt $(4,0,3,2)$, $A_3=\Box(p\lor\Box^3\neg(p\lor q))$ ends stag/stag with exactly 4444 of the 4459 opponents that hunt stag vs StagBot and with none of the other 3102; vs FairBot it gains $+3848$ on the first group and loses $2156$ on the second.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K4.** At Stag Hunt payoffs $(4,0,3,2)$ in the size-$\le10$ census, $A_3$ gains 1,692 points over FairBot: 1,643 opponents change $HH\to SS$ and 562 change $HS\to SS$, offset by other outcome changes.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K8.** For all $k,j,m\ge0$, $A_k$ plays stag/hare vs HareBot and stag/stag vs StagBot, $A_m$, and $F_j=\Box(\Box^j\bot\lor p)$. Against $PB_j=\Box p\land\Box(\Box^{j+1}\bot\lor\neg q)$, it plays stag/hare for $k=0$ and hare/hare for $k\ge1$.

- Status: derived · author check only
- Machine-checked: 2 of 2 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K3.** For all $k\ge0$, $R_k=\Box(p\lor\Box^kp)$ ($R_0$ = FairBot) never ends hunting stag against an opponent that ends hunting hare, and in the Stag Hunt ends stag/stag with $E_j=\neg\Box^j\bot$ iff $j\le k$ (else hare vs stag) and with $N_n=\Box(\Box^n\bot\lor\neg q)$ iff $n>k$ (else hare/hare).

- Status: derived · author check only
- Machine-checked: 2 of 2 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K17.** Against the 7561 size-$\\le10$ census agents, $R_k=\\Box(p\\lor\\Box^kp)$ has round-robin score strictly increasing in $k$ for $0\\le k\\le8$ and constant for $8\\le k\\le12$, for all payoffs with $a>t,a>d$; so $R_6$'s K15 region reflects the size bound (size $k+4$).

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K18.** Against the 7561 size-$\le10$ census agents, $A_k=\Box(p\lor\Box^k\neg(p\lor q))$ (size $k+7$) has 543 SH and 2087 HH for $1\le k\le10$; its score rises strictly for $k\le5$ (by $\Delta SS(a-t)$) and is constant after, so $A_5-A_3=15(a-t)$ whenever $a>t$.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

## Discussion

Round-robin results depend on the opponent population: here all small formulas with equal
weight, which over-represents some behaviours. The scores are aggregate quantities, not
equilibrium thresholds; they are not comparable to the learning-dynamics threshold of Todorov et
al. for parametric (non-modal) agents [4]. Open: whether the scores of $A_k$ and $R_k$ keep their
order in larger censuses, and which agent wins in the limit.

## How to verify

Run each script in `claims/staghunt-round-robin/checks/` with `python -I <script>`; it passes if it
exits with status 0. The results recorded in the original run are in
`claims/staghunt-round-robin/results/`; the full claim text is in `claims/staghunt-round-robin/claim.md`.

## Provenance

- run: 20261021-0517
- claims: K15, K6, K14, K5, K7, K4, K8, K3, K17, K18
- run-folder commit: 580565ffd3b3f1a8ca3ffa0407c949c8d724865c
- K15 author: r1 (claude)
- K6 author: r2 (codex)
- K14 author: r2 (codex)
- K5 author: r2 (codex)
- K7 author: r1 (claude)
- K4 author: r2 (codex)
- K8 author: r2 (codex)
- K3 author: r1 (claude)
- K17 author: r1 (claude)
- K18 author: r1 (claude)

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:solovay1976provability --> Solovay, Robert M.. 1976. Provability Interpretations of Modal Logic. Israel Journal of Mathematics
3. <!-- cite:boolos1993logic --> Boolos, George. 1993. The Logic of Provability. Cambridge University Press
4. <!-- cite:todorov2026parametric --> Todorov, Aleksandar and ten Napel, Jesse and M\"uller, Alexander. 2026. Parametric Open Source Games. [Link](https://arxiv.org/abs/2606.27068)

<!-- autoresearch:revisions -->
## Revisions

- 2026-10-21 — Production note: Lean proofs run inside check scripts are now described as such, separately from harness-built proofs
