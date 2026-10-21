---
layout: default
title: "Round robins of modal agents in the Stag Hunt"
scholar: {"citation_title": "Round robins of modal agents in the Stag Hunt", "citation_author": "Kodakodapa", "citation_publication_date": "2026/10/21", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/staghunt-round-robin.html", "citation_keywords": "C046", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/staghunt-round-robin/paper.pdf"}
---

# Round robins of modal agents in the Stag Hunt

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

## K15

Normalising $a=1,s=0$, the strict Stag Hunt triangle $0<d<t<1$ splits into exactly 6 census (size $\le10$) round-robin winner regions, each one agent; $A_3$ wins on 44.6% of the area and $R_6=\Box(p\lor\Box^6p)$ near $t,d\to1$; FairBot nowhere.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K15-c046_sh_triangle.py`: 7561 classes re-enumerated (own engine); K13/K14 values; 3309 score planes; exact Fraction clipping gives 6 winner polygons with total area exactly 1/2, one agent each, exact areas and A3 vertices; unique exact argmax at 7 interior points; 6 GLS self-certificates — pass (`results/K15-1.json`)
- reasoning: Round-robin argmax is invariant under positive affine payoff maps, so (a,s,t,d) reduces to (1,0,t,d); scores are affine in (t,d), so winner regions are convex polygons.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R13.md`)

### Provenance

- run: 20261021-0517
- claim: K15
- author: r1 (claude)
- round: 6
- run-folder commit: 580565ffd3b3f1a8ca3ffa0407c949c8d724865c
- check results: K15-1.json

## K6

In the 7,561-class guarded-language census of size $\le10$, $A_3=\Box(p\lor\Box^3\neg(p\lor q))$ uniquely maximizes round-robin score $21950+487t$ for every $2<t<4$, with payoffs $(SS,SH,HS,HH)=(4,0,t,2)$.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K6-stag_payoffs.py`: Pinned solver source; exact census counts; all ordered cells solved; GLS certificates for A3/self, A3/HareBot, A3/FairBot and FairBot/self; exact outcome counts, transitions, and upper envelopes for both payoff slices. — pass (`results/K6-1.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R13.md`)

### Provenance

- run: 20261021-0517
- claim: K6
- author: r2 (codex)
- round: 1
- run-folder commit: 580565ffd3b3f1a8ca3ffa0407c949c8d724865c
- check results: K6-1.json

## K14

At $(SS,SH,HS,HH)=(3,0,2,1)$, $A_3=\Box(p\lor\Box^3\neg(p\lor q))$ uniquely maximizes the equally weighted round robin over the 7561 guarded size-$\le10$ census classes, scoring 16393 versus FairBot's 14158.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K14-todorov_safety.py`: SHA256-pinned solver; all 7561-class cells re-solved; unique winner A3 at (3,0,2,1), score 16393 versus FairBot 14158; 7561 winner cells independently re-solved; 4 GLS certificates; 1693 census-safe classes, 517 self-stag. — pass (`results/K14-1.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R13.md`)

### Provenance

- run: 20261021-0517
- claim: K14
- author: r2 (codex)
- round: 5
- run-folder commit: 580565ffd3b3f1a8ca3ffa0407c949c8d724865c
- check results: K14-1.json

## K5

For $(SS,SH,HS,HH)=(4,0,3,h)$ and $0<h<4$, the size-$\le10$ modal census has six winner intervals, separated by $116/1423$, $15/22$, $2537/1001$, $4079/1071$, and $463/116$.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K6-stag_payoffs.py`: Pinned solver source; exact census counts; all ordered cells solved; GLS certificates for A3/self, A3/HareBot, A3/FairBot and FairBot/self; exact outcome counts, transitions, and upper envelopes for both payoff slices. — pass (`results/K6-1.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R13.md`)

### Provenance

- run: 20261021-0517
- claim: K5
- author: r2 (codex)
- round: 1
- run-folder commit: 580565ffd3b3f1a8ca3ffa0407c949c8d724865c
- check results: K6-1.json

## K7

In L up to size 10 with Stag Hunt $(4,0,3,2)$, $A_3=\Box(p\lor\Box^3\neg(p\lor q))$ ends stag/stag with exactly 4444 of the 4459 opponents that hunt stag vs StagBot and with none of the other 3102; vs FairBot it gains $+3848$ on the first group and loses $2156$ on the second.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K7-c046_xreview_k4k6.py`: 7561 classes; A3/FB counts and K4 transitions; K5/K6 envelopes; StagBot split 4459/3102, A3 SS = 4444 all in first group, 15 HS exceptions of size \>=9 with \[\]^4, gains +3848/-2156; 60488 cells re-solved independently; 4 GLS certificates — pass (`results/K7-1.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R13.md`)

### Provenance

- run: 20261021-0517
- claim: K7
- author: r1 (claude)
- round: 2
- run-folder commit: 580565ffd3b3f1a8ca3ffa0407c949c8d724865c
- check results: K7-1.json

## K4

At Stag Hunt payoffs $(4,0,3,2)$ in the size-$\le10$ census, $A_3$ gains 1,692 points over FairBot: 1,643 opponents change $HH\to SS$ and 562 change $HS\to SS$, offset by other outcome changes.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K6-stag_payoffs.py`: Pinned solver source; exact census counts; all ordered cells solved; GLS certificates for A3/self, A3/HareBot, A3/FairBot and FairBot/self; exact outcome counts, transitions, and upper envelopes for both payoff slices. — pass (`results/K6-1.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R13.md`)

### Provenance

- run: 20261021-0517
- claim: K4
- author: r2 (codex)
- round: 1
- run-folder commit: 580565ffd3b3f1a8ca3ffa0407c949c8d724865c
- check results: K6-1.json

## K8

For all $k,j,m\ge0$, $A_k$ plays stag/hare vs HareBot and stag/stag vs StagBot, $A_m$, and $F_j=\Box(\Box^j\bot\lor p)$. Against $PB_j=\Box p\land\Box(\Box^{j+1}\bot\lor\neg q)$, it plays stag/hare for $k=0$ and hare/hare for $k\ge1$.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K8-ak_laws.py`: Seven core Lean theorems for all indices and arbitrary solution traces; no sorryAx; incorrect strict bound rejected; 261 independent height cells; eight GLS fixed-point certificates; pinned prior solver source. — pass (`results/K8-2.json`)
- check `checks/K8-ak_laws.py`: 11 core Lean theorem reports, no sorryAx; faithful PB guard equivalent to original P\_(j+1) when q=true; all-index A/PB outcomes; false mutation rejected; 342 height cells; 12 GLS certificates. — pass (`results/K8-2.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R12.md`)

### Provenance

- run: 20261021-0517
- claim: K8
- author: r2 (codex)
- round: 2
- run-folder commit: 580565ffd3b3f1a8ca3ffa0407c949c8d724865c
- check results: K8-2.json

## K3

For all $k\ge0$, $R_k=\Box(p\lor\Box^kp)$ ($R_0$ = FairBot) never ends hunting stag against an opponent that ends hunting hare, and in the Stag Hunt ends stag/stag with $E_j=\neg\Box^j\bot$ iff $j\le k$ (else hare vs stag) and with $N_n=\Box(\Box^n\bot\lor\neg q)$ iff $n>k$ (else hare/hare).

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K3-c046_lenient_laws.py`: Lean (17 theorems, no sorryAx): rk\_safe, rr\_pair, rk\_db, rk\_E (stag/stag iff j\<=k), rk\_N (stag/stag iff n\>k, else hare/hare), modal bridges; false variant rejected; height tables k\<=7, j,n\<=8; 14 GLS certificates — pass (`results/K2-2.json`)
- reasoning: Height semantics on the GL chain (box holds at h iff its argument holds at all g\<h). Game tails equal standard-model actions; Lean proves the laws for every index, given any traces solving the height equations.
- check `checks/K3-c046_relabel_gk.py`: Lean re-proves rk\_E, rk\_N, rk\_Z, rk\_db for all indices alongside gk\_E, gk\_N (same E\_j/N\_n laws for G\_k); no sorryAx; false bound rejected; 588 height cells; 10 GLS certificates — pass (`results/K3-2.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R7.md`)

### Provenance

- run: 20261021-0517
- claim: K3
- author: r1 (claude)
- round: 1
- run-folder commit: 580565ffd3b3f1a8ca3ffa0407c949c8d724865c
- check results: K2-2.json, K3-2.json

## K17

Against the 7561 size-$\\le10$ census agents, $R_k=\\Box(p\\lor\\Box^kp)$ has round-robin score strictly increasing in $k$ for $0\\le k\\le8$ and constant for $8\\le k\\le12$, for all payoffs with $a>t,a>d$; so $R_6$'s K15 region reflects the size bound (size $k+4$).

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K17-c046_rk_artifact.py`: 7561 classes re-enumerated; R\_k counts k=0..12 (machine solver = height solver for k\<=6), SH=0; SS up, HS/HH non-increasing, strict until k=8 then constant; 200 exact random payoffs: score strictly increasing to k=8, R\_8-R\_6=4(a-t); R\_6-\>R\_7 differs on ~\[\]^7F,~\[\]^7~p,~\[\]^7~q, R\_7-\>R\_8 on ~\[\]^8F; 4 GLS certificates — pass (`results/K17-1.json`)
- reasoning: SH=0 for all k and counts sum to 7561, so the score difference is -dHS(a-t)-dHH(a-d), positive whenever dHS,dHH\<=0 with one strict and a\>t,a\>d.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R9.md`)

### Provenance

- run: 20261021-0517
- claim: K17
- author: r1 (claude)
- round: 8
- run-folder commit: 580565ffd3b3f1a8ca3ffa0407c949c8d724865c
- check results: K17-1.json

## K18

Against the 7561 size-$\le10$ census agents, $A_k=\Box(p\lor\Box^k\neg(p\lor q))$ (size $k+7$) has 543 SH and 2087 HH for $1\le k\le10$; its score rises strictly for $k\le5$ (by $\Delta SS(a-t)$) and is constant after, so $A_5-A_3=15(a-t)$ whenever $a>t$.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K18-c046_ak_artifact.py`: 7561 classes re-enumerated; A\_k counts k=1..10 (machine = height solver for k\<=3, A\_4.. not census members); SH 543, HH 2087 fixed; only HS-\>SS for k\>=2; 200 exact random payoffs: strict increase to k=5, constant to k=10, A\_5-A\_3=15(a-t); A\_5 SS set = 4459 stag-vs-StagBot agents; 12 then 3 listed flips; 5 GLS certificates — pass (`results/K18-1.json`)
- reasoning: SH and HH counts are constant and counts sum to 7561, so the score difference is dSS\*a + dHS\*t = dSS(a-t) \> 0 when dSS\>0 and a\>t.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R10.md`)

### Provenance

- run: 20261021-0517
- claim: K18
- author: r1 (claude)
- round: 9
- run-folder commit: 580565ffd3b3f1a8ca3ffa0407c949c8d724865c
- check results: K18-1.json

## Discussion

<!-- owner-discussion -->
Round-robin results depend on the opponent population: here all small formulas with equal
weight, which over-represents some behaviours. The scores are aggregate quantities, not
equilibrium thresholds; they are not comparable to the learning-dynamics threshold of Todorov et
al. for parametric (non-modal) agents [4]. Open: whether the scores of $A_k$ and $R_k$ keep their
order in larger censuses, and which agent wins in the limit.
<!-- /owner-discussion -->

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:solovay1976provability --> Solovay, Robert M.. 1976. Provability Interpretations of Modal Logic. Israel Journal of Mathematics
3. <!-- cite:boolos1993logic --> Boolos, George. 1993. The Logic of Provability. Cambridge University Press
4. <!-- cite:todorov2026parametric --> Todorov, Aleksandar and ten Napel, Jesse and M\"uller, Alexander. 2026. Parametric Open Source Games. [Link](https://arxiv.org/abs/2606.27068)

<!-- autoresearch:revisions -->
## Revisions

- 2026-10-21 — Production note: Lean proofs run inside check scripts are now described as such, separately from harness-built proofs
