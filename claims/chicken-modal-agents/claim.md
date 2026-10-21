# Modal agents in the game of Chicken

<!-- owner-summary -->
## Setting

Two programs play a one-shot game and each can read the other's source code. Following Barasz et
al. [1], a *modal agent* decides by asking what can be proved about the opponent,
written with the provability box $\Box$ of the logic GL. Earlier findings on this site study the
prisoner's dilemma; here the game is mostly **Chicken**: both swerve 3/3, swerve against straight
1/4, both go straight (crash) 0/0. $p$ means "the opponent swerves against me", $q$ "the opponent
swerves against NerveBot", the bot that never swerves. SwerveBot always swerves; FairBot is
$\Box p$, graded FairBots are $\Box^j p$. The census covers every agent built from $p$, $q$, $\bot$,
$\neg$, $\wedge$, $\vee$ and $\Box$ (atoms under a box) up to size 10, 7561 behaviourally distinct
agents. Mennen [2] set up modal agents for general games; this finding works out
Chicken concretely.

## Result

- **Equilibria never crash.** Among the census agents there are 517 symmetric program equilibria,
  all with mutual swerving, and no equilibrium at all involves a crash. Every asymmetric
  equilibrium pairs one of the 701 agents that never swerve against anyone in the census with an
  agent that swerves against it.
- **The smallest sensible Chicken agents** (swerve against themselves and against NerveBot, go
  straight against SwerveBot) have size 3: exactly $\neg\Box p$ and $\neg\Box q$. The first never
  crashes against any census agent; the second crashes against 755 of them.
- **Safe and fair.** Exactly 4 census agents never crash against a census agent, go straight against
  SwerveBot and swerve together with FairBot, and all 4 never crash against any modal opponent at
  all. The smallest, of size 9, is the $k=2$ member of a family
  $Q_k = \Box^k\bot \vee \neg\Box(p \wedge q)$ with exact laws for every $k$: $Q_k$ never crashes,
  beats SwerveBot, swerves against itself, swerves together with $\Box^j p$ exactly when $j < k$
  and with $\Box(\Box^j\bot \vee p)$ exactly when $j + 2 \le k$, and goes straight against $Q_m$
  for $m > k$.
- **A limit for every two-action game.** If an agent of modal depth $d$ exploits the
  always-cooperating bot, then graded FairBots $\Box^j p$ with $j \ge d$ end up playing action 2
  against it, and the two never settle on mutual action 1. The $Q_k$ family shows the bound is
  tight.
- **Tournaments and evolution.** In a round robin the top Chicken agent is
  $\neg\Box p \wedge \Box(\neg p \vee \Box p)$, which crashes against itself. Under replicator
  dynamics the surviving agents are the same 1116 classes in the prisoner's dilemma, Chicken and
  Stag Hunt, and they form a maximal set of mutual cooperators containing FairBot.

## Why it matters

Modal agents have been studied almost only in the prisoner's dilemma. Chicken punishes mutual
defection (a crash) instead of rewarding it, so the question changes from "can I avoid being
exploited?" to "can I avoid crashing without being a pushover?". The census answers it
concretely: equilibria never crash, safe agents exist and form a family with exact thresholds, and
a general depth bound limits how such agents can coexist with graded FairBots.

## Proved vs checked

The laws for $Q_k$ and the depth bound are proved for all indices in Lean 4, in the height
semantics of closed GL fixed points (see [3]; the link to provability is Solovay's
theorem [4]). The census results (equilibria, smallest agents, the four safe
agents, round robin, replicator dynamics) hold for all agents up to size 10, computed exactly and
re-checked on samples; the replicator results are numerical (2000 steps from the uniform start).
<!-- /owner-summary -->

We believe this result is new. Our prior-art search (2026-10-20) covered:

- Mennen, "Modal combat for games other than the prisoner's dilemma" (LessWrong / Alignment Forum, 2017): framework for modal agents in games with any number of players and actions (player types, ranks, opponent tests naming a target player, an agent to test against and an action); existence and Pareto theorems; no agent families with index laws, no enumeration.
- Gram_Stone, "Modal Chicken" (LessWrong, 2015) and its comments (AlexMennen, SilentCal): SwerveBot, NerveBot, CarefulBot, AstuteBot; informal claims about graded CarefulBots and BoldBots.
- Hobson, "Yet More Modal Combat" (LessWrong / Alignment Forum, 2021): a two-system PD bot; generalisation to Chicken and more players left open.
- Critch, Dennis & Russell, "Cooperative and uncooperative institution designs: surprises and problems in open-source game theory" (arXiv 2208.07006): two-player bounded proof-search agents.
- Todorov, ten Napel & Müller, "Parametric Open Source Games" (arXiv 2606.27068): non-modal parametric agents; Chicken and Stag Hunt thresholds.
- Barasz et al. 2014 (arXiv 1401.5577); LaVictoire et al. 2014; Critch, parametric bounded Löb (arXiv 1602.04184); Oesterheld 2022 (arXiv 2211.05057); LessWrong / Alignment Forum wiki "Modal combat"; web searches for modal or provability-based agents in Chicken, Stag Hunt and multiplayer program equilibrium.

We found no earlier statement of it, but we can't be certain. If you know of prior work, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was partly checked by scripts that run Lean proofs (claims K7, K8, K10) and partly checked by script (claims K1, K2, K3, K4); the proof and check files are included so anyone can re-run them.

## K1

`In L up to size 10 (7561 classes; Chicken 3/3, 1/4, 0/0), census program equilibria: 517 symmetric, all mutual swerve; none with a crash; every swerve/straight one pairs one of the 701 agents that never swerve against any census agent with an agent swerving against it.`

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K1-c046_games10.py`: (1) class counts; (2) independent re-solve + 13 GLS certificates; (3) Chicken equilibrium counts 517 symmetric all CC, 262741 CC, 2138719 CD/DC, and CD-equilibrium iff straight player never swerves (701 classes) and the other swerves vs it — pass (`results/K1-1.json`)
- reasoning: SwerveBot guarantees at least 1, so a crash is never a best response; a best-response payoff of 1 against b requires that b never swerves.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R3.md`)

### Provenance

- run: 20261019-1400
- claim: K1
- author: r1 (claude)
- round: 1
- run-folder commit: 24c2a64bf8b8cb8be184b4d449ce11068d8270ea
- check results: K1-1.json

## K2

In L up to size 10, round robin incl. self: Chicken (3,1,4,0) max 17666 only by $\neg\Box p\wedge\Box(\neg p\vee\Box p)$, which crashes vs itself (SwerveBot 16479, FairBot 14303); Stag Hunt (4,0,3,2) max 23411 only by $\Box(p\vee\Box^3\neg(p\vee q))$, which hunts stag vs HareBot (FairBot 21719).

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K1-c046_games10.py`: (5) unique RR maxima 17666 (Chicken) and 23411 (Stag Hunt) with stated agents of size 10 and stated scores of CB, DB, FB; leader cells vs self/DB/CB/FB GLS-certified in (2) — pass (`results/K1-1.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R3.md`)

### Provenance

- run: 20261019-1400
- claim: K2
- author: r1 (claude)
- round: 1
- run-folder commit: 24c2a64bf8b8cb8be184b4d449ce11068d8270ea
- check results: K1-1.json

## K3

In L up to size 10, discrete replicator dynamics from uniform start (2000 steps) leave exactly the same 1116 observational classes (weight $>10^{-6}$) in PD, Chicken and Stag Hunt; they form a maximal set of mutual cooperators containing FairBot.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K3-c046_replicator10.py`: 3402 observational classes; in each game survivors \>1e-6 are the same 1116 (2158 chain classes), others \<1e-12, mean payoff R within 1e-9; survivors pairwise CC (exact) and maximal (exact); FB in S, DB not — pass (`results/K3-1.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R3.md`)

### Provenance

- run: 20261019-1400
- claim: K3
- author: r1 (claude)
- round: 1
- run-folder commit: 24c2a64bf8b8cb8be184b4d449ce11068d8270ea
- check results: K3-1.json

## K4

In L up to size 10, the smallest agents that swerve vs themselves and vs NerveBot but go straight vs SwerveBot have size 3: exactly $\neg\Box p$ and $\neg\Box q$; $\neg\Box p$ crashes against no census agent, $\neg\Box q$ against 755.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K1-c046_games10.py`: (6) property set minimum size 3 = {~\[\]p, ~\[\]q}; ~\[\]p no crash vs any of 7561; ~\[\]q 755 crashes; no census agent anti-coordinates with all others; ~\[\]p cells vs self/F/~F/\[\]p GLS-certified in (2) — pass (`results/K1-1.json`)
- reasoning: Never-crash of ~\[\]p against any opponent: going straight means \[\]p holds in the standard model, so p holds by soundness and the opponent swerves.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R3.md`)

### Provenance

- run: 20261019-1400
- claim: K4
- author: r1 (claude)
- round: 1
- run-folder commit: 24c2a64bf8b8cb8be184b4d449ce11068d8270ea
- check results: K1-1.json

## K7

For all $k\ge0$, $Q_k=\Box^k\bot\vee\neg\Box(p\wedge q)$ never crashes vs any opponent, beats SwerveBot, self-swerves; it mutually swerves with $\Box^jp$ ($j\ge1$) iff $j<k$ and with $\Box(\Box^j\bot\vee p)$ iff $j+2\le k$, else is exploited; vs $Q_m$, $m>k$, $Q_k$ goes straight. Lean.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K7-c046_chicken_q.py`: (5) Lean 4 core theorems q\_safe, q\_sb, q\_nb, q\_fj, q\_gj, q\_db, q\_qm\_lt, q\_qq, q\_bn for all indices and any solving traces, no sorryAx, negative control (j+1\<=k for G\_j) rejected; (4) height tables for k,j,m,n\<=8 agree; (3) GLS certificates for Q\_2 cells — pass (`results/K7-1.json`)
- reasoning: Q\_k is straight at h\>=k only if the opponent swerved (and swerved vs NB) at all g\<h; vs \[\]^j p, Q\_k's first straight height k is seen by F\_j iff k+j\<=h, and F\_j's NB trace fails at j, which frees Q\_k iff j\<k.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R1.md`)

### Provenance

- run: 20261019-1400
- claim: K7
- author: r1 (claude)
- round: 2
- run-folder commit: 24c2a64bf8b8cb8be184b4d449ce11068d8270ea
- check results: K7-1.json

## K8

In L up to size 10 (Chicken), exactly 4 agents crash against no census agent, go straight vs SwerveBot and mutually swerve with FairBot; all 4 never crash vs any modal opponent; the unique smallest (size 9) is $\Box^2\bot\vee\neg\Box(p\wedge q)$.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K7-c046_chicken_q.py`: (1) 7561 classes, 808 census-safe, 695 SU, SU subset of safe; (2) safe & straight vs CB & CC with FB: exactly 4, sizes 9,10,10,10, all SU, unique of size\<=9 is (\[\]\[\]F\|~\[\](p&q)); Q\_0, Q\_1 fail only the FB clause; (3) 9 GLS certificates — pass (`results/K7-1.json`)
- reasoning: If Q\_2 goes straight at height h\>=2, box(p&q) held there, so the opponent swerved at all g\<h; hence no tail where both go straight.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R3.md`)

### Provenance

- run: 20261019-1400
- claim: K8
- author: r1 (claude)
- round: 2
- run-folder commit: 24c2a64bf8b8cb8be184b4d449ce11068d8270ea
- check results: K7-1.json

## K10

For every guarded agent $A$ of modal depth $d$ playing action 2 vs the constant action-1 bot: $\Box^jp$ ($j\ge d$) plays 2 vs $A$ from height $d+j$, and $\Box(\Box^j\bot\vee p)$ ($j\ge d-1$) from height $j+2$; never mutual action 1 (any 2-action game; Lean). Both tight via $Q_k$.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K10-c046_depth_bound.py`: (1) Lean 4 core theorem depth\_bound over an inductive formula type (locality + stabilisation lemmas), no sorryAx, two weakened variants rejected; (2) size\<=10 census: 7561 classes, constant vs SwerveBot from height md, 3102 straight vs SwerveBot, 12407 (agent,j\>=md) pairs with F\_j straight from md+j, 92 tight classes, smallest \[\](\[\]F\|~q); (3) explicit height tables — pass (`results/K10-1.json`)
- reasoning: Guarded formulas are local; with constant inputs a depth-d formula is constant from height d. F\_j swerves unconditionally below j\>=d, so A sees SwerveBot's inputs below d and goes straight at d; F\_j sees that from d+j on.
- check `checks/K10-c046_depth_bound_g.py`: (1) Lean 4 core: depth\_bound, straight\_at, depth\_bound\_G over inductive Fm, no sorryAx, four weakened variants rejected; (2) size\<=10 census: 3102 straight-vs-SB classes, 12407 F\_j and 12407 G\_j pairs straight from md+j resp. j+2, largest CC index vs G\_j = vs F\_j minus 1, 178 CC, 92 tight (same sets), smallest \[\](\[\]F\|~q); (3) explicit height tables — pass (`results/K10-2.json`)
- reasoning: straight\_at: inputs equal SwerveBot's below t\>=d, so A is straight at t by locality and stabilisation. G\_j plays 1 below j+1 vs A and vs NB; take t=j+1.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R3.md`)

### Provenance

- run: 20261019-1400
- claim: K10
- author: r1 (claude)
- round: 3
- run-folder commit: 24c2a64bf8b8cb8be184b4d449ce11068d8270ea
- check results: K10-1.json, K10-2.json

## Discussion

<!-- owner-discussion -->
The census stops at size 10, and round-robin winners in particular can change as larger agents
are added. The language has a single probe ($q$, how the opponent treats NerveBot); richer probes
would give a larger space. The replicator results describe this population, not modal agents in
general. A natural next step is Stag Hunt, where the round-robin leader found here is unusual, and
a search for threshold families beyond FairBot-like agents there.
<!-- /owner-discussion -->

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:mennen2017modal --> Mennen, Alex. 2017. Modal Combat for Games Other Than the Prisoner's Dilemma. [Link](https://www.lesswrong.com/posts/5bd75cc58225bf0670375375/modal-combat-for-games-other-than-the-prisoner-s-dilemma)
3. <!-- cite:boolos1993logic --> Boolos, George. 1993. The Logic of Provability. Cambridge University Press
4. <!-- cite:solovay1976provability --> Solovay, Robert M.. 1976. Provability Interpretations of Modal Logic. Israel Journal of Mathematics

<!-- autoresearch:revisions -->
## Revisions

- 2026-10-21 — Production note: Lean proofs run inside check scripts are now described as such, separately from harness-built proofs
