## Setting

Two programs play a one-shot game and each can read the other's source code. Following Barasz et
al. [@barasz2014robust], a *modal agent* decides by asking what can be proved about the opponent,
written with the provability box $\Box$ of the logic GL. Earlier findings on this site study the
prisoner's dilemma; here the game is mostly **Chicken**: both swerve 3/3, swerve against straight
1/4, both go straight (crash) 0/0. $p$ means "the opponent swerves against me", $q$ "the opponent
swerves against NerveBot", the bot that never swerves. SwerveBot always swerves; FairBot is
$\Box p$, graded FairBots are $\Box^j p$. The census covers every agent built from $p$, $q$, $\bot$,
$\neg$, $\wedge$, $\vee$ and $\Box$ (atoms under a box) up to size 10, 7561 behaviourally distinct
agents. Mennen [@mennen2017modal] set up modal agents for general games; this finding works out
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
semantics of closed GL fixed points (see [@boolos1993logic]; the link to provability is Solovay's
theorem [@solovay1976provability]). The census results (equilibria, smallest agents, the four safe
agents, round robin, replicator dynamics) hold for all agents up to size 10, computed exactly and
re-checked on samples; the replicator results are numerical (2000 steps from the uniform start).

## Discussion

The census stops at size 10, and round-robin winners in particular can change as larger agents
are added. The language has a single probe ($q$, how the opponent treats NerveBot); richer probes
would give a larger space. The replicator results describe this population, not modal agents in
general. A natural next step is Stag Hunt, where the round-robin leader found here is unusual, and
a search for threshold families beyond FairBot-like agents there.
