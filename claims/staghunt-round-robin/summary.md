## Setting

In the Stag Hunt both players do best by hunting stag together; hunting stag alone pays nothing,
and hare is a safe middle option. We write the payoffs as stag/stag $a$, stag against hare $s$,
hare against stag $t$, hare/hare $d$, with $a > t > d > s$. The players are modal agents in the
sense of Barasz et al. [@barasz2014robust]: programs that decide by what can be proved about the
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
[@solovay1976provability], cited, not formalised (see also [@boolos1993logic]). Scores, regions
and breakpoints are exact rational computations over the stated census.

## Discussion

Round-robin results depend on the opponent population: here all small formulas with equal
weight, which over-represents some behaviours. The scores are aggregate quantities, not
equilibrium thresholds; they are not comparable to the learning-dynamics threshold of Todorov et
al. for parametric (non-modal) agents [@todorov2026parametric]. Open: whether the scores of $A_k$ and $R_k$ keep their
order in larger censuses, and which agent wins in the limit.
