## Setting

Two programs play a one-shot prisoner's dilemma, and each can read the other's source code.
Following Barasz et al. [@barasz2014robust], a *modal agent* decides by asking what can be proved
about the opponent, written with the provability box $\Box$ of the logic GL: $p$ means "the
opponent cooperates with me" and $q$ "the opponent cooperates with DefectBot". FairBot is
$\Box p$: it cooperates exactly when it can prove that the opponent cooperates with it. An agent
is *unexploitable* if no modal opponent ever ends up defecting while the agent cooperates, and
*self-cooperating* if two copies cooperate. We take guarded formulas (every atom under a box)
built from $p$, $q$, $\bot$, $\neg$, $\wedge$, $\vee$, $\Box$, measure size as the number of
nodes, and call two agents behaviourally equal when they make the same moves against every
opponent. Agents using only $p$ are the rank-0 agents of Barasz et al.

A LessWrong post [@onlyonefairbot2026] asked whether every rank-0 agent that is unexploitable and
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
arithmetic is Solovay's theorem [@solovay1976provability], cited, not formalised (see also
[@boolos1993logic]). The counts are exhaustive computations up to the stated sizes, with every
separating opponent recorded and re-solved by the checks. The minimality statement for the size-9
agent is an exhaustive search over smaller rank-0 agents.

## Discussion

The counts depend on the agent language and the size measure; they say how common
non-FairBot unexploitable self-cooperators are among small formulas, not in any absolute sense.
"Unexploitable" is about what actually happens in play (truth in the standard model, as in Barasz
et al.), not about what Peano arithmetic can prove about the agent; the LessWrong discussion
points out that the two differ. Open questions: how the counts grow with size, and whether the
non-FairBot classes fall into a small number of families.
