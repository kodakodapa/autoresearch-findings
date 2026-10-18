## Setting

Two programs play a one-shot prisoner's dilemma, and each can read the other's source code.
Following Barasz et al. (2014), a *modal agent* decides by asking what can be proved about the
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
to provability in arithmetic is Solovay's theorem, cited, not formalised). The minimality of size
12 is an exhaustive computation over all agents up to size 12 in the stated language.
