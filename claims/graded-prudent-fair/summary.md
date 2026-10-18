## Setting

Two programs play a one-shot prisoner's dilemma, and each can read the other's source code. A
*modal agent* [@barasz2014robust] decides by asking what Peano arithmetic (PA) can prove about
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
[@solovay1976provability] (see also [@boolos1993logic]), cited, not formalised, and the reading
in the standard model assumes PA is sound.
