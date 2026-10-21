## Setting

Two programs play a one-shot prisoner's dilemma, and each can read the other's source code.
Following Barasz et al. [@barasz2014robust], a *modal agent* decides by asking what can be proved
about the opponent, written with the provability box $\Box$ of the logic GL: $p$ means "the
opponent cooperates with me" and $q$ "the opponent cooperates with DefectBot". Graded FairBots
are $F_k = \Box^k p$ ($F_1$ is FairBot). They are all unexploitable and cooperate with themselves
and with each other, and a LessWrong discussion [@onlyonefairbot2026] lists them among the agents
that share these properties with FairBot without being FairBot. We take guarded formulas built
from $p$, $q$, $\bot$, $\neg$, $\wedge$, $\vee$, $\Box$ and measure size as the number of nodes. An
opponent *separates* two agents if it gets a different outcome against them.

## Result

- **Smallest separators.** Every opponent that separates $F_k$ from $F_{k+1}$ has size at least
  $k+5$, and the only one of size $k+5$ is $S_k = \Box(\neg q \vee \Box^k\bot)$ (up to the order
  of the disjuncts): it cooperates with $F_k$ and mutually defects with $F_{k+1}$. Without $q$ the
  minimum is $k+6$, attained by $T_k = \neg\Box(\neg p \vee \Box^k\bot)$.
- **Depth.** Every opponent of modal depth at most $k$ gets the same outcome against $F_k$ and
  $F_{k+1}$, so a separator needs depth at least $k+1$; $S_k$ and $T_k$ show this is tight.
- **Ingredients.** An opponent with no negation, or with no $\wedge$/$\vee$, gets the same outcome
  against every graded FairBot; without $q$ the same holds for every boxed opponent and every
  opponent with at most one negation and at most one binary connective.

## Why it matters

Graded FairBots look alike: each is unexploitable, cooperates with itself and with every other
graded FairBot. These results say exactly how complex a program must be to tell two neighbouring
ones apart, and that the cost grows linearly with the grade.

## Proved vs checked

All statements are proved for every $k$ in Lean 4, in the height semantics of closed GL fixed
points; the link to provability in arithmetic is Solovay's theorem [@solovay1976provability],
cited, not formalised (see also [@boolos1993logic]). The uniqueness of $T_k$ among $q$-free
separators of size $k+6$ is proved only for $k \le 22$, by exhaustive search; the lower bound
$k+6$ holds for all $k$.

## Discussion

The depth bound uses the standard back-and-forth (n-bisimulation) method of modal logic
[@blackburn2001modal]; the new part is its application to games between modal agents. The
results concern separating graded FairBots from each other; how large a separator must be for
other pairs of agents (for example the gate-family members of earlier findings) is open, as is a
numerical bound on separator size at fixed modal depth.
