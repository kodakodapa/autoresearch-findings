## Setting

In the Stag Hunt two players each choose stag or hare: both hunting stag pays most, hunting stag
alone pays least, and hare is a safe middle option. Here the players are programs that read each
other's source code. Following Barasz et al. [@barasz2014robust], a *modal agent* decides by
asking what can be proved about the opponent, written with the provability box $\Box$ of the
logic GL: $p$ means "the opponent hunts stag against me" and $q$ "the opponent hunts stag against
HareBot", the agent that always hunts hare. Call an agent *safe* if no modal opponent ever ends up
hunting hare while the agent hunts stag (the Stag Hunt reading of unexploitability). Two simple
probes test willingness to coordinate: $E_1 = \neg\Box\bot$, which hunts stag unconditionally in
practice, and $N_1 = \Box(\Box\bot \vee \neg q)$, which hunts stag against agents that do not
hunt stag against HareBot. We take guarded formulas built from $p$, $q$, $\bot$, $\neg$,
$\wedge$, $\vee$, $\Box$ and measure size as the number of nodes.

## Result

- **No small safe coordinator.** Among the 56,503 agent classes of size at most 12, exactly 356
  reach stag/stag with themselves, with $E_1$ and with $N_1$, and every one of them is exploited
  by some opponent of size at most 10. So no safe agent of size at most 12 has all three
  coordination properties.
- **Size 13 is enough.** The agent $X_1 = \Box(p \vee \Box p) \wedge (\Box\bot \vee \neg\Box\neg p)$
  of size 13 is safe against every modal opponent and reaches stag/stag with itself, with FairBot,
  with $E_1$ and with $N_1$. More generally, the family
  $X_k = \Box(p \vee \Box^k p) \wedge (\Box\bot \vee \neg\Box\neg p)$ is safe for every $k \ge 1$,
  coordinates with itself and with FairBot, with $E_j$ exactly when $j \le k$, and with every
  $N_n$, $n \ge 1$.
- **Census safety counts.** Among the 7,561 classes of size at most 10, exactly 1,693 avoid being
  left hunting stag alone against every agent in that census, and 517 of these hunt stag with
  themselves; tested against all opponents of size at most 12, only one of the 517,
  $\Box(p \vee (q \wedge \neg\Box^3 q))$, is exploited (by an opponent of size 11).

## Why it matters

Safe agents in the Stag Hunt must refuse to hunt stag unless they can be sure of a partner, which
pulls against coordinating with simple partners such as $E_1$ and $N_1$. The result locates the
smallest size at which safety and these coordination properties can be combined, and gives an
explicit infinite family that does it.

## Proved vs checked

The laws for $X_k$, including safety against every modal opponent, are proved for all $k$ in
Lean 4, in the height semantics of closed GL fixed points; the link to provability in arithmetic
is Solovay's theorem [@solovay1976provability], cited, not formalised (see also
[@boolos1993logic]). The non-existence below size 13 and the census counts are exhaustive
computations up to the stated sizes, with every exploiting opponent recorded and re-solved.

## Discussion

The census counts are finite statements: "safe" there means safe against the agents in the census,
and tests against larger opponents can still find exploits, as they did for one agent.
The size-13 agent is safe against every modal opponent by proof. Safety is the same outcome
condition as unexploitability in the prisoner's dilemma; what changes in the Stag Hunt is which
coordination properties one wants alongside it.
