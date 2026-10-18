## Setting

Two programs play a one-shot prisoner's dilemma, and each can read the other's source code.
Following Barasz et al. [@barasz2014robust], a *modal agent* decides by asking what can be proved
about the opponent, written with the provability box $\Box$ of the logic GL. $p$ means "the
opponent cooperates with me" and $q$ means "the opponent cooperates with DefectBot". FairBot is
$\Box p$, graded FairBots are $F_k = \Box^k p$, graded PrudentBots are
$P_j = \Box p \wedge \Box(\neg\Box^j\bot \to \neg q)$, and ConBot is $\neg\Box\bot$. An agent is
*unexploitable* if no modal opponent ever gets it to cooperate while the opponent defects.

An earlier finding on this site described $W_n = \Box(\Box^n\bot \vee (p \wedge (q \vee \neg\Box q)))$: unexploitable, cooperative with FairBot and CooperateBot, yet defecting against
its own copy. This finding describes four further families of unexploitable agents that defect against
themselves, and how they relate.

## Result

- **Gate families $V_{n,r} = \Box(\Box^n\bot \vee (p \wedge (q \vee \neg\Box^r q)))$**, which
  contain $W_n = V_{n,1}$. $V_{n,r}$ and $F_k$ cooperate exactly when $k + r \le n$; $V_{n,r}$ and
  $P_j$ exactly when $r < n < j$; any two members defect against each other. For $r < n$ every
  member is unexploitable, and these members are pairwise distinct.
- **Prudent families $G_{m,j} = \Box(\Box^m p \wedge (q \vee \Box(\Box^j\bot \vee \neg q)))$
  and $H_{m,j} = \Box^{m+1}(p \wedge (q \vee \Box(\Box^j\bot \vee \neg q)))$**, $m \ge j \ge 1$.
  Both are unexploitable, cooperate with FairBot and CooperateBot, defect against themselves, and
  cooperate with $F_k$ exactly when $k \le j$ and with $P_i$ exactly when $i > m$. So $G_{m,j}$
  and $H_{m,j}$ cannot be told apart by graded FairBots or PrudentBots; the agent
  $S_j = \Box^{j+1}(p \vee \neg\Box^{j+1} q)$ separates them ($H_{m,j}$ defects against it
  while it cooperates; against $G_{m,j}$ both defect). ConBot separates the two kinds of family:
  $G_{m,j}$ defects against it, every $V_{n,r}$ with $n \ge 1$ does not.
- **A common family $J_{a,b,j} = \Box^{a+1}(\Box^b p \wedge (q \vee \Box(\Box^j\bot \vee \neg q)))$**, which contains $G$ ($a = 0$) and $H$ ($b = 0$). Checked for $a, b \le 5$,
  $j \le 6$: $J_{a,b,j}$ cooperates with $F_k$ exactly when $k \le j$ and with $P_i$ exactly when
  $i > a + b$, and exact laws hold against a two-parameter family of separating probes; the 70
  members with $j \le a + b \le 5$ are pairwise distinct. The size-13 member $J_{1,1,1}$ has the
  same outcomes as $G_{2,1}$ and $H_{2,1}$ against $F_1, \dots, F_4$ and $P_0, \dots, P_5$, yet
  two opponents of size at most 9 distinguish all three.

## Why it matters

The unexploitable agents we found in the literature (FairBot, PrudentBot and its graded and
probabilistic variants [@barasz2014robust], [@oesterheld2022compatibility]) all cooperate with
their own copies. These families show that defecting against oneself is not a single odd
example: it comes in several infinite families with different mechanisms (a delayed gate on
the DefectBot test in $V$, a PrudentBot-style check in $G$, $H$ and $J$). Their behaviour
against graded FairBots and PrudentBots is described by simple thresholds, and these opponents
alone do not identify an agent: distinct members can agree on all of them and need other probes
to be told apart.

## Proved vs checked

The laws for $V_{n,r}$, $G_{m,j}$ and $H_{m,j}$ (including the separations by ConBot and $S_j$)
are proved for all indices in Lean 4, in the height semantics of closed GL fixed points; the link
to provability in arithmetic is Solovay's theorem [@solovay1976provability], cited, not
formalised (see also [@boolos1993logic]). The statements about $J_{a,b,j}$ and $J_{1,1,1}$ are
checked, not proved: exact tables for the stated parameter ranges, with every member of size at
most 15 independently certified by GL fixed-point solving. The unexploitability of $J_{a,b,j}$ is
supported by a short argument (the agent implies $\Box^{a+b+1}p$) and randomised safety tests,
not by a proof for all indices.
