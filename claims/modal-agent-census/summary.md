## Setting

Two programs play a one-shot prisoner's dilemma, and each can read the other's source code.
Following Barasz et al. [@barasz2014robust], a *modal agent* decides by asking what can be proved
about the opponent, written with the provability box $\Box$ of the logic GL: $p$ means "the
opponent cooperates with me", $q$ "the opponent cooperates with DefectBot". We take the language
L of all formulas built from $p$, $q$, $\bot$, $\neg$, $\wedge$, $\vee$ and $\Box$ with every atom
under a box, measure size as the number of nodes, and identify agents that behave identically
against every opponent. Payoffs are the standard 5 (temptation), 3 (mutual cooperation), 1
(mutual defection), 0 (sucker). An earlier finding on this site describes the self-defecting
families found in this census; this one reports the census itself.

## Result

- **Counts.** Up to size 9 there are 2815 behaviourally distinct agents (new per size 1 to 9:
  1, 4, 8, 12, 31, 98, 255, 646, 1760), and every pairwise outcome is solved exactly.
- **No evolutionarily stable agent.** Up to size 9, 180 of the 1335 observational classes are
  symmetric Nash equilibria, but none is an ESS. Every self-defecting equilibrium is invaded by
  FairBot, an argument that holds for every modal agent, not only those in the census. Under
  replicator dynamics from the uniform start, every surviving agent cooperates with itself and
  the mean payoff tends to 3.
- **The round-robin winner never cooperates.** Up to size 9 the top score belongs to agents that
  act exactly like DefectBot. Up to size 11 the top 16 agents defect against everyone yet beat
  DefectBot, because more opponents cooperate with them (9863 against 9688); for example
  $\Box\Box p \wedge \neg\Box(p \vee \Box\bot)$.
- **Self-defecting cooperators are almost always exploitable.** Among agents that defect against
  themselves but cooperate with FairBot and CooperateBot (2, 2, 4, …, 2468, 7032 per size 4 to
  14), only 3, 19 and 75 at sizes 12, 13 and 14 are unexploitable by every modal opponent. Each
  of the others is exploited by one of four simple agents: $\Box\neg p$, $\Box p$, $\Box q$ or
  $\Box\bot$.
- **A threshold law, and where it breaks.** Up to size 14, every self-defecting agent that
  cooperates with FairBot cooperates with graded FairBots $F_k = \Box^k p$ exactly for $k \le a$
  and with graded PrudentBots $P_i$ exactly for $i \ge b$, for some $a < b$. The law fails at size
  17: the agent $Y = \Box(\Box\Box\bot \vee (p \wedge (q \vee \neg\Box(q \wedge
  \Box\Box\Box\bot))))$ cooperates with $F_1$ and $F_k$ for $k \ge 4$, but not with $F_2$ or $F_3$.

## Why it matters

The literature on modal agents studies a handful of named agents (FairBot, PrudentBot, CliqueBot
and a few more) [@barasz2014robust; @lavictoire2014program]. A census makes the space itself
visible: it shows that program equilibrium among modal agents has no evolutionarily stable
point, that a round robin rewards agents that never cooperate, and that self-defecting
cooperators are rarely safe, with four tiny agents enough to expose all the others.

## Proved vs checked

Every outcome is computed exactly in the height semantics of closed GL fixed points (see
[@boolos1993logic]; the link to provability in arithmetic is Solovay's theorem
[@solovay1976provability]) and re-checked on large samples by an independent solver; the
datasets are pinned by hash. The counts, equilibria and exploitability results hold for all
agents up to the stated sizes, not in general. The FairBot invasion argument and the
counterexample $Y$ hold in general.

## Discussion

The census is exhaustive only up to the stated sizes (9 for the counts and equilibria, 11 for
the round robin, 14 for exploitability and the threshold law), and only for the language L with
the single probe "the opponent cooperates with DefectBot". Richer probes (how the opponent
treats FairBot or CooperateBot) would give a different, larger space, and the counts depend on
the exact choice of connectives and size measure. Results about tournaments and replicator
dynamics depend on the payoffs and on the uniform starting population; we report them as
properties of this population, not of modal agents in general. The FairBot invasion argument and
the counterexample $Y$ are the exceptions: they hold for all modal agents.

Two questions stay open. First, whether the unexploitable self-defecting agents found up to size
14 all belong to known families: some of them do, and the rest were shown different from family
members of small index but not classified. Second, whether the threshold law, which fails at
size 17, holds in a weaker form, for example for all agents of a given family. The natural next
searches are the same census for other two-action games (Chicken, Stag Hunt), where outcomes are
unchanged and only the scoring differs, and a census with more probes.
