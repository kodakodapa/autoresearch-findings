## Setting

Modal agents decide what to do by asking what can be proved about the other players, written with
the provability box $\Box$ of the logic GL [@barasz2014robust]. Mennen [@mennen2017modal] set up a
framework for more than two players; here we study three players concretely. The game is a
public-goods game: each player contributes ($a_i = 1$) or not, and earns
$u_i = 2\sum_j a_j - 3a_i$, so contributing costs 1 net but gives each other player 2. An agent sees
$p_1, p_2$ ("opponent $j$ contributes in this game") and probes $q_1, q_2$ ("opponent $j$
contributes when I am replaced by a defector"). Behaviour is read off in the long run (tail
semantics). An agent is *safe* if it never earns less than either opponent, whoever they are.

## Result

- **The three-player FairBot is safe.** $F = \Box(p_1 \wedge p_2)$ (contribute iff it is provable
  that both others contribute) never earns less than either opponent against any two modal
  opponents, contributes with two copies of itself and defects against a defector.
- **It is the smallest.** No agent smaller than $F$ (size 4) both cooperates with copies of itself
  and is safe.
- **All small safe cooperators are FairBot-like.** Exactly 66 agents up to size 6 cooperate with
  themselves and are safe; none of them uses the probes, and for each GL proves that it contributes
  only if $\Box^3(p_1 \wedge p_2)$. Every other agent of that size fails against some pair of
  opponents of size at most 3.
- **A prudent three-player agent needs the probe.**
  $E = \Box((p_1 \wedge p_2) \wedge (\Box\bot \vee \neg q_1))$ (size 10) cooperates with itself,
  is safe, and defects against two unconditional contributors; no agent of size at most 7 has all
  three properties.
- **The definition of the probe matters.** For five basic three-player bots we certify all 125
  triples. Changing the probe from "only I am replaced by a defector" to "everyone except the
  queried opponent is replaced" changes the outcome of 9 of the 125 triples.

## Why it matters

Program equilibrium with modal agents has been worked out almost only for two players. In a
three-player public-goods game the natural FairBot generalisation stays safe, is the smallest safe
cooperator, and is essentially the only kind up to size 6. Exploiting unconditional contributors
requires the probe, as with PrudentBot in two-player games, and the exact definition of the probe
is a real modelling choice, since outcomes change with it.

## Proved vs checked

The safety of $F$ against all modal opponents is proved in Lean 4 under tail semantics. The
minimality, the 66-agent classification, the properties of $E$ and the 125-triple tables are exact
computations over all agents up to the stated sizes in the stated language, with GL certificates.

## Discussion

The results use one language (two "contributes" atoms and two probes), one payoff function and
tail semantics; other probe definitions change some outcomes, as shown. The classifications stop
at sizes 6 to 10. Open questions are the minimum size of a safe self-cooperator that needs the
probe (between 8 and 10) and whether these patterns extend to more players or other multiplayer
games.
