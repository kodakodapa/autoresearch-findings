# Three-player modal agents in a public-goods game

<!-- owner-summary -->
## Setting

Modal agents decide what to do by asking what can be proved about the other players, written with
the provability box $\Box$ of the logic GL [1]. Mennen [2] set up a
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
<!-- /owner-summary -->

We believe this result is new. Our prior-art search (2026-10-20) covered:

- Mennen, "Modal combat for games other than the prisoner's dilemma" (LessWrong / Alignment Forum, 2017): framework for modal agents in games with any number of players and actions (player types, ranks, opponent tests naming a target player, an agent to test against and an action); existence and Pareto theorems; no agent families with index laws, no enumeration.
- Gram_Stone, "Modal Chicken" (LessWrong, 2015) and its comments (AlexMennen, SilentCal): SwerveBot, NerveBot, CarefulBot, AstuteBot; informal claims about graded CarefulBots and BoldBots.
- Hobson, "Yet More Modal Combat" (LessWrong / Alignment Forum, 2021): a two-system PD bot; generalisation to Chicken and more players left open.
- Critch, Dennis & Russell, "Cooperative and uncooperative institution designs: surprises and problems in open-source game theory" (arXiv 2208.07006): two-player bounded proof-search agents.
- Todorov, ten Napel & Müller, "Parametric Open Source Games" (arXiv 2606.27068): non-modal parametric agents; Chicken and Stag Hunt thresholds.
- Barasz et al. 2014 (arXiv 1401.5577); LaVictoire et al. 2014; Critch, parametric bounded Löb (arXiv 1602.04184); Oesterheld 2022 (arXiv 2211.05057); LessWrong / Alignment Forum wiki "Modal combat"; web searches for modal or provability-based agents in Chicken, Stag Hunt and multiplayer program equilibrium.

We found no earlier statement of it, but we can't be certain. If you know of prior work, please open an issue.

This result extends Mennen's framework for multiplayer modal agents, whose opponent tests fix one definition of probe atoms (Mennen 2017). Our prior-art search (2026-10-20) covered:

- Mennen, "Modal combat for games other than the prisoner's dilemma" (LessWrong / Alignment Forum, 2017): framework for modal agents in games with any number of players and actions (player types, ranks, opponent tests naming a target player, an agent to test against and an action); existence and Pareto theorems; no agent families with index laws, no enumeration.
- Gram_Stone, "Modal Chicken" (LessWrong, 2015) and its comments (AlexMennen, SilentCal): SwerveBot, NerveBot, CarefulBot, AstuteBot; informal claims about graded CarefulBots and BoldBots.
- Hobson, "Yet More Modal Combat" (LessWrong / Alignment Forum, 2021): a two-system PD bot; generalisation to Chicken and more players left open.
- Critch, Dennis & Russell, "Cooperative and uncooperative institution designs: surprises and problems in open-source game theory" (arXiv 2208.07006): two-player bounded proof-search agents.
- Todorov, ten Napel & Müller, "Parametric Open Source Games" (arXiv 2606.27068): non-modal parametric agents; Chicken and Stag Hunt thresholds.
- Barasz et al. 2014 (arXiv 1401.5577); LaVictoire et al. 2014; Critch, parametric bounded Löb (arXiv 1602.04184); Oesterheld 2022 (arXiv 2211.05057); LessWrong / Alignment Forum wiki "Modal combat"; web searches for modal or provability-based agents in Chicken, Stag Hunt and multiplayer program equilibrium.

If you know of related work we missed, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was partly proved in Lean (claims K14, K16, K18, K19) and partly checked by script (claims K13, K21); the proof and check files are included so anyone can re-run them.

## K13

For five three-player bots $D,C,F=\Box(p_1\land p_2),O=\Box(p_1\lor p_2),Q=\Box(q_1\land q_2)$, 125 triples are GL-certified under evaluator-replacement probes: $FFF=111$, $FFD=000$, $QQQ=000$; exactly $D,F,Q$ never earn less than either opponent within this five-bot set.

Status: derived

Kind: model

Evidence:
- check `checks/K13-three_player.py`: 125 triples, all 3000 simultaneous replacement-subset equations GL-certified; 375 flipped-candidate controls; headline cells and finite payoff/self-play classifications. — pass (`results/K13-1.json`)
- check `checks/K13-probe_semantics_alternative.py`: Re-certifies the original 125 triples and alternative 125 triples; 6000 equations and 750 flip controls; exactly nine stated differences. — pass (`results/K13-2.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R5.md`)

### Provenance

- run: 20261019-1400
- claim: K13
- author: r2 (codex)
- round: 5
- run-folder commit: 24c2a64bf8b8cb8be184b4d449ce11068d8270ea
- check results: K13-1.json, K13-2.json

## K14

In the three-player public-goods game $u_i=2\sum_j a_j-3a_i$, $F=\Box(p_1\land p_2)$ never earns less than either opponent against any two modal opponents (Lean, tail semantics), while cooperating with two copies and defecting against a defector.

Status: derived

Kind: model

Evidence:
- check `checks/K14-c046_xreview_k13.py`: (4) Lean 4 core fair3\_tail (any opponent traces, X-\>Y&Z) and fair3\_payoff (decided over 8 tails), no sorryAx, false variant rejected; (2) FFF=111, FFD=000, QQQ=000, FCD=010, QBC=101 GL-certified on all 24 replacement equations; (1) 125 K13 triples re-solved independently — pass (`results/K14-1.json`)
- reasoning: If F contributes in the tail, both opponents contributed one height earlier, still in the tail; otherwise F defects and a defector earns at least as much as anyone.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R5.md`)

### Provenance

- run: 20261019-1400
- claim: K14
- author: r1 (claude)
- round: 6
- run-folder commit: 24c2a64bf8b8cb8be184b4d449ce11068d8270ea
- check results: K14-1.json

## K16

In the guarded three-player language with node-count size and evaluator-replacement probes, size 4 is minimal for self-cooperation plus never earning less than either opponent in $u_i=2\sum_j a_j-3a_i$: $F=\Box(p_1\land p_2)$ attains it (tail semantics).

Status: derived

Kind: model

Evidence:
- check `checks/K16-three_player_minimal.py`: Exhaustive 25 raw guarded trees through size 3; 15625 augmented triples, 375000 GL equations, 46875 flip controls; each smaller self-cooperator has a disadvantage witness; size-4 FairBot self-cooperates and passes finite safety. — pass (`results/K16-2.json`)
- reasoning: The exhaustive finite witnesses rule out universal safety for every smaller self-cooperator. K14 proves universal safety of size-4 conjunction FairBot, supplying the matching upper bound.
- check `checks/K16-three_player_minimal.py`: 25 exhaustive raw trees through size 3; 15625 triples / 375000 GL equations / 46875 flip controls; smaller self-cooperators have disadvantage witnesses; embedded K14 Lean fair3\_tail and fair3\_payoff prove universal upper bound, no sorryAx, false variant rejected. — pass (`results/K16-2.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R5.md`)

### Provenance

- run: 20261019-1400
- claim: K16
- author: r2 (codex)
- round: 8
- run-folder commit: 24c2a64bf8b8cb8be184b4d449ce11068d8270ea
- check results: K16-2.json

## K18

In the guarded three-player language (evaluator-replacement probes, $u_i=2\sum_j a_j-3a_i$), exactly 66 trees of size $\le6$ self-cooperate and never earn less than either opponent; all are $q$-free and GL proves $A\to\Box^3(p_1\land p_2)$; others fail vs size-$\le3$ pairs.

Status: derived

Kind: model

Evidence:
- check `checks/K18-c046_safe6.py`: (1) 1,6,18,112,596,3756 guarded trees; (2) self-cooperators 11,41,263,1448; survivors 0,0,0,2,8,56, all others beaten by size\<=3 pairs (constants except 8 named trees); (3) survivors q-free, GL proves A-\>\[\]\[\]\[\](p1&p2), control rejected; (4) 3438 triples GL-certified, 24 equations each, flips rejected; (5) Lean lag\_tail, fair3\_payoff, no sorryAx, false variant rejected — pass (`results/K18-1.json`)
- reasoning: The height chain with arbitrary atom valuations is a GL model, so A-\>\[\]^3(p1&p2) gives: x h implies y g and z g for g+3\<=h; lag\_tail then yields tail X-\>Y&Z, and a defector never earns less than anyone.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R5.md`)

### Provenance

- run: 20261019-1400
- claim: K18
- author: r1 (claude)
- round: 13
- run-folder commit: 24c2a64bf8b8cb8be184b4d449ce11068d8270ea
- check results: K18-1.json

## K19

In K18's three-player language, $E=\Box((p_1\land p_2)\land(\Box\bot\lor\neg q_1))$ (size 10) self-cooperates, defects against two constant contributors (payoffs 4,1,1) and never earns less than either opponent; no tree of size $\le7$ has all three properties.

Status: derived

Kind: model

Evidence:
- check `checks/K19-c046_prudent3.py`: (1) 9 E-cells (EEE=111, ECC=011, ECD=010, EDD=000, E FB FB=111, E E FB=111, E C FB=010, E D FB=000, EEC=111) GL-certified, 24 equations each, flips rejected; (2) GL proves E-\>\[\](p1&p2), control rejected; (3) sizes\<=7: 1,6,18,112,596,3756,23636 trees, self-coop & defect vs (C,C) 0,0,4,4,68,220,1808, each beaten by a size\<=3 pair; (5) Lean lag\_tail, fair3\_payoff, no sorryAx, false variant rejected — pass (`results/K19-1.json`)
- reasoning: GL soundness on the height chain turns E-\>\[\](p1&p2) into: E contributes at h implies both opponents contribute at all g\<h; lag\_tail with k=1 gives tail X-\>Y&Z, and a defector never earns less than anyone.
- check `checks/K19-c046_xreview_k20.py`: K20 cells incl. RRR=000 (q1-\>p1) GL-certified on 24 equations, flips rejected; GL proves A\<-\>E with 8 mixed triples 111; GL rejects A\<-\>R (probe essential) — pass (`results/K19-2.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R5.md`)

### Provenance

- run: 20261019-1400
- claim: K19
- author: r1 (claude)
- round: 14
- run-folder commit: 24c2a64bf8b8cb8be184b4d449ce11068d8270ea
- check results: K19-1.json, K19-2.json

## K21

For K13’s five bots, replacing the evaluator alone versus replacing all players other than the queried opponent changes exactly 9 of 125 triples: permutations of $(Q,C,O)$ and $(Q,O,O)$ change from $111$ to only $Q$ defecting (GL-certified).

Status: derived

Kind: model

Evidence:
- check `checks/K13-probe_semantics_alternative.py`: 250 triples, 6000 GL equations, 750 flips; exactly the specified nine differences, QOC 111 versus 011; all probe-free triples unchanged. — pass (`results/K21-1.json`)

Prior art: partial prior art (answer: `prior-art/R2.md`)

### Provenance

- run: 20261019-1400
- claim: K21
- author: r2 (codex)
- round: 15
- run-folder commit: 24c2a64bf8b8cb8be184b4d449ce11068d8270ea
- check results: K21-1.json

## Discussion

<!-- owner-discussion -->
The results use one language (two "contributes" atoms and two probes), one payoff function and
tail semantics; other probe definitions change some outcomes, as shown. The classifications stop
at sizes 6 to 10. Open questions are the minimum size of a safe self-cooperator that needs the
probe (between 8 and 10) and whether these patterns extend to more players or other multiplayer
games.
<!-- /owner-discussion -->

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:mennen2017modal --> Mennen, Alex. 2017. Modal Combat for Games Other Than the Prisoner's Dilemma. [Link](https://www.lesswrong.com/posts/5bd75cc58225bf0670375375/modal-combat-for-games-other-than-the-prisoner-s-dilemma)
