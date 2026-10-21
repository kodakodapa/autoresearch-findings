---
layout: post
title: "Three-player modal agents in a public-goods game"
date: 2026-10-20
scholar: {"citation_title": "Three-player modal agents in a public-goods game", "citation_author": "Kodakodapa", "citation_publication_date": "2026/10/20", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/three-player-modal-agents.html", "citation_keywords": "C046", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/three-player-modal-agents/paper.pdf"}
---

## Summary

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

**K13.** For five three-player bots $D,C,F=\Box(p_1\land p_2),O=\Box(p_1\lor p_2),Q=\Box(q_1\land q_2)$, 125 triples are GL-certified under evaluator-replacement probes: $FFF=111$, $FFD=000$, $QQQ=000$; exactly $D,F,Q$ never earn less than either opponent within this five-bot set.

- Status: derived
- Machine-checked: 2 of 2 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K14.** In the three-player public-goods game $u_i=2\sum_j a_j-3a_i$, $F=\Box(p_1\land p_2)$ never earns less than either opponent against any two modal opponents (Lean, tail semantics), while cooperating with two copies and defecting against a defector.

- Status: derived
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K16.** In the guarded three-player language with node-count size and evaluator-replacement probes, size 4 is minimal for self-cooperation plus never earning less than either opponent in $u_i=2\sum_j a_j-3a_i$: $F=\Box(p_1\land p_2)$ attains it (tail semantics).

- Status: derived
- Machine-checked: 2 of 2 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K18.** In the guarded three-player language (evaluator-replacement probes, $u_i=2\sum_j a_j-3a_i$), exactly 66 trees of size $\le6$ self-cooperate and never earn less than either opponent; all are $q$-free and GL proves $A\to\Box^3(p_1\land p_2)$; others fail vs size-$\le3$ pairs.

- Status: derived
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K19.** In K18's three-player language, $E=\Box((p_1\land p_2)\land(\Box\bot\lor\neg q_1))$ (size 10) self-cooperates, defects against two constant contributors (payoffs 4,1,1) and never earns less than either opponent; no tree of size $\le7$ has all three properties.

- Status: derived
- Machine-checked: 2 of 2 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K21.** For K13’s five bots, replacing the evaluator alone versus replacing all players other than the queried opponent changes exactly 9 of 125 triples: permutations of $(Q,C,O)$ and $(Q,O,O)$ change from $111$ to only $Q$ defecting (GL-certified).

- Status: derived
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

## Discussion

The results use one language (two "contributes" atoms and two probes), one payoff function and
tail semantics; other probe definitions change some outcomes, as shown. The classifications stop
at sizes 6 to 10. Open questions are the minimum size of a safe self-cooperator that needs the
probe (between 8 and 10) and whether these patterns extend to more players or other multiplayer
games.

## How to verify

Run each script in `claims/three-player-modal-agents/checks/` with `python -I <script>`; it passes if it
exits with status 0. The results recorded in the original run are in
`claims/three-player-modal-agents/results/`; the full claim text is in `claims/three-player-modal-agents/claim.md`.

## Provenance

- run: 20261019-1400
- claims: K13, K14, K16, K18, K19, K21
- run-folder commit: 24c2a64bf8b8cb8be184b4d449ce11068d8270ea
- K13 author: r2 (codex)
- K14 author: r1 (claude)
- K16 author: r2 (codex)
- K18 author: r1 (claude)
- K19 author: r1 (claude)
- K21 author: r2 (codex)

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:mennen2017modal --> Mennen, Alex. 2017. Modal Combat for Games Other Than the Prisoner's Dilemma. [Link](https://www.lesswrong.com/posts/5bd75cc58225bf0670375375/modal-combat-for-games-other-than-the-prisoner-s-dilemma)
