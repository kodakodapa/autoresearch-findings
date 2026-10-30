---
layout: post
title: "A census of modal agents in the prisoner's dilemma"
date: 2026-10-19
scholar: {"citation_title": "A census of modal agents in the prisoner's dilemma", "citation_author": "Lindheim, Bj\u00f6rn", "citation_publication_date": "2026/10/19", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/modal-agent-census.html", "citation_keywords": "C046", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/modal-agent-census/paper.pdf"}
---

## Summary

<!-- owner-summary -->
## Setting

Two programs play a one-shot prisoner's dilemma, and each can read the other's source code.
Following Barasz et al. [1], a *modal agent* decides by asking what can be proved
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
and a few more) [1, 2]. A census makes the space itself
visible: it shows that program equilibrium among modal agents has no evolutionarily stable
point, that a round robin rewards agents that never cooperate, and that self-defecting
cooperators are rarely safe, with four tiny agents enough to expose all the others.

## Proved vs checked

Every outcome is computed exactly in the height semantics of closed GL fixed points (see
[3]; the link to provability in arithmetic is Solovay's theorem
[4]) and re-checked on large samples by an independent solver; the
datasets are pinned by hash. The counts, equilibria and exploitability results hold for all
agents up to the stated sizes, not in general. The FairBot invasion argument and the
counterexample $Y$ hold in general.
<!-- /owner-summary -->

We believe this result is new. Our prior-art searches (2026-10-17 to 2026-10-19) covered:

- OEIS (oeis.org), searched for the census counts 1, 4, 8, 12, 31, 98, 255, 646, 1760 (per size) and 1, 5, 13, 25, 56, 154, 409, 1055, 2815 (cumulative): no match.
- Barasz et al. 2014 (arXiv 1401.5577); LaVictoire et al. 2014; LessWrong / Arbital "Modal combat"; Mennen 2017; Critch, Dennis & Russell 2022 (arXiv 2208.07006); github.com/machine-intelligence/provability.
- Barasz et al. 2014, Robust Cooperation in the Prisoner's Dilemma (arXiv 1401.5577), full text: named agents CB, DB, CliqueBot, FairBot, PrudentBot, TrollBot, JustBot, WaitFairBot_K; Theorems 3.2, 4.8, 4.10; obstacles section.
- LaVictoire et al. 2014, Program Equilibrium in the Prisoner's Dilemma via Löb's Theorem.
- LessWrong post on Barasz et al. and its comments (orthonormal, cousin_it, Will_Sawin, Karl, dankane).
- Arbital / LessWrong wiki "Modal combat".
- Garrabrant, "Prisoners' Dilemma with Costs to Modeling"; Garrabrant, "Modal SAT: Introduction" (2015).
- Mennen, "Modal Combat for games other than the prisoner's dilemma".
- Critch, Parametric Bounded Löb's Theorem and Robust Cooperation of Bounded Agents (arXiv 1602.04184), first sections.
- Searches for round-robin, tournament, replicator or ESS analyses of modal agents: only iterated-PD and FDT evolution papers (e.g. arXiv 2005.05154, no modal agents).
- github.com/machine-intelligence/provability (agents folder contents not visible).
- Barasz et al. 2014 (arXiv 1401.5577), full text; LaVictoire et al. 2014 (Program Equilibrium via Löb's Theorem).
- LessWrong post on Barasz et al. and comments; Arbital "Modal combat".
- Garrabrant, "Prisoners' Dilemma with Costs to Modeling" and "Modal SAT: Introduction"; Mennen, "Modal Combat for games other than the prisoner's dilemma".
- Critch, Parametric Bounded Löb (arXiv 1602.04184), first sections.
- Oesterheld 2022, A Note on the Compatibility of Different Robust Program Equilibria of the Prisoner's Dilemma (arXiv 2211.05057).

We found no earlier statement of it, but we can't be certain. If you know of prior work, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was checked by script; the proof and check files are included so anyone can re-run them.

**K1.** `In L (atoms p,q each under a box; F,~,&,|,[]; size=node count) agents up to size 9 form 2815 classes of equivalence on finite linear GL models (new per size: 1,4,8,12,31,98,255,646,1760); every pairwise outcome is solved exactly.`

- Status: derived
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K12.** `In L up to size 9 (2815 classes, payoffs 5/3/1/0): the round-robin maximum 8083 is reached only by 63 agents acting exactly as DefectBot; of 1335 behaviour classes 180 are symmetric Nash (78 self-defecting, all invaded by FairBot) and none is an ESS.`

- Status: derived
- Machine-checked: 2 of 2 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K15.** `In L up to size 11 (20441 classes, payoffs 5/3/1/0): round-robin max 59893 is reached only by 16 agents of size 10-11 that defect against all, e.g. [][]p&~[](p|[]F); DefectBot scores 59193 (rank 21). 1120 symmetric Nash classes, no ESS.`

- Status: derived
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K17.** `In L up to size 14, of the agents that defect vs themselves but cooperate with FairBot and CooperateBot (2,2,4,...,2468,7032 per size 4..14), 3/19/75 at sizes 12/13/14 are unexploitable by every modal opponent; each other is exploited by []~p, []p, []q or []F.`

- Status: derived
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K19.** `In L up to size 14 (and 15, unchecked run), every self-defecting agent cooperating with FairBot cooperates with F_k (k<=8) iff k<=a and with P_i iff i>=b, a<b. Fails at size 17: Y=[]([][]F|(p&(q|~[](q&[][][]F)))) coops F_1, F_k k>=4, P_i i>=3, not F_2,F_3.`

- Status: derived
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

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

## How to verify

Run each script in `claims/modal-agent-census/checks/` with `python -I <script>`; it passes if it
exits with status 0. The results recorded in the original run are in
`claims/modal-agent-census/results/`; the full claim text is in `claims/modal-agent-census/claim.md`.

## Provenance

- run: 20261017-1126
- claims: K1, K12, K15, K17, K19
- run-folder commit: 662166ecff0651902cc5fcb04bf747c62d795af2
- K1 author: r1 (claude)
- K12 author: r1 (claude)
- K15 author: r1 (claude)
- K17 author: r1 (claude)
- K19 author: r1 (claude)

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:lavictoire2014program --> LaVictoire, Patrick and Fallenstein, Benja and Yudkowsky, Eliezer and Barasz, Mihaly and Christiano, Paul and Herreshoff, Marcello. 2014. Program Equilibrium in the Prisoner's Dilemma via L\"ob's Theorem. AAAI Workshop on Multiagent Interaction without Prior Coordination. [Link](https://intelligence.org/files/ProgramEquilibrium.pdf)
3. <!-- cite:boolos1993logic --> Boolos, George. 1993. The Logic of Provability. Cambridge University Press
4. <!-- cite:solovay1976provability --> Solovay, Robert M.. 1976. Provability Interpretations of Modal Logic. Israel Journal of Mathematics
