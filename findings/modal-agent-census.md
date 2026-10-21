---
layout: default
title: "A census of modal agents in the prisoner's dilemma"
scholar: {"citation_title": "A census of modal agents in the prisoner's dilemma", "citation_author": "Kodakodapa", "citation_publication_date": "2026/10/19", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/modal-agent-census.html", "citation_keywords": "C046", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/modal-agent-census/paper.pdf"}
---

# A census of modal agents in the prisoner's dilemma

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

## K1

`In L (atoms p,q each under a box; F,~,&,|,[]; size=node count) agents up to size 9 form 2815 classes of equivalence on finite linear GL models (new per size: 1,4,8,12,31,98,255,646,1760); every pairwise outcome is solved exactly.`

Status: derived

Kind: model

Evidence:
- check `checks/K1-c046_census9.py`: class counts per size 1..9; pinned dataset equals rebuilt class list; 18890 games (6 named agents' full rows/columns + 2000 random) agree with an independent height-table solver — pass (`results/K1-1.json`)
- reasoning: Letter-free fixed points depend only on height (Boolos, Logic of Provability, ch. 7), so play is a causal operator on the height chain; canonical minimized machines give a sound, exact dedup, and a repeated joint state is a fixed point.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R19.md`)

### Provenance

- run: 20261017-1126
- claim: K1
- author: r1 (claude)
- round: 1
- run-folder commit: 662166ecff0651902cc5fcb04bf747c62d795af2
- check results: K1-1.json

## K12

`In L up to size 9 (2815 classes, payoffs 5/3/1/0): the round-robin maximum 8083 is reached only by 63 agents acting exactly as DefectBot; of 1335 behaviour classes 180 are symmetric Nash (78 self-defecting, all invaded by FairBot) and none is an ESS.`

Status: derived

Kind: model

Evidence:
- check `checks/K12-c046_structure9.py`: sha-pinned census9 matrix: round-robin max 8083 by exactly 63 DB-identical agents, second 7979; 1335 observational classes; 180 Nash (78 defect, 102 coop); FB invades all 78; each of 102 has a neutral mutant (CB for 95); no ESS; 183965 used/random games re-solved by independent height-table solver — pass (`results/K12-1.json`)
- reasoning: FairBot is unexploitable (Barasz et al. 2014), so vs any X it gets 3, 5 or mutual defection; a self-defecting Nash X therefore mutually defects with FB, and FB (3 vs itself \> X's 1 vs FB) invades. Holds for every modal X, not only the census.
- check `checks/K12-c046_replicator9.py`: pinned census9; discrete replicator, uniform over 2815 chain classes, 20000 steps (exact 1335-class reduction verified 300 steps \<1e-12): mean payoff 3 within 1e-6, 788 survivors \>1e-6, all self-cooperating, 0.38+-0.005 weight on exploitable classes, final vector equals embedded pin within 2e-6 — pass (`results/K12-2.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R7.md`)

### Provenance

- run: 20261017-1126
- claim: K12
- author: r1 (claude)
- round: 7
- run-folder commit: 662166ecff0651902cc5fcb04bf747c62d795af2
- check results: K12-1.json, K12-2.json

## K15

`In L up to size 11 (20441 classes, payoffs 5/3/1/0): round-robin max 59893 is reached only by 16 agents of size 10-11 that defect against all, e.g. [][]p&~[](p|[]F); DefectBot scores 59193 (rank 21). 1120 symmetric Nash classes, no ESS.`

Status: derived

Kind: model

Evidence:
- check `checks/K15-c046_structure11.py`: sha-pinned census11 agents+matrix: rr max 59893 by exactly 16 total defectors of sizes 10,11, each cooperated with by 9863; DB 59193, 9688, 20 above; T vs \[\]F\|~\[\]~p = D/C; 9095 obs classes; Nash 1120 (401 FB-invaded, 719 with neutral mutant); ESS none; 53938 cells re-solved independently — pass (`results/K15-1.json`)
- reasoning: T's tail requires p at all g\<h-1 and ~p at some g in \[1,h), impossible for a constant opponent tail, so T defects against every modal agent; its round-robin edge over DB is only in who cooperates with it.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R8.md`)

### Provenance

- run: 20261017-1126
- claim: K15
- author: r1 (claude)
- round: 29
- run-folder commit: 662166ecff0651902cc5fcb04bf747c62d795af2
- check results: K15-1.json

## K17

`In L up to size 14, of the agents that defect vs themselves but cooperate with FairBot and CooperateBot (2,2,4,...,2468,7032 per size 4..14), 3/19/75 at sizes 12/13/14 are unexploitable by every modal opponent; each other is exploited by []~p, []p, []q or []F.`

Status: derived

Kind: model

Evidence:
- check `checks/K17-c046_dichotomy14.py`: census counts to size 14 (..,36062,100823,279115); combination counts per size 4..14; machine criterion U holds for exactly 3,19,75 members at sizes 12,13,14 (sha256-pinned list incl. W) and none below; every non-U member exploited by one of \[\]~p,\[\]p,\[\]q,\[\]F; independent height-table solver re-checks 400 witnesses and all 97 U agents' properties; random-trace test finds no exploit for U agents and finds one for 40/40 non-U controls — pass (`results/K17-1.json`)
- reasoning: Closed GL fixed points are letter-free and decided by height on finite linear frames (Boolos, Logic of Provability ch. 7). An opponent defecting at the tail gives eventually constant inputs p=0, q=c; U forbids an all-1 output cycle under such inputs from any state, hence from any state the game reaches.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R10.md`)

### Provenance

- run: 20261017-1126
- claim: K17
- author: r1 (claude)
- round: 29
- run-folder commit: 662166ecff0651902cc5fcb04bf747c62d795af2
- check results: K17-1.json

## K19

`In L up to size 14 (and 15, unchecked run), every self-defecting agent cooperating with FairBot cooperates with F_k (k<=8) iff k<=a and with P_i iff i>=b, a<b. Fails at size 17: Y=[]([][]F|(p&(q|~[](q&[][][]F)))) coops F_1, F_k k>=4, P_i i>=3, not F_2,F_3.`

Status: derived

Kind: model

Evidence:
- check `checks/K19-c046_segment.py`: census counts to 14; law (initial F-segment, final P-segment, a\<b) on all 9979 S=0 FB-cooperating classes; Y size 17, S=0, CC FB/CB/F\_1/F\_4..F\_12/P\_3..P\_12, DD with F\_2,F\_3,P\_0..P\_2, D vs DB, criterion U; independent string solver for all Y rows; 3000 random traces; GLS certificates with flipped controls for Y vs Y,F\_1..F\_4,P\_2,P\_3,CB — pass (`results/K19-1.json`)
- reasoning: Closed GL fixed points are letter-free and decided by height on finite linear frames (Boolos, Logic of Provability ch. 7). Y's q-test fails only at heights 2,3, so it rejects DB-traces \[h\<=c\] only for c in {1,2}, which covers its own trace (c=2) and F\_2,F\_3.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R12.md`)

### Provenance

- run: 20261017-1126
- claim: K19
- author: r1 (claude)
- round: 14
- run-folder commit: 662166ecff0651902cc5fcb04bf747c62d795af2
- check results: K19-1.json

## Discussion

<!-- owner-discussion -->
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
<!-- /owner-discussion -->

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:lavictoire2014program --> LaVictoire, Patrick and Fallenstein, Benja and Yudkowsky, Eliezer and Barasz, Mihaly and Christiano, Paul and Herreshoff, Marcello. 2014. Program Equilibrium in the Prisoner's Dilemma via L\"ob's Theorem. AAAI Workshop on Multiagent Interaction without Prior Coordination. [Link](https://intelligence.org/files/ProgramEquilibrium.pdf)
3. <!-- cite:boolos1993logic --> Boolos, George. 1993. The Logic of Provability. Cambridge University Press
4. <!-- cite:solovay1976provability --> Solovay, Robert M.. 1976. Provability Interpretations of Modal Logic. Israel Journal of Mathematics
