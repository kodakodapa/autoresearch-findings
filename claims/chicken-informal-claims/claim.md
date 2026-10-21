# Settling informal claims about modal agents in Chicken

<!-- owner-summary -->
## Setting

Modal agents play one-shot games by asking what can be proved about each other, written with the
provability box $\Box$ of the logic GL [1]. Two informal posts made claims about
specific agents that were never checked. "Modal Chicken" [2] introduced
CarefulBot and AstuteBot for the game of Chicken, and its comments proposed graded variants:
$C_n = \neg\Box(\Box^n\bot \vee p)$ ("swerve unless the opponent provably swerves", with proof
strength $n$) and BoldBots $B_n = \Box(\Box^n\bot \vee \neg p)$, the name a commenter gave to the
post's original CarefulBot ($B_0$); here $p$ means "the opponent swerves against me". "Yet More Modal Combat" [3] proposed, for the prisoner's
dilemma, a bot that defects if a weak system proves the opponent cooperates and otherwise acts like
FairBot with a strong system; in graded form $H_{a,b} = \neg P_a(p) \wedge P_b(p)$ with
$P_a(z) = \Box(\Box^a\bot \vee z)$, $a < b$.

## Result

- **Graded CarefulBots and BoldBots, for all grades:** $C_n$ swerves against $C_m$ exactly when
  $n \le m$, while $B_n$ swerves against $B_m$ exactly when $n > m$. A CarefulBot against a BoldBot
  always goes straight while the BoldBot swerves, so the pair always ends at payoffs $(4, 1)$,
  whatever the grades.
- **The named agents:** a certified table of all 64 pairings of SwerveBot, NerveBot, the
  original CarefulBot $B_0$, $C_0$, AstuteBot as displayed in the post, the FairBots $P_0(p) = \Box p$
  and $P_1(p)$, and Hobson's bot $H_{0,1}$ (which cooperates with itself but ends in mutual
  defection with both FairBots). The original CarefulBot crashes against itself, as a comment pointed out; the
  displayed AstuteBot swerves against itself, as the post claimed.
- **Hobson's bot, for all grades:** $H_{a,b}$ and $H_{c,d}$ end in mutual cooperation exactly when
  their weak grades agree ($a = c$), and otherwise in mutual defection. Against any FairBot of the
  form $P_e(p)$ it ends in mutual defection, for every $e$.

## Why it matters

Informal claims about small agents are easy to make and easy to get wrong; two of the claims in
these posts were already disputed in their comment threads. These results settle them for every
grade at once. They also show that Hobson's bot, proposed as a bot that cooperates with FairBots,
does not cooperate with any graded FairBot of this form.

## Proved vs checked

The graded laws (CarefulBots, BoldBots, the mixed pair, Hobson's bot) are proved for all indices in
Lean 4, in the height semantics of closed GL fixed points (see [4];
[5]). The 64-cell table is certified by GL fixed-point computation.
<!-- /owner-summary -->

This result extends the informal claims about CarefulBot, AstuteBot and graded CarefulBots and BoldBots in "Modal Chicken" and its comments (Gram_Stone 2015); Hobson's two-system bot and the counterexample in its comments (Hobson 2021). Our prior-art search (2026-10-20) covered:

- Mennen, "Modal combat for games other than the prisoner's dilemma" (LessWrong / Alignment Forum, 2017): framework for modal agents in games with any number of players and actions (player types, ranks, opponent tests naming a target player, an agent to test against and an action); existence and Pareto theorems; no agent families with index laws, no enumeration.
- Gram_Stone, "Modal Chicken" (LessWrong, 2015) and its comments (AlexMennen, SilentCal): SwerveBot, NerveBot, CarefulBot, AstuteBot; informal claims about graded CarefulBots and BoldBots.
- Hobson, "Yet More Modal Combat" (LessWrong / Alignment Forum, 2021): a two-system PD bot; generalisation to Chicken and more players left open.
- Critch, Dennis & Russell, "Cooperative and uncooperative institution designs: surprises and problems in open-source game theory" (arXiv 2208.07006): two-player bounded proof-search agents.
- Todorov, ten Napel & Müller, "Parametric Open Source Games" (arXiv 2606.27068): non-modal parametric agents; Chicken and Stag Hunt thresholds.
- Barasz et al. 2014 (arXiv 1401.5577); LaVictoire et al. 2014; Critch, parametric bounded Löb (arXiv 1602.04184); Oesterheld 2022 (arXiv 2211.05057); LessWrong / Alignment Forum wiki "Modal combat"; web searches for modal or provability-based agents in Chicken, Stag Hunt and multiplayer program equilibrium.

If you know of related work we missed, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was partly checked by scripts that run Lean proofs (claims K5, K11, K12) and partly checked by script (claims K6); the proof and check files are included so anyone can re-run them.

## K5

For all $n,m\ge0$, $C_n=\neg P_n(p)$ swerves against $C_m$ iff $n\le m$, while $B_n=P_n(\neg p)$ swerves against $B_m$ iff $n>m$, where $P_n(a)=\Box(\Box^n\bot\lor a)$. Exact height laws are Lean-proved.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K5-informal_tables.py`: 50 graded pair outcomes for indices 0..4, each with both simultaneous GL fixed-point equations certified. — pass (`results/K6-2.json`)
- check `checks/K5-graded_families.py`: Lean core proves exact height laws for every n,m,h and every solution, plus boxed-formula bridge; no sorryAx; false tie law rejected; 20480 finite recurrence cells agree. — pass (`results/K5-2.json`)

Prior art: partial prior art (answer: `prior-art/R4.md`)

### Provenance

- run: 20261019-1400
- claim: K5
- author: r2 (codex)
- round: 1
- run-folder commit: 24c2a64bf8b8cb8be184b4d449ce11068d8270ea
- check results: K5-2.json, K6-2.json

## K6

The 64-cell GL table for $S,N,B_0,C_0,A,H,F_0,F_1$ is certified: original CarefulBot $B_0$ self-crashes; displayed AstuteBot $A$ self-swerves; $H=\neg\Box p\land\Box(\Box\bot\lor p)$ self-cooperates but mutually defects with $F_0,F_1$.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K5-informal_tables.py`: All 64 stated outcomes, both GL fixed-point equations per cell, rejection of flipped candidates, and closed-form tail evaluation. — pass (`results/K6-2.json`)
- check `checks/K5-informal_tables.py`: 64 outcomes and both simultaneous GL equations per pair, flipped controls rejected; no calculation changed. — pass (`results/K6-2.json`)

Prior art: partial prior art (answer: `prior-art/R4.md`)

### Provenance

- run: 20261019-1400
- claim: K6
- author: r2 (codex)
- round: 1
- run-folder commit: 24c2a64bf8b8cb8be184b4d449ce11068d8270ea
- check results: K6-2.json

## K11

For all $n,m\ge0$, $C_n=\neg P_n(p)$ goes straight and $B_m=P_m(\neg p)$ swerves against it at every height, where $P_k(a)=\Box(\Box^k\bot\lor a)$. The mixed pair always yields Chicken payoffs $(4,1)$, independent of grades (Lean).

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K11-mixed_graded.py`: Lean proves mixed\_all for all natural indices/heights and every solution, with no axioms; boxed-formula bridge; 25 GLS cells and 10240 recurrence cells pass; false conclusion rejected. — pass (`results/K11-1.json`)

Prior art: partial prior art (answer: `prior-art/R4.md`)

### Provenance

- run: 20261019-1400
- claim: K11
- author: r2 (codex)
- round: 3
- run-folder commit: 24c2a64bf8b8cb8be184b4d449ce11068d8270ea
- check results: K11-1.json

## K12

For $H_{a,b}=\neg P_a(p)\land P_b(p)$, $P_a(z)=\Box(\Box^a\bot\lor z)$, all $a<b,c<d$ give eventual mutual action 1 iff $a=c$, else mutual action 2. Every pairing with $P_e(p)$ eventually gives mutual action 2, for all $e$ (Lean).

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K12-hobson_grades.py`: 100 generalized Hobson pair cells plus 50 graded FairBot cells; both fixed-point equations GL-proved per cell, flipped candidates rejected. — pass (`results/K12-1.json`)
- check `checks/K12-hobson_all_indices.py`: Copied another researcher proof: Lean hob\_eq, hob\_tail, hob\_fair for all indices, boxed bridge, no sorryAx; two false variants rejected; 7098 recurrence cells. — pass (`results/K12-2.json`)

Prior art: partial prior art (answer: `prior-art/R4.md`)

### Provenance

- run: 20261019-1400
- claim: K12
- author: r2 (codex)
- round: 4
- run-folder commit: 24c2a64bf8b8cb8be184b4d449ce11068d8270ea
- check results: K12-1.json, K12-2.json

## Discussion

<!-- owner-discussion -->
The results depend on reading each informal definition as a specific modal formula; where a post
was ambiguous we state the formula we used, and a different reading could change the outcome.
Hobson's proposal allows other pairs of systems than the graded ones here, so the negative result
covers this graded family, not every possible instantiation.
<!-- /owner-discussion -->

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:gramstone2015chicken --> Gram\_Stone. 2015. Modal Chicken. [Link](https://www.lesswrong.com/posts/JEHRWbQub9ryiWxaD/modal-chicken)
3. <!-- cite:hobson2021modal --> Hobson, Donald. 2021. Yet More Modal Combat. [Link](https://www.lesswrong.com/posts/EPMnjRdhHNd65XpDt/yet-more-modal-combat)
4. <!-- cite:boolos1993logic --> Boolos, George. 1993. The Logic of Provability. Cambridge University Press
5. <!-- cite:solovay1976provability --> Solovay, Robert M.. 1976. Provability Interpretations of Modal Logic. Israel Journal of Mathematics

<!-- autoresearch:revisions -->
## Revisions

- 2026-10-21 — Production note: Lean proofs run inside check scripts are now described as such, separately from harness-built proofs
