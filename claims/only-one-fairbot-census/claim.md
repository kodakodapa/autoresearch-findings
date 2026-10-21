# Unexploitable modal agents that cooperate with themselves: a census

<!-- owner-summary -->
## Setting

Two programs play a one-shot prisoner's dilemma, and each can read the other's source code.
Following Barasz et al. [1], a *modal agent* decides by asking what can be proved
about the opponent, written with the provability box $\Box$ of the logic GL: $p$ means "the
opponent cooperates with me" and $q$ "the opponent cooperates with DefectBot". FairBot is
$\Box p$: it cooperates exactly when it can prove that the opponent cooperates with it. An agent
is *unexploitable* if no modal opponent ever ends up defecting while the agent cooperates, and
*self-cooperating* if two copies cooperate. We take guarded formulas (every atom under a box)
built from $p$, $q$, $\bot$, $\neg$, $\wedge$, $\vee$, $\Box$, measure size as the number of
nodes, and call two agents behaviourally equal when they make the same moves against every
opponent. Agents using only $p$ are the rank-0 agents of Barasz et al.

A LessWrong post [2] asked whether every rank-0 agent that is unexploitable and
self-cooperating is FairBot. A comment there shows that the answer is yes up to modal depth 1 and
no from depth 2, with examples such as $\Box\Box p$, FairBot over PA+1 and $\Box^k p$.

## Result

- **Rank 0.** Among rank-0 agents of size at most 15 there are exactly 5031 classes that are
  unexploitable and self-cooperating (4374 of them also cooperate with FairBot and CooperateBot).
  Only $\Box p$ itself is FairBot; every other class is told apart from FairBot by an explicit
  opponent.
- **With $q$.** Allowing $q$, up to size 14 there are 26449 such classes (16756 up to behaviour);
  387 of them behave exactly like FairBot against every opponent, and each of the others is told
  apart from FairBot by an explicit opponent.
- **Why some different formulas are FairBot.** Two agents behave identically against every
  opponent exactly when they have the same moves against DefectBot and agree on every input the
  opponent can actually produce: until the agent first cooperates, the opponent's move against it
  equals its move against DefectBot. So, for example, $\Box(p \vee (q \wedge \Box\bot))$ is
  behaviourally FairBot.
- **A small example that is not FairBot.** $\neg\Box\bot \wedge \Box(p \vee \Box\bot)$ (size 9)
  is unexploitable and cooperates with itself and with CooperateBot, yet mutually defects with
  FairBot; it is the agent WaitFairBot$_1$ of Barasz et al. Every smaller rank-0 agent that is
  unexploitable and self-cooperating cooperates with FairBot.

## Why it matters

The LessWrong question was answered with a few examples. These counts make the answer
quantitative: among small agents, FairBot is one of thousands of unexploitable self-cooperators,
and for each one there is a concrete opponent that tells it apart from FairBot. The criterion for
behavioural equality explains which syntactically different agents are nevertheless FairBot.

## Proved vs checked

The equality criterion and the FairBot-equivalence of $\Box(p \vee (q \wedge \Box\bot))$ are
proved in Lean 4, in the height semantics of closed GL fixed points; the link to provability in
arithmetic is Solovay's theorem [3], cited, not formalised (see also
[4]). The counts are exhaustive computations up to the stated sizes, with every
separating opponent recorded and re-solved by the checks. The minimality statement for the size-9
agent is an exhaustive search over smaller rank-0 agents.
<!-- /owner-summary -->

This result extends Barasz et al. (arXiv 1401.5577): modal agents, unexploitability, rank, and WaitFairBot_K; "Is there only one FairBot?" (LessWrong, 2026), with Zac Hatfield-Dodds's comment answering it to modal depth 1 and giving examples. Our prior-art search (2026-10-21) covered:

- Barasz, LaVictoire, Christiano, Fallenstein, Herreshoff, Yudkowsky, "Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic" (arXiv 1401.5577): unexploitability (Section 2), rank and Theorem 4.10 (Section 4), WaitFairBot_K and the obstacle theorem (Section 5).
- LessWrong, "Is there only one FairBot?" (transhumanist_atom_understander, 29 Aug 2026) and comments: Zac Hatfield-Dodds shows the uniqueness conjecture holds up to modal depth 1 for rank-0 agents and fails from depth 2 (Box Box p; FairBot over PA+1 = Box(p or Box False); Box^k p for k >= 3); PrudentBot separates Box Box p from FairBot; the author notes Box Box p is not provably unexploitable in PA. No enumeration or counts.
- LessWrong / Alignment Forum wiki "Modal combat": DefectBot, CooperateBot, FairBot, PrudentBot, CliqueBot, TrollBot; no uniqueness result, no enumeration.
- LaVictoire et al. 2014 (MIPC); comment thread on "Robust Cooperation in the Prisoner's Dilemma" (LessWrong, on instability of FairBot equilibria); Hobson, "Yet More Modal Combat" (2021); Critch, parametric bounded Löb (arXiv 1602.04184); Critch, Dennis & Russell (arXiv 2208.07006); MIRI provability repository (github.com/machine-intelligence/provability, a modal-agent evaluator, no published census).
- Out of scope by direction: probabilistic blends (Oesterheld arXiv 2211.05057; Cooper et al. arXiv 2412.14570).
- Web searches for deterministic blends, behavioural distance and classifications of modal agents (2026-10-20/21); none means not found in this search.

If you know of related work we missed, please open an issue.

We believe this result is new. Our prior-art search (2026-10-21) covered:

- Barasz, LaVictoire, Christiano, Fallenstein, Herreshoff, Yudkowsky, "Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic" (arXiv 1401.5577): unexploitability (Section 2), rank and Theorem 4.10 (Section 4), WaitFairBot_K and the obstacle theorem (Section 5).
- LessWrong, "Is there only one FairBot?" (transhumanist_atom_understander, 29 Aug 2026) and comments: Zac Hatfield-Dodds shows the uniqueness conjecture holds up to modal depth 1 for rank-0 agents and fails from depth 2 (Box Box p; FairBot over PA+1 = Box(p or Box False); Box^k p for k >= 3); PrudentBot separates Box Box p from FairBot; the author notes Box Box p is not provably unexploitable in PA. No enumeration or counts.
- LessWrong / Alignment Forum wiki "Modal combat": DefectBot, CooperateBot, FairBot, PrudentBot, CliqueBot, TrollBot; no uniqueness result, no enumeration.
- LaVictoire et al. 2014 (MIPC); comment thread on "Robust Cooperation in the Prisoner's Dilemma" (LessWrong, on instability of FairBot equilibria); Hobson, "Yet More Modal Combat" (2021); Critch, parametric bounded Löb (arXiv 1602.04184); Critch, Dennis & Russell (arXiv 2208.07006); MIRI provability repository (github.com/machine-intelligence/provability, a modal-agent evaluator, no published census).
- Out of scope by direction: probabilistic blends (Oesterheld arXiv 2211.05057; Cooper et al. arXiv 2412.14570).
- Web searches for deterministic blends, behavioural distance and classifications of modal agents (2026-10-20/21); none means not found in this search.

We found no earlier statement of it, but we can't be certain. If you know of prior work, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was partly proved in Lean (claims K11, K18) and partly checked by script (claims K51, K53, K2); the proof and check files are included so anyone can re-run them.

## K51

In rank-0 $L$ (atom $p$, guarded, size $\le15$) exactly 5031 classes are unexploitable and self-cooperating, 4374 of them cooperating with FairBot and CooperateBot; only $\Box p$ is FairBot, every other one is separated from it by an explicit opponent.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K51-c046_ponly15.py`: guarded p-only class counts per size 1..15; 15092 exploitable self-cooperators each exploited by a re-solved letterless opponent; 5031 unexploitable self-cooperators (per-size list); 5030 non-FB each separated from \[\]p by a constructed re-solved opponent; FB-defecting 4,8,16,33,80,171,345 (sizes 9..15), CB-defecting 2,4,8,16,41,87,181, FB&CB-cooperating 4374; depth-1 reproduction; K1 prefix counts — pass (`results/K51-1.json`)
- check `checks/K51-c046_top.py`: K51 engine enumerated to size 13 with and without primitive top (size 1): guarded counts differ only at sizes 1,2; unexploitable self-cooperator counts per size identical (1202); top itself exploitable — pass (`results/K51-2.json`)
- reasoning: Census language is bot,p,~,&,\|,box with top = ~bot (size 2). Top is absorbed in every context (~T=F smaller, \[\]T=T, T&x=x, T\|x=T), so a primitive top moves only the exploitable class T; counts of unexploitable self-cooperators are unchanged at every size bound and for any atom set.

Prior art: partial prior art (answer: `prior-art/R57.md`)

### Provenance

- run: 20261020-1600
- claim: K51
- author: r1 (claude)
- round: 35
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K51-1.json, K51-2.json

## K53

In $L$ with atoms $p,q$ (guarded, size $\le14$), 26449 machine classes (16756 behaviour classes) are unexploitable and self-cooperating; 387 of them behave as FairBot, and each other one gets a different outcome than FairBot against an explicit opponent.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K53-c046_qfull14.py`: guarded class counts 1..14 (279115 at 14); 249390 self-cooperators, 222941 exploited by re-solved explicit opponents; 26449 unexploitable (per-size list), 16756 behaviour classes; FairBot class 387 machine classes with per-size list; 26062 others separated from \[\]p by re-solved opponents; rank-0 2468 (=K51 prefix); 1058 not CC with FB (smallest size 9), 15306 CC with FB and CB; literal evaluator cross-check — pass (`results/K53-1.json`)

Prior art: partial prior art (answer: `prior-art/R58.md`)

### Provenance

- run: 20261020-1600
- claim: K53
- author: r1 (claude)
- round: 39
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K53-1.json

## K11

$X=\Box(p\vee(q\wedge\Box\bot))$ (size 7) has the same moves as FairBot $\Box p$ at every height against every modal opponent, since an opponent's height-0 move against any agent equals its move against DefectBot.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K11-c046_xfb_lean.py`: Lean 4 core theorem X\_same\_as\_FairBot for every causal opponent operator (fixed points coincide at all heights), no sorryAx; 3 mutations rejected — pass (`results/K11-1.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R37.md`)

### Provenance

- run: 20261020-1600
- claim: K11
- author: r1 (claude)
- round: 3
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K11-1.json

## K18

For causal agents $A,A'$ in height semantics: they make the same moves in every game against every causal opponent iff their DefectBot traces are equal and they agree on all realizable words ($p=q$ up to the first cooperation of $A$ or its DefectBot trace).

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K18-c046_realizable_lean.py`: Lean 4 core theorems game\_exists, inputs\_realizable, same\_behaviour, separation, behaviour\_iff, X\_beheq\_FB; SHA-pinned source; no sorryAx; 4 mutations rejected — pass (`results/K18-1.json`)
- check `checks/K18-c046_qfull12.py`: behav() realizable-word machines: 2574 classes, FairBot class has 86 machine classes with identical realizable-word machine to \[\]p (consequence: FairBot behaviour against every opponent via same\_behaviour) — pass (`results/K18-2.json`)
- reasoning: In any game the opponent's inputs are all-false until the agent or its DefectBot trace cooperates, so by causality its play equals its DefectBot play there; hence inputs are realizable, and by induction equal realizable behaviour gives equal games.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R38.md`)

### Provenance

- run: 20261020-1600
- claim: K18
- author: r1 (claude)
- round: 7
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K18-1.json, K18-2.json

## K2

$A=\neg\Box\bot\wedge\Box(p\vee\Box\bot)$ (size 9) is unexploitable by every modal opponent, cooperates with its copy and with CooperateBot, yet mutually defects with FairBot; every rank-0 unexploitable self-cooperator of size $\le 8$ cooperates with FairBot.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K2-c046_ponly12.py`: A and ~\[\]p&\[\](p\|\[\]F) are among the 591 unexploitable self-cooperators, A vs A = CC, A vs \[\]p = DD, A vs ~F = CC; all such agents not cooperating with FB have size \>= 9 — pass (`results/K2-1.json`)
- reasoning: Height semantics: A(0)=F, A(h)=AND of p(g) over 1\<=g\<h; self-play all C from height 1; vs FairBot FB(1)=A(0)=F forces DD from height 2; opponent tail D forces A tail D.

Prior art: partial prior art (answer: `prior-art/R59.md`)

### Provenance

- run: 20261020-1600
- claim: K2
- author: r1 (claude)
- round: 1
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K2-1.json

## Discussion

<!-- owner-discussion -->
The counts depend on the agent language and the size measure; they say how common
non-FairBot unexploitable self-cooperators are among small formulas, not in any absolute sense.
"Unexploitable" is about what actually happens in play (truth in the standard model, as in Barasz
et al.), not about what Peano arithmetic can prove about the agent; the LessWrong discussion
points out that the two differ. Open questions: how the counts grow with size, and whether the
non-FairBot classes fall into a small number of families.
<!-- /owner-discussion -->

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:onlyonefairbot2026 --> transhumanist\_atom\_understander. 2026. Is there only one FairBot?. [Link](https://www.lesswrong.com/posts/auAq7Rcstop3FBEob/is-there-only-one-fairbot)
3. <!-- cite:solovay1976provability --> Solovay, Robert M.. 1976. Provability Interpretations of Modal Logic. Israel Journal of Mathematics
4. <!-- cite:boolos1993logic --> Boolos, George. 1993. The Logic of Provability. Cambridge University Press
