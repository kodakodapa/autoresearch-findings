# Safe modal agents that coordinate in the Stag Hunt: size 13 is the minimum

<!-- owner-summary -->
## Setting

In the Stag Hunt two players each choose stag or hare: both hunting stag pays most, hunting stag
alone pays least, and hare is a safe middle option. Here the players are programs that read each
other's source code. Following Barasz et al. [1], a *modal agent* decides by
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
is Solovay's theorem [2], cited, not formalised (see also
[3]). The non-existence below size 13 and the census counts are exhaustive
computations up to the stated sizes, with every exploiting opponent recorded and re-solved.
<!-- /owner-summary -->

We believe this result is new. Our prior-art search (2026-10-21) covered:

- Barasz, LaVictoire et al., arXiv 1401.5577.
- LessWrong / Alignment Forum wiki "Modal combat" and "Is there only one FairBot?" (2026).
- Mennen, "Modal combat for games other than the prisoner's dilemma" (2017).
- Todorov, ten Napel & Müller, "Parametric Open Source Games", arXiv 2606.27068.
- Tennenholtz (2004), program equilibrium (background).
- Web searches for modal agents in the Stag Hunt and for tournaments of modal agents (2026-10-21); none means not found in this search.

We found no earlier statement of it, but we can't be certain. If you know of prior work, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was partly proved in Lean (claims K9) and partly checked by script (claims K16, K13, K19); the proof and check files are included so anyone can re-run them.

## K16

In guarded $L$ of syntax-node size $\le12$, exactly 356 of 56,503 classes get stag/stag with self, $E_1$, and $N_1$; every one is exploited by a size-$\le10$ opponent. Hence no universally safe agent of size $\le12$ has all three coordination properties.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K16-no_safe12.py`: SHA256-pinned full enumerator; 56503 classes through size 12; independent machine and formula filters give exactly 356 self/E1/N1 candidates; each has re-solved size\<=10 exploitation witness; 362 GLS certificates. — pass (`results/K16-1.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R15.md`)

### Provenance

- run: 20261021-0517
- claim: K16
- author: r2 (codex)
- round: 7
- run-folder commit: 580565ffd3b3f1a8ca3ffa0407c949c8d724865c
- check results: K16-1.json

## K9

For all $k\ge1$, $X_k=\Box(p\lor\Box^kp)\land(\Box\bot\lor\neg\Box\neg p)$ never ends hunting stag against an eventual hare hunter, ends stag/stag with itself, FairBot and every $R_m$, $D_m$, $X_m$, with $E_j$ ($j\ge1$) iff $j\le k$ and with $N_n$ iff $n\ge1$.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K9-c046_patient_laws.py`: Lean 16 theorems (xk\_safe, xk\_self, xx/xr/xd\_pair, xk\_db, xk\_E, xk\_N, xk\_Z, xk\_modal,...), no sorryAx, false bound rejected; 452 height cells k\<=7; 12 GLS certificates; census size\<=10: 1693 safe, 517 safe self-stag, 230 SS with E\_1, 75 with N\_1, 0 with both — pass (`results/K9-1.json`)
- reasoning: Height semantics on the GL chain (box holds at h iff its argument holds at all g\<h); game tails equal standard-model actions, Lean proves laws for any traces solving the height equations.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R8.md`)

### Provenance

- run: 20261021-0517
- claim: K9
- author: r1 (claude)
- round: 3
- run-folder commit: 580565ffd3b3f1a8ca3ffa0407c949c8d724865c
- check results: K9-1.json

## K13

Among the 7561 guarded $L$ classes of syntax-node size $\le10$, exactly 1693 avoid stag/hare against every census opponent; exactly 517 of these hunt stag with themselves. These are finite-census safety counts.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K13-todorov_safety.py`: SHA256-pinned solver; all 7561-class cells re-solved; unique winner A3 at (3,0,2,1), score 16393 versus FairBot 14158; 7561 winner cells independently re-solved; 4 GLS certificates; 1693 census-safe classes, 517 self-stag. — pass (`results/K14-1.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R15.md`)

### Provenance

- run: 20261021-0517
- claim: K13
- author: r2 (codex)
- round: 5
- run-folder commit: 580565ffd3b3f1a8ca3ffa0407c949c8d724865c
- check results: K14-1.json

## K19

Of the 517 size-$\le10$ census-safe self-stag agents, exactly one is exploited by a size-$\le12$ opponent: $V=\Box(p\lor(q\land\neg\Box^3q))$, by $B=\neg\Box^2p\lor\Box(p\land\Box^2q)$ of minimum size 11. The other 516 survive this finite test.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K19-safety12.py`: Pinned full enumeration: 56503 classes; 7561-class matrix recovers 1693/517; 25303014 extension cells at exact joint fixed states; exactly V refuted, 516 survive; minimum exploiter size11; 7561 independent V row cells; exploitation and self-play GLS certificates. — pass (`results/K19-1.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R11.md`)

### Provenance

- run: 20261021-0517
- claim: K19
- author: r2 (codex)
- round: 9
- run-folder commit: 580565ffd3b3f1a8ca3ffa0407c949c8d724865c
- check results: K19-1.json

## Discussion

<!-- owner-discussion -->
The census counts are finite statements: "safe" there means safe against the agents in the census,
and tests against larger opponents can still find exploits, as they did for one agent.
The size-13 agent is safe against every modal opponent by proof. Safety is the same outcome
condition as unexploitability in the prisoner's dilemma; what changes in the Stag Hunt is which
coordination properties one wants alongside it.
<!-- /owner-discussion -->

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:solovay1976provability --> Solovay, Robert M.. 1976. Provability Interpretations of Modal Logic. Israel Journal of Mathematics
3. <!-- cite:boolos1993logic --> Boolos, George. 1993. The Logic of Provability. Cambridge University Press
