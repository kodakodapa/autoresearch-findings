---
layout: post
title: "Families of unexploitable agents that defect against themselves"
date: 2026-10-18
scholar: {"citation_title": "Families of unexploitable agents that defect against themselves", "citation_author": "Kodakodapa", "citation_publication_date": "2026/10/18", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/gate-families.html", "citation_keywords": "C046", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/gate-families/paper.pdf"}
---

## Summary

<!-- owner-summary -->
## Setting

Two programs play a one-shot prisoner's dilemma, and each can read the other's source code.
Following Barasz et al. [1], a *modal agent* decides by asking what can be proved
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
probabilistic variants [1], [2]) all cooperate with
their own copies. These families show that defecting against oneself is not a single odd
example: it comes in several infinite families with different mechanisms (a delayed gate on
the DefectBot test in $V$, a PrudentBot-style check in $G$, $H$ and $J$). Their behaviour
against graded FairBots and PrudentBots is described by simple thresholds, and these opponents
alone do not identify an agent: distinct members can agree on all of them and need other probes
to be told apart.

## Proved vs checked

The laws for $V_{n,r}$, $G_{m,j}$ and $H_{m,j}$ (including the separations by ConBot and $S_j$)
are proved for all indices in Lean 4, in the height semantics of closed GL fixed points; the link
to provability in arithmetic is Solovay's theorem [3], cited, not
formalised (see also [4]). The statements about $J_{a,b,j}$ and $J_{1,1,1}$ are
checked, not proved: exact tables for the stated parameter ranges, with every member of size at
most 15 independently certified by GL fixed-point solving. The unexploitability of $J_{a,b,j}$ is
supported by a short argument (the agent implies $\Box^{a+b+1}p$) and randomised safety tests,
not by a proof for all indices.
<!-- /owner-summary -->

We believe this result is new. Our prior-art searches (2026-10-17 to 2026-10-18) covered:

- Barasz et al. 2014, Robust Cooperation in the Prisoner's Dilemma (arXiv 1401.5577), full text: named agents CB, DB, CliqueBot, FairBot, PrudentBot, TrollBot, JustBot, WaitFairBot_K; Theorems 3.2, 4.8, 4.10; obstacles section.
- LaVictoire et al. 2014, Program Equilibrium in the Prisoner's Dilemma via Löb's Theorem.
- LessWrong post on Barasz et al. and its comments (orthonormal, cousin_it, Will_Sawin, Karl, dankane).
- Arbital / LessWrong wiki "Modal combat".
- Garrabrant, "Prisoners' Dilemma with Costs to Modeling"; Garrabrant, "Modal SAT: Introduction" (2015).
- Mennen, "Modal Combat for games other than the prisoner's dilemma".
- Critch, Parametric Bounded Löb's Theorem and Robust Cooperation of Bounded Agents (arXiv 1602.04184), first sections.
- Searches for round-robin, tournament, replicator or ESS analyses of modal agents: only iterated-PD and FDT evolution papers (e.g. arXiv 2005.05154, no modal agents).
- github.com/machine-intelligence/provability (owner, 2026-10-18): its example agent file (target.ua) and the Haskell agent catalogue (Agents.hs) (CB, DB, FB, FB_1..5, TbF_1..3, FB_r, MB, WB, WB_2, aMB, sMB, IB, PB, PB_2, PB_3, NB, JB, TB, QB_1..3, modal UDT). Evaluated in height semantics (our reading of its [k] and boxk notation as PA+k provability): none of them defects against itself while cooperating with FairBot and CooperateBot; none has the form of V, G, H or J.
- Barasz et al. 2014 (arXiv 1401.5577), full text; LaVictoire et al. 2014 (Program Equilibrium via Löb's Theorem).
- LessWrong post on Barasz et al. and comments; Arbital "Modal combat".
- Garrabrant, "Prisoners' Dilemma with Costs to Modeling" and "Modal SAT: Introduction"; Mennen, "Modal Combat for games other than the prisoner's dilemma".
- Critch, Parametric Bounded Löb (arXiv 1602.04184), first sections.
- Oesterheld 2022, A Note on the Compatibility of Different Robust Program Equilibria of the Prisoner's Dilemma (arXiv 2211.05057).

We found no earlier statement of it, but we can't be certain. If you know of prior work, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was partly proved in Lean (claims K14, K18, K21) and partly checked by script (claims K20, K22, K23); the proof and check files are included so anyone can re-run them.

**K14.** `For all n>=0, r>=1, k>=1, j>=0 (height semantics of closed GL fixed points), V_{n,r}=[]([]^nF|(p&(q|~[]^r q))): CC with F_k iff k+r<=n; with P_j iff r<n<j; any two V's defect. For r<n each is universally unexploitable, all pairwise distinct. Lean.`

- Status: derived
- Machine-checked: 2 of 2 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K18.** `For all m>=j>=1 (height semantics of closed GL fixed points), G_{m,j}=[]([]^m p&(q|[]([]^jF|~q))), size m+j+10, is unexploitable, coops with FB and CB, defects vs itself; CC with F_k iff k<=j, P_i iff i>m; defects vs ~[]F unlike every V_{n,r} with n>=1. Lean.`

- Status: derived
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K20.** `For all H_{m,j}=box^{m+1}(p&(q|box(box^j F|~q))), 1<=j<=m, size m+j+10<=15 (six agents), self-play is DD, FB/CB CC; CC with F_k iff k<=j (k<=4), P_i iff i>m (i<=5). GLS certifies 102 cells including separators from matching G and bounded V.`

- Status: derived
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K21.** `For m>=1, j>=1 (height semantics of closed GL fixed points), H_{m,j}=[]^{m+1}(p&(q|[]([]^jF|~q))) is unexploitable; DB trace h<=m; CC with F_k iff k<=j, P_i iff i>m; H vs H defect (j<=m); S_j=[]^{j+1}(p|~[]^{j+1}q) gives D/C vs H_{m,j}, D/D vs G_{m,j}. Lean.`

- Status: derived
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K22.** `In L, the size-13 agent J=[][]([]p&(q|[]([]F|~q))) has self DD and FB/CB CC. Its F1..4/P0..5 outcomes match G21 and H21, but two size<=9 opponents distinguish all three; all 48 stated cells are GLS-certified.`

- Status: derived
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K23.** For $J_{a,b,j}=\Box^{a+1}(\Box^b p\wedge(q\vee\Box(\Box^jF\vee\neg q)))$, $0\le a,b\le5$, $1\le j\le6$: CC with $F_k$ ($k\le9$) iff $k\le j$, $P_i$ ($i\le9$) iff $i>a+b$; vs $S_{u,t}$ ($u,t\le8$): CC if $u\le j$, else D/C iff $t+b\le u$, else DD. The 70 with $j\le a+b\le5$ are distinct.

- Status: derived
- Machine-checked: 2 of 2 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

## How to verify

Run each script in `claims/gate-families/checks/` with `python -I <script>`; it passes if it
exits with status 0. The results recorded in the original run are in
`claims/gate-families/results/`; the full claim text is in `claims/gate-families/claim.md`.

## Provenance

- run: 20261017-1126
- claims: K14, K18, K20, K21, K22, K23
- run-folder commit: 662166ecff0651902cc5fcb04bf747c62d795af2
- K14 author: r1 (claude)
- K18 author: r1 (claude)
- K20 author: r2 (codex)
- K21 author: r1 (claude)
- K22 author: r2 (codex)
- K23 author: r1 (claude)

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:oesterheld2022compatibility --> Oesterheld, Caspar. 2022. A Note on the Compatibility of Different Robust Program Equilibria of the Prisoner's Dilemma. [Link](https://arxiv.org/abs/2211.05057)
3. <!-- cite:solovay1976provability --> Solovay, Robert M.. 1976. Provability Interpretations of Modal Logic. Israel Journal of Mathematics
4. <!-- cite:boolos1993logic --> Boolos, George. 1993. The Logic of Provability. Cambridge University Press
