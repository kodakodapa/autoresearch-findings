---
layout: post
title: "Blending self-defecting modal agents with FairBot: exact laws"
date: 2026-10-21
scholar: {"citation_title": "Blending self-defecting modal agents with FairBot: exact laws", "citation_author": "Kodakodapa", "citation_publication_date": "2026/10/21", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/blend-window-laws.html", "citation_keywords": "C046", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/blend-window-laws/paper.pdf"}
---

## Summary

<!-- owner-summary -->
## Setting

Two programs play a one-shot prisoner's dilemma, and each can read the other's source code.
Following Barasz et al. [1], a *modal agent* decides by asking what can be proved
about the opponent, written with the provability box $\Box$ of the logic GL: $p$ means "the
opponent cooperates with me" and $q$ "the opponent cooperates with DefectBot". FairBot is
$\Box p$, graded FairBots are $F_k = \Box^k p$. An agent is *unexploitable* if no modal opponent
ever ends up defecting while the agent cooperates. Outcomes are computed in the height semantics:
a game is a sequence of moves at heights $0, 1, 2, \dots$, and its result is the eventual move.

Earlier findings on this site describe infinite families of unexploitable agents that cooperate
with FairBot and CooperateBot but defect against their own copy: the gate families
$V_{n,r} = \Box(\Box^n\bot \vee (p \wedge (q \vee \neg\Box^r q)))$, with $W_n = V_{n,1}$, and
$J_{a,b,j} = \Box^{a+1}(\Box^b p \wedge (q \vee \Box(\Box^j\bot \vee \neg q)))$. Here we ask what
happens when such an agent is *blended* with another agent X: a formula $\sigma_S$ without atoms
picks out a set $S$ of heights (finite, or all but finitely many), and the blend plays like X at
the heights in $S$ and like the family member elsewhere. X is FairBot, a graded FairBot,
DefectBot or CooperateBot.

## Result

- **FairBot-type blends.** For a graded-FairBot blend with finitely many selected heights:
  - a $W_n$ blend cooperates with itself exactly when $S$ meets $\{k, \dots, n-1\}$;
  - a $J_{a,b,j}$ blend exactly when $k \le j$ and $S$ contains all of $\{j, \dots, a+b\}$;
  - for $V_{n,r}$ the condition is a window determined by the blend's DefectBot trace, and it is
    not monotone: for $V_{3,2}$, selecting height 2 makes the blend cooperate with itself, while
    selecting heights 2 and 3 does not.

  All these blends stay unexploitable and keep cooperating with FairBot and CooperateBot.
- **DefectBot blends.** Playing DefectBot at even one height rules out mutual cooperation with
  FairBot and with every $F_k$, because an agent ends in mutual cooperation with $F_k$ exactly
  when it cooperates at every height of that game. A DefectBot blend of $W_n$ still cooperates
  with itself exactly when $S$ is a non-empty subset of $\{0, \dots, n-1\}$; for $J_{a,b,j}$
  never.
- **CooperateBot blends** cooperate with themselves only when CooperateBot is played at all but
  finitely many heights, and then DefectBot exploits them.
- **Not FairBot in disguise.** For finitely many selected heights, a single graded FairBot
  ($F_{j+1}$ for $J$, $F_{\max(1,n-r+1)}$ for $V$) behaves differently against the blend than
  against FairBot or any $\Box^m p$. A blend selecting all but finitely many heights behaves
  exactly like FairBot only in the trivial case (FairBot at every height from 1 on); otherwise an
  explicit opponent tells them apart.

## Why it matters

Unexploitable agents that defect against themselves seem to sit far from FairBot, which
cooperates with itself. These laws say exactly how much FairBot behaviour, and at which heights,
is needed to restore self-cooperation without losing safety, and they give an infinite supply of
unexploitable self-cooperating agents that are provably not FairBot.

## Proved vs checked

All laws are proved for all indices in Lean 4, in the height semantics of closed GL fixed points;
the link to provability in arithmetic is Solovay's theorem [2], cited, not
formalised (see also [3]). Finite grids of cases were also checked independently
by GL fixed-point solving with certificates.
<!-- /owner-summary -->

We believe this result is new. Our prior-art search (2026-10-21) covered:

- Barasz, LaVictoire, Christiano, Fallenstein, Herreshoff, Yudkowsky, "Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic" (arXiv 1401.5577): unexploitability (Section 2), rank and Theorem 4.10 (Section 4), WaitFairBot_K and the obstacle theorem (Section 5).
- LessWrong, "Is there only one FairBot?" (transhumanist_atom_understander, 29 Aug 2026) and comments: Zac Hatfield-Dodds shows the uniqueness conjecture holds up to modal depth 1 for rank-0 agents and fails from depth 2 (Box Box p; FairBot over PA+1 = Box(p or Box False); Box^k p for k >= 3); PrudentBot separates Box Box p from FairBot; the author notes Box Box p is not provably unexploitable in PA. No enumeration or counts.
- LessWrong / Alignment Forum wiki "Modal combat": DefectBot, CooperateBot, FairBot, PrudentBot, CliqueBot, TrollBot; no uniqueness result, no enumeration.
- LaVictoire et al. 2014 (MIPC); comment thread on "Robust Cooperation in the Prisoner's Dilemma" (LessWrong, on instability of FairBot equilibria); Hobson, "Yet More Modal Combat" (2021); Critch, parametric bounded Löb (arXiv 1602.04184); Critch, Dennis & Russell (arXiv 2208.07006); MIRI provability repository (github.com/machine-intelligence/provability, a modal-agent evaluator, no published census).
- Out of scope by direction: probabilistic blends (Oesterheld arXiv 2211.05057; Cooper et al. arXiv 2412.14570).
- Web searches for deterministic blends, behavioural distance and classifications of modal agents (2026-10-20/21); none means not found in this search.

We found no earlier statement of it, but we can't be certain. If you know of prior work, please open an issue.

This result extends Barasz et al. (arXiv 1401.5577): FairBot, the height guards of WaitFairBot_K, and the evaluation of modal agents on linear GL frames; Boolos, The Logic of Provability (1993): semantics of GL; Our earlier published findings on W_n and the gate families. Our prior-art search (2026-10-21) covered:

- Barasz, LaVictoire, Christiano, Fallenstein, Herreshoff, Yudkowsky, "Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic" (arXiv 1401.5577): unexploitability (Section 2), rank and Theorem 4.10 (Section 4), WaitFairBot_K and the obstacle theorem (Section 5).
- LessWrong, "Is there only one FairBot?" (transhumanist_atom_understander, 29 Aug 2026) and comments: Zac Hatfield-Dodds shows the uniqueness conjecture holds up to modal depth 1 for rank-0 agents and fails from depth 2 (Box Box p; FairBot over PA+1 = Box(p or Box False); Box^k p for k >= 3); PrudentBot separates Box Box p from FairBot; the author notes Box Box p is not provably unexploitable in PA. No enumeration or counts.
- LessWrong / Alignment Forum wiki "Modal combat": DefectBot, CooperateBot, FairBot, PrudentBot, CliqueBot, TrollBot; no uniqueness result, no enumeration.
- LaVictoire et al. 2014 (MIPC); comment thread on "Robust Cooperation in the Prisoner's Dilemma" (LessWrong, on instability of FairBot equilibria); Hobson, "Yet More Modal Combat" (2021); Critch, parametric bounded Löb (arXiv 1602.04184); Critch, Dennis & Russell (arXiv 2208.07006); MIRI provability repository (github.com/machine-intelligence/provability, a modal-agent evaluator, no published census).
- Out of scope by direction: probabilistic blends (Oesterheld arXiv 2211.05057; Cooper et al. arXiv 2412.14570).
- Web searches for deterministic blends, behavioural distance and classifications of modal agents (2026-10-20/21); none means not found in this search.
- Boolos, The Logic of Provability (1993): GL semantics.

If you know of related work we missed, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was checked by scripts that run Lean proofs; the proof and check files are included so anyone can re-run them.

**K14.** For $n\ge2,k\ge1$, an $F_k$ height blend of $W_n$ with finite $S$ self-cooperates iff $S\cap\{k,\ldots,n-1\}\ne\varnothing$; all such blends remain unexploitable and cooperate with FairBot and CooperateBot.

- Status: derived · author check only
- Machine-checked: 3 of 3 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K6.** For $n\ge2$, a FairBot height blend of $W_n$ self-cooperates iff the first false height $t$ of its DefectBot trace satisfies $t<n$ or all $h>t$ belong to $S$; all such blends remain unexploitable.

- Status: derived · author check only
- Machine-checked: 3 of 3 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K16.** For an $F_k$ height blend of $V_{n,r}$, let $d$ be its DefectBot trace, $t$ its first false height and $E=\{g\ge n:\neg d(g),\ g<t+r\}$. Self-play cooperates iff every height above every $g\in E$ is selected; for finite $S$, iff $E=\varnothing$.

- Status: derived · author check only
- Machine-checked: 3 of 3 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K19.** For $1\le j\le a+b$ and $k\ge1$, an $F_k$ height blend of $J_{a,b,j}$ with finite $S$ self-cooperates iff $k\le j$ and $\{j,\ldots,a+b\}\subseteq S$; all such blends are unexploitable and cooperate with FairBot and CooperateBot.

- Status: derived · author check only
- Machine-checked: 3 of 3 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K9.** A DefectBot height blend of $W_n$ ($n\ge2$) self-cooperates iff $\varnothing\ne S\subseteq\{0,\ldots,n-1\}$; a CooperateBot blend self-cooperates iff $S$ is cofinite.

- Status: derived · author check only
- Machine-checked: 2 of 2 check scripts passed.
- Prior art: partial prior art

**K25.** For $r\ge1$, a DefectBot height blend of $V_{n,r}$ self-cooperates iff $S\subseteq\{0,\ldots,n-1\}$ and some $s\in S$ satisfies $s+r\le n+1$; all remain unexploitable. CooperateBot blends self-cooperate iff $S$ is cofinite, when DefectBot exploits them.

- Status: derived · author check only
- Machine-checked: 3 of 3 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K23.** For $1\le j\le a+b$, no DefectBot height blend of $J_{a,b,j}$ self-cooperates; a CooperateBot blend self-cooperates iff its selector is cofinite, and then DefectBot exploits it. Every DefectBot blend and every finite-selector CooperateBot blend is unexploitable.

- Status: derived · author check only
- Machine-checked: 3 of 3 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K28.** For every agent and $k\ge1$: it ends CC with $F_k=\Box^kp$ iff it cooperates at every height of that game. Hence any height blend that plays DefectBot at some height, whatever its other branches, never ends CC with FairBot or any $F_k$; if unexploitable, it ends DD.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

**K20.** For finite $S$, $k,m\ge1$: the $F_k$ height blend of $J_{a,b,j}$ and $F_m=\Box^m p$ cooperate at every height iff $m\le j$, else both eventually defect; so $F_{j+1}$ separates every such blend, including every self-cooperating one, from FairBot and from each $\Box^{m'}p$.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K22.** For $r,k,m\ge1$ and any $S$, the $F_k$ height blend of $V_{n,r}$ ($W_n=V_{n,1}$) and $F_m=\Box^mp$ cooperate at every height iff $m+r\le n$ or all $h>\max(n,m)$ are selected, else both eventually defect; for finite $S$, $F_{\max(1,n-r+1)}$ separates the blend from every $\Box^{m'}p$.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K24.** An $F_k$ height blend of $J_{a,b,j}$ ($k\ge1$, cofinite $S$) is FairBot-equivalent iff $k=1$ and all $h\ge1$ are selected; else $R_h(q)$ (its DefectBot trace true at $h\ge1$) or $Y_{h_0}$ (unselected $h_0\ge a+b+1$) gets CC or DC from it and DD from FairBot.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K26.** For $n,r,k\ge1$ and any finite or cofinite $S$, the $F_k$ height blend of $V_{n,r}$ ($W_n=V_{n,1}$) is FairBot-equivalent iff $k=1$ and all $h\ge1$ are selected; else, for cofinite $S$, $R_h(q)$ gets CC from it and DD from FairBot, or $Z_{n,h_0}$ gets DD from it and CC from FairBot.

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

## Discussion

The blends are a deliberately simple, deterministic way to mix agents: a formula without atoms
decides, height by height, which agent to imitate. Probabilistic mixtures of FairBot-like agents
have been studied elsewhere [4] and are not covered here. The results
are stated for the W, V and J families; whether similar window laws hold for every
self-defecting unexploitable agent is open. The use of height guards to switch behaviour goes
back to WaitFairBot in Barasz et al.

## How to verify

Run each script in `claims/blend-window-laws/checks/` with `python -I <script>`; it passes if it
exits with status 0. The results recorded in the original run are in
`claims/blend-window-laws/results/`; the full claim text is in `claims/blend-window-laws/claim.md`.

## Provenance

- run: 20261020-1600
- claims: K14, K6, K16, K19, K9, K25, K23, K28, K20, K22, K24, K26
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- K14 author: r2 (codex)
- K6 author: r2 (codex)
- K16 author: r2 (codex)
- K19 author: r2 (codex)
- K9 author: r2 (codex)
- K25 author: r2 (codex)
- K23 author: r2 (codex)
- K28 author: r1 (claude)
- K20 author: r1 (claude)
- K22 author: r1 (claude)
- K24 author: r1 (claude)
- K26 author: r1 (claude)

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:solovay1976provability --> Solovay, Robert M.. 1976. Provability Interpretations of Modal Logic. Israel Journal of Mathematics
3. <!-- cite:boolos1993logic --> Boolos, George. 1993. The Logic of Provability. Cambridge University Press
4. <!-- cite:oesterheld2022compatibility --> Oesterheld, Caspar. 2022. A Note on the Compatibility of Different Robust Program Equilibria of the Prisoner's Dilemma. [Link](https://arxiv.org/abs/2211.05057)

<!-- autoresearch:revisions -->
## Revisions

- 2026-10-21 — Production note: Lean proofs run inside check scripts are now described as such, separately from harness-built proofs
