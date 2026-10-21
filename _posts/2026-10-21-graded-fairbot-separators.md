---
layout: post
title: "How large must a program be to tell graded FairBots apart?"
date: 2026-10-21
scholar: {"citation_title": "How large must a program be to tell graded FairBots apart?", "citation_author": "Kodakodapa", "citation_publication_date": "2026/10/21", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/graded-fairbot-separators.html", "citation_keywords": "C046", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/graded-fairbot-separators/paper.pdf"}
---

## Summary

<!-- owner-summary -->
## Setting

Two programs play a one-shot prisoner's dilemma, and each can read the other's source code.
Following Barasz et al. [1], a *modal agent* decides by asking what can be proved
about the opponent, written with the provability box $\Box$ of the logic GL: $p$ means "the
opponent cooperates with me" and $q$ "the opponent cooperates with DefectBot". Graded FairBots
are $F_k = \Box^k p$ ($F_1$ is FairBot). They are all unexploitable and cooperate with themselves
and with each other, and a LessWrong discussion [2] lists them among the agents
that share these properties with FairBot without being FairBot. We take guarded formulas built
from $p$, $q$, $\bot$, $\neg$, $\wedge$, $\vee$, $\Box$ and measure size as the number of nodes. An
opponent *separates* two agents if it gets a different outcome against them.

## Result

- **Smallest separators.** Every opponent that separates $F_k$ from $F_{k+1}$ has size at least
  $k+5$, and the only one of size $k+5$ is $S_k = \Box(\neg q \vee \Box^k\bot)$ (up to the order
  of the disjuncts): it cooperates with $F_k$ and mutually defects with $F_{k+1}$. Without $q$ the
  minimum is $k+6$, attained by $T_k = \neg\Box(\neg p \vee \Box^k\bot)$.
- **Depth.** Every opponent of modal depth at most $k$ gets the same outcome against $F_k$ and
  $F_{k+1}$, so a separator needs depth at least $k+1$; $S_k$ and $T_k$ show this is tight.
- **Ingredients.** An opponent with no negation, or with no $\wedge$/$\vee$, gets the same outcome
  against every graded FairBot; without $q$ the same holds for every boxed opponent and every
  opponent with at most one negation and at most one binary connective.

## Why it matters

Graded FairBots look alike: each is unexploitable, cooperates with itself and with every other
graded FairBot. These results say exactly how complex a program must be to tell two neighbouring
ones apart, and that the cost grows linearly with the grade.

## Proved vs checked

All statements are proved for every $k$ in Lean 4, in the height semantics of closed GL fixed
points; the link to provability in arithmetic is Solovay's theorem [3],
cited, not formalised (see also [4]). The uniqueness of $T_k$ among $q$-free
separators of size $k+6$ is proved only for $k \le 22$, by exhaustive search; the lower bound
$k+6$ holds for all $k$.
<!-- /owner-summary -->

We believe this result is new. Our prior-art search (2026-10-21) covered:

- Barasz, LaVictoire, Christiano, Fallenstein, Herreshoff, Yudkowsky, "Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic" (arXiv 1401.5577): unexploitability (Section 2), rank and Theorem 4.10 (Section 4), WaitFairBot_K and the obstacle theorem (Section 5).
- LessWrong, "Is there only one FairBot?" (transhumanist_atom_understander, 29 Aug 2026) and comments: Zac Hatfield-Dodds shows the uniqueness conjecture holds up to modal depth 1 for rank-0 agents and fails from depth 2 (Box Box p; FairBot over PA+1 = Box(p or Box False); Box^k p for k >= 3); PrudentBot separates Box Box p from FairBot; the author notes Box Box p is not provably unexploitable in PA. No enumeration or counts.
- LessWrong / Alignment Forum wiki "Modal combat": DefectBot, CooperateBot, FairBot, PrudentBot, CliqueBot, TrollBot; no uniqueness result, no enumeration.
- LaVictoire et al. 2014 (MIPC); comment thread on "Robust Cooperation in the Prisoner's Dilemma" (LessWrong, on instability of FairBot equilibria); Hobson, "Yet More Modal Combat" (2021); Critch, parametric bounded Löb (arXiv 1602.04184); Critch, Dennis & Russell (arXiv 2208.07006); MIRI provability repository (github.com/machine-intelligence/provability, a modal-agent evaluator, no published census).
- Out of scope by direction: probabilistic blends (Oesterheld arXiv 2211.05057; Cooper et al. arXiv 2412.14570).
- Web searches for deterministic blends, behavioural distance and classifications of modal agents (2026-10-20/21); none means not found in this search.

We found no earlier statement of it, but we can't be certain. If you know of prior work, please open an issue.

This result extends Blackburn, de Rijke & Venema, Modal Logic (2001); "Is there only one FairBot?" (LessWrong, 2026). Our prior-art search (2026-10-21) covered:

- Barasz, LaVictoire, Christiano, Fallenstein, Herreshoff, Yudkowsky, "Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic" (arXiv 1401.5577): unexploitability (Section 2), rank and Theorem 4.10 (Section 4), WaitFairBot_K and the obstacle theorem (Section 5).
- LessWrong, "Is there only one FairBot?" (transhumanist_atom_understander, 29 Aug 2026) and comments: Zac Hatfield-Dodds shows the uniqueness conjecture holds up to modal depth 1 for rank-0 agents and fails from depth 2 (Box Box p; FairBot over PA+1 = Box(p or Box False); Box^k p for k >= 3); PrudentBot separates Box Box p from FairBot; the author notes Box Box p is not provably unexploitable in PA. No enumeration or counts.
- LessWrong / Alignment Forum wiki "Modal combat": DefectBot, CooperateBot, FairBot, PrudentBot, CliqueBot, TrollBot; no uniqueness result, no enumeration.
- LaVictoire et al. 2014 (MIPC); comment thread on "Robust Cooperation in the Prisoner's Dilemma" (LessWrong, on instability of FairBot equilibria); Hobson, "Yet More Modal Combat" (2021); Critch, parametric bounded Löb (arXiv 1602.04184); Critch, Dennis & Russell (arXiv 2208.07006); MIRI provability repository (github.com/machine-intelligence/provability, a modal-agent evaluator, no published census).
- Out of scope by direction: probabilistic blends (Oesterheld arXiv 2211.05057; Cooper et al. arXiv 2412.14570).
- Blackburn, de Rijke & Venema, Modal Logic (2001): n-bisimulation and modal depth.
- Web searches for deterministic blends, behavioural distance and classifications of modal agents (2026-10-20/21); none means not found in this search.

If you know of related work we missed, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the proof and check files are included so anyone can re-run them.

**K49.** For all $k\ge1$, every guarded separator of $F_k=\Box^kp$ and $F_{k+1}$ has size $\ge k+5$, and every size-$(k+5)$ one is $S_k=\Box(\neg q\vee\Box^k\bot)$ up to disjunct order (CC with $F_k$, DD with $F_{k+1}$).

- Status: derived · author check only
- Machine-checked: 7 of 7 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K56.** For all $k\ge1$, every $q$-free guarded separator of $F_k=\Box^kp$ and $F_{k+1}$ has size $\ge k+6$, attained by $T_k=\neg\Box(\neg p\lor\Box^k\bot)$ (DD with $F_k$, exploited by $F_{k+1}$); for $k\le22$ every size-$(k+6)$ one is $T_k$ up to disjunct order.

- Status: derived · author check only
- Machine-checked: 4 of 4 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K58.** For every $k\ge1$, every guarded opponent $O$ in $p,q$ of modal depth $\le k$ gets the same eventual outcome against $F_k=\Box^kp$ and $F_{k+1}$; so every separator has depth $\ge k+1$ (size $\ge k+2$), tight for $S_k$ (K49) and $T_k$ (K56).

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: partial prior art

**K59.** For guarded $O$ in $p,q$ with no negation, or with no $\land/\lor$, and all $j,j'\ge1$: $O$ gets the same eventual outcome against $F_j=\Box^jp$ and $F_{j'}$ (Lean, height semantics).

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

**K60.** In $L$ without $q$ (guarded), every boxed opponent $\Box W$, and every opponent with at most one $\neg$ and at most one $\land/\lor$, gets the same eventual outcome against $F_j=\Box^jp$ and $F_{j'}$ for all $j,j'\ge1$ (Lean, height semantics).

- Status: derived · author check only
- Machine-checked: 1 of 1 check scripts passed.
- Prior art: possibly new: no prior art found in the owner's search

## Discussion

The depth bound uses the standard back-and-forth (n-bisimulation) method of modal logic
[5]; the new part is its application to games between modal agents. The
results concern separating graded FairBots from each other; how large a separator must be for
other pairs of agents (for example the gate-family members of earlier findings) is open, as is a
numerical bound on separator size at fixed modal depth.

## How to verify

Run each script in `claims/graded-fairbot-separators/checks/` with `python -I <script>`; it passes if it
exits with status 0. The results recorded in the original run are in
`claims/graded-fairbot-separators/results/`; the full claim text is in `claims/graded-fairbot-separators/claim.md`.

## Provenance

- run: 20261020-1600
- claims: K49, K56, K58, K59, K60
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- K49 author: r1 (claude)
- K56 author: r1 (claude)
- K58 author: r1 (claude)
- K59 author: r1 (claude)
- K60 author: r1 (claude)

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:onlyonefairbot2026 --> transhumanist\_atom\_understander. 2026. Is there only one FairBot?. [Link](https://www.lesswrong.com/posts/auAq7Rcstop3FBEob/is-there-only-one-fairbot)
3. <!-- cite:solovay1976provability --> Solovay, Robert M.. 1976. Provability Interpretations of Modal Logic. Israel Journal of Mathematics
4. <!-- cite:boolos1993logic --> Boolos, George. 1993. The Logic of Provability. Cambridge University Press
5. <!-- cite:blackburn2001modal --> Blackburn, Patrick and de Rijke, Maarten and Venema, Yde. 2001. Modal Logic. Cambridge University Press
