---
layout: default
title: "How large must a program be to tell graded FairBots apart?"
scholar: {"citation_title": "How large must a program be to tell graded FairBots apart?", "citation_author": "Lindheim, Bj\u00f6rn", "citation_publication_date": "2026/10/21", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/findings/graded-fairbot-separators.html", "citation_keywords": "C046", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/claims/graded-fairbot-separators/paper.pdf"}
---

# How large must a program be to tell graded FairBots apart?

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

This result was found by AI research agents (the autoresearch harness). It was checked by scripts that run Lean proofs; the proof and check files are included so anyone can re-run them.

## K49

For all $k\ge1$, every guarded separator of $F_k=\Box^kp$ and $F_{k+1}$ has size $\ge k+5$, and every size-$(k+5)$ one is $S_k=\Box(\neg q\vee\Box^k\bot)$ up to disjunct order (CC with $F_k$, DD with $F_{k+1}$).

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K49-c046_fk_sep.py`: Lean 4 core sizes, sk\_ev, sep\_coop (j\<=k CC all heights), sep\_defect (j\>k), fk\_fk, separator (all k; SHA-pinned, no sorryAx, 4 mutations rejected); exact engine over guarded classes of size \<=11: k=1..6 no separator of size \<=k+4, unique S\_k at size k+5, k=7,8 none \<=11; literal evaluator S\_k vs F\_j CC iff j\<=k for k\<=10, j\<=12 — pass (`results/K49-1.json`)
- check `checks/K49-c046_fk_sep13.py`: guarded class counts 1..13 (36062, 100823 at 12, 13); exact engine k=1..8: no separator of F\_k/F\_{k+1} of size \<=k+4, unique machine class S\_k at size k+5; same Lean theorems as c046\_fk\_sep.py (sizes, sep\_coop, sep\_defect, fk\_fk, separator; no sorryAx; 4 mutations rejected); literal evaluator S\_k vs F\_j CC iff j\<=k — pass (`results/K49-2.json`)
- check `checks/K49-c046_fk_sep14.py`: guarded class counts 1..14 (100823 at 13, 279115 at 14; guarded-only products at top size); exact engine k=1..9: no F\_k/F\_{k+1} separator of size \<=k+4, unique machine class S\_k at size k+5; Lean sizes, sep\_coop, sep\_defect, fk\_fk, separator (no sorryAx, 4 mutations rejected); literal evaluator S\_k vs F\_j CC iff j\<=k — pass (`results/K49-3.json`)
- check `checks/K49-c046_fk_size40.py`: every reduced guarded formula of depth \>=k+1: p,q sizes k+2..k+5 for k=1..40 (803710 solved), p-only sizes k+2..k+6 for k=1..22 (498344): no separator below k+5 / k+6, unique reduced separator S\_k / T\_k; full all-depth enumeration k\<=2 reproduces minima without K58; bitmask games = naive literal evaluator on 1112 games — pass (`results/K49-4.json`)
- check `checks/K49-c046_fk_depth.py`: K58 Lean same\_outcome: no guarded opponent of modal depth \<=k separates F\_k/F\_{k+1}, for every k — pass (`results/K49-5.json`)
- check `checks/K49-c046_fk_shape.py`: Lean 4 core (SHA-pinned, includes K58 development): negfree\_same (no negation: same outcome vs all F\_j,F\_j'), nobin\_same (no &/\|: same outcome vs all F\_j,F\_j', j,j'\>=1), size\_bound (k\>=1: separator has ~, binary node, md\>=k+1, size\>=k+5), sk\_size; no sorryAx; 4 mutations rejected; literal evaluator: 4333 such formulas of size\<=8 same vs F\_1..F\_5, all 414 separator cells (size\<=9, k\<=4) have ~ and a binary node — pass (`results/K49-6.json`)
- check `checks/K49-c046_fk_unique.py`: Lean 4 core unique\_sep (all k\>=1: guarded size-(k+5) separator of F\_k/F\_{k+1} is S\_k up to disjunct order), code\_same, shapeA/B/C, size\_bound, sk\_codes; SHA-pinned; no sorryAx/ofReduceBool; 4 mutations rejected; literal evaluator S\_k k\<=10 and exhaustive unreduced guarded syntax of size 6,7: only S\_1,S\_2 (both orders) separate — pass (`results/K49-7.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R52.md`)

### Provenance

- run: 20261020-1600
- claim: K49
- author: r1 (claude)
- round: 33
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K49-1.json, K49-2.json, K49-3.json, K49-4.json, K49-5.json, K49-6.json, K49-7.json

## K56

For all $k\ge1$, every $q$-free guarded separator of $F_k=\Box^kp$ and $F_{k+1}$ has size $\ge k+6$, attained by $T_k=\neg\Box(\neg p\lor\Box^k\bot)$ (DD with $F_k$, exploited by $F_{k+1}$); for $k\le22$ every size-$(k+6)$ one is $T_k$ up to disjunct order.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K56-c046_fk_psep17.py`: p-only guarded class counts 1..17 (K51 list to 15, then 35721, 74728); exact engine k=1..11: no p-only F\_k/F\_{k+1} separator of size \<=k+5, unique machine class T\_k at size k+6 with F\_k DD and F\_{k+1} (D,C); k=12 none \<=17; Lean tsize, tk\_ev, t\_low, t\_high, psep for all k (no sorryAx, 4 mutations rejected); literal evaluator k\<=12, j\<=14 — pass (`results/K56-1.json`)
- check `checks/K49-c046_fk_size40.py`: every reduced guarded formula of depth \>=k+1: p,q sizes k+2..k+5 for k=1..40 (803710 solved), p-only sizes k+2..k+6 for k=1..22 (498344): no separator below k+5 / k+6, unique reduced separator S\_k / T\_k; full all-depth enumeration k\<=2 reproduces minima without K58; bitmask games = naive literal evaluator on 1112 games — pass (`results/K49-4.json`)
- check `checks/K49-c046_fk_depth.py`: K58 Lean same\_outcome: no guarded opponent of modal depth \<=k separates F\_k/F\_{k+1}, for every k — pass (`results/K49-5.json`)
- check `checks/K56-c046_fk_psize.py`: Lean 4 core (SHA-pinned, includes K58 and K49 shape developments): stab\_box, stab\_top, pone\_same, one\_one\_same (q-free, \<=1 neg and \<=1 binary: same outcome vs all F\_j,F\_j', j,j'\>=1), psize\_bound (q-free separator of F\_k,F\_{k+1}: size \>= k+6, all k\>=1), tk\_size; no sorryAx; 4 mutations rejected; literal evaluator 8890 small and 40758 boxed q-free formulas same vs F\_1..F\_6, T\_k DD/CD k\<=6 — pass (`results/K56-4.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R53.md`)

### Provenance

- run: 20261020-1600
- claim: K56
- author: r1 (claude)
- round: 44
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K49-4.json, K49-5.json, K56-1.json, K56-4.json

## K58

For every $k\ge1$, every guarded opponent $O$ in $p,q$ of modal depth $\le k$ gets the same eventual outcome against $F_k=\Box^kp$ and $F_{k+1}$; so every separator has depth $\ge k+1$ (size $\ge k+2$), tight for $S_k$ (K49) and $T_k$ (K56).

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K49-c046_fk_depth.py`: Lean 4 core (SHA-pinned) same\_outcome for all k and guarded O with md\<=k, separator\_bound (md\>=k+1, size\>=k+2), sk\_depth=k+1; no sorryAx; 5 mutations rejected; exact engine k=1..6: no depth\<=k class of size\<=12 separates, depth k+1 control finds S\_k; literal evaluator 3200 random depth\<=k opponents, exact K40 horizon — pass (`results/K49-5.json`)

Prior art: partial prior art (answer: `prior-art/R54.md`)

### Provenance

- run: 20261020-1600
- claim: K58
- author: r1 (claude)
- round: 46
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K49-5.json

## K59

For guarded $O$ in $p,q$ with no negation, or with no $\land/\lor$, and all $j,j'\ge1$: $O$ gets the same eventual outcome against $F_j=\Box^jp$ and $F_{j'}$ (Lean, height semantics).

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K49-c046_fk_shape.py`: Lean 4 core (SHA-pinned, includes K58 development): negfree\_same (no negation: same outcome vs all F\_j,F\_j'), nobin\_same (no &/\|: same outcome vs all F\_j,F\_j', j,j'\>=1), size\_bound (k\>=1: separator has ~, binary node, md\>=k+1, size\>=k+5), sk\_size; no sorryAx; 4 mutations rejected; literal evaluator: 4333 such formulas of size\<=8 same vs F\_1..F\_5, all 414 separator cells (size\<=9, k\<=4) have ~ and a binary node — pass (`results/K49-6.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R55.md`)

### Provenance

- run: 20261020-1600
- claim: K59
- author: r1 (claude)
- round: 48
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K49-6.json

## K60

In $L$ without $q$ (guarded), every boxed opponent $\Box W$, and every opponent with at most one $\neg$ and at most one $\land/\lor$, gets the same eventual outcome against $F_j=\Box^jp$ and $F_{j'}$ for all $j,j'\ge1$ (Lean, height semantics).

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K56-c046_fk_psize.py`: Lean 4 core (SHA-pinned): stab\_box, stab\_top, pone\_same (q-free O boxed or with top-level boxes negation-free or binary-free: same outcome vs all F\_j,F\_j', j,j'\>=1), one\_one\_same (\<=1 neg, \<=1 binary), psize\_bound, tk\_size; no sorryAx; 4 mutations rejected; literal evaluator 8890 small and 40758 boxed q-free formulas same vs F\_1..F\_6 — pass (`results/K56-4.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R56.md`)

### Provenance

- run: 20261020-1600
- claim: K60
- author: r1 (claude)
- round: 49
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K56-4.json

## Discussion

<!-- owner-discussion -->
The depth bound uses the standard back-and-forth (n-bisimulation) method of modal logic
[5]; the new part is its application to games between modal agents. The
results concern separating graded FairBots from each other; how large a separator must be for
other pairs of agents (for example the gate-family members of earlier findings) is open, as is a
numerical bound on separator size at fixed modal depth.
<!-- /owner-discussion -->

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:onlyonefairbot2026 --> transhumanist\_atom\_understander. 2026. Is there only one FairBot?. [Link](https://www.lesswrong.com/posts/auAq7Rcstop3FBEob/is-there-only-one-fairbot)
3. <!-- cite:solovay1976provability --> Solovay, Robert M.. 1976. Provability Interpretations of Modal Logic. Israel Journal of Mathematics
4. <!-- cite:boolos1993logic --> Boolos, George. 1993. The Logic of Provability. Cambridge University Press
5. <!-- cite:blackburn2001modal --> Blackburn, Patrick and de Rijke, Maarten and Venema, Yde. 2001. Modal Logic. Cambridge University Press

<!-- autoresearch:revisions -->
## Revisions

- 2026-10-21 — Production note: Lean proofs run inside check scripts are now described as such, separately from harness-built proofs
