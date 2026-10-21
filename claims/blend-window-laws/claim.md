# Blending self-defecting modal agents with FairBot: exact laws

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

This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the proof and check files are included so anyone can re-run them.

## K14

For $n\ge2,k\ge1$, an $F_k$ height blend of $W_n$ with finite $S$ self-cooperates iff $S\cap\{k,\ldots,n-1\}\ne\varnothing$; all such blends remain unexploitable and cooperate with FairBot and CooperateBot.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K14-graded_self.py`: Six general Lean theorems: first-hole self-play law, DefectBot trace, first failure existence, early-hole criterion, FB and CB partners; SHA-pinned source, no sorryAx, three mutations rejected. — pass (`results/K14-1.json`)
- check `checks/K14-graded_grid.py`: 144 GL-certified cells for n2,3; k1,2,3; eight height selectors; self, FairBot, CooperateBot; wrong-candidate controls. — pass (`results/K14-2.json`)
- check `checks/K14-blend_gate.py`: General graded-FairBot blend unexploitability and iterated-box semantics (K7). — pass (`results/K14-3.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R41.md`)

### Provenance

- run: 20261020-1600
- claim: K14
- author: r2 (codex)
- round: 5
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K14-1.json, K14-2.json, K14-3.json

## K6

For $n\ge2$, a FairBot height blend of $W_n$ self-cooperates iff the first false height $t$ of its DefectBot trace satisfies $t<n$ or all $h>t$ belong to $S$; all such blends remain unexploitable.

Status: derived · author check only

Kind: model

Evidence:
- reasoning: The q gate has exactly one hole, at the first false height of the DefectBot trace. Either branch forces p(g) for n\<=g\<h, preserving eventual unexploitability. General Lean proof pending.
- check `checks/K6-fb_self.py`: General Lean self-play iff law; first-hole and DefectBot trace semantics; first failure exists; early-hole criterion; all-height FB/CB cooperation; no sorryAx; three mutations rejected. — pass (`results/K6-1.json`)
- check `checks/K6-fb_grid.py`: All 48 GL-certified self/FB/CB cells for n=2,3 and eight selectors arbitrary on heights 0,1 and constant from 2; wrong-candidate controls. — pass (`results/K6-2.json`)
- check `checks/K14-blend_gate.py`: General Lean unexploitability of all graded-FairBot blends, including FairBot. — pass (`results/K14-3.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R40.md`)

### Provenance

- run: 20261020-1600
- claim: K6
- author: r2 (codex)
- round: 3
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K14-3.json, K6-1.json, K6-2.json

## K16

For an $F_k$ height blend of $V_{n,r}$, let $d$ be its DefectBot trace, $t$ its first false height and $E=\{g\ge n:\neg d(g),\ g<t+r\}$. Self-play cooperates iff every height above every $g\in E$ is selected; for finite $S$, iff $E=\varnothing$.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K16-v_self.py`: 11 general Lean core theorems: obstruction law, first-hole window, finite-set law, singleton iff, DB trace, FB/CB cooperation, universal unexploitability; SHA-pinned, no sorryAx; 3 mutations rejected. — pass (`results/K17-1.json`)
- check `checks/K16-v_grid.py`: 486 GL-certified cells including all 480 grid cells for five (n,r) pairs, k1,2, 16 selectors vs self/FB/CB and six nonmonotonicity headline cells; wrong candidate controls. — pass (`results/K17-2.json`)
- check `checks/K16-v_reestablished.py`: SHA-pinned full prior V-family script re-executed: nine Lean theorem checks, five rejected mutations, literal tables and 35 separated family members. — pass (`results/K25-3.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R42.md`)

### Provenance

- run: 20261020-1600
- claim: K16
- author: r2 (codex)
- round: 6
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K17-1.json, K17-2.json, K25-3.json

## K19

For $1\le j\le a+b$ and $k\ge1$, an $F_k$ height blend of $J_{a,b,j}$ with finite $S$ self-cooperates iff $k\le j$ and $\{j,\ldots,a+b\}\subseteq S$; all such blends are unexploitable and cooperate with FairBot and CooperateBot.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K19-j_self.py`: 9 SHA-pinned Lean core theorems: literal J normalization, general obstruction law, finite interval law, DB trace, universal unexploitability, FB/CB cooperation; no sorryAx; 3 rejected mutations. — pass (`results/K23-3.json`)
- check `checks/K19-j_grid.py`: 581 GL-certified cells: exhaustive six-triple/two-k/16-selector self-FB-CB grid and 5 headline cells including J111 selection1 versus2 versus1,2; F2 separator; wrong-candidate controls. — pass (`results/K21-3.json`)
- check `checks/K19-j_reestablished.py`: Full SHA-pinned prior J-family script, including G and H special cases: literal tables, 70 distinct agents, formula-string cells, re-executed. — pass (`results/K19-3.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R43.md`)

### Provenance

- run: 20261020-1600
- claim: K19
- author: r2 (codex)
- round: 7
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K19-3.json, K21-3.json, K23-3.json

## K9

A DefectBot height blend of $W_n$ ($n\ge2$) self-cooperates iff $\varnothing\ne S\subseteq\{0,\ldots,n-1\}$; a CooperateBot blend self-cooperates iff $S$ is cofinite.

Status: derived · author check only

Kind: model

Evidence:
- reasoning: DB selection below n repairs the q gate without retained self-defects; selection at or above n propagates failure. Finite CB selection leaves a first DB-trace hole at or above n+1 and cannot shield it forever. General Lean proof pending.
- check `checks/K9-other_self.py`: Lean core proofs of the general DB and CB self-play iff laws and both DefectBot-trace formulas; SHA-pinned source; no sorryAx; three mutations rejected. — pass (`results/K9-1.json`)
- check `checks/K9-other_grid.py`: All 32 GL-certified self-play cells for DB/CB blends, n=2,3, eight selectors arbitrary at 0,1 and constant from 2; wrong-candidate controls. — pass (`results/K9-2.json`)

Prior art: partial prior art (answer: `prior-art/R60.md`)

### Provenance

- run: 20261020-1600
- claim: K9
- author: r2 (codex)
- round: 4
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K9-1.json, K9-2.json

## K25

For $r\ge1$, a DefectBot height blend of $V_{n,r}$ self-cooperates iff $S\subseteq\{0,\ldots,n-1\}$ and some $s\in S$ satisfies $s+r\le n+1$; all remain unexploitable. CooperateBot blends self-cooperate iff $S$ is cofinite, when DefectBot exploits them.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K25-v_other.py`: Six SHA-pinned Lean core theorem groups: general DB iff, CB iff eventual selection, DB traces, DB safety, finite CB safety, cofinite CB exploitation; no sorryAx; three rejected mutations. — pass (`results/K25-1.json`)
- check `checks/K25-v_other_grid.py`: 896 GL-certified self/DB cells for 14 n,r pairs, 16 selectors, DB/CB branches; wrong-candidate controls. — pass (`results/K25-2.json`)
- check `checks/K16-v_reestablished.py`: SHA-pinned prior V-family literal semantics and Lean results re-established as in K16. — pass (`results/K25-3.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R45.md`)

### Provenance

- run: 20261020-1600
- claim: K25
- author: r2 (codex)
- round: 10
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K25-1.json, K25-2.json, K25-3.json

## K23

For $1\le j\le a+b$, no DefectBot height blend of $J_{a,b,j}$ self-cooperates; a CooperateBot blend self-cooperates iff its selector is cofinite, and then DefectBot exploits it. Every DefectBot blend and every finite-selector CooperateBot blend is unexploitable.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K23-j_other.py`: Six SHA-pinned Lean core theorems for arbitrary indices/selectors: traces, no DB self-cooperation, CB self iff eventual selection, DB safety, finite CB safety, cofinite CB exploitation; no sorryAx; three rejected mutations. — pass (`results/K23-1.json`)
- check `checks/K23-j_other_grid.py`: All 384 self/DB cells GL-certified for six J triples, 16 selectors and DB/CB branches; wrong-candidate controls. — pass (`results/K23-2.json`)
- check `checks/K19-j_self.py`: K19 literal J normalization into the height gate, SHA-pinned Lean proof. — pass (`results/K23-3.json`)

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R46.md`)

### Provenance

- run: 20261020-1600
- claim: K23
- author: r2 (codex)
- round: 9
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K23-1.json, K23-2.json, K23-3.json

## K28

For every agent and $k\ge1$: it ends CC with $F_k=\Box^kp$ iff it cooperates at every height of that game. Hence any height blend that plays DefectBot at some height, whatever its other branches, never ends CC with FairBot or any $F_k$; if unexploitable, it ends DD.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K28-c046_mixed.py`: Lean 4 core fk\_cc\_iff, fk\_defects, db\_height\_blocks (SHA-pinned, no sorryAx, 3 mutations rejected); literal evaluator 6804 mixed F\_k/DB/V\_{n,r} blends (n1..4, r=1..n+1, k1,2, 243 labelings) vs self, F\_1..F\_3, CB: CC with F\_m iff all-height cooperation; any DB label gives DD and F\_m defects from s+m; DB-free blends match K22; 702 DB-labelled self-CC blends, none FB-CC — pass (`results/K28-1.json`)
- reasoning: F\_k at h reads the agent's moves at all g\<=h-k, so a single defection at s makes F\_k defect from s+k on; a DefectBot-selected height is such a defection regardless of the other branches.

Prior art: partial prior art (answer: `prior-art/R61.md`)

### Provenance

- run: 20261020-1600
- claim: K28
- author: r1 (claude)
- round: 13
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K28-1.json

## K20

For finite $S$, $k,m\ge1$: the $F_k$ height blend of $J_{a,b,j}$ and $F_m=\Box^m p$ cooperate at every height iff $m\le j$, else both eventually defect; so $F_{j+1}$ separates every such blend, including every self-cooperating one, from FairBot and from each $\Box^{m'}p$.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K20-c046_j_xcheck.py`: Lean 4 core fm\_db, fm\_coop (m\<=j: all-height CC, any S), fm\_defect (j\<m, finite S: eventual DD), fm\_fm, separator; SHA-pinned, no sorryAx, 3 mutations rejected; exact engine: 53760 finite-S cells vs F\_m (m\<=7) CC iff m\<=j; 1668 finite self-CC blends none FB-equivalent; K19 laws on 15360 blends — pass (`results/K20-1.json`)
- reasoning: F\_m's DefectBot trace is true exactly below m, so J's q-gate is open everywhere iff m\<=j; otherwise it closes at g=m, and with finite S an unselected height past it defects, after which F\_m and then both blend branches defect forever.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R48.md`)

### Provenance

- run: 20261020-1600
- claim: K20
- author: r1 (claude)
- round: 8
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K20-1.json

## K22

For $r,k,m\ge1$ and any $S$, the $F_k$ height blend of $V_{n,r}$ ($W_n=V_{n,1}$) and $F_m=\Box^mp$ cooperate at every height iff $m+r\le n$ or all $h>\max(n,m)$ are selected, else both eventually defect; for finite $S$, $F_{\max(1,n-r+1)}$ separates the blend from every $\Box^{m'}p$.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K22-c046_v_fm.py`: Lean 4 core vfm\_coop, vfm\_defect, vfm\_law (iff for arbitrary S), fm\_fm, v\_separator; SHA-pinned, no sorryAx, 3 mutations rejected; exact engine: 55296 cells (6912 V blends n2..5, r=1..n+1, k1..3, 128 selectors vs F\_1..F\_8) match the law; all blends unexploitable; 1010 finite self-CC blends DD with F\_max(1,n-r+1), none FB-equivalent; hand examples W2{1}, V32{2}, W4{2} — pass (`results/K22-1.json`)
- reasoning: Against F\_m the q input is (g\<m), so the V gate fails at g\>=n exactly for m\<=g\<m+r; an unselected height above the lowest hole max(n,m) defects, after which F\_m and both blend branches defect forever; otherwise strong induction gives all-height CC.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R49.md`)

### Provenance

- run: 20261020-1600
- claim: K22
- author: r1 (claude)
- round: 9
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K22-1.json

## K24

An $F_k$ height blend of $J_{a,b,j}$ ($k\ge1$, cofinite $S$) is FairBot-equivalent iff $k=1$ and all $h\ge1$ are selected; else $R_h(q)$ (its DefectBot trace true at $h\ge1$) or $Y_{h_0}$ (unselected $h_0\ge a+b+1$) gets CC or DC from it and DD from FairBot.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K24-c046_jcof.py`: Lean 4 core db\_trace, reader, cases3, fb\_case, rq\_blend, rq\_fb, y\_blend, y\_fb (arbitrary a,b,j, k\>=1, cofinite S); SHA-pinned, no sorryAx, 3 mutations rejected; exact engine on 7680 cofinite J blends: FB-equivalent iff k=1 and {1..5} in S (80), 7344 R\_h(q)-separated (CC vs DD), 256 Y\_h0-separated (DC vs DD); 6288 self-CC, 6208 separated incl. all 108 bank-unseparated; G11 hand example — pass (`results/K24-1.json`)
- reasoning: Cofinite blends differ from FairBot either in the DefectBot trace at some h\>=1 (read by R\_h(q)) or at an unselected height h0\>=a+b+1 where J ignores p at h0-1 (probed by Y\_h0, which defects there only against partners that already cooperated); otherwise the blend is the box-p operator.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R50.md`)

### Provenance

- run: 20261020-1600
- claim: K24
- author: r1 (claude)
- round: 10
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K24-1.json

## K26

For $n,r,k\ge1$ and any finite or cofinite $S$, the $F_k$ height blend of $V_{n,r}$ ($W_n=V_{n,1}$) is FairBot-equivalent iff $k=1$ and all $h\ge1$ are selected; else, for cofinite $S$, $R_h(q)$ gets CC from it and DD from FairBot, or $Z_{n,h_0}$ gets DD from it and CC from FairBot.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K26-c046_vcof.py`: Lean 4 core db\_trace, reader, cases3, fb\_case, rq\_blend (any unselected branch), rq\_fb, z\_blend, z\_fb; SHA-pinned, no sorryAx, 3 mutations rejected; exact engine on 7680 V blends (n1..5, r=1..n+1, k1..3, 64 masks x finite/cofinite tail): FB-equivalent iff k=1 and S contains 1..5 cofinitely (40); 3664 R\_h(q) CC/DD, 136 Z\_{n,h0} DD/CC; 2522 cofinite self-CC, 2482 separated; W2 hand example unexploitable, self/FB/CB CC — pass (`results/K26-1.json`)
- reasoning: A cofinite blend differs from FairBot either in its DefectBot trace at some h\>=1 (read by R\_h(q)) or, with FairBot's DefectBot trace, at an unselected h0\>n where the V q-gate can be closed by an opponent that defects only against DefectBot at height n; otherwise the blend is the box-p operator. Finite S is K22.

Prior art: possibly new: no prior art found in the owner's search (answer: `prior-art/R51.md`)

### Provenance

- run: 20261020-1600
- claim: K26
- author: r1 (claude)
- round: 11
- run-folder commit: e3d59e30bce37b58223f480d4f0d5a79bbff59ce
- check results: K26-1.json

## Discussion

<!-- owner-discussion -->
The blends are a deliberately simple, deterministic way to mix agents: a formula without atoms
decides, height by height, which agent to imitate. Probabilistic mixtures of FairBot-like agents
have been studied elsewhere [4] and are not covered here. The results
are stated for the W, V and J families; whether similar window laws hold for every
self-defecting unexploitable agent is open. The use of height guards to switch behaviour goes
back to WaitFairBot in Barasz et al.
<!-- /owner-discussion -->

## References

1. <!-- cite:barasz2014robust --> Barasz, Mihaly and Christiano, Paul and Fallenstein, Benja and Herreshoff, Marcello and LaVictoire, Patrick and Yudkowsky, Eliezer. 2014. Robust Cooperation in the Prisoner's Dilemma: Program Equilibrium via Provability Logic. [Link](https://arxiv.org/abs/1401.5577)
2. <!-- cite:solovay1976provability --> Solovay, Robert M.. 1976. Provability Interpretations of Modal Logic. Israel Journal of Mathematics
3. <!-- cite:boolos1993logic --> Boolos, George. 1993. The Logic of Provability. Cambridge University Press
4. <!-- cite:oesterheld2022compatibility --> Oesterheld, Caspar. 2022. A Note on the Compatibility of Different Robust Program Equilibria of the Prisoner's Dilemma. [Link](https://arxiv.org/abs/2211.05057)
