## Setting

Two programs play a one-shot prisoner's dilemma, and each can read the other's source code.
Following Barasz et al. [@barasz2014robust], a *modal agent* decides by asking what can be proved
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
the link to provability in arithmetic is Solovay's theorem [@solovay1976provability], cited, not
formalised (see also [@boolos1993logic]). Finite grids of cases were also checked independently
by GL fixed-point solving with certificates.

## Discussion

The blends are a deliberately simple, deterministic way to mix agents: a formula without atoms
decides, height by height, which agent to imitate. Probabilistic mixtures of FairBot-like agents
have been studied elsewhere [@oesterheld2022compatibility] and are not covered here. The results
are stated for the W, V and J families; whether similar window laws hold for every
self-defecting unexploitable agent is open. The use of height guards to switch behaviour goes
back to WaitFairBot in Barasz et al.
