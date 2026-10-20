## Setting

Modal agents play one-shot games by asking what can be proved about each other, written with the
provability box $\Box$ of the logic GL [@barasz2014robust]. Two informal posts made claims about
specific agents that were never checked. "Modal Chicken" [@gramstone2015chicken] introduced
CarefulBot and AstuteBot for the game of Chicken, and its comments proposed graded variants:
$C_n = \neg\Box(\Box^n\bot \vee p)$ ("swerve unless the opponent provably swerves", with proof
strength $n$) and BoldBots $B_n = \Box(\Box^n\bot \vee \neg p)$, the name a commenter gave to the
post's original CarefulBot ($B_0$); here $p$ means "the opponent swerves against me". "Yet More Modal Combat" [@hobson2021modal] proposed, for the prisoner's
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
Lean 4, in the height semantics of closed GL fixed points (see [@boolos1993logic];
[@solovay1976provability]). The 64-cell table is certified by GL fixed-point computation.

## Discussion

The results depend on reading each informal definition as a specific modal formula; where a post
was ambiguous we state the formula we used, and a different reading could change the outcome.
Hobson's proposal allows other pairs of systems than the graded ones here, so the negative result
covers this graded family, not every possible instantiation.
