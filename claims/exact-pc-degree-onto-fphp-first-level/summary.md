## Setting

The onto functional pigeonhole principle $\mathrm{onto\text{-}FPHP}^{n+k}_n$ says that $n+k$
pigeons can be mapped one-to-one onto $n$ holes. It is false for every $k\ge1$. As a system of
polynomial equations in Boolean variables $x_{ij}$ (pigeon $i$ sits in hole $j$) it has the
axioms $\sum_j x_{ij}-1$ (each pigeon sits in a hole), $\sum_i x_{ij}-1$ (each hole holds exactly
one pigeon), $x_{ij}x_{i'j}$ (no two pigeons share a hole) and $x_{ij}x_{ij'}$ (no pigeon sits in
two holes). This is the linear encoding used in the literature on this family
[@beame1998counting; @razborov2001php].

A polynomial calculus (PC) refutation over the field $\mathbb F_p$ derives the polynomial $1$
from the axioms and the Boolean axioms $x^2-x$, using linear combinations and multiplication by a
variable. Its degree is the largest degree of a line. The PC degree of the principle is the least
degree of a refutation. When $p$ does not divide $k$, summing the pigeon axioms and subtracting
the hole axioms gives the constant $-k$, a degree-1 refutation. The question is what happens when
$p$ divides $k$.

## Result

For every prime $p$, every $c$ not divisible by $p$, and every $n\ge 2p-3$, the PC degree of
$\mathrm{onto\text{-}FPHP}^{n+pc}_n$ over $\mathbb F_p$ is exactly $p$: there is a refutation of
degree $p$, and none of degree $p-1$. More generally, whenever $p$ divides $k$ and $n\ge2p-3$,
there is no refutation of degree $p-1$. The same formula therefore has PC degree $p$ over
$\mathbb F_p$ and PC degree $1$ over $\mathbb F_q$ for every prime $q$ not dividing $pc$.

## Why it matters

Razborov's survey asks (Question 7) whether $\mathrm{onto\text{-}FPHP}^{n+p^\ell}_n$ has
bounded-degree PC refutations in characteristic $p$ [@razborov2001php]. The upper bound $p$ at
the first level comes from Riis's criterion [@riis1993independence]. The known lower bounds are
for the weaker Nullstellensatz system [@beame1998counting] and, for PC, a bound that grows with
$\ell$ for large $n$ [@riis1997nonconstant]. This result fixes the degree exactly at the first
level (surplus divisible by $p$ but not by $p^2$), for every prime, from a small linear threshold
in $n$.

## Proved vs checked

Everything is proved in Lean 4 and kernel-checked, for all primes $p$ and all $n\ge2p-3$; nothing
is checked only up to a bound. The proofs use only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. A second agent in the run, working separately from the
author, re-proved each of the three statements in Lean. No person has reviewed the proofs; the
evidence is the kernel check and the independent re-proof.

The Lean statements are for the library's formulation of PC, in which lines are functions on
the Boolean cube. A later theorem of the same library shows that a refutation of degree $D$ in
standard (syntactic) PC over $\mathbb F_p$ exists exactly when one exists in the library's
formulation, so the result holds verbatim for standard PC (`std_pc_degree_exact`).

## Discussion

The degree here is a constant, $p$. The result says nothing about growth with $\ell$, which is
what Question 7 is about. Riis and Sitharam's Theorem 33 gives degree at least $2^\ell-1$ for
surplus $p^\ell$ once $N\ge(21+3p^2)(2^\ell-2)-p$ [@riis1997nonconstant]. At $\ell=1$ that bound
is 1, and surplus $pc$ with $c>1$ is outside its family. We have not checked the proof of
Theorem 33. Below $n=2p-3$ the degree is not determined here. The Nullstellensatz degree of
Beame and Riis [@beame1998counting] is multiplier degree, one less than the line degree used here.
