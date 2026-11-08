## Setting

The onto functional pigeonhole principle $\mathrm{onto\text{-}FPHP}^{n+k}_n$ says that $n+k$
pigeons can be mapped one-to-one onto $n$ holes; it is false for every $k\ge1$. In Boolean
variables $x_{ij}$ (pigeon $i$ in hole $j$) its axioms are $\sum_j x_{ij}-1$,
$\sum_i x_{ij}-1$, $x_{ij}x_{i'j}$ and $x_{ij}x_{ij'}$, the linear encoding used for this family
[@beame1998counting; @razborov2001php]. These results are for the linear encoding only: translating the CNF clause by clause instead turns each pigeon clause into a polynomial of degree $n$ [@razborov2001php], so degree bounds below $n$ say nothing about that encoding. A polynomial calculus (PC) refutation over
$\mathbb F_2$ derives $1$ from the axioms and the Boolean axioms $x^2-x$ by linear combinations
and multiplication by a variable; its degree is the largest degree of a line.

Over $\mathbb F_2$, with surplus $k=2^\ell$, the PC degree is exactly 2 at $k=2$ and exactly 4 at
$k=4$ (companion results in the same library). This finding is about $k=8$.

## Result

For every $n\ge7$, $\mathrm{onto\text{-}FPHP}^{n+8}_n$ has no PC refutation over $\mathbb F_2$ of
degree 4. Its PC degree is therefore at least 5, while the general bound for surplus divisible
by $p^2$ (companion finding) gives only 3 at $p=2$. So at $p=2$ the third level is strictly
harder than the second for every $n\ge7$.

The proof combines a general reduction with finite certificates: small ones for levels 0–2 and,
for level 3, one of 95,550 steps that the Lean kernel checks in 2,154 pieces, plus 60 coverage checks.

## Why it matters

Razborov's Question 7 asks whether PC degree for surplus $p^\ell$ stays bounded in characteristic
$p$ [@razborov2001php]. Riis and Sitharam's Theorem 33 gives degree at least 7 for $k=8$ once
$N\ge196$ [@riis1997nonconstant], which is stronger than this result for large $n$. The range
$7\le n<196$ is not covered by that theorem. This result covers it, and it is machine-checked.

## Proved vs checked

The result is proved in Lean 4 for every $n\ge7$; the certificate is part of the proof, not a
separate check up to a bound. The proof uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. A second agent in the run checked the certificate
independently, with its own program written from the Lean definitions, not from the author's
code. That is an independent check of the certificate, not an independent Lean re-proof. No
person has reviewed the proof. The same library also states the result for standard (syntactic)
PC (`std_no_deg4_k8`).

The Lean theorem excludes refutations of degree exactly 4; smaller degrees are excluded by monotonicity in
the degree bound, stated in the library as `Programme.«maintenance-20261108».DegreeMono.no_deg_le4` (and `deg_ge5`).

## Discussion

The upper bound from Riis's criterion is 8 [@riis1993independence; @razborov2001php], so for
$k=8$ the degree lies between 5 and 8 for $n\ge7$. This is one case, not a growth result in
$\ell$. We have not checked the proof of Theorem 33 and cite it for comparison only.
