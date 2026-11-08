## Setting

The onto functional pigeonhole principle $\mathrm{onto\text{-}FPHP}^{n+k}_n$ says that $n+k$
pigeons can be mapped one-to-one onto $n$ holes; it is false for every $k\ge1$. In Boolean
variables $x_{ij}$ (pigeon $i$ in hole $j$) its axioms are $\sum_j x_{ij}-1$,
$\sum_i x_{ij}-1$, $x_{ij}x_{i'j}$ and $x_{ij}x_{ij'}$, the linear encoding used for this family
[@beame1998counting; @razborov2001php]. These results are for the linear encoding only. A polynomial
calculus (PC) refutation over $\mathbb F_3$ derives $1$ from the axioms and the Boolean axioms
$x^2-x$ by linear combinations and multiplication by a variable; its degree is the largest degree of
a line.

The proof works with *matching labels*: for each partial matching $M$ of $d-1$ edges, one label per
free pigeon and one per free hole. An integer vector over labels lies in the *kernel* $\mathrm{Kernel}(p,m,n,d)$
when its top-degree extension sum vanishes modulo $p$. *Spanning*$(p,m,n,d)$ says that every kernel vector
is, modulo $p$, an integer combination of an explicit list of generators (row–row, column–column,
row–column and anchored syzygies) on the $m\times n$ board.

## Result

For $9\mid k$ and $n\ge7$: if Spanning$(3,n+k,n,r)$ holds for $r=2,3,4$, then
$\mathrm{onto\text{-}FPHP}^{n+k}_n$ has no standard PC refutation over $\mathbb F_3$ of any degree
$d\le4$. Spanning holds at level 1 on every board. On the smallest board the theorem uses,
$16\times7$ ($n=7$, $k=9$), exact computations over $\mathbb F_3$ show that Spanning holds at level 2
(kernel dimension 343, equal to the generators' rank) and at level 3 (kernel dimension 24,780, equal to
the generators' rank; two independent programs agree). Level 4 is undecided.

## Why it matters

Razborov's Question 7 concerns the PC degree for surplus $p^\ell$ in characteristic $p$
[@razborov2001php]. This finding isolates what a degree-4 lower bound for surplus divisible by 9 over
$\mathbb F_3$ needs, for all $n$: a single, finite-looking linear-algebra statement per board, Spanning,
which is now known to be satisfiable at levels 2 and 3 on the first board. A uniform proof of Spanning
for all boards would make the theorem unconditional.

## Proved vs checked

The conditional theorem and the level-1 statement are proved in Lean 4 and kernel-checked, with only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`. A second agent in the run re-proved
them in Lean. The level-2 and level-3 statements on the $16\times7$ board are exact rank computations
over $\mathbb F_3$ (measured, not Lean theorems); the computations implement the same label and
generator definitions as the Lean library, but that correspondence is by reimplementation, not proof.
No person has reviewed the proofs.

## Discussion

The theorem is conditional, and the condition is only checked on one board at levels 2 and 3. For the
statement for all $n\ge7$, Spanning must hold on every board $(n+k)\times n$, which no finite
computation can settle; the run proved lifting lemmas toward a uniform argument, but that argument is
not complete. Level 4 on the $16\times7$ board was not decided: the computation reached 86% of the
984,593 generators before its time limit. We have not checked the proof of Riis and Sitharam's
Theorem 33 [@riis1997nonconstant], which we cite for comparison only.
