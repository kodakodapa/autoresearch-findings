"""Countermodel: variant-2 Ax2a, Ax2b, Ax4 (module OpenQuestions.Ax1GenRigidVariant2) do not
derive P G.  Full model (every e->sigma function is a property), so it is L-general.
W = {0,1,2}, R universal (S5), one entity a, actual at every world,
P(phi) at w  iff  phi a holds at >= 2 of the 3 worlds (majority; world-independent, so rigid).
Asserts: Ax2a, Ax2b, Ax4 hold at every world; G a is false everywhere and P G fails everywhere;
the Ax1GenR instance for PosGlobal = {psi | forall w. P psi w} fails (so K1's extra hypothesis is
what blocks this model).  Also a sanity model of the full theory TR (1 world, R reflexive,
P phi iff phi a) where the instance holds and P G holds."""
import itertools

def check(W, D, R, E, Pfun):
    props = list(itertools.product([False, True], repeat=len(D) * len(W)))
    ev = lambda f, d, w: f[d * len(W) + w]
    neg = lambda f: tuple(not x for x in f)
    P = {(f, w): Pfun(f, ev, w) for f in props for w in W}
    ax2a = all(P[f, w] != P[neg(f), w] for f in props for w in W)          # exclusive or
    ax2b = all(not P[f, w] or all(P[f, v] for v in W if (w, v) in R) for f in props for w in W)
    inc = lambda f, g, w: all(ev(g, d, v) for v in W if (w, v) in R for d in D if (d, v) in E and ev(f, d, v))
    ax4 = all(not (P[f, w] and inc(f, g, w)) or P[g, w] for f in props for g in props for w in W)
    G = tuple(all(ev(f, d, w) for f in props if P[f, w]) for d in D for w in W)
    PG = [P[G, w] for w in W]
    pg = [f for f in props if all(P[f, v] for v in W)]                      # PosGlobal
    posprops = all(P[f, w] for f in pg for w in W)
    conj = lambda f, w: all(ev(f, d, v) == all(ev(p, d, v) for p in pg)
                            for v in W if (w, v) in R for d in D if (d, v) in E)
    inst = all(not (posprops and conj(f, w)) or P[f, w] for f in props for w in W)
    return ax2a, ax2b, ax4, inst, PG

# Countermodel
W = [0, 1, 2]; D = [0]
R = {(w, v) for w in W for v in W}
E = {(0, w) for w in W}
maj = lambda f, ev, w: sum(ev(f, 0, v) for v in W) >= 2
ax2a, ax2b, ax4, inst, PG = check(W, D, R, E, maj)
assert ax2a and ax2b and ax4, "variant-2 axioms must hold"
assert not any(PG), "P G must fail at every world"
assert not inst, "the Ax1GenR(PosGlobal) instance must fail (else K1 would be contradicted)"

# Sanity model of TR: one reflexive world, P phi iff phi a
W1 = [0]; R1 = {(0, 0)}; E1 = {(0, 0)}
r = check(W1, [0], R1, E1, lambda f, ev, w: ev(f, 0, w))
assert all(r[:4]) and all(r[4]), "TR satisfiable with P G"

# Exhaustive: every full model with |W|<=2, |D|=1 (all R, actuality, P) of TR has P G everywhere
for nW in (1, 2):
    W2 = list(range(nW)); props = list(itertools.product([False, True], repeat=nW))
    for Rb in itertools.product([0, 1], repeat=nW * nW):
        R2 = {(w, v) for w in W2 for v in W2 if Rb[w * nW + v]}
        for Eb in itertools.product([0, 1], repeat=nW):
            E2 = {(0, w) for w in W2 if Eb[w]}
            for Pb in itertools.product(range(2 ** len(props)), repeat=nW):
                Pf = lambda f, ev, w: bool((Pb[w] >> props.index(f)) & 1)
                a, b, c, i, pgv = check(W2, [0], R2, E2, Pf)
                if a and b and c and i:
                    assert all(pgv), "K1 would fail"
print("OK: Ax2a+Ax2b+Ax4 hold, P G fails (3-world S5 majority model); TR consistent; small exhaustive agrees with K1")
