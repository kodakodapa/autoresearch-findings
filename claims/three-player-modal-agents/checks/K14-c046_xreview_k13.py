"""r1 cross-review of r2's K13 (three-player evaluator-replacement probes).
Independent of r2's code. Height-chain semantics of closed GL fixed points:
box(phi) at h iff phi at all g<h.  World = set M of slots replaced by the
constant defector D.  In world M, slot i (not in M) reads p_j = local opponent
j's action in M and q_j = local opponent j's action in M+{i}.  Local opponent
order = increasing global slot order.  True = contribute.
(1) All 125 triples of D,C,F=box(p1&p2),O=box(p1|p2),Q=box(q1&q2) solved to
    height 40, tails constant over the last 20 heights; K13's headline cells and
    both finite classifications reproduced.
(2) Q's no-disadvantage is finite-set only: with B=box(~p_1) (cooperate iff
    provably the first opponent defects), triple (Q,B,C) has tail (1,0,1),
    payoffs (1,4,1). Cells QBC, FFF, FFD, QQQ, FCD are GL-certified (all 24
    replacement equations) by an embedded GLS prover; actual-player flips rejected.
(3) QQQ=000 mirrors the two-player box(q) vs box(q) = DD (q = opponent vs DB).
(4) Lean 4 core: for ANY opponent traces y,z (any programs, any probes), if
    x h <-> forall g<h, y g & z g and all three are eventually constant with
    tails X,Y,Z then X -> Y & Z; hence F never earns less than either opponent
    in u_i = 2*sum a - 3*a_i (decided over all 8 tails). False variant rejected.
Self-contained; stdlib + lean binary only.
"""
import itertools, subprocess, shutil, os
from functools import lru_cache
HMAX = 40
def mk(kind):
    # each bot: function(h, P, Q) where P(j,g), Q(j,g) give opponent actions
    bx = lambda f, h: all(f(g) for g in range(h))
    return {
        'D': lambda h, P, Q: False,
        'C': lambda h, P, Q: True,
        'F': lambda h, P, Q: bx(lambda g: P(0, g) and P(1, g), h),
        'O': lambda h, P, Q: bx(lambda g: P(0, g) or P(1, g), h),
        'Q': lambda h, P, Q: bx(lambda g: Q(0, g) and Q(1, g), h),
        'B': lambda h, P, Q: bx(lambda g: not P(0, g), h),
    }[kind]
def solve(names):
    bots = [mk(n) for n in names]
    @lru_cache(maxsize=None)
    def act(M, i, h):
        if M & (1 << i): return False
        opp = [j for j in range(3) if j != i]
        P = lambda j, g: act(M, opp[j], g)
        Q = lambda j, g: act(M | (1 << i), opp[j], g)
        return bots[i](h, P, Q)
    tr = [[act(0, i, h) for h in range(HMAX)] for i in range(3)]
    for t in tr: assert t[-20:] == [t[-1]] * 20, names
    return tuple(t[-1] for t in tr)
names5 = 'DCFOQ'
mat = {t: solve(t) for t in itertools.product(names5, repeat=3)}
assert mat['F','F','F'] == (True,)*3 and mat['F','F','D'] == (False,)*3
assert mat['F','C','D'] == (False, True, False)
assert mat['O','O','D'] == (True, True, False)
assert mat['Q','Q','Q'] == (False,)*3 and mat['Q','C','C'] == (True,)*3
def u(a, i): return 2 * sum(a) - 3 * a[i]
nodis = [n for n in names5 if all(u(mat[n,b,c],0) >= max(u(mat[n,b,c],1), u(mat[n,b,c],2))
                                   for b in names5 for c in names5)]
selfc = [n for n in names5 if mat[n,n,n] == (True,)*3]
assert nodis == ['D','F','Q'] and selfc == ['C','F','O'], (nodis, selfc)
print('(1) 125 triples re-solved; headline cells and classifications agree')
qbc = solve(('Q','B','C'))
assert qbc == (True, False, True)
assert [u(qbc, i) for i in range(3)] == [1, 4, 1]
print('(2) (Q,B,C) tail', qbc, 'payoffs', [u(qbc, i) for i in range(3)])
# two-player box(q) vs box(q): q = opponent's action vs DB
@lru_cache(maxsize=None)
def two(rep, i, h):  # rep: set of replaced players (bitmask)
    if rep & (1 << i): return False
    return all(two(rep | (1 << i), 1 - i, g) for g in range(h))
assert [two(0, i, HMAX-1) for i in (0,1)] == [False, False]
print('(3) two-player box(q) vs box(q): DD')

# ---- GLS certificate for (Q,B,C): own sequent prover, formulas as tuples
Fl = ('F',)
def imp(a, b): return ('imp', a, b)
def neg(a): return imp(a, Fl)
def box(a): return ('box', a)
def conj(a, b): return neg(imp(a, neg(b)))
def iff(a, b): return conj(imp(a, b), imp(b, a))
Tr = neg(Fl)
@lru_cache(maxsize=None)
def prv(L, R):
    if Fl in L or L & R: return True
    for f in L:
        if f[0] == 'imp':
            L2 = L - {f}
            return prv(L2, R | {f[1]}) and prv(L2 | {f[2]}, R)
    for f in R:
        if f[0] == 'imp':
            return prv(L | {f[1]}, (R - {f}) | {f[2]})
    bl = frozenset(f for f in L if f[0] == 'box')
    ub = frozenset(f[1] for f in bl)
    return any(f[0] == 'box' and prv(bl | ub | {f}, frozenset({f[1]})) for f in R)
def prove(f): return prv(frozenset(), frozenset({f}))
def boxn(x, n):
    for _ in range(n): x = box(x)
    return x
def closed(tr):  # height-slice normal form of an eventually constant trace
    m = len(tr) - 1
    while m > 0 and tr[m-1] == tr[-1]: m -= 1
    if m == 0: return Tr if tr[-1] else Fl
    parts = [conj(boxn(Fl, h+1), neg(boxn(Fl, h))) for h in range(m) if tr[h]]
    if tr[-1]: parts.append(neg(boxn(Fl, m)))
    out = parts[0]
    for x in parts[1:]: out = imp(neg(out), x)
    return out
def certify(names):
    def eqn(M, i):  # right-hand side with variables ('v', M', slot)
        if M & (1 << i): return Fl
        o = [j for j in range(3) if j != i]
        v = lambda MM, j: ('v', MM, j)
        n = names[i]
        if n == 'D': return Fl
        if n == 'C': return Tr
        if n == 'F': return box(conj(v(M, o[0]), v(M, o[1])))
        if n == 'B': return box(neg(v(M, o[0])))
        if n == 'Q': return box(conj(v(M | (1 << i), o[0]), v(M | (1 << i), o[1])))
    bots = [mk(n) for n in names]
    @lru_cache(maxsize=None)
    def act(M, i, h):
        if M & (1 << i): return False
        opp = [j for j in range(3) if j != i]
        return bots[i](h, lambda j, g: act(M, opp[j], g), lambda j, g: act(M | (1 << i), opp[j], g))
    cand = {(M, i): closed([act(M, i, h) for h in range(12)]) for M in range(8) for i in range(3)}
    for (M, i) in cand:
        assert prove(iff(cand[M, i], sub(eqn(M, i), cand))), (names, M, i)
    for i in range(3):
        bad = dict(cand); bad[0, i] = neg(bad[0, i])
        assert not all(prove(iff(bad[k], sub(eqn(*k), bad))) for k in bad)
    prv.cache_clear()
    return tuple(act(0, i, 11) for i in range(3))
def sub(f, c):
    if f[0] == 'v': return c[(f[1], f[2])]
    return (f[0],) + tuple(sub(x, c) for x in f[1:])
assert certify(('Q','B','C')) == (True, False, True)
assert certify(('F','F','F')) == (True, True, True)
assert certify(('F','F','D')) == (False, False, False)
assert certify(('Q','Q','Q')) == (False, False, False)
assert certify(('F','C','D')) == (False, True, False)
print('(2) QBC, FFF, FFD, QQQ, FCD: 24 replacement equations each GL-certified; flips rejected')

LEAN = r'''
theorem fair3_tail (x y z : Nat → Prop) (hx : ∀ h, x h ↔ ∀ g, g < h → y g ∧ z g)
    (T : Nat) (X Y Z : Prop) (hX : ∀ h, T ≤ h → (x h ↔ X)) (hY : ∀ h, T ≤ h → (y h ↔ Y))
    (hZ : ∀ h, T ≤ h → (z h ↔ Z)) : X → Y ∧ Z := by
  intro hxX
  have H := (hx (T+1)).1 ((hX (T+1) (by omega)).2 hxX) T (by omega)
  exact ⟨(hY T (Nat.le_refl T)).1 H.1, (hZ T (Nat.le_refl T)).1 H.2⟩
def u (a b c : Bool) : Int := 2 * ((if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0)) - 3 * (if a then 1 else 0)
theorem fair3_payoff : ∀ X Y Z : Bool, (X = true → Y = true ∧ Z = true) →
    u Y X Z ≤ u X Y Z ∧ u Z X Y ≤ u X Y Z := by decide
#print axioms fair3_tail
#print axioms fair3_payoff
'''
def lean():
    for c in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')):
        if c and os.path.exists(c): return c
    raise AssertionError('lean binary not found')
def run_lean(src):
    r = subprocess.run([lean(), '--stdin'], input=src, capture_output=True, text=True, timeout=100)
    return r.returncode, r.stdout + r.stderr
rc, out = run_lean(LEAN)
assert rc == 0 and 'sorryAx' not in out and 'error' not in out, out
bad = LEAN.replace('(X = true → Y = true ∧ Z = true) →', '')
assert bad != LEAN and run_lean(bad)[0] != 0
print('(4) Lean: fair3_tail, fair3_payoff proved; false variant rejected')
print('PASS')
