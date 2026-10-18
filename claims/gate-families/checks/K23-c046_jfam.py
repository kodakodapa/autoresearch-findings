"""C046 (r1): box-placement family J_{a,b,j} = []^{a+1}([]^b p & (q | []([]^j F | ~q))), size a+b+j+10.
b=0 is H_{a,j} (K20/K21), a=0 is G_{b,j} (K18), (a,b,j)=(1,1,1) is r2's K22 agent J.
Separators S_{u,t} = []^u(p | ~[]^t q), size u+t+4 (S_j of K21 is S_{j+1,j+1}).
Height semantics of closed GL fixed points (letter-free => decided by height on finite linear frames):
box phi at h  <=>  phi at every g < h.  Self-contained, stdlib only, finite ranges stated below.

(1) literal tables (prefix boxes, synchronous play, 60 heights) for 0<=a,b<=5, 1<=j<=6:
    DB trace h<=a+b; CB coop; ConBot: J defects from a+b+1, ConBot coops;
    F_k (k<=9): CC everywhere iff k<=j, else J defects from k+a+1 and F_k from 2k+a+1;
    P_i (i<=9): CC iff i>a+b, else P_i defects from i+1, J from i+a+b+2;
    S_{u,t} (1<=u,t<=8): CC if u<=j; if u>j, J coops exactly at h<=u+a, S coops everywhere iff t+b<=u,
      else S defects from 2u+a+1;
    J vs J' (j<=a+b, j'<=a'+b', a+b,a'+b'<=4): both defect from 2(a+b+a'+b')+3;
    safety: on 3000 random opponent traces, J(h) true => opponent true at every f with f+a+b+1<=h.
(2) all (a,b,j) with 1<=j<=a+b<=5 (70 agents) have pairwise distinct F_1..7/P_0..7/S_{u,t<=8} outcome vectors
    (vectors as verified in (1)).
(3) independent solver from formula strings for every member of size <=15 with 1<=j<=a+b:
    self DD, FB CC, CB CC, DB DD, ConBot D/C, F_1..5, P_0..6, S_{u,t} u,t<=5 match (1).
"""
import random
H = 60
def bxn(r, q, g): return all(q[i] for i in range(g - r + 1)) if r >= 1 else q[g]
def qc(j, q, g): return q[g] or all(f < j or not q[f] for f in range(g))
def Jh(a, b, j, p, q, h): return all(bxn(b, p, g) and qc(j, q, g) for g in range(h - a))
def Sh(u, t, p, q, h): return all(p[g] or not bxn(t, q, g) for g in range(h - u + 1))
def play(fx, fy):
    xs, ys = [], []
    for h in range(H):
        xs.append(fx(ys, h)); ys.append(fy(xs, h))
    return xs, ys
pad = lambda t: t + [None] * (H - len(t))
dle = lambda c: [h <= c for h in range(H)]
T = [True] * H; Z = [False] * H; CON = [h >= 1 for h in range(H)]
def F_k(k): return lambda xs, h: bxn(k, pad(xs), h)
def P_i(i, m): return lambda xs, h: all(xs[:h]) and all(g < i or not dle(m)[g] for g in range(h))
assert all([Sh(u, t, Z, Z, h) for h in range(H)] == dle(u-1) for u in range(1, 9) for t in range(1, 9))
for a in range(6):
    for b in range(6):
        m = a + b
        for j in range(1, 7):
            assert [Jh(a, b, j, Z, Z, h) for h in range(H)] == dle(m)
            assert all(Jh(a, b, j, T, T, h) for h in range(H))
            assert not any(Jh(a, b, j, CON, CON, h) for h in range(m+1, H))
            for k in range(1, 10):
                xs, ys = play(lambda ys, h: Jh(a, b, j, pad(ys), dle(k-1), h), F_k(k))
                if k <= j: assert all(xs) and all(ys), (a, b, j, k)
                else: assert not any(xs[k+a+1:]) and not any(ys[2*k+a+1:]), (a, b, j, k)
            for i in range(10):
                xs, ys = play(lambda ys, h: Jh(a, b, j, pad(ys), dle(0), h), P_i(i, m))
                if m < i: assert all(xs) and all(ys), (a, b, j, i)
                else: assert not any(ys[i+1:]) and not any(xs[i+m+2:]), (a, b, j, i)
            for u in range(1, 9):
                for t in range(1, 9):
                    xs, ys = play(lambda ys, h: Jh(a, b, j, pad(ys), dle(u-1), h),
                                  lambda xs, h: Sh(u, t, pad(xs), dle(m), h))
                    if u <= j: assert all(xs) and all(ys), (a, b, j, u, t)
                    else:
                        assert xs == dle(u+a), (a, b, j, u, t)
                        if t + b <= u: assert all(ys), (a, b, j, u, t)
                        else: assert not any(ys[2*u+a+1:]), (a, b, j, u, t)
# ConBot cooperates with J (ConBot = ~[]F is C at every h>=1 regardless of opponent): trivially by its trace.
fam = [(a, b, j) for a in range(6) for b in range(6) for j in range(1, a+b+1) if a + b <= 4]
for (a, b, j) in fam:
    for (a2, b2, j2) in fam:
        xs, ys = play(lambda ys, h: Jh(a, b, j, pad(ys), dle(a2+b2), h),
                      lambda xs, h: Jh(a2, b2, j2, pad(xs), dle(a+b), h))
        B = 2*(a+b+a2+b2)+3
        assert not any(xs[B:]) and not any(ys[B:]), (a, b, j, a2, b2, j2)
rng = random.Random(46)
for _ in range(3000):
    a, b, j = rng.randrange(5), rng.randrange(5), rng.randrange(1, 6)
    y = [rng.random() < 0.85 for _ in range(40)]; d = [rng.random() < 0.5 for _ in range(40)]
    for h in range(40):
        if Jh(a, b, j, y, d, h): assert all(y[f] for f in range(max(0, h - a - b)))
# (2) distinctness
def vec(a, b, j):
    m = a + b
    return tuple([k <= j for k in range(1, 8)] + [i > m for i in range(8)] +
                 [(u <= j, u <= j or t + b <= u) for u in range(1, 9) for t in range(1, 9)])
fam5 = [(a, b, j) for a in range(6) for b in range(6) for j in range(1, a+b+1) if a + b <= 5]
assert len(fam5) == 70 and len({vec(*z) for z in fam5}) == 70
# (3) independent string solver
def parse(s):
    def p(i):
        c = s[i]
        if c in 'Fpq': return (c,), i+1
        if c == '~': x, k = p(i+1); return ('~', x), k
        if s.startswith('[]', i): x, k = p(i+2); return ('[]', x), k
        assert c == '('
        x, k = p(i+1); op = s[k]; y, l = p(k+1); assert s[l] == ')'
        return (op, x, y), l+1
    t, k = p(0); assert k == len(s); return t
def ev(t, h, P, Q, memo):
    key = (id(t), h)
    if key not in memo:
        k = t[0]
        if k == 'F': r = False
        elif k == 'p': r = P[h]
        elif k == 'q': r = Q[h]
        elif k == '~': r = not ev(t[1], h, P, Q, memo)
        elif k == '&': r = ev(t[1], h, P, Q, memo) and ev(t[2], h, P, Q, memo)
        elif k == '|': r = ev(t[1], h, P, Q, memo) or ev(t[2], h, P, Q, memo)
        else: r = all(ev(t[1], g, P, Q, memo) for g in range(h))
        memo[key] = r
    return memo[key]
def game(sa, sb, HH=45):
    A, B = parse(sa), parse(sb); x, y, za, zb = [], [], [], []; Zs = [False]*HH; ms = [{}, {}, {}, {}]
    for h in range(HH):
        za.append(ev(A, h, Zs, Zs, ms[2])); zb.append(ev(B, h, Zs, Zs, ms[3]))
        xa = ev(A, h, y + [None], zb, ms[0]); yb = ev(B, h, x + [None], za, ms[1])
        x.append(xa); y.append(yb)
    return x[-1], y[-1]
bx = lambda s, n: '[]' * n + s
def Jstr(a, b, j): return bx('(' + bx('p', b) + '&(q|[](' + bx('F', j) + '|~q)))', a+1)
def Sstr(u, t): return bx('(p|~' + bx('q', t) + ')', u)
def size(s): return len(s.replace('[]', 'B').replace('(', '').replace(')', ''))
assert Jstr(1, 1, 1) == '[][]([]p&(q|[]([]F|~q)))' and size(Jstr(1, 1, 1)) == 13
assert all(size(Jstr(a, b, j)) == a+b+j+10 for a in range(5) for b in range(5) for j in range(1, 5))
assert all(size(Sstr(u, t)) == u+t+4 for u in range(1, 6) for t in range(1, 6))
FB, CB, DB, CON = '[]p', '~F', 'F', '~[]F'
small = [(a, b, j) for (a, b, j) in fam5 if a+b+j+10 <= 15]
ncell = 0
for (a, b, j) in small:
    s = Jstr(a, b, j); m = a + b
    assert game(s, s) == (False, False) and game(s, FB) == (True, True) and game(s, CB) == (True, True)
    assert game(s, DB) == (False, False) and game(s, CON) == (False, True), (a, b, j)
    for k in range(1, 6): assert game(s, bx('p', k)) == ((k <= j),) * 2
    for i in range(7):
        assert game(s, '([]p&[]~q)' if i == 0 else '([]p&[](' + bx('F', i) + '|~q))') == ((i > m),) * 2
    for u in range(1, 6):
        for t in range(1, 6):
            want = (True, True) if u <= j else (False, t + b <= u)
            assert game(s, Sstr(u, t)) == want, (a, b, j, u, t)
    ncell += 5 + 5 + 7 + 25
print('PASS: J_{a,b,j} tables (a,b<=5, j<=6), 70 distinct agents, %d string-solver cells for %d agents of size<=15'
      % (ncell, len(small)))
