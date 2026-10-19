"""C046 r1 structure check on the size<=11 census (20441 finite-linear-model classes, same
language/dedup as K1: atoms p,q boxed; F,~,&,|,[]; size = syntax nodes). Payoffs T=5,R=3,P=1,S=0.
Pinned data: census11_agents.json (names in census order) and census11_M.zlib (zlib of numpy
packbits of the 20441x20441 matrix, M[a,b]=1 iff a cooperates with b), sha256 below.
Asserts: (1) round robin (vs all 20441 incl. self): max 59893, attained by exactly 16 agents, of
sizes 10 and 11, each defecting against every census agent and cooperated with by 9863 agents;
DefectBot scores 59193 (cooperated with by 9688), 20 agents strictly above it. The census-9 leader
(DB, K12) is therefore not the census-11 leader. (2) 9095 observational classes; 1120 symmetric
Nash classes (401 self-defecting, each invaded by FairBot; 719 self-cooperating, each with a
neutral non-losing mutant); no ESS. (3) hand example: T=([][]p&~[](p|[]F)) vs X=([]F|~[]~p):
T defects, X cooperates; X defects vs DB. (4) every cell of the rows/columns of the leader
representative and DB, 400 random cells of each other leader's column, every Nash/mutant cell
used, and 6000 random cells re-solved by the independent height-table solver below.
Exact integers; no tolerances.
"""
import sys, hashlib, time, json, random, zlib
import numpy as np

"""Independent exact game solver from formula strings (no machines).
Height table: value of box(f) at height h = AND of f over heights < h.
A game's joint value at height h is a function of the set of boxed subformulas
true at h (in A-vs-B, B-vs-A, A-vs-DB, B-vs-DB); that set only shrinks with h,
so it is constant from some height <= total number of boxes + 1 onward."""
def parse_tree(s):
    s = s.replace(' ', '')
    def p(i):
        c = s[i]
        if c in 'FTpq': return (c,), i+1
        if c == '~': m, j = p(i+1); return ('~', m), j
        if s.startswith('[]', i): m, j = p(i+2); return ('[]', m), j
        if c == '(':
            a, j = p(i+1); op = s[j]; b, k = p(j+1); assert s[k] == ')'
            return (op, a, b), k+1
        raise ValueError(s[i:])
    t, j = p(0); assert j == len(s); return t

def nboxes(t): return (t[0] == '[]') + sum(nboxes(x) for x in t[1:])

def game(sa, sb):
    """returns (A coops B, B coops A) in the standard model (tail value)."""
    A, B = parse_tree(sa), parse_tree(sb)
    H = 2 * (nboxes(A) + nboxes(B)) + 3
    # traces: x[h]=A vs B, y[h]=B vs A, za[h]=A vs DB, zb[h]=B vs DB
    x, y, za, zb = [], [], [], []
    def ev(t, h, pt, qt, memo):
        key = (id(t), h)
        if key in memo: return memo[key]
        k = t[0]
        if k == 'F': r = False
        elif k == 'T': r = True
        elif k == 'p': r = pt[h]
        elif k == 'q': r = qt[h]
        elif k == '~': r = not ev(t[1], h, pt, qt, memo)
        elif k == '&': r = ev(t[1], h, pt, qt, memo) and ev(t[2], h, pt, qt, memo)
        elif k == '|': r = ev(t[1], h, pt, qt, memo) or ev(t[2], h, pt, qt, memo)
        elif k == '[]': r = all(ev(t[1], g, pt, qt, memo) for g in range(h))
        memo[key] = r; return r
    zero = [False] * H
    m1, m2, m3, m4 = {}, {}, {}, {}
    for h in range(H):
        # guardedness: values at h only read traces at heights < h
        za.append(ev(A, h, zero, zero, m3)); zb.append(ev(B, h, zero, zero, m4))
        xa = ev(A, h, y, zb, m1); yb = ev(B, h, x, za, m2)
        x.append(xa); y.append(yb)
    return x[-1], y[-1]


PATHS = ['/run/agents/r1/census/', '/work/agents/r1/census/']
SHA_A = '04a4a117183b345ba543b77b5a5841cbf064f068d960eba5a270da5e0255bb7a'
SHA_M = '4cf7d9895fc0267f9e2473ae8c4d5de78c6e97d09d31394ddd0ac342c3dab31b'

def readp(name):
    for d in PATHS:
        try: return open(d + name, 'rb').read()
        except OSError: pass
    raise AssertionError('dataset missing: ' + name)

def main():
    t0 = time.time()
    ra, rm = readp('census11_agents.json'), readp('census11_M.zlib')
    assert hashlib.sha256(ra).hexdigest() == SHA_A and hashlib.sha256(rm).hexdigest() == SHA_M
    d = json.loads(ra); names = d['agents']; sizes = d['sizes']; n = len(names); assert n == 20441
    M = np.unpackbits(np.frombuffer(zlib.decompress(rm), np.uint8))[:n * n].reshape(n, n).astype(np.int64)
    ix = {s: i for i, s in enumerate(names)}
    DB, CB, FB = ix['F'], ix['~F'], ix['[]p']
    r = M.sum(1); c = M.sum(0); cc = (M * M.T).sum(1)
    rr = n - r + 4 * c - cc          # = 3*CC + 5*DC + 0*CD + 1*DD
    top = int(rr.max()); W = [int(a) for a in np.where(rr == top)[0]]
    assert top == 59893 and len(W) == 16 and sorted(set(sizes[a] for a in W)) == [10, 11]
    for a in W: assert r[a] == 0 and c[a] == 9863
    assert rr[DB] == 59193 and c[DB] == 9688 and r[DB] == 0 and int((rr > rr[DB]).sum()) == 20
    T = ix['([][]p&~[](p|[]F))']; X = ix['([]F|~[]~p)']; assert T in W
    assert M[T, X] == 0 and M[X, T] == 1 and M[X, DB] == 0
    # (2) observational quotient, Nash, ESS
    MT = np.ascontiguousarray(M.T.astype(np.int8)); M8 = M.astype(np.int8)
    key = {}
    for a in range(n): key.setdefault(M8[a].tobytes() + MT[a].tobytes(), []).append(a)
    R = np.array([v[0] for v in key.values()]); assert len(R) == 9095
    rep = {a: v[0] for v in key.values() for a in v}
    Mr = M[np.ix_(R, R)]; B = 3 * Mr * Mr.T + 5 * (1 - Mr) * Mr.T + (1 - Mr) * (1 - Mr.T)
    dg = np.diag(B); pos = {int(R[k]): k for k in range(len(R))}
    nash = [k for k in range(len(R)) if dg[k] >= B[:, k].max()]
    dn = [k for k in nash if Mr[k, k] == 0]; cn = [k for k in nash if Mr[k, k] == 1]
    assert (len(nash), len(dn), len(cn)) == (1120, 401, 719)
    fb = pos[rep[FB]]; used = set()
    for k in dn:
        assert B[fb, k] == dg[k] == 1 and B[fb, fb] == 3 > B[k, fb]; used.add((int(R[k]), FB))
    for k in cn:
        mut = [b for b in np.where(B[:, k] == dg[k])[0] if b != k and B[k, b] <= B[b, b]]
        assert mut; b = int(mut[0]); used.add((int(R[k]), int(R[b]))); used.add((int(R[b]), int(R[b])))
    ess = [k for k in nash if all(B[b, k] < dg[k] or (B[b, k] == dg[k] and B[k, b] > B[b, b])
                                  for b in np.where(B[:, k] == dg[k])[0] if b != k)]
    assert ess == []
    # (4) independent re-solve
    cells = set((min(a, b), max(a, b)) for a, b in used)
    for b in range(n): cells.add((min(T, b), max(T, b))); cells.add((min(DB, b), max(DB, b)))
    rnd = random.Random(11)
    for a in W:
        for _ in range(400): b = rnd.randrange(n); cells.add((min(a, b), max(a, b)))
    for _ in range(6000):
        a, b = rnd.randrange(n), rnd.randrange(n); cells.add((min(a, b), max(a, b)))
    for a, b in cells:
        x, y = game(names[a], names[b])
        assert x == bool(M[a, b]) and y == bool(M[b, a]), (names[a], names[b])
    print('PASS: round-robin max', top, 'by', len(W), 'total defectors (sizes 10-11), DB', int(rr[DB]),
          'rank 21; obs classes', len(R), '; Nash', len(nash), '(', len(dn), 'defect,', len(cn),
          'coop ); ESS 0; re-solved', len(cells), 'games', round(time.time() - t0, 1), 's')

if __name__ == '__main__':
    main()
