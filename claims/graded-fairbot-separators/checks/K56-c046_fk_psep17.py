"""C046 r1: smallest q-free opponent separating consecutive graded FairBots F_k = []^k p and F_{k+1}.
Language: rank-0 fragment of L (atom p only = opponent's move vs me; F,~,&,|,[]; guarded; size = AST nodes;
top = ~F), the K51 census language. Height semantics; game wiring as in K38.
T_k = ~[](~p | []^k F), size k+6.
Part 1 (Lean 4 core, SHA-pinned, all k = m+1 >= 1): tsize, tk_ev (T_k at h iff the partner cooperated at some
 g with k <= g < h), t_low (j<=k: T_k never cooperates, F_j defects from j), t_high (j>k: from j on F_j defects,
 T_k cooperates), psep (T_k: DD with F_k from height k; with F_{k+1}, F defects and T_k cooperates from k+2).
 No sorryAx; 4 mutations rejected.
Part 2 (exact Mealy engine of c046_fk_sep14.py, q never seeded) over all guarded p-only classes of size <= 17
 (per-size counts extend K51's list): for k=1..11 no p-only opponent of size <= k+5 separates F_k from F_{k+1};
 at size k+6 exactly one machine class does, T_k (DD vs F_k; vs F_{k+1}: F defects, T cooperates).
 Compared with K49 (S_k = [](~q | []^k F), size k+5, uses q): forbidding q costs exactly one node for k<=9.
Part 3 (literal height evaluator, H=60): T_k vs F_j = DD if j<=k, (F_j D, T_k C) if j>k, k=1..12, j=1..14.
General lower bound is NOT proved; only the size-(k+6) upper bound is general.
"""
import sys, time
t0=time.time()

from collections import Counter, defaultdict, deque
INPUTS = range(4)  # bit0 = p, bit1 = q

def canon(trans, out, init=0):
    """minimize + BFS-renumber. trans[s][i], out[s][i]. returns hashable key."""
    n = len(trans)
    # reachable
    seen = {init}; order = [init]; k = 0
    while k < len(order):
        s = order[k]; k += 1
        for i in INPUTS:
            t = trans[s][i]
            if t not in seen: seen.add(t); order.append(t)
    # partition refinement
    block = {s: tuple(out[s]) for s in order}
    while True:
        sig = {s: (block[s],) + tuple(block[trans[s][i]] for i in INPUTS) for s in order}
        ids = {}
        nb = {s: ids.setdefault(sig[s], len(ids)) for s in order}
        nblocks_old = len(set(block.values()))
        block = nb
        if len(ids) == nblocks_old: break
    # BFS renumber over blocks
    rep = {}
    for s in order: rep.setdefault(block[s], s)
    num = {block[init]: 0}; q = [block[init]]; k = 0
    T = []; O = []
    while k < len(q):
        b = q[k]; k += 1; s = rep[b]
        row = []
        for i in INPUTS:
            tb = block[trans[s][i]]
            if tb not in num: num[tb] = len(q); q.append(tb)
            row.append(num[tb])
        T.append(tuple(row)); O.append(tuple(out[s]))
    return (tuple(T), tuple(O))

def atom(bit):
    return canon([[0]*4], [[(i >> bit) & 1 for i in INPUTS]])
BOT = canon([[0]*4], [[0]*4])
P = atom(0); Q = atom(1)

def neg(m):
    T, O = m
    return canon([list(r) for r in T], [[1-o for o in r] for r in O])

def binop(m1, m2, f):
    T1, O1 = m1; T2, O2 = m2
    idx = {(0, 0): 0}; st = [(0, 0)]; trans = []; out = []; k = 0
    while k < len(st):
        a, b = st[k]; k += 1
        row = []
        for i in INPUTS:
            t = (T1[a][i], T2[b][i])
            if t not in idx: idx[t] = len(st); st.append(t)
            row.append(idx[t])
        trans.append(row); out.append([f(O1[a][i], O2[b][i]) for i in INPUTS])
    return canon(trans, out)

def AND(a, b): return binop(a, b, lambda x, y: x & y)
def OR(a, b): return binop(a, b, lambda x, y: x | y)

def box(m):
    T, O = m
    idx = {(0, 1): 0}; st = [(0, 1)]; trans = []; out = []; k = 0
    while k < len(st):
        s, f = st[k]; k += 1
        row = []
        for i in INPUTS:
            t = (T[s][i], f & O[s][i])
            if t not in idx: idx[t] = len(st); st.append(t)
            row.append(idx[t])
        trans.append(row); out.append([f]*4)
    return canon(trans, out)

def is_moore(m):
    return all(len(set(r)) == 1 for r in m[1])

def enumerate_classes(N, log=True):
    """U[n]: classes first reached at size n by any formula; G[n]: by guarded formula.
    first[cls] = (size, formula string) of a smallest realiser (guarded for G)."""
    U = {}; G = {}           # size -> list of classes (new at that size)
    firstU = {}; firstG = {}
    def addU(n, c, s):
        if c not in firstU: firstU[c] = (n, s); U[n].append(c)
    def addG(n, c, s):
        if c not in firstG: firstG[c] = (n, s); G[n].append(c)
    for n in range(1, N+1):
        t0 = time.time()
        U[n] = []; G[n] = []
        if n == 1:
            addU(1, BOT, 'F'); addU(1, P, 'p'); addG(1, BOT, 'F')
        else:
            # unary
            for c in U[n-1]:
                s = firstU[c][1]
                addU(n, neg(c), '~' + s)
                b = box(c); addU(n, b, '[]' + s); addG(n, b, '[]' + s)
            for c in G[n-1]:
                addG(n, neg(c), '~' + firstG[c][1])
            # binary: sizes i + j = n-1
            for i in range(1, n-1):
                j = n - 1 - i
                if i > j: break
                for (pool, first, add) in (((G, firstG, addG),) if n == N else ((U, firstU, addU), (G, firstG, addG))):
                    for ai, a in enumerate(pool[i]):
                        sa = first[a][1]
                        for bi, b in enumerate(pool[j]):
                            if i == j and bi < ai: continue
                            sb = first[b][1]
                            add(n, AND(a, b), '(' + sa + '&' + sb + ')')
                            add(n, OR(a, b), '(' + sa + '|' + sb + ')')
        # guarded classes must also enter U pool (they're formulas too)
        for c in G[n]:
            addU(n, c, firstG[c][1])
    return U, G, firstU, firstG




def tailrun(step,s):
    seen={};tr=[]
    while s not in seen: seen[s]=len(tr); o,s2=step(s); tr.append(o); s=s2
    cyc=tr[seen[s]:]; assert len(set(cyc))==1,cyc; return cyc[0]
def game(A,B):
    TA,OA=A;TB,OB=B
    def step(st):
        sa,sb,da,db=st; a=OA[sa][0]; b=OB[sb][0]
        return (a,b),(TA[sa][b+2*OB[db][0]],TB[sb][a+2*OA[da][0]],TA[da][0],TB[db][0])
    return tailrun(step,(0,0,0,0))

def bxk(k,m):
    for _ in range(k): m=box(m)
    return m
def at(g): return AND(bxk(g+1,BOT),neg(bxk(g,BOT)))
def sig(S,cof=False):
    m=BOT
    for g in S: m=OR(m,at(g))
    return neg(m) if cof else m
def reader(h,a): return box(OR(OR(neg(bxk(h+1,BOT)),bxk(h,BOT)),a))
D=neg(box(AND(neg(P),neg(Q))))
def detector_opp(Sq,cofq,Sp):
    return OR(AND(neg(D),sig(Sq,cofq)),AND(D,sig(Sp)))



def Fk(k): return bxk(k,P)
def Tk(k): return neg(box(OR(neg(P),bxk(k,BOT))))
NMAX=17
U,G,fU,fG=enumerate_classes(NMAX, log=False)
CNT=[len(G[n]) for n in range(1,NMAX+1)]
print('p-only guarded classes per size', CNT)
assert CNT[:15]==[1,3,5,6,9,25,60,102,189,424,925,1854,3755,7981,17063], CNT  # = K51 census counts
assert CNT==[1,3,5,6,9,25,60,102,189,424,925,1854,3755,7981,17063,35721,74728], CNT
for k in range(1,12):
    A=Fk(k);B=Fk(k+1)
    assert game(A,A)==(1,1) and game(B,B)==(1,1) and game(A,B)==(1,1)
    found=None
    for sz in range(1,NMAX+1):
        seps=[o for o in G[sz] if game(A,o)!=game(B,o)]
        if seps: found=(sz,seps);break
    assert found and found[0]==k+6 and found[1]==[Tk(k)], (k,found and (found[0],[fG[o][1] for o in found[1]]))
    assert game(A,Tk(k))==(0,0) and game(B,Tk(k))==(0,1)
k=12; A=Fk(k);B=Fk(k+1)
assert all(game(A,o)==game(B,o) for sz in range(1,NMAX+1) for o in G[sz])
print('engine: k=1..11 min p-only separator size k+6, unique T_k; k=12 none <=17; %.1fs'%(time.time()-t0))

def parse(s):
    i=[0]
    def e():
        c=s[i[0]]
        if c=='(':
            i[0]+=1;a=e();op=s[i[0]];i[0]+=1;b=e();assert s[i[0]]==')';i[0]+=1;return (op,a,b)
        if c=='~': i[0]+=1;return ('~',e())
        if s.startswith('[]',i[0]): i[0]+=2;return ('[]',e())
        i[0]+=1;return c
    t=e();assert i[0]==len(s);return t
def val(f,h,pp,qq,memo):
    key=(id(f),h)
    if key in memo: return memo[key]
    if f=='F': r=0
    elif f=='p': r=pp[h]
    elif f=='q': r=qq[h]
    elif f[0]=='~': r=1-val(f[1],h,pp,qq,memo)
    elif f[0]=='&': r=val(f[1],h,pp,qq,memo)&val(f[2],h,pp,qq,memo)
    elif f[0]=='|': r=val(f[1],h,pp,qq,memo)|val(f[2],h,pp,qq,memo)
    else: r=int(all(val(f[1],g,pp,qq,memo) for g in range(h)))
    memo[key]=r;return r
def size(f): return 1 if isinstance(f,str) else 1+sum(size(x) for x in f[1:])
def lit_game(sa,sb,H=60):
    fa,fb=parse(sa),parse(sb);a=[];b=[];da=[];db=[];ma={};mb={};mda={};mdb={};Z=[0]*H
    for h in range(H):
        da.append(val(fa,h,Z,Z,mda));db.append(val(fb,h,Z,Z,mdb))
        a.append(val(fa,h,b+[None],db+[None],ma));b.append(val(fb,h,a[:-1]+[None],da+[None],mb))
    assert len(set(a[-10:]))==1 and len(set(b[-10:]))==1
    return a[-1],b[-1]
for k in range(1,13):
    tk='~[](~p|'+'[]'*k+'F)'
    assert size(parse(tk))==k+6
    for j in range(1,15):
        fj='[]'*j+'p'
        assert lit_game(fj,tk)==((0,0) if j<=k else (0,1)), (k,j)
print('literal evaluator agrees')

import subprocess, shutil, os, hashlib
LEAN = "-- C046 r1: q-free separator T_k = ~box(~p | box^k F) of F_k = box^k p and F_{k+1} (k = m+1 >= 1).\ninductive Fm where\n  | bot : Fm\n  | p : Fm\n  | q : Fm\n  | neg : Fm → Fm\n  | conj : Fm → Fm → Fm\n  | disj : Fm → Fm → Fm\n  | box : Fm → Fm\n\n-- height semantics; x = partner's move against me (p), y = partner's move against DefectBot (q)\ndef ev (x y : Nat → Prop) : Fm → Nat → Prop\n  | .bot, _ => False\n  | .p, h => x h\n  | .q, h => y h\n  | .neg a, h => ¬ ev x y a h\n  | .conj a b, h => ev x y a h ∧ ev x y b h\n  | .disj a b, h => ev x y a h ∨ ev x y b h\n  | .box a, h => ∀ g, g < h → ev x y a g\n\ndef size : Fm → Nat\n  | .bot => 1\n  | .p => 1\n  | .q => 1\n  | .neg a => size a + 1\n  | .conj a b => size a + size b + 1\n  | .disj a b => size a + size b + 1\n  | .box a => size a + 1\ndef Fl : Nat → Prop := fun _ => False\n-- an agent's DefectBot trace: both inputs false\ndef db (a : Fm) : Nat → Prop := fun h => ev Fl Fl a h\n\n-- K30-style: with constant (false) inputs the trace is constant from the modal depth\ndef boxN : Nat → Fm → Fm\n  | 0, a => a\n  | n+1, a => .box (boxN n a)\n\ntheorem boxN_size (n : Nat) (a : Fm) : size (boxN n a) = n + size a := by\n  induction n with\n  | zero => simp [boxN]\n  | succ n ih => simp only [boxN, size, ih]; omega\n\ntheorem boxN_ev (x y : Nat → Prop) (a : Fm) (n : Nat) :\n    ∀ h, ev x y (boxN (n+1) a) h ↔ ∀ g, g + (n+1) ≤ h → ev x y a g := by\n  induction n with\n  | zero =>\n    intro h; simp only [boxN, ev]\n    exact ⟨fun H g hg => H g (by omega), fun H g hg => H g (by omega)⟩\n  | succ n ih =>\n    intro h\n    show (∀ g, g < h → ev x y (boxN (n+1) a) g) ↔ _\n    constructor\n    · intro H g hg; exact (ih (g + (n+1))).1 (H _ (by omega)) g (Nat.le_refl _)\n    · intro H g hg; exact (ih g).2 (fun g' hg' => H g' (by omega))\n\n-- the agents (k = m+1)\ndef Fk (m : Nat) : Fm := boxN (m+1) .p\n\ndef Sys (A B : Fm) (x y : Nat → Prop) : Prop :=\n  (∀ h, x h ↔ ev y (db B) A h) ∧ (∀ h, y h ↔ ev x (db A) B h)\n\ntheorem fk_ev (m : Nat) (x y : Nat → Prop) (h : Nat) :\n    ev x y (Fk m) h ↔ ∀ g, g + (m+1) ≤ h → x g := boxN_ev x y .p m h\n\ntheorem bot_ev (m : Nat) (x y : Nat → Prop) (g : Nat) : ev x y (boxN (m+1) .bot) g ↔ g < m+1 := by\n  rw [boxN_ev]; constructor\n  · intro H; by_cases c : g < m+1\n    · exact c\n    · exact False.elim (H (g - (m+1)) (by omega))\n  · intro H g' hg'; omega\n\n\ndef Tk (m : Nat) : Fm := .neg (.box (.disj (.neg .p) (boxN (m+1) .bot)))\n\ntheorem tsize (m : Nat) : size (Tk m) = m + 7 := by\n  simp only [Tk, size, boxN_size]; omega\n\ntheorem tk_ev (m : Nat) (x y : Nat → Prop) (h : Nat) :\n    ev x y (Tk m) h ↔ ∃ g, g < h ∧ m + 1 ≤ g ∧ x g := by\n  simp only [Tk, ev]\n  constructor\n  · intro H\n    exact Classical.byContradiction fun N => H fun g hg => by\n      by_cases c : g < m + 1\n      · exact Or.inr ((bot_ev m x y g).2 c)\n      · left; intro xg; exact N ⟨g, hg, by omega, xg⟩\n  · rintro ⟨g, hg, hm, xg⟩ H\n    rcases H g hg with c | c\n    · exact c xg\n    · have := (bot_ev m x y g).1 c; omega\n\n-- T_k (reads the partner's game only) against F_{j+1}\ntheorem t_low (j m : Nat) (hj : j ≤ m) (x y : Nat → Prop) (S : Sys (Fk j) (Tk m) x y) :\n    ∀ h, ¬ y h ∧ (j + 1 ≤ h → ¬ x h) := by\n  have Y0 : ¬ y 0 := by\n    intro H; rw [S.2 0, tk_ev] at H; obtain ⟨g, hg, _, _⟩ := H; omega\n  have X : ∀ h, j + 1 ≤ h → ¬ x h := by\n    intro h hh H; rw [S.1 h, fk_ev] at H; exact Y0 (H 0 (by omega))\n  intro h; refine ⟨?_, X h⟩\n  intro H; rw [S.2 h, tk_ev] at H; obtain ⟨g, _, hm, xg⟩ := H\n  exact X g (by omega) xg\n\ntheorem t_high (j m : Nat) (hj : m < j) (x y : Nat → Prop) (S : Sys (Fk j) (Tk m) x y) :\n    ∀ h, j + 1 ≤ h → y h ∧ ¬ x h := by\n  have Y0 : ¬ y 0 := by\n    intro H; rw [S.2 0, tk_ev] at H; obtain ⟨g, hg, _, _⟩ := H; omega\n  intro h hh; constructor\n  · rw [S.2 h, tk_ev]; refine ⟨m+1, by omega, Nat.le_refl _, ?_⟩\n    rw [S.1, fk_ev]; intro g hg; omega\n  · intro H; rw [S.1 h, fk_ev] at H; exact Y0 (H 0 (by omega))\n\n-- headline: T_k (size k+6, no q) gets DD with F_k from height k and (F_{k+1} D, T_k C) from height k+2\ntheorem psep (m : Nat) :\n    size (Tk m) = m + 7 ∧\n    (∀ x y, Sys (Fk m) (Tk m) x y → ∀ h, m + 1 ≤ h → ¬ x h ∧ ¬ y h) ∧\n    (∀ x y, Sys (Fk (m+1)) (Tk m) x y → ∀ h, m + 2 ≤ h → ¬ x h ∧ y h) := by\n  refine ⟨tsize m, ?_, ?_⟩\n  · intro x y S h hh\n    have A := t_low m m (Nat.le_refl _) x y S h\n    exact ⟨A.2 hh, A.1⟩\n  · intro x y S h hh\n    have A := t_high (m+1) m (by omega) x y S h hh\n    exact ⟨A.2, A.1⟩\n\n#print axioms tk_ev\n#print axioms t_low\n#print axioms t_high\n#print axioms psep\n"
assert hashlib.sha256(LEAN.encode()).hexdigest() == '1aa34cc2b4ed38a7d1a6c658599138c94cf2eb8be874a6b06ea0d936c930255c'
binary = next((p for p in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')) if p and os.path.exists(p)), None)
assert binary, 'lean missing'
def run(src): return subprocess.run([binary, '--stdin'], input=src, text=True, capture_output=True, timeout=100)
r = run(LEAN)
assert r.returncode == 0, (r.stdout + r.stderr)[-3000:]
assert 'sorryAx' not in r.stdout
for t in ('tk_ev','t_low','t_high','psep'):
    assert "'"+t+"' depends on axioms" in r.stdout, t
MUTS = [('def Tk (m : Nat) : Fm := .neg (.box (.disj (.neg .p) (boxN (m+1) .bot)))', 'def Tk (m : Nat) : Fm := .neg (.box (.disj (.neg .p) (boxN m .bot)))'),
        ('theorem t_low (j m : Nat) (hj : j ≤ m)', 'theorem t_low (j m : Nat) (hj : j ≤ m + 1)'),
        ('    ∀ h, j + 1 ≤ h → y h ∧ ¬ x h := by', '    ∀ h, j ≤ h → y h ∧ ¬ x h := by'),
        ('    (∀ x y, Sys (Fk (m+1)) (Tk m) x y → ∀ h, m + 2 ≤ h → ¬ x h ∧ y h)', '    (∀ x y, Sys (Fk (m+1)) (Tk m) x y → ∀ h, m + 2 ≤ h → ¬ x h ∧ ¬ y h)')]
for a, b in MUTS:
    assert LEAN.count(a) == 1, a
    assert run(LEAN.replace(a, b)).returncode != 0, 'mutation accepted: ' + a
print('Lean: 4 theorems, no sorryAx, %d mutations rejected; total %.1fs' % (len(MUTS), time.time()-t0))
print('PASS')
