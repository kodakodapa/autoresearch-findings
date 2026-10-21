"""C046 r1: minimal separator between consecutive graded FairBots F_k = []^k p and F_{k+1}.
Language L: atoms p (opponent's move vs me), q (opponent's move vs DefectBot); F,~,&,|,[];
guarded; size = AST nodes; height semantics; game wiring as in K38 (p = partner's game, q = partner's DB trace).
S_k = [](~q | []^k F), size k+5.
Part 1 (Lean 4 core, SHA-pinned, all k = m+1 >= 1): sizes, sk_ev, sep_coop (S_k with F_j, j<=k: CC at every
 height), sep_defect (j>k: S_k defects from k+1, F_j from k+1+j), fk_fk (F_i/F_j CC at every height), separator
 (S_k: CC with F_k, DD from 2k+2 with F_{k+1}). No sorryAx; 4 mutations rejected.
Part 2 (exact Mealy engine, verbatim from c046_xk_gap.py) over all guarded classes of size <= 13
 (36062 new at 12, 100823 new at 13): for k=1..8 no opponent of size <= k+4 separates F_k from F_{k+1};
 at size k+5 exactly one machine class does, S_k. (Extends K49's k<=6 to k<=8.) F_k, F_{k+1}, both unexploitable, self CC.
Part 3 (independent literal height evaluator, H=60): S_k vs F_j CC iff j<=k, else DD, for k=1..10, j=1..12.
Lower bound beyond k=8 is NOT proved (only the size-(k+5) upper bound is general).
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
            addU(1, BOT, 'F'); addU(1, P, 'p'); addU(1, Q, 'q'); addG(1, BOT, 'F')
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
                for (pool, first, add) in ((U, firstU, addU), (G, firstG, addG)):
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


def exploit(m):
    """None if unexploitable, else an explicit exploiter (re-solved by caller)."""
    T,O=m
    par={(0,0):None};st=deque([(0,0)]);post={}
    while st:
        s=st.popleft();sa,sd=s;det=O[sa][0] or O[sd][0]
        for x in (0,3):
            nx=T[sa][x]
            if det:
                if nx not in post: post[nx]=(s,x)
            else:
                ns=(nx,T[sd][0])
                if ns not in par: par[ns]=(s,x);st.append(ns)
    ppar={s:('pre',)+post[s] for s in post};st=deque(post)
    while st:
        s=st.popleft()
        for i in range(4):
            t=T[s][i]
            if t not in ppar: ppar[t]=('post',s,i);st.append(t)
    for s0 in ppar:
        for c in (0,1):
            if tailrun(lambda s:(O[s][0],T[s][2*c]),s0)==1:
                w=[];t=s0
                while True:
                    e=ppar[t]
                    if e[0]=='pre': w.append(e[2]);t=e[1];break
                    w.append(e[2]);t=e[1]
                while par[t] is not None: t,i=par[t];w.append(i)
                w.reverse();L=len(w)
                Sq=[g for g in range(L) if w[g]>>1]; Sp=[g for g in range(L) if w[g]&1]
                if c: Sq=[g for g in range(L) if not w[g]>>1]
                return detector_opp(Sq,bool(c),Sp)
    return None



def Fk(k): return bxk(k,P)
def Sk(k): return box(OR(neg(Q),bxk(k,BOT)))
NMAX=13
U,G,fU,fG=enumerate_classes(NMAX, log=False)
CNT=[len(G[n]) for n in range(1,NMAX+1)]
print('classes per size', CNT)
assert CNT[:9]==[1, 4, 8, 12, 31, 98, 255, 646, 1760], CNT
assert CNT==[1, 4, 8, 12, 31, 98, 255, 646, 1760, 4746, 12880, 36062, 100823], CNT
for k in range(1,9):
    A=Fk(k);B=Fk(k+1)
    assert exploit(A) is None and exploit(B) is None
    assert game(A,A)==(1,1) and game(B,B)==(1,1) and game(A,B)==(1,1)
    found=None
    for sz in range(1,NMAX+1):
        seps=[o for o in G[sz] if game(A,o)!=game(B,o)]
        if seps: found=(sz,seps);break
    if k<=8:
        assert found and found[0]==k+5 and found[1]==[Sk(k)], (k,found and (found[0],[fG[o][1] for o in found[1]]))
        assert game(Sk(k),A)==(1,1) and game(Sk(k),B)==(0,0)
    else:
        assert found is None, k
print('engine: k=1..8 min separator size k+5, unique S_k (classes up to size 13); %.1fs'%(time.time()-t0))

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
for k in range(1,11):
    sk='[](~q|'+'[]'*k+'F)'
    assert size(parse(sk))==k+5
    for j in range(1,13):
        fj='[]'*j+'p'
        assert lit_game(sk,fj)==((1,1) if j<=k else (0,0)), (k,j)
print('literal evaluator agrees')

import subprocess, shutil, os, hashlib
LEAN = "-- C046 r1: X_k = box^k p & box(box^k F | q | ~box q) versus F_k = box^k p (k = m+1 >= 1).\ninductive Fm where\n  | bot : Fm\n  | p : Fm\n  | q : Fm\n  | neg : Fm → Fm\n  | conj : Fm → Fm → Fm\n  | disj : Fm → Fm → Fm\n  | box : Fm → Fm\n\n-- height semantics; x = partner's move against me (p), y = partner's move against DefectBot (q)\ndef ev (x y : Nat → Prop) : Fm → Nat → Prop\n  | .bot, _ => False\n  | .p, h => x h\n  | .q, h => y h\n  | .neg a, h => ¬ ev x y a h\n  | .conj a b, h => ev x y a h ∧ ev x y b h\n  | .disj a b, h => ev x y a h ∨ ev x y b h\n  | .box a, h => ∀ g, g < h → ev x y a g\n\ndef size : Fm → Nat\n  | .bot => 1\n  | .p => 1\n  | .q => 1\n  | .neg a => size a + 1\n  | .conj a b => size a + size b + 1\n  | .disj a b => size a + size b + 1\n  | .box a => size a + 1\ndef Fl : Nat → Prop := fun _ => False\n-- an agent's DefectBot trace: both inputs false\ndef db (a : Fm) : Nat → Prop := fun h => ev Fl Fl a h\n\n-- K30-style: with constant (false) inputs the trace is constant from the modal depth\ndef boxN : Nat → Fm → Fm\n  | 0, a => a\n  | n+1, a => .box (boxN n a)\n\ntheorem boxN_size (n : Nat) (a : Fm) : size (boxN n a) = n + size a := by\n  induction n with\n  | zero => simp [boxN]\n  | succ n ih => simp only [boxN, size, ih]; omega\n\ntheorem boxN_ev (x y : Nat → Prop) (a : Fm) (n : Nat) :\n    ∀ h, ev x y (boxN (n+1) a) h ↔ ∀ g, g + (n+1) ≤ h → ev x y a g := by\n  induction n with\n  | zero =>\n    intro h; simp only [boxN, ev]\n    exact ⟨fun H g hg => H g (by omega), fun H g hg => H g (by omega)⟩\n  | succ n ih =>\n    intro h\n    show (∀ g, g < h → ev x y (boxN (n+1) a) g) ↔ _\n    constructor\n    · intro H g hg; exact (ih (g + (n+1))).1 (H _ (by omega)) g (Nat.le_refl _)\n    · intro H g hg; exact (ih g).2 (fun g' hg' => H g' (by omega))\n\n-- the agents (k = m+1)\ndef Fk (m : Nat) : Fm := boxN (m+1) .p\n\n-- separator S_k = box(~q | box^k F), k = m+1\ndef Sk (m : Nat) : Fm := .box (.disj (.neg .q) (boxN (m+1) .bot))\n\ndef Sys (A B : Fm) (x y : Nat → Prop) : Prop :=\n  (∀ h, x h ↔ ev y (db B) A h) ∧ (∀ h, y h ↔ ev x (db A) B h)\n\ntheorem sizes (m : Nat) : size (Fk m) = m + 2 ∧ size (Sk m) = m + 6 := by\n  constructor\n  · show size (boxN (m+1) .p) = m + 2\n    rw [boxN_size]; rfl\n  · simp only [Sk, size, boxN_size]; omega\n\ntheorem fk_ev (m : Nat) (x y : Nat → Prop) (h : Nat) :\n    ev x y (Fk m) h ↔ ∀ g, g + (m+1) ≤ h → x g := boxN_ev x y .p m h\n\ntheorem bot_ev (m : Nat) (x y : Nat → Prop) (g : Nat) : ev x y (boxN (m+1) .bot) g ↔ g < m+1 := by\n  rw [boxN_ev]; constructor\n  · intro H; by_cases c : g < m+1\n    · exact c\n    · exact False.elim (H (g - (m+1)) (by omega))\n  · intro H g' hg'; omega\n\ntheorem sk_ev (m : Nat) (x y : Nat → Prop) (h : Nat) :\n    ev x y (Sk m) h ↔ ∀ g, g < h → (¬ y g ∨ g < m+1) := by\n  simp only [Sk, ev]\n  constructor\n  · intro H g hg; rcases H g hg with c | c\n    · exact Or.inl c\n    · exact Or.inr ((bot_ev m x y g).1 c)\n  · intro H g hg; rcases H g hg with c | c\n    · exact Or.inl c\n    · exact Or.inr ((bot_ev m x y g).2 c)\n\ntheorem db_fk (m h : Nat) : db (Fk m) h ↔ h < m+1 := by\n  simp only [db]; rw [fk_ev]; simp only [Fl]\n  constructor\n  · intro H; by_cases c : h < m+1\n    · exact c\n    · exact False.elim (H (h - (m+1)) (by omega))\n  · intro H g hg; omega\n\n-- S_k against F_{j+1}: cooperation at every height iff j <= m\ntheorem sep_coop (j m : Nat) (hj : j ≤ m) (x y : Nat → Prop) (S : Sys (Fk j) (Sk m) x y) :\n    ∀ h, x h ∧ y h := by\n  have Y : ∀ h, y h := by\n    intro h; rw [S.2 h, sk_ev]; intro g hg\n    by_cases c : g < m+1\n    · exact Or.inr c\n    · left; intro H; rw [db_fk] at H; omega\n  intro h; refine ⟨?_, Y h⟩\n  rw [S.1 h, fk_ev]; intro g _; exact Y g\n\ntheorem sep_defect (j m : Nat) (hj : m < j) (x y : Nat → Prop) (S : Sys (Fk j) (Sk m) x y) :\n    ∀ h, m + 2 ≤ h → ¬ y h ∧ ¬ x (h + j + 1) := by\n  have NY : ∀ h, m + 2 ≤ h → ¬ y h := by\n    intro h hh H\n    rw [S.2 h, sk_ev] at H\n    rcases H (m+1) (by omega) with c | c\n    · exact c ((db_fk j (m+1)).2 (by omega))\n    · omega\n  intro h hh; refine ⟨NY h hh, ?_⟩\n  intro H; rw [S.1 _, fk_ev] at H\n  exact NY h hh (H h (by omega))\n\n-- F_k and F_{k+1} cooperate with each other at every height\ntheorem fk_fk (i j : Nat) (x y : Nat → Prop) (S : Sys (Fk i) (Fk j) x y) : ∀ h, x h ∧ y h := by\n  have : ∀ n, ∀ h, h < n → x h ∧ y h := by\n    intro n; induction n with\n    | zero => intro h hh; omega\n    | succ n ih =>\n      intro h hh\n      constructor\n      · rw [S.1 h, fk_ev]; intro g hg; exact (ih g (by omega)).2\n      · rw [S.2 h, fk_ev]; intro g hg; exact (ih g (by omega)).1\n  intro h; exact this (h+1) h (by omega)\n\n-- headline: S_k (size k+5) separates F_k (CC) from F_{k+1} (DD from height 2k+2)\ntheorem separator (m : Nat) :\n    size (Sk m) = m + 6 ∧\n    (∀ x y, Sys (Fk m) (Sk m) x y → ∀ h, x h ∧ y h) ∧\n    (∀ x y, Sys (Fk (m+1)) (Sk m) x y → ∀ h, 2 * m + 4 ≤ h → ¬ x h ∧ ¬ y h) := by\n  refine ⟨(sizes m).2, fun x y S => sep_coop m m (Nat.le_refl _) x y S, ?_⟩\n  intro x y S h hh\n  have A := sep_defect (m+1) m (by omega) x y S\n  refine ⟨?_, (A h (by omega)).1⟩\n  have := (A (h - (m+2)) (by omega)).2\n  have e : h - (m+2) + (m+1) + 1 = h := by omega\n  rw [e] at this; exact this\n\n#print axioms sizes\n#print axioms sk_ev\n#print axioms sep_coop\n#print axioms sep_defect\n#print axioms fk_fk\n#print axioms separator\n"
assert hashlib.sha256(LEAN.encode()).hexdigest() == 'c51e4cde6350c83f6912d0db6c1b6487e04c7e32b4de8913bf82854235950bca'
binary = next((p for p in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')) if p and os.path.exists(p)), None)
assert binary, 'lean missing'
def run(src): return subprocess.run([binary, '--stdin'], input=src, text=True, capture_output=True, timeout=100)
r = run(LEAN)
assert r.returncode == 0, (r.stdout + r.stderr)[-3000:]
assert 'sorryAx' not in r.stdout
for t in ('sizes','sk_ev','sep_coop','sep_defect','fk_fk','separator'):
    assert "'"+t+"' depends on axioms" in r.stdout, t
MUTS = [('def Sk (m : Nat) : Fm := .box (.disj (.neg .q) (boxN (m+1) .bot))', 'def Sk (m : Nat) : Fm := .box (.disj (.neg .q) (boxN m .bot))'),
        ('theorem sep_coop (j m : Nat) (hj : j ≤ m)', 'theorem sep_coop (j m : Nat) (hj : j ≤ m + 1)'),
        ('    ∀ h, m + 2 ≤ h → ¬ y h ∧ ¬ x (h + j + 1) := by', '    ∀ h, m + 1 ≤ h → ¬ y h ∧ ¬ x (h + j + 1) := by'),
        ('    (∀ x y, Sys (Fk (m+1)) (Sk m) x y → ∀ h, 2 * m + 4 ≤ h', '    (∀ x y, Sys (Fk (m+1)) (Sk m) x y → ∀ h, 2 * m + 3 ≤ h')]
for a, b in MUTS:
    assert LEAN.count(a) == 1, a
    assert run(LEAN.replace(a, b)).returncode != 0, 'mutation accepted: ' + a
print('Lean: 6 theorems, no sorryAx, %d mutations rejected; total %.1fs' % (len(MUTS), time.time()-t0))
print('PASS')
