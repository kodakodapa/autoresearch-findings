"""C046 r1: independent exact cross-check of r2's K19 (F_k height blends of J_{a,b,j}) and a new
separation law: every finite-S F_k blend of J_{a,b,j} cooperates with F_m = box^m p iff m <= j, so F_{j+1}
separates every such blend (in particular every self-cooperating one) from FairBot and from every box^m' p.

Language L: atoms p (opponent's move against me), q (opponent's move against DefectBot); F,~,&,|,[];
guarded; height semantics; outcomes are Boolean tails (no payoffs).
Engine copied verbatim from c046_graded_xcheck.py (K10/K12/K15 engine): minimised Mealy machines on (p,q),
exact games by joint-state cycle detection, exact unexploitability test exploit() (K10), behav()/depth() (K15, K18).
Shares no code with r2's GLS core or Lean files.
J_{a,b,j} = box^{a+1}(box^b p & (q | box(box^j F | ~q))); blend B = (sigma_S & F_k) | (~sigma_S & J).
Grid: 1 <= a+b <= 4 (a,b >= 0), 1 <= j <= a+b, k = 1..3, S = any subset of {0..5} plus tail {h>=6} in/out:
15360 blends. Asserted for each: DefectBot trace d(h) = (S(h)&h<k)|(~S(h)&h<a+b+1); r2's general obstruction
law (E = {g: ~d(g), exists f, j<=f<g, d(f)}; self CC iff every h >= g+a+1 for g in E is selected, else DD);
r2's finite interval law (CC iff k<=j and {j..a+b} in S); exploit None; vs DB DD, vs FB CC, vs CB CC.
New: for finite S (tail out), all 7680 blends: B vs F_m CC iff m <= j, else DD (m = 1..7); FB vs F_m CC.
No self-CC blend with finite S is behaviourally FairBot (depth() never None); 80 cofinite ones are.
Lean 4 core (SHA-pinned): fm_db, fm_coop (m<=j: all-height CC for every S), fm_defect (j<m, finite S:
both eventually defect), fm_fm (F_m vs F_m' CC), separator; no sorryAx; 3 mutations rejected.
Height-trace bridge for modal fixed points assumed as in earlier claims.
"""
import hashlib, os, shutil, subprocess
import time
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

def behav(m):
    T,O=m;idx={};st=[];tr=[];out=[];SINK=('sink',)
    def get(s):
        if s not in idx: idx[s]=len(st);st.append(s)
        return idx[s]
    get((0,0,0));k=0
    while k<len(st):
        s=st[k];k+=1
        if s==SINK: tr.append([idx[SINK]]*4);out.append([4]*4);continue
        sa,sd,ph=s;a=O[sa][0];d=O[sd][0];nph=1 if (ph or a or d) else 0
        tr.append([get(SINK) if (not ph and i in (1,2)) else get((T[sa][i],T[sd][0],nph)) for i in range(4)])
        out.append([a+2*d]*4)
    return canon(tr,out)
def depth(m1, m2):
    (T1, O1), (T2, O2) = m1, m2
    seen = {(0, 0)}; frontier = [(0, 0)]; h = 0
    while frontier:
        nxt = []
        for a, b in frontier:
            if O1[a][0] != O2[b][0]: return h
            for i in INPUTS:
                s = (T1[a][i], T2[b][i])
                if s not in seen: seen.add(s); nxt.append(s)
        frontier = nxt; h += 1
    return None

t0 = time.time()
FB = box(P); CB = neg(BOT); DB = BOT
L = 6
ATS = [at(g) for g in range(L)]
TAIL = neg(bxk(L, BOT))
def sigma(Sfin, tail):
    m = TAIL if tail else BOT
    for g in Sfin: m = OR(m, ATS[g])
    return m
def J(a, b, j): return bxk(a + 1, AND(bxk(b, P), OR(Q, box(OR(bxk(j, BOT), neg(Q))))))
def blend(sg, R, A): return OR(AND(sg, R), AND(neg(sg), A))
def dbtrace(m, H):
    T, O = m; s = 0; out = []
    for _ in range(H): out.append(O[s][0]); s = T[s][0]
    return out
CC, DD = (1, 1), (0, 0)
Fm = {m: bxk(m, P) for m in range(1, 8)}
def PB(i): return AND(box(P), box(OR(neg(neg(bxk(i, BOT))), neg(Q))))   # P_i = []p & [](~[]^i F -> ~q)
BANK = [('DB', DB), ('CB', CB)] + [('F%d' % m, Fm[m]) for m in range(2, 8)] + [('P%d' % i, PB(i)) for i in range(0, 7)]
FBb = behav(FB)
LEAN = "def blend (S f g : Nat → Prop) (h : Nat) := (S h ∧ f h) ∨ (¬ S h ∧ g h)\ndef eventual (x : Nat → Prop) := ∃ H, ∀ h, H ≤ h → x h\n-- normalized J_{a,b,j} = box^{a+1}(box^b p ∧ (q ∨ box(box^j F ∨ ¬q))), as in r2's j_self.lean `normalized`\ndef gate (a b j : Nat) (p q : Nat → Prop) (h : Nat) :=\n (∀ u, u+a+b+1 ≤ h → p u) ∧\n (∀ g, g+a+1 ≤ h → q g ∨ ∀ f, j ≤ f → f < g → ¬ q f)\n\n/-- F_m = box^m p against DefectBot cooperates exactly below height m. -/\ntheorem fm_db (m h : Nat) : (∀ u, u+m ≤ h → False) ↔ h < m := by\n constructor\n · intro H; apply Classical.byContradiction; intro e; exact H 0 (by omega)\n · intro H u uh; omega\n\n/-- x = moves of the F_k height blend of J_{a,b,j} (selection S) against F_m, y = F_m's moves;\n    F_m's DefectBot trace is (g < m). If m ≤ j both cooperate at every height, for every S. -/\ntheorem fm_coop (a b j k m : Nat) (hk : 1 ≤ k) (hm : 1 ≤ m) (mj : m ≤ j) (S x y : Nat → Prop)\n (ex : ∀ h, x h ↔ blend S (fun h => ∀ u, u+k ≤ h → y u) (gate a b j y (fun g => g < m)) h)\n (ey : ∀ h, y h ↔ ∀ u, u+m ≤ h → x u) : ∀ h, x h ∧ y h := by\n classical\n intro h\n induction h using Nat.strongRecOn with\n | ind h ih =>\n   constructor\n   · apply (ex h).2\n     by_cases sh : S h\n     · exact Or.inl ⟨sh, fun u uh => (ih u (by omega)).2⟩\n     · exact Or.inr ⟨sh, ⟨fun u uh => (ih u (by omega)).2,\n         fun g _ => Or.inr (fun f jf _ fm => by omega)⟩⟩\n   · exact (ey h).2 (fun u uh => (ih u (by omega)).1)\n\n/-- If j < m and S is finite, both eventually defect. -/\ntheorem fm_defect (a b j k m M : Nat) (jm : j < m) (S x y : Nat → Prop)\n (fin : ∀ h, M ≤ h → ¬ S h)\n (ex : ∀ h, x h ↔ blend S (fun h => ∀ u, u+k ≤ h → y u) (gate a b j y (fun g => g < m)) h)\n (ey : ∀ h, y h ↔ ∀ u, u+m ≤ h → x u) :\n eventual (fun h => ¬ x h) ∧ eventual (fun h => ¬ y h) := by\n classical\n let h0 := M+m+a+1\n have nx0 : ¬ x h0 := by\n   intro xh\n   rcases (ex h0).1 xh with ⟨sh,_⟩ | ⟨_,_,hq⟩\n   · exact fin h0 (by omega) sh\n   · rcases hq m (by omega) with lt | hh\n     · omega\n     · exact hh j (by omega) jm jm\n have ny : ∀ h, h0+m ≤ h → ¬ y h := fun h hh yh => nx0 ((ey h).1 yh h0 (by omega))\n refine ⟨⟨h0+m+k+a+b+1, ?_⟩, ⟨h0+m, ny⟩⟩\n intro h hh xh\n rcases (ex h).1 xh with ⟨_,hf⟩ | ⟨_,hp,_⟩\n · exact ny (h0+m) (by omega) (hf (h0+m) (by omega))\n · exact ny (h0+m) (by omega) (hp (h0+m) (by omega))\n\n/-- FairBot-type agents F_m, F_m' (m, m' ≥ 1) cooperate with each other at every height. -/\ntheorem fm_fm (m m' : Nat) (hm : 1 ≤ m) (hm' : 1 ≤ m') (x y : Nat → Prop)\n (ex : ∀ h, x h ↔ ∀ u, u+m ≤ h → y u) (ey : ∀ h, y h ↔ ∀ u, u+m' ≤ h → x u) :\n ∀ h, x h ∧ y h := by\n intro h\n induction h using Nat.strongRecOn with\n | ind h ih =>\n   exact ⟨(ex h).2 (fun u uh => (ih u (by omega)).2), (ey h).2 (fun u uh => (ih u (by omega)).1)⟩\n\n/-- Separation: for finite S, F_{j+1} gets mutual defection from the blend but mutual\n    cooperation from every F_{m'} (m' ≥ 1, including FairBot m'=1). -/\ntheorem separator (a b j k M m' : Nat) (hm' : 1 ≤ m') (S x y u v : Nat → Prop)\n (fin : ∀ h, M ≤ h → ¬ S h)\n (ex : ∀ h, x h ↔ blend S (fun h => ∀ w, w+k ≤ h → y w) (gate a b j y (fun g => g < j+1)) h)\n (ey : ∀ h, y h ↔ ∀ w, w+(j+1) ≤ h → x w)\n (eu : ∀ h, u h ↔ ∀ w, w+m' ≤ h → v w) (ev : ∀ h, v h ↔ ∀ w, w+(j+1) ≤ h → u w) :\n eventual (fun h => ¬ x h) ∧ (∀ h, u h ∧ v h) :=\n ⟨(fm_defect a b j k (j+1) M (by omega) S x y fin ex ey).1, fm_fm m' (j+1) hm' (by omega) u v eu ev⟩\n\n#print axioms fm_db\n#print axioms fm_coop\n#print axioms fm_defect\n#print axioms fm_fm\n#print axioms separator\n"
assert hashlib.sha256(LEAN.encode()).hexdigest() == '67e017b510c8e993eb1ae04d5c6f89163cc4ee8764b940e8522830ed08340ce1'

nb = 0; fmc = 0; selfcc_fin = 0; fbeq = 0; fbeq_fin = 0
for m in range(1, 8): assert game(FB, Fm[m]) == CC
for s_ in range(1, 5):
    for a in range(0, s_ + 1):
        b = s_ - a
        for j in range(1, a + b + 1):
            A = J(a, b, j)
            assert game(A, A) == DD and exploit(A) is None
            for k in range(1, 4):
                Fk = Fm[k]
                for bits in range(1 << L):
                    Sfin = [g for g in range(L) if bits >> g & 1]
                    for tail in (False, True):
                        inS = lambda h: (h in Sfin) if h < L else tail
                        B = blend(sigma(Sfin, tail), Fk, A)
                        H = L + a + b + k + 4
                        d = [(inS(h) and h < k) or (not inS(h) and h < a + b + 1) for h in range(H)]
                        assert dbtrace(B, H) == [int(x) for x in d], (a, b, j, k, Sfin, tail)
                        E = [g for g in range(H) if not d[g] and any(d[f] for f in range(j, g))]
                        law = all(inS(h) for g in E for h in range(g + a + 1, g + a + 2 + H))
                        got = game(B, B)
                        assert got == (CC if law else DD), ('self', a, b, j, k, Sfin, tail, got)
                        assert exploit(B) is None, ('exploitable', a, b, j, k, Sfin, tail)
                        assert game(B, DB) == DD and game(B, FB) == CC and game(B, CB) == CC
                        if not tail:
                            assert law == (k <= j and all(f in Sfin for f in range(j, a + b + 1))), ('finite', a, b, j, k, Sfin)
                            for m in range(1, 8):
                                assert game(B, Fm[m]) == (CC if m <= j else DD), ('Fm', a, b, j, k, Sfin, m)
                                fmc += 1
                        if got == CC:
                            eq = depth(behav(B), FBb) is None
                            fbeq += eq
                            if not tail: selfcc_fin += 1; assert not eq
                        nb += 1
assert nb == 15360 and fmc == 7680 * 7, (nb, fmc)
assert selfcc_fin == 1668 and fbeq == 80, (selfcc_fin, fbeq)
# hand example from K19: J_{1,1,1}, FairBot at {1,2}
B = blend(sigma([1, 2], False), FB, J(1, 1, 1))
assert game(B, B) == CC and game(B, Fm[2]) == DD and game(FB, Fm[2]) == CC and game(B, Fm[1]) == CC
t1 = time.time()
binary = next((p for p in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')) if p and os.path.exists(p)), None)
assert binary, 'lean missing'
def run(s): return subprocess.run([binary, '--stdin'], input=s, text=True, capture_output=True, timeout=100)
r = run(LEAN)
assert r.returncode == 0, r.stdout + r.stderr
assert 'sorryAx' not in r.stdout and r.stdout.count('depends on axioms') == 5, r.stdout
for x, y in [('(mj : m ≤ j)', '(mj : m ≤ j+1)'), ('(jm : j < m)', '(jm : j ≤ m)'), ('(hm\' : 1 ≤ m\') (S x y u v', '(hm\' : 0 ≤ m\') (S x y u v')]:
    assert LEAN.count(x) == 1, x
    assert run(LEAN.replace(x, y)).returncode != 0, ('mutation accepted', y)
print('PASS: %d J blends: K19 DB trace, obstruction law, finite interval law, unexploitable, DB/FB/CB cells; '
      '%d finite-S cells vs F_m (CC iff m<=j); %d finite self-CC blends none FB-equivalent; %d cofinite FB-equivalent; '
      'Lean 5 theorems, 3 mutations rejected (%.1fs)' % (nb, fmc, selfcc_fin, fbeq, time.time() - t0))
