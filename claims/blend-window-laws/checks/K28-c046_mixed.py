"""C046 r1: mixed selectors. Any height blend that plays DefectBot at some height cannot end CC
with FairBot or any graded FairBot F_k = box^k p, whatever its other branches.
Part 1, Lean 4 core (height semantics; a = agent's moves against F_k, f = F_k's moves):
  fk_cc_iff: eventual mutual cooperation with F_k iff the agent cooperates at every height of that game;
  fk_defects: a defection at s makes F_k defect at every height >= s+k;
  db_height_blocks: a blend defecting at every DefectBot-selected height, with one selected height s,
  cannot end CC with F_k, F_k ends D, and if the agent is unexploitable (eventual a -> eventual f) it ends D.
  Three mutations must be rejected. Bridge assumed as in prior runs (closed fixed points on the height chain).
Part 2, independent literal-formula evaluator (incremental box evaluation, guardedness asserted):
  mixed blends M = (selA & box^k p) | (selD & F) | (~selA & ~selD & V_{n,r}), V_{n,r} = box(box^n F | (p & (q | ~box^r q))),
  W_n = V_{n,1}; n=1..4, r=1..n+1, k=1,2; labels V/A/D arbitrary on heights 0..3 and constant from 4
  (243 labelings): 6804 blends, each vs itself, F_1, F_2, F_3, CooperateBot; heights 0..39, tails = last 10.
  Asserts: CC with F_m iff all-height cooperation; any D label => DD with F_1..F_3 and F_m defects from s+m;
  no D label => K22 law (CC iff m+r<=n or all h>max(n,m) labelled A); every self-CC & FB-CC blend has no D label.
  Finite corroboration of the general Lean statements.
"""
import subprocess, shutil, os, hashlib, itertools, time
LEAN = '-- Graded FairBot F_k = box^k p at height h: partner cooperated at every g with g + k ≤ h.\ndef eventual (p : Nat → Prop) : Prop := ∃ H, ∀ h, H ≤ h → p h\n\n/-- Against F_k (k ≥ 1), mutual eventual cooperation holds iff the agent cooperates at every height. -/\ntheorem fk_cc_iff (k : Nat) (a f : Nat → Prop) (feq : ∀ h, f h ↔ ∀ g, g + k ≤ h → a g) :\n    eventual (fun h => a h ∧ f h) ↔ ∀ h, a h := by\n  constructor\n  · intro ⟨H, hH⟩ s\n    apply Classical.byContradiction\n    intro ns\n    exact ns (((feq (H + s + k)).1 (hH _ (by omega)).2) s (by omega))\n  · intro all\n    exact ⟨0, fun h _ => ⟨all h, (feq h).2 (fun g _ => all g)⟩⟩\n\n/-- A defection at s makes F_k defect at every height ≥ s + k. -/\ntheorem fk_defects (k : Nat) (a f : Nat → Prop) (feq : ∀ h, f h ↔ ∀ g, g + k ≤ h → a g)\n    (s : Nat) (hs : ¬ a s) : ∀ h, s + k ≤ h → ¬ f h :=\n  fun h hh hf => hs (((feq h).1 hf) s hh)\n\n/-- Any height blend that plays DefectBot at a selected height s (whatever its other branches)\n    cannot end CC with F_k; if it is unexploitable against F_k it does not eventually cooperate. -/\ntheorem db_height_blocks (k : Nat) (D a f : Nat → Prop)\n    (blend : ∀ h, D h → ¬ a h) (feq : ∀ h, f h ↔ ∀ g, g + k ≤ h → a g)\n    (s : Nat) (hs : D s) (unexpl : eventual a → eventual f) :\n    ¬ eventual (fun h => a h ∧ f h) ∧ ¬ eventual f ∧ ¬ eventual a := by\n  have nf : ¬ eventual f := fun ⟨H, hH⟩ =>\n    fk_defects k a f feq s (blend s hs) (H + s + k) (by omega) (hH _ (by omega))\n  refine ⟨fun hc => blend s hs ((fk_cc_iff k a f feq).1 hc s), nf, fun ha => nf (unexpl ha)⟩\n\n#print axioms fk_cc_iff\n#print axioms db_height_blocks\n'
assert hashlib.sha256(LEAN.encode()).hexdigest() == '8d424f5617022837ae08d4082a2970bf36e6d423c93792eb9128c97f9c3fc422'
binary = next((p for p in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')) if p and os.path.exists(p)), None)
assert binary, 'lean missing'
def run(src):
    return subprocess.run([binary, '--stdin'], input=src, text=True, capture_output=True, timeout=60)
r = run(LEAN)
assert r.returncode == 0, r.stdout + r.stderr
assert 'sorryAx' not in r.stdout and "'db_height_blocks' depends on axioms" in r.stdout, r.stdout
mutations = [
    ("eventual (fun h => a h ∧ f h) ↔ ∀ h, a h := by", "eventual (fun h => a h ∧ f h) ↔ ∀ h, 1 ≤ h → a h := by"),
    ("(s : Nat) (hs : D s) (unexpl : eventual a → eventual f)", "(s : Nat) (hs : D s) (unexpl : True)"),
    ("(blend : ∀ h, D h → ¬ a h)", "(blend : ∀ h, D h → a h)"),
]
for a_, b_ in mutations:
    assert LEAN.count(a_) == 1, a_
    m_ = run(LEAN.replace(a_, b_))
    assert m_.returncode != 0, ('mutation accepted', b_)
# ---- literal evaluator, incremental: node values per height; box = running AND over earlier heights
H = 40
def boxn(k, f):
    for _ in range(k): f = ('box', f)
    return f
def V(n, r): return ('box', ('or', boxn(n, ('F',)), ('and', ('p',), ('or', ('q',), ('not', boxn(r, ('q',)))))))
def MIX(n, r, k):  # labels: 'A' = F_k branch, 'D' = DefectBot branch, else V_{n,r}
    return ('or', ('or', ('and', ('selA',), boxn(k, ('p',))), ('and', ('selD',), ('F',))),
            ('and', ('and', ('not', ('selA',)), ('not', ('selD',))), V(n, r)))
FK = lambda m: boxn(m, ('p',))
CB, DB = ('not', ('F',)), ('F',)
def nodes(f, out):
    for c in f[1:]: nodes(c, out)
    out.append(f); return out
class Agent:
    def __init__(self, f, lab):
        self.order = nodes(f, []); self.f = f; self.lab = lab
        self.run = {id(x): True for x in self.order}
    def eval(self, h, P, Q):
        val = {}
        for x in self.order:
            t = x[0]; i = id(x)
            if t == 'F': v = False
            elif t == 'p': v = P(h)
            elif t == 'q': v = Q(h)
            elif t == 'selA': v = self.lab(h) == 'A'
            elif t == 'selD': v = self.lab(h) == 'D'
            elif t == 'not': v = None if val[id(x[1])] is None else not val[id(x[1])]
            elif t == 'and':
                u, w = val[id(x[1])], val[id(x[2])]
                v = False if (u is False or w is False) else (None if (u is None or w is None) else True)
            elif t == 'or':
                u, w = val[id(x[1])], val[id(x[2])]
                v = True if (u is True or w is True) else (None if (u is None or w is None) else False)
            elif t == 'box': v = self.run[i]
            val[i] = v
        return val
    def move(self, h, P, Q):  # partner inputs at h unknown (None): guardedness makes the move defined
        v = self.eval(h, lambda g: None, Q)[id(self.f)]
        assert v is not None, 'unguarded'
        return v
    def commit(self, h, P, Q):  # inputs at h now known: update the running ANDs of every box
        val = self.eval(h, P, Q)
        for x in self.order:
            if x[0] == 'box':
                assert val[id(x[1])] is not None
                self.run[id(x)] = self.run[id(x)] and val[id(x[1])]
def dbtrace(f, lab):
    a = Agent(f, lab); out = []
    for h in range(H):
        out.append(a.move(h, None, lambda g: False)); a.commit(h, lambda g: False, lambda g: False)
    return out
def play(f1, l1, f2, l2):
    d1, d2 = dbtrace(f1, l1), dbtrace(f2, l2)
    a, b = Agent(f1, l1), Agent(f2, l2); A, B = [], []
    for h in range(H):  # q = partner's DefectBot trace, p = partner's move against me
        A.append(a.move(h, None, lambda g: d2[g])); B.append(b.move(h, None, lambda g: d1[g]))
        a.commit(h, lambda g: B[g], lambda g: d2[g]); b.commit(h, lambda g: A[g], lambda g: d1[g])
    return A, B
def tail(T):
    assert len(set(T[-10:])) == 1; return T[-1]
# sanity: known cells
lab0 = lambda h: None
assert tail(play(V(2,1), lab0, V(2,1), lab0)[0]) is False          # W_2 self DD
assert tail(play(V(2,1), lab0, FK(1), lab0)[0]) is True             # W_2 vs FB CC
w21 = lambda h: 'A' if h == 1 else None
A,B = play(MIX(2,1,1), w21, MIX(2,1,1), w21); assert tail(A) and tail(B)   # K5 self CC
A,B = play(MIX(2,1,1), w21, FK(2), lab0); assert not tail(A) and not tail(B) # K5 vs F2 DD
d0 = lambda h: 'D' if h == 0 else None
A,B = play(MIX(2,1,1), d0, MIX(2,1,1), d0); assert tail(A)         # K8 self CC
A,B = play(MIX(2,1,1), d0, FK(1), lab0); assert not tail(A) and not tail(B)  # K8 vs FB DD
import itertools, time
t0 = time.time()
T = 4  # labels arbitrary at heights 0..T-1, constant label from T
cnt = dict(blends=0, withD=0, selfCC_withD=0, selfCC_fbCC=0, cells=0)
for n in range(1, 5):
    for r in range(1, n+2):
        for k in (1, 2):
            f = MIX(n, r, k)
            for labs in itertools.product('VAD', repeat=T+1):
                lab = (lambda L: lambda h: L[min(h, T)])(labs)
                Dh = [h for h in range(H) if lab(h) == 'D']
                A, _ = play(f, lab, f, lab); selfC = tail(A)
                fbC = None
                for m in (1, 2, 3):
                    X, Y = play(f, lab, FK(m), lambda h: None)
                    cc = tail(X) and tail(Y)
                    assert cc == all(X), (n, r, k, labs, m)            # fk_cc_iff instance
                    if Dh:
                        s = Dh[0]
                        assert not tail(X) and not tail(Y), (n, r, k, labs, m)   # DD
                        assert not any(Y[s+m:]), (n, r, k, labs, m)             # fk_defects bound
                    else:
                        allA = all(lab(h) == 'A' for h in range(max(n, m)+1, H))
                        assert cc == (m + r <= n or allA), (n, r, k, labs, m)    # K22 law
                    if m == 1: fbC = cc
                    cnt['cells'] += 1
                X, Y = play(f, lab, CB, lambda h: None)
                cnt['cells'] += 2
                cnt['blends'] += 1; cnt['withD'] += bool(Dh)
                cnt['selfCC_withD'] += bool(Dh) and selfC
                cnt['selfCC_fbCC'] += selfC and fbC
                if selfC and fbC: assert not Dh
assert cnt == dict(blends=6804, withD=5908, selfCC_withD=702, selfCC_fbCC=476, cells=34020), cnt
print('PASS: Lean fk_cc_iff, fk_defects, db_height_blocks (no sorryAx), 3 mutations rejected;', cnt, round(time.time()-t0, 1), 's')
