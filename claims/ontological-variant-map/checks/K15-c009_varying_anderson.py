"""C009 varying-domain (actualist) Anderson slice, 32 subsets of A1a,A2,H,A4,A5 x 9 frame classes.
Semantics: K9 / r2 K8 Anderson definitions with an existence predicate E (domains may be empty):
  entails(Y,Z,w) := box forall x (E x -> Y x -> Z x);  A2 closure under this entailment;
  God_A(x,w) := forall Y, P(Y,w) <-> box Y(x);  Ess_A(Y,x,w) := forall Z, box Z(x) <-> entails(Y,Z,w);
  NE_A(x,w) := forall Y, Ess_A(Y,x,w) -> box exists z (E z and Y z);  conclusion exists x (E x and God_A x).
Lean 4 core (lean --stdin), no sorry, no axiom declarations, standard axioms only:
  god_exists_succ (A2 alone: a God-like x at w exists at every successor of w), poss, sym_god, sym_box,
  eucl_box, A2H_A5, entails_top, kd45_varying (3-world KD45 frame r->a,b, {a,b} cluster; g exists at a,b,
  o exists at r only; P(Y,t) := Y g a and Y g b; all five axioms, nonempty domains, no existent God-like being
  at r, box-exists true, collapse fails).
Python: K8 bound re-evaluated with an independent guarded evaluator equal to r2's verbatim evaluator at E = all;
varying-E sanity sweep; 288-cell table asserted and sha256-pinned."""
LEAN = r"""
/- Varying-domain Anderson: E x w = x exists at w; domains may be empty.
   Entailment (A2, essence) and the NE exemplification are guarded by E; property
   quantifiers and the box in God_A / essence range over all D → W → Prop. -/
namespace VAnd
variable {W D : Type}
abbrev Prp (W D : Type) := D → W → Prop
def box (R : W → W → Prop) (p : W → Prop) (w : W) : Prop := ∀ v, R w v → p v
def entails (E : Prp W D) (R : W → W → Prop) (Y Z : Prp W D) (w : W) : Prop :=
  box R (fun v => ∀ x, E x v → Y x v → Z x v) w
def God (R : W → W → Prop) (P : Prp W D → W → Prop) : Prp W D :=
  fun x w => ∀ Y, P Y w ↔ box R (Y x) w
def Ess (E : Prp W D) (R : W → W → Prop) (Y : Prp W D) (x : D) (w : W) : Prop :=
  ∀ Z : Prp W D, box R (Z x) w ↔ entails E R Y Z w
def NE (E : Prp W D) (R : W → W → Prop) : Prp W D :=
  fun x w => ∀ Y, Ess E R Y x w → box R (fun v => ∃ z, E z v ∧ Y z v) w
def A1a (P : Prp W D → W → Prop) : Prop := ∀ Y w, ¬ (P Y w ∧ P (fun x v => ¬ Y x v) w)
def A2 (E : Prp W D) (R : W → W → Prop) (P : Prp W D → W → Prop) : Prop :=
  ∀ Y Z w, P Y w → entails E R Y Z w → P Z w
def H (R : W → W → Prop) (P : Prp W D → W → Prop) : Prop := ∀ w, P (God R P) w
def A4 (R : W → W → Prop) (P : Prp W D → W → Prop) : Prop := ∀ Y w, P Y w → box R (P Y) w
def A5 (E : Prp W D) (R : W → W → Prop) (P : Prp W D → W → Prop) : Prop := ∀ w, P (NE E R) w
def ExG (E : Prp W D) (R : W → W → Prop) (P : Prp W D → W → Prop) (w : W) : Prop :=
  ∃ x, E x w ∧ God R P x w

section
variable {E : Prp W D} {R : W → W → Prop} {P : Prp W D → W → Prop}

/-- A2 alone: a God-like individual exists at every successor world. -/
theorem god_exists_succ (h2 : A2 E R P) {x : D} {w : W} (hg : God R P x w) :
    ∀ u, R w u → E x u := by
  intro u hu
  apply Classical.byContradiction
  intro hn
  have htop : P (fun _ _ => True) w := (hg _).mpr (fun _ _ => trivial)
  have hY : P (fun z t => ¬ (z = x ∧ t = u)) w :=
    h2 _ _ w htop (fun t _ z hz _ ⟨hzx, htu⟩ => hn (hzx ▸ htu ▸ hz))
  exact ((hg _).mp hY u hu) ⟨rfl, rfl⟩

theorem poss (h1 : A1a P) (h2 : A2 E R P) (hH : H R P) (w : W) :
    ∃ v x, R w v ∧ E x v ∧ God R P x v :=
  Classical.byContradiction fun h =>
    h1 _ w ⟨hH w, h2 _ _ w (hH w) (fun v hv x hx hg _ => h ⟨v, x, hv, hx, hg⟩)⟩

theorem god_box (hH : H R P) {x : D} {v : W} (hg : God R P x v) : box R (God R P x) v :=
  (hg _).mp (hH v)

theorem sym_god (hs : ∀ w v, R w v → R v w) (h1 : A1a P) (h2 : A2 E R P) (hH : H R P)
    (w : W) : ExG E R P w :=
  let ⟨v, x, hv, _, hg⟩ := poss h1 h2 hH w
  ⟨x, god_exists_succ h2 hg w (hs w v hv), god_box hH hg w (hs w v hv)⟩

theorem sym_box (hs : ∀ w v, R w v → R v w) (h1 : A1a P) (h2 : A2 E R P) (hH : H R P)
    (w : W) : box R (ExG E R P) w :=
  fun u _ => sym_god hs h1 h2 hH u

theorem eucl_box (he : ∀ w u v, R w u → R w v → R u v) (h1 : A1a P) (h2 : A2 E R P)
    (hH : H R P) (w : W) : box R (ExG E R P) w :=
  fun u hu =>
    let ⟨v, x, hv, _, hg⟩ := poss h1 h2 hH w
    ⟨x, god_exists_succ h2 hg u (he w v u hv hu), god_box hH hg u (he w v u hv hu)⟩

/-- A2 and H still give A5: a God-like individual at u exists at all successors of u. -/
theorem A2H_A5 (h2 : A2 E R P) (hH : H R P) : A5 E R P :=
  fun w => h2 _ _ w (hH w) (fun _ _ y _ hg Y hE t ht =>
    ⟨y, god_exists_succ h2 hg t ht, (hE Y).mpr (fun _ _ _ _ hz => hz) t ht⟩)
end

/- Countermodel: KD45 frame r → a, r → b, {a,b} universal; individuals g, o.
   g exists exactly at a, b; o exists exactly at r. P(Y,t) := Y g a ∧ Y g b at every t. -/
inductive Wd | r | a | b
inductive Dd | g | o
open Wd Dd
def Rk : Wd → Wd → Prop
  | r, r => False
  | r, _ => True
  | _, r => False
  | _, _ => True
def Ek : Prp Wd Dd
  | g, r => False
  | g, _ => True
  | o, r => True
  | o, _ => False
def Pk : Prp Wd Dd → Wd → Prop := fun Y _ => Y g a ∧ Y g b

theorem box_iff (p : Wd → Prop) (w : Wd) : box Rk p w ↔ p a ∧ p b := by
  constructor
  · intro h; cases w
    · exact ⟨h a trivial, h b trivial⟩
    · exact ⟨h a trivial, h b trivial⟩
    · exact ⟨h a trivial, h b trivial⟩
  · intro ⟨ha, hb⟩ v hv; cases w <;> cases v <;> first | exact ha | exact hb | exact absurd hv id

theorem god_g (w : Wd) : God Rk Pk g w := fun Y => (box_iff (Y g) w).symm

theorem not_god_o (w : Wd) : ¬ God Rk Pk o w := fun h =>
  ((box_iff _ w).mp ((h (fun z _ => z = g)).mp ⟨rfl, rfl⟩)).1 |> Dd.noConfusion

theorem kd45_varying :
    (∀ w, ∃ v, Rk w v) ∧ (∀ w v u, Rk w v → Rk v u → Rk w u) ∧
    (∀ w u v, Rk w u → Rk w v → Rk u v) ∧ ¬ Rk r r ∧ (∀ w, ∃ x, Ek x w) ∧
    A1a Pk ∧ A2 Ek Rk Pk ∧ H Rk Pk ∧ A4 Rk Pk ∧ A5 Ek Rk Pk ∧
    ¬ ExG Ek Rk Pk r ∧ box Rk (ExG Ek Rk Pk) r ∧ ¬ (∀ Q : Wd → Prop, Q a → box Rk Q a) := by
  have h2 : A2 Ek Rk Pk := fun Y Z w ⟨ha, hb⟩ he =>
    have h := (box_iff _ w).mp he
    ⟨h.1 g trivial ha, h.2 g trivial hb⟩
  have hH : H Rk Pk := fun _ => ⟨god_g a, god_g b⟩
  refine ⟨?_, ?_, ?_, id, ?_, ?_, h2, hH, ?_, A2H_A5 h2 hH, ?_, ?_, ?_⟩
  · intro w; cases w <;> exact ⟨a, trivial⟩
  · intro w v u h1 h2; cases w <;> cases v <;> cases u <;> first | trivial | contradiction
  · intro w u v h1 h2; cases w <;> cases u <;> cases v <;> first | trivial | contradiction
  · intro w; cases w
    · exact ⟨o, trivial⟩
    · exact ⟨g, trivial⟩
    · exact ⟨g, trivial⟩
  · intro Y w ⟨h, h'⟩; exact h'.1 h.1
  · intro Y w hY v _; exact hY
  · intro ⟨x, hx, _⟩; cases x
    · exact hx
    · exact not_god_o r ‹_›
  · intro v hv; cases v
    · exact absurd hv id
    · exact ⟨g, trivial, god_g a⟩
    · exact ⟨g, trivial, god_g b⟩
  · intro h
    exact Wd.noConfusion (((box_iff _ a).mp (h (fun v => v = a) rfl)).2)

/-- With E universal the guarded notions coincide with the constant-domain ones. -/
theorem entails_top (R : W → W → Prop) (Y Z : Prp W D) (w : W) :
    entails (fun _ _ => True) R Y Z w ↔ box R (fun v => ∀ x, Y x v → Z x v) w :=
  ⟨fun h v hv x hy => h v hv x trivial hy, fun h v hv x _ hy => h v hv x hy⟩
end VAnd
#print axioms VAnd.god_exists_succ
#print axioms VAnd.poss
#print axioms VAnd.sym_god
#print axioms VAnd.sym_box
#print axioms VAnd.eucl_box
#print axioms VAnd.A2H_A5
#print axioms VAnd.kd45_varying
#print axioms VAnd.entails_top
"""
PIN = "68c42afb8718f655b152ba1f9d8669c84ac3030846e4faaac584030cacd16689"
import os, re, shutil, subprocess, itertools, hashlib, json
exe = shutil.which("lean")
if exe is None:
    for c in ("/opt/elan/bin/lean", "/opt/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"):
        if os.path.isfile(c):
            exe = c
            break
assert exe, "lean not found"
p = subprocess.run([exe, "--stdin"], input=LEAN, capture_output=True, text=True, timeout=100)
out = p.stdout + p.stderr
print(out)
assert p.returncode == 0, "lean exit %d" % p.returncode
assert "error" not in out
assert "sorry" not in LEAN and "sorryAx" not in out
assert not re.search(r"(?m)^\s*axiom\s", LEAN), "no axiom declarations allowed"
STD = {"propext", "Classical.choice", "Quot.sound"}
NAMES = ['god_exists_succ', 'poss', 'sym_god', 'sym_box', 'eucl_box', 'A2H_A5', 'kd45_varying', 'entails_top']
def axioms(name):
    name = 'VAnd.' + name
    if re.search(r"'" + re.escape(name) + r"' does not depend on any axioms", out):
        return set()
    m = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", out)
    assert m, "no #print axioms line for " + name
    return {a.strip() for a in m.group(1).split(",")}
for n in NAMES:
    assert axioms(n) <= STD, n

# ---- r2's constant-domain evaluator, verbatim from agents/r2/checks/anderson_census.py ----
FRAMES=('K','T','D','B','K4','KB','KD45','S4','S5')
def classes(n,r):
    edge=lambda w,v: bool(r & (1<<(w*n+v)))
    ref=all(edge(w,w) for w in range(n))
    sym=all(not edge(w,v) or edge(v,w) for w in range(n) for v in range(n))
    serial=all(any(edge(w,v) for v in range(n)) for w in range(n))
    trans=all(not(edge(w,v) and edge(v,u)) or edge(w,u) for w in range(n) for v in range(n) for u in range(n))
    eucl=all(not(edge(w,v) and edge(w,u)) or edge(v,u) for w in range(n) for v in range(n) for u in range(n))
    return [f for f,b in zip(FRAMES,(True,ref,serial,ref and sym,trans,sym,serial and trans and eucl,ref and trans,ref and sym and trans)) if b]
def evaluate(n,d,r,p):
    ps=range(1<<(n*d)); ws=range(n); xs=range(d); top=(1<<(n*d))-1
    has=lambda q,x,w: bool(q & (1<<(w*d+x)))
    pos=lambda q,w: bool(p[w] & (1<<q))
    edge=lambda w,v: bool(r & (1<<(w*n+v)))
    box=lambda f,w: all(not edge(w,v) or f(v) for v in ws)
    entail=lambda a,b,w: box(lambda v: all(not has(a,x,v) or has(b,x,v) for x in xs),w)
    necessary=lambda q,x,w: box(lambda v:has(q,x,v),w)
    god=sum(1<<(w*d+x) for w in ws for x in xs if all(pos(q,w)==necessary(q,x,w) for q in ps))
    essence=lambda q,x,w: all(necessary(z,x,w)==entail(q,z,w) for z in ps)
    ne=sum(1<<(w*d+x) for w in ws for x in xs if all(not essence(q,x,w) or box(lambda v:any(has(q,y,v) for y in xs),w) for q in ps))
    axioms=[all(not(pos(q,w) and pos(top^q,w)) for w in ws for q in ps),
      all(not(pos(q,w) and entail(q,z,w)) or pos(z,w) for w in ws for q in ps for z in ps),
      all(pos(god,w) for w in ws),
      all(not pos(q,w) or box(lambda v:pos(q,v),w) for w in ws for q in ps),
      all(pos(ne,w) for w in ws)]
    eg=[any(has(god,x,w) for x in xs) for w in ws]
    return sum(1<<i for i,a in enumerate(axioms) if a),all(eg),all(box(lambda v:eg[v],w) for w in ws),all(not edge(w,v) or w==v for w in ws for v in ws)
# ---- end verbatim ----

def vevaluate(n, d, r, p, e):
    """Varying-domain evaluator, written independently: e = bitmask of (x,w) existence.
    Entailment and NE exemplification guarded by e; God_A, essence boxes unguarded."""
    ps = range(1 << (n*d)); ws = range(n); xs = range(d); top = (1 << (n*d)) - 1
    has = lambda q, x, w: (q >> (w*d+x)) & 1 == 1
    ex = lambda x, w: (e >> (w*d+x)) & 1 == 1
    pos = lambda q, w: (p[w] >> q) & 1 == 1
    succ = [[v for v in ws if (r >> (w*n+v)) & 1] for w in ws]
    nec = lambda q, x, w: all(has(q, x, v) for v in succ[w])
    ent = lambda a, b, w: all(not ex(x, v) or not has(a, x, v) or has(b, x, v) for v in succ[w] for x in xs)
    god = sum(1 << (w*d+x) for w in ws for x in xs if all(pos(q, w) == nec(q, x, w) for q in ps))
    ess = lambda q, x, w: all(nec(z, x, w) == ent(q, z, w) for z in ps)
    ne = sum(1 << (w*d+x) for w in ws for x in xs
             if all(not ess(q, x, w) or all(any(ex(y, v) and has(q, y, v) for y in xs) for v in succ[w]) for q in ps))
    ax = [all(not (pos(q, w) and pos(top ^ q, w)) for w in ws for q in ps),
          all(not (pos(q, w) and ent(q, z, w)) or pos(z, w) for w in ws for q in ps for z in ps),
          all(pos(god, w) for w in ws),
          all(not pos(q, w) or all(pos(q, v) for v in succ[w]) for w in ws for q in ps),
          all(pos(ne, w) for w in ws)]
    eg = [any(ex(x, w) and has(god, x, w) for x in xs) for w in ws]
    mask = sum(1 << i for i, a in enumerate(ax) if a)
    collapse = all(succ[w] in ([], [w]) for w in ws)
    return mask, all(eg), all(all(eg[v] for v in succ[w]) for w in ws), collapse, god, ne

# (1) bound of K8 (|W||D| <= 2), all positivity families; with E = all the varying evaluator
#     reproduces r2's constant one exactly, so every K8 countermodel is a varying-domain model.
pool = []
for nn, dd in ((1, 1), (1, 2), (2, 1)):
    for r in range(1 << (nn*nn)):
        cl = classes(nn, r)
        for p in itertools.product(range(1 << (1 << (nn*dd))), repeat=nn):
            full = (1 << (nn*dd)) - 1
            v = vevaluate(nn, dd, r, p, full)
            assert v[:4] == evaluate(nn, dd, r, p), (nn, dd, r, p)
            pool.append((v[0], v[1], v[2], v[3], cl, ('bound', nn, dd, r, p, full)))
assert len(pool) == 4136

# (2) the Lean KD45 countermodel re-evaluated: worlds 0=r,1=a,2=b; individuals 0=g,1=o
n, d = 3, 2
R = sum(1 << (w*n+v) for (w, v) in [(0, 1), (0, 2), (1, 1), (1, 2), (2, 1), (2, 2)])
E = sum(1 << (w*d+x) for (x, w) in [(0, 1), (0, 2), (1, 0)])
Pw = sum(1 << q for q in range(1 << (n*d)) if (q >> (1*d+0)) & 1 and (q >> (2*d+0)) & 1)
m, eg, beg, mc, god, ne = vevaluate(n, d, R, [Pw]*3, E)
assert classes(n, R) == ['K', 'D', 'K4', 'KD45'], classes(n, R)
assert m == 31 and eg is False and beg is True and mc is False
assert god == sum(1 << (w*d+0) for w in range(3))          # g God-like everywhere (exists only at a,b)
pool.append((m, eg, beg, mc, classes(n, R), ('kd45_varying',)))

# (3) varying-E sanity sweep over the bound: every Lean theorem holds on every (model, E)
cnt = 0
for nn, dd in ((1, 1), (1, 2), (2, 1)):
    for r in range(1 << (nn*nn)):
        cl = classes(nn, r)
        succ = [[v for v in range(nn) if (r >> (w*nn+v)) & 1] for w in range(nn)]
        for p in itertools.product(range(1 << (1 << (nn*dd))), repeat=nn):
            for e in range(1 << (nn*dd)):
                m, eg, beg, mc, god, ne = vevaluate(nn, dd, r, p, e)
                cnt += 1
                if m & 2:   # god_exists_succ
                    assert all((e >> (u*dd+x)) & 1 for w in range(nn) for x in range(dd)
                               if (god >> (w*dd+x)) & 1 for u in succ[w])
                if m & 2 and m & 4:
                    assert m & 16                                   # A2H_A5
                if m & 7 == 7:
                    if 'KB' in cl: assert eg and beg                # sym_god, sym_box
                    if all(not ((r >> (w*nn+u)) & 1 and (r >> (w*nn+v)) & 1) or (r >> (u*nn+v)) & 1
                           for w in range(nn) for u in range(nn) for v in range(nn)):
                        assert beg                                  # eucl_box
print("varying sweep:", cnt)

# (4) 288-cell table, varying domains
SYM = ('B', 'KB', 'S5'); EUC = ('B', 'KB', 'KD45', 'S5')
table = {}
for s in range(32):
    for f in FRAMES:
        ms = [x for x in pool if x[0] & s == s and f in x[4]]
        cons = any(True for x in ms); noncol = any(not x[3] for x in ms)
        if s & 7 == 7 and f in SYM:
            ex = 'valid:sym_god'
        else:
            ex = 'refuted' if any(not x[1] for x in ms) else 'OPEN'
        if s & 7 == 7 and f in EUC:
            bx = 'valid:sym_box' if f in SYM else 'valid:eucl_box'
        else:
            bx = 'refuted' if any(not x[2] for x in ms) else 'OPEN'
        if ex.startswith('valid') or bx.startswith('valid'):
            assert not any((ex.startswith('valid') and not x[1]) or (bx.startswith('valid') and not x[2]) for x in ms)
        table['%d/%s' % (s, f)] = [cons, noncol, ex, bx]
assert len(table) == 288
assert all(v[0] and v[1] for v in table.values())                   # consistent, noncollapse everywhere
assert not any('OPEN' in v for v in table.values())
for k, v in table.items():
    s, f = int(k.split('/')[0]), k.split('/')[1]
    assert v[2].startswith('valid') == (s & 7 == 7 and f in SYM), k
    assert v[3].startswith('valid') == (s & 7 == 7 and f in EUC), k
# flip relative to constant-domain K9: actual existence on KD45 with A4 (masks 15, 31)
assert table['15/KD45'][2] == 'refuted' and table['31/KD45'][2] == 'refuted'
blob = json.dumps(table, sort_keys=True).encode()
h = hashlib.sha256(blob).hexdigest()
print("table sha256", h)
assert h == PIN, h
print("PASS: %d theorems, 288 varying cells certified, KD45+A4 actual existence flips" % len(NAMES))
