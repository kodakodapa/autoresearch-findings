import os, re, shutil, subprocess
LEAN = 'namespace Conjunction\nvariable {W D : Type}\nabbrev Pr (W D : Type) := D → W → Prop\ndef God (P : Pr W D → W → Prop) : Pr W D := fun x w => ∀ q, P q w → q x w\ndef Local (P : Pr W D → W → Prop) := ∀ q s w, P q w → (∀ x, q x w → s x w) → P s w\ndef Meet (S : Pr W D → Prop) : Pr W D := fun x w => ∀ q, S q → q x w\ndef AllMeet (P : Pr W D → W → Prop) := ∀ w S, (∀ q, S q → P q w) → P (Meet S) w\ndef PG (P : Pr W D → W → Prop) := ∀ w, P (God P) w\n\ntheorem allMeet_iff_PG {P : Pr W D → W → Prop} (c : Local P) : AllMeet P ↔ PG P := by\n  constructor\n  · intro a w\n    have h := a w (fun q => P q w) (fun _ h => h)\n    exact c _ _ w h (fun x hx q hp => hx q hp)\n  · intro g w S hs\n    exact c _ _ w (g w) (fun x hx q hq => hx q (hs q hq))\n\ndef Modal (R : W → W → Prop) (P : Pr W D → W → Prop) :=\n  ∀ q s w, P q w → (∀ v, R w v → ∀ x, q x v → s x v) → P s w\ndef ModalMeet (R : W → W → Prop) (P : Pr W D → W → Prop) :=\n  ∀ w S, (∀ q, S q → P q w) → ∀ X,\n    (∀ v, R w v → ∀ x, X x v ↔ Meet S x v) → P X w\n\ntheorem modalMeet_iff_allMeet {R : W → W → Prop} {P : Pr W D → W → Prop}\n    (c : Modal R P) : ModalMeet R P ↔ AllMeet P := by\n  constructor\n  · intro h w S hs\n    exact h w S hs (Meet S) (fun _ _ _ => Iff.rfl)\n  · intro h w S hs X hx\n    exact c _ _ w (h w S hs) (fun v hv x hm => (hx v hv x).mpr hm)\n\ntheorem modalMeet_iff_PG {R : W → W → Prop} {P : Pr W D → W → Prop}\n    (l : Local P) (m : Modal R P) : ModalMeet R P ↔ PG P :=\n  (modalMeet_iff_allMeet m).trans (allMeet_iff_PG l)\n\ndef Tail (q : Pr Unit Nat) (_ : Unit) : Prop := ∃ n, ∀ k, n ≤ k → q k ()\n\ntheorem tail_local : Local Tail := by\n  intro q s w hp h\n  obtain ⟨n, hn⟩ := hp\n  cases w\n  exact ⟨n, fun k hk => h k (hn k hk)⟩\n\ntheorem tail_bottom : ∀ w, ¬ Tail (fun _ _ => False) w := by\n  intro w h\n  obtain ⟨n, hn⟩ := h\n  exact hn n (Nat.le_refl n)\n\ntheorem tail_binary : ∀ q s w, Tail q w → Tail s w → Tail (fun x v => q x v ∧ s x v) w := by\n  intro q s w hq hs\n  obtain ⟨n, hn⟩ := hq\n  obtain ⟨m, hm⟩ := hs\n  exact ⟨n+m, fun k hk => ⟨hn k (Nat.le_trans (Nat.le_add_right n m) hk), hm k (Nat.le_trans (Nat.le_add_left m n) hk)⟩⟩\n\ntheorem tail_no_god : ∀ x w, ¬ God Tail x w := by\n  intro x w h\n  cases w\n  have hp : Tail (fun k _ => x < k) () := ⟨x+1, fun k hk => hk⟩\n  exact (Nat.lt_irrefl x) (h _ hp)\n\ntheorem tail_not_PG : ¬ PG Tail := by\n  intro h\n  obtain ⟨n, hn⟩ := h ()\n  exact tail_no_god n () (hn n (Nat.le_refl n))\n\ntheorem tail_not_allMeet : ¬ AllMeet Tail := by\n  intro h\n  exact tail_not_PG ((allMeet_iff_PG tail_local).mp h)\nend Conjunction\n#print axioms Conjunction.allMeet_iff_PG\n#print axioms Conjunction.tail_local\n#print axioms Conjunction.tail_bottom\n#print axioms Conjunction.tail_binary\n#print axioms Conjunction.tail_no_god\n#print axioms Conjunction.tail_not_PG\n#print axioms Conjunction.tail_not_allMeet\n\n#print axioms Conjunction.modalMeet_iff_allMeet\n#print axioms Conjunction.modalMeet_iff_PG\n\nnamespace Prime\nvariable {W D : Type}\nabbrev Pr (W D : Type) := D → W → Prop\ndef SD : Pr W D := fun x _ => x ≠ x\ndef NB (P : Pr W D → W → Prop) := ∀ w, ¬ P (fun _ _ => False) w\ndef AP (P : Pr W D → W → Prop) := ∀ w, ¬ P SD w\ntheorem sd_bottom : (SD : Pr W D) = (fun _ _ => False) := by\n  funext x w\n  exact propext ⟨fun h => h rfl, False.elim⟩\ntheorem prime_iff_nb (P : Pr W D → W → Prop) : AP P ↔ NB P := by\n  unfold AP NB\n  rw [sd_bottom]\ntheorem meet_exists {P : Pr W D → W → Prop} (a : AP P)\n    (c : Conjunction.Local P) (m : Conjunction.AllMeet P) (w : W) :\n    ∃ x, Conjunction.God P x w := by\n  classical\n  have pg := (Conjunction.allMeet_iff_PG c).mp m\n  apply Classical.byContradiction\n  intro h\n  exact ((prime_iff_nb P).mp a) w (c _ _ w (pg w) (fun x hx => h ⟨x,hx⟩))\ntheorem meet_box {P : Pr W D → W → Prop} (a : AP P)\n    (c : Conjunction.Local P) (m : Conjunction.AllMeet P)\n    (R : W → W → Prop) (w : W) : ∀ v, R w v → ∃ x, Conjunction.God P x v := by\n  intro v _\n  exact meet_exists a c m v\n\ndef Tail (q : Pr Bool Nat) (w : Bool) := ∃ n, ∀ k, n ≤ k → q k w\ntheorem tail_local : Conjunction.Local Tail := by\n  intro q s w hp h\n  obtain ⟨n, hn⟩ := hp\n  exact ⟨n, fun k hk => h k (hn k hk)⟩\ntheorem tail_prime : AP Tail := by\n  intro w h\n  obtain ⟨n, hn⟩ := h\n  exact hn n (Nat.le_refl n) rfl\ntheorem tail_binary : ∀ q s w, Tail q w → Tail s w → Tail (fun x v => q x v ∧ s x v) w := by\n  intro q s w hq hs\n  obtain ⟨n, hn⟩ := hq\n  obtain ⟨m, hm⟩ := hs\n  exact ⟨n+m, fun k hk => ⟨hn k (Nat.le_trans (Nat.le_add_right n m) hk), hm k (Nat.le_trans (Nat.le_add_left m n) hk)⟩⟩\ntheorem tail_a1w : ∀ q w, Tail (fun x v => ¬ q x v) w → ¬ Tail q w := by\n  intro q w hn hp\n  obtain ⟨n, h⟩ := tail_binary _ _ w hp hn\n  exact (h n (Nat.le_refl n)).2 (h n (Nat.le_refl n)).1\ntheorem tail_modal : Conjunction.Modal (fun (_ _ : Bool) => True) Tail := by\n  intro q s w hp h\n  exact tail_local q s w hp (h w True.intro)\ntheorem tail_no_god : ∀ x w, ¬ Conjunction.God Tail x w := by\n  intro x w h\n  have hp : Tail (fun k _ => x < k) w := ⟨x+1, fun k hk => hk⟩\n  exact (Nat.lt_irrefl x) (h _ hp)\ntheorem tail_no_box : ∀ w : Bool, ¬ (∀ v : Bool, True → ∃ x, Conjunction.God Tail x v) := by\n  intro w h\n  obtain ⟨x,hx⟩ := h w True.intro\n  exact tail_no_god x w hx\ntheorem noncollapse : ∃ Q : Bool → Prop, ∃ w, Q w ∧ ¬ (∀ v : Bool, True → Q v) := by\n  exact ⟨fun w => w = true, true, rfl, fun h => Bool.noConfusion (h false True.intro)⟩\nend Prime\n\n#print axioms Prime.sd_bottom\n#print axioms Prime.prime_iff_nb\n#print axioms Prime.meet_exists\n#print axioms Prime.meet_box\n#print axioms Prime.tail_local\n#print axioms Prime.tail_prime\n#print axioms Prime.tail_binary\n#print axioms Prime.tail_a1w\n#print axioms Prime.tail_modal\n#print axioms Prime.tail_no_god\n#print axioms Prime.tail_no_box\n#print axioms Prime.noncollapse\n'
NAMES = ['Prime.sd_bottom', 'Prime.prime_iff_nb', 'Prime.meet_exists', 'Prime.meet_box', 'Prime.tail_local', 'Prime.tail_prime', 'Prime.tail_binary', 'Prime.tail_a1w', 'Prime.tail_modal', 'Prime.tail_no_god', 'Prime.tail_no_box', 'Prime.noncollapse']
exe = shutil.which("lean")
if exe is None:
    for c in ("/opt/elan/bin/lean", "/opt/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"):
        if os.path.isfile(c):
            exe = c
            break
assert exe, "lean not found"
p = subprocess.run([exe, "--stdin"], input=LEAN, capture_output=True, text=True, timeout=110)
out = p.stdout + p.stderr
print(out)
assert p.returncode == 0, "lean exit %d" % p.returncode
assert "error" not in out
assert "declaration uses 'sorry'" not in out and "sorryAx" not in out
assert "sorry" not in LEAN
assert not re.search(r"(?m)^\s*axiom\s", LEAN), "no axiom declarations allowed"
STD = {"propext", "Classical.choice", "Quot.sound"}
def axioms(name):
    if re.search(r"'" + re.escape(name) + r"' does not depend on any axioms", out):
        return set()
    m = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", out)
    assert m, "no #print axioms line for " + name
    return {a.strip() for a in m.group(1).split(",")}
for n in NAMES:
    assert axioms(n) <= STD, n

print("PASS conjunction boundary proofs")

"""Exhaustive finite witnesses, not an unbounded completeness claim.
Inputs: nonempty W,D; |W|*|D|<=2; all properties D x W -> Bool;
all world-dependent positivity assignments; global axiom subsets.
A=not P(bottom), C=closure, G=AllMeet; no essence/NE axioms.
B means reflexive+symmetric; KB means symmetric. Dimensionless exact Booleans.
"""
import itertools, json, hashlib
FRAMES=('K','T','D','B','K4','KB','KD45','S4','S5')
def classes(n,r):
    edge=lambda w,v: bool(r & (1<<(w*n+v)))
    ref=all(edge(w,w) for w in range(n))
    sym=all(not edge(w,v) or edge(v,w) for w in range(n) for v in range(n))
    serial=all(any(edge(w,v) for v in range(n)) for w in range(n))
    trans=all(not(edge(w,v) and edge(v,u)) or edge(w,u) for w in range(n) for v in range(n) for u in range(n))
    eucl=all(not(edge(w,v) and edge(w,u)) or edge(v,u) for w in range(n) for v in range(n) for u in range(n))
    return [f for f,b in zip(FRAMES,(True,ref,serial,ref and sym,trans,sym,serial and trans and eucl,ref and trans,ref and sym and trans)) if b]
def evaluate(n,d,r,p,mode):
    ps=range(1<<(n*d)); ws=range(n)
    has=lambda q,x,w: bool(q & (1<<(w*d+x)))
    pos=lambda q,w: bool(p[w] & (1<<q))
    edge=lambda w,v: bool(r & (1<<(w*n+v)))
    local=lambda a,b,w: all(not has(a,x,w) or has(b,x,w) for x in range(d))
    god=sum(1<<(w*d+x) for w in ws for x in range(d) if all(not pos(q,w) or has(q,x,w) for q in ps))
    a=all(not pos(0,w) for w in ws)
    c=True
    for w,a0,b0 in itertools.product(ws,ps,ps):
        loc=local(a0,b0,w)
        nec=all(not edge(w,v) or local(a0,b0,v) for v in ws)
        ent=loc if mode=='local' else nec if mode=='modal' else loc or nec
        if pos(a0,w) and ent and not pos(b0,w): c=False
    # In this finite powerset, arbitrary-meet closure is exactly top plus
    # binary closure: every collection has finitely many distinct members.
    top=(1<<(n*d))-1
    g=all(pos(top,w) and all(not(pos(q,w) and pos(t,w)) or pos(q&t,w)
          for q in ps for t in ps) for w in ws)
    eg=[any(has(god,x,w) for x in range(d)) for w in ws]
    boxeg=all(not edge(w,v) or eg[v] for w in ws for v in ws)
    collapse=all(not edge(w,v) or w==v for w in ws for v in ws)
    return int(a)+2*int(c)+4*int(g),all(eg),boxeg,collapse

def census():
    table={(mode,f,s):{} for mode in ('local','modal','either') for f in FRAMES for s in range(8)}
    counts=0
    for n,d in ((1,1),(1,2),(2,1)):
      for r in range(1<<(n*n)):
       fs=classes(n,r)
       for p in itertools.product(range(1<<(1<<(n*d))),repeat=n):
        counts+=1
        for mode in ('local','modal','either'):
         mask,eg,boxeg,mc=evaluate(n,d,r,p,mode)
         for s in range(8):
          if mask&s!=s: continue
          for f in fs:
           cell=table[mode,f,s]
           model={'worlds':n,'individuals':d,'R':r,'P':list(p)}
           for key,ok in [('consistent',True),('not_exists',not eg),('not_box_exists',not boxeg),('not_collapse',not mc)]:
            if ok: cell.setdefault(key,model)
    # Every emitted certificate is re-evaluated, not merely sampled.
    for (mode,f,s),cell in table.items():
      for key,m in cell.items():
        assert f in classes(m['worlds'],m['R'])
        mask,eg,beg,mc=evaluate(m['worlds'],m['individuals'],m['R'],m['P'],mode)
        assert mask&s==s
        assert {'consistent':True,'not_exists':not eg,'not_box_exists':not beg,'not_collapse':not mc}[key]
    # Known simplified full variant: existence countermodels absent at this bound;
    # all nine classes have explicit consistency and noncollapse witnesses.
    for mode in ('local','either'):
      for f in FRAMES:
        c=table[mode,f,7]
        assert 'consistent' in c and 'not_collapse' in c
        assert 'not_exists' not in c and 'not_box_exists' not in c
    # Every single-axiom deletion has an S5 actual-existence countermodel.
    for mode in ('local','modal','either'):
      for s in (3,5,6): assert 'not_exists' in table[mode,'S5',s]
    rows=[{'closure':mode,'frame':f,'axioms':s,'certificates':c} for (mode,f,s),c in table.items()]
    return {'bound':'nonempty worlds and individuals; W*D<=2','models_enumerated':counts,'rows':rows}


result=census()
for row in result['rows']:
    proved=row['axioms']==7 and row['closure'] in ('local','either')
    expected={'consistent','not_collapse'} if proved else {'consistent','not_collapse','not_exists','not_box_exists'}
    assert set(row['certificates'])==expected
    row['provenance']='Lean meet_exists/meet_box reused' if proved else 'explicit model'
assert len(result['rows'])==216
payload=json.dumps(result,sort_keys=True,separators=(',',':'))
assert hashlib.sha256(payload.encode()).hexdigest() == 'c5a212d2872e6b9fd76e7d55c65bfa302274fc494cb325d7dbf9858f483bb910'
print('PASS AllMeet: 216 cells; every model re-evaluated; 36 proof outcomes supplied by Lean above')
