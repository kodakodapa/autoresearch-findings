"""C009 varying-domain (actualist) extensional Fitting slice: 32 subsets of A1a,A1b,A2,H,N x 9 classes.
See header of LEAN for definitions. Countermodels from exhaustive search over (|W|,|D|) in
(1,1..3),(2,1..3),(3,1..2), re-evaluated by a direct evaluator; positive cells by Lean theorems."""
LEAN = r"""/- Varying-domain extensional Fitting: properties are extensions D → Prop, positivity is
   world-indexed, E x w = x exists at w (domains may be empty). Entailment, essence and NE
   are guarded by E; H and N assert positivity of the current extensions of G and NE. -/
namespace VFit
variable {W D : Type}
abbrev Ext (D : Type) := D → Prop
def ent (R : W → W → Prop) (E : D → W → Prop) (Y Z : Ext D) (w : W) : Prop :=
  ∀ v, R w v → ∀ x, E x v → Y x → Z x
def God (P : Ext D → W → Prop) (w : W) : Ext D := fun x => ∀ Y, P Y w → Y x
def Ess (R : W → W → Prop) (E : D → W → Prop) (Y : Ext D) (x : D) (w : W) : Prop :=
  Y x ∧ ∀ Z : Ext D, Z x → ent R E Y Z w
def NE (R : W → W → Prop) (E : D → W → Prop) (w : W) : Ext D :=
  fun x => ∀ Y, Ess R E Y x w → ∀ v, R w v → ∃ z, E z v ∧ Y z
def A1a (P : Ext D → W → Prop) : Prop := ∀ (Y : Ext D) w, P (fun x => ¬ Y x) w → ¬ P Y w
def A1b (P : Ext D → W → Prop) : Prop := ∀ (Y : Ext D) w, ¬ P Y w → P (fun x => ¬ Y x) w
def A2 (R : W → W → Prop) (E : D → W → Prop) (P : Ext D → W → Prop) : Prop :=
  ∀ Y Z w, P Y w → ent R E Y Z w → P Z w
def H (P : Ext D → W → Prop) : Prop := ∀ w, P (God P w) w
def N (R : W → W → Prop) (E : D → W → Prop) (P : Ext D → W → Prop) : Prop := ∀ w, P (NE R E w) w
def ExG (E : D → W → Prop) (P : Ext D → W → Prop) (w : W) : Prop := ∃ x, E x w ∧ God P w x

section
variable {R : W → W → Prop} {E : D → W → Prop} {P : Ext D → W → Prop}

/-- A1a + A2 + H: the current extension of G is nonempty (the being need not exist). -/
theorem god_nonempty (h1 : A1a P) (h2 : A2 R E P) (hH : H P) (w : W) : ∃ x, God P w x :=
  Classical.byContradiction fun hn =>
    h1 _ w (h2 _ _ w (hH w) (fun _ _ x _ hg => absurd ⟨x, hg⟩ hn)) (hH w)

/-- The haecceity extension is an essence of x. -/
theorem haec_ess (x : D) (w : W) : Ess R E (fun z => z = x) x w :=
  ⟨rfl, fun _ hz _ _ _ _ he => he ▸ hz⟩

/-- N alone: a God-like x at w exists at every successor of w. -/
theorem god_exists_succ (hN : N R E P) {x : D} {w : W} (hg : God P w x) :
    ∀ v, R w v → E x v := fun v hv =>
  let ⟨_, hz, he⟩ := hg _ (hN w) _ (haec_ess x w) v hv
  he ▸ hz

/-- NE(x) at w is exactly existence at all successors. -/
theorem NE_iff (x : D) (w : W) : NE R E w x ↔ ∀ v, R w v → E x v :=
  ⟨fun h v hv => let ⟨_, hz, he⟩ := h _ (haec_ess x w) v hv; he ▸ hz,
   fun h Y hY v hv => ⟨x, h v hv, hY.1⟩⟩

theorem refl_god (h1 : A1a P) (h2 : A2 R E P) (hH : H P) (hN : N R E P) (w : W) (hw : R w w) :
    ExG E P w :=
  let ⟨x, hg⟩ := god_nonempty h1 h2 hH w
  ⟨x, god_exists_succ hN hg w hw, hg⟩

theorem T_god (hr : ∀ w, R w w) (h1 : A1a P) (h2 : A2 R E P) (hH : H P) (hN : N R E P)
    (w : W) : ExG E P w := refl_god h1 h2 hH hN w (hr w)

theorem T_box (hr : ∀ w, R w w) (h1 : A1a P) (h2 : A2 R E P) (hH : H P) (hN : N R E P)
    (w : W) : ∀ v, R w v → ExG E P v := fun v _ => T_god hr h1 h2 hH hN v

theorem eucl_box (he : ∀ w u v, R w u → R w v → R u v) (h1 : A1a P) (h2 : A2 R E P)
    (hH : H P) (hN : N R E P) (w : W) : ∀ v, R w v → ExG E P v :=
  fun v hv => refl_god h1 h2 hH hN v (he w v v hv hv)
end

/-- Headline countermodel 1 (mask A1a,A1b,A2,H; no N): two-world universal S5 frame,
    individual b exists only at world b, positivity P Y := Y true. At world false the only
    God-like individual (true) does not exist. -/
theorem noN_S5 :
    let R : Bool → Bool → Prop := fun _ _ => True
    let E : Bool → Bool → Prop := fun x w => x = w
    let P : Ext Bool → Bool → Prop := fun Y _ => Y true
    A1a P ∧ A1b P ∧ A2 R E P ∧ H P ∧ (∀ w, ∃ x, E x w) ∧ ¬ ExG E P false ∧ ¬ N R E P := by
  intro R E P
  refine ⟨fun Y _ h1 h2 => h1 h2, fun Y _ h => h, ?_, fun _ _ h => h, fun w => ⟨w, rfl⟩, ?_, ?_⟩
  · intro Y Z w hY he; exact he true trivial true rfl hY
  · rintro ⟨x, hx, hg⟩
    have : x = true := hg (fun z => z = true) rfl
    subst hx; exact Bool.noConfusion this
  · intro hN
    have h := (NE_iff (R := R) (E := E) true false).mp (hN false) false trivial
    exact Bool.noConfusion h

/-- Headline countermodel 2 (mask A1a,A1b,H,N; no A2): one reflexive world, D = Bool,
    only true exists, P Y := ¬ Y false. G has empty extension, so no God-like individual. -/
theorem noA2_S5 :
    let R : Unit → Unit → Prop := fun _ _ => True
    let E : Bool → Unit → Prop := fun x _ => x = true
    let P : Ext Bool → Unit → Prop := fun Y _ => ¬ Y false
    A1a P ∧ A1b P ∧ H P ∧ N R E P ∧ (∀ w, ∃ x, E x w) ∧ ¬ (∃ x, God P () x) ∧ ¬ A2 R E P := by
  intro R E P
  have hG : ∀ x, ¬ God P () x := fun x hg => hg (fun _ => False) (fun h => h)
  refine ⟨fun Y _ h1 h2 => h1 h2, fun Y _ h => fun h' => h h', ?_, ?_, fun _ => ⟨true, rfl⟩,
    fun ⟨x, hx⟩ => hG x hx, ?_⟩
  · intro w hg; exact hG false hg
  · intro w hne
    have ⟨z, hz, he⟩ := hne _ (haec_ess (R := R) (E := E) false w) () trivial
    rw [hz] at he; exact Bool.noConfusion he
  · intro h2
    have hb : P (God P ()) () := fun hg => hG false hg
    have ht : P (fun _ => True) () := h2 _ _ () hb (fun _ _ x _ hg => trivial)
    exact ht trivial

end VFit
#print axioms VFit.god_nonempty
#print axioms VFit.haec_ess
#print axioms VFit.god_exists_succ
#print axioms VFit.NE_iff
#print axioms VFit.refl_god
#print axioms VFit.T_god
#print axioms VFit.T_box
#print axioms VFit.eucl_box
#print axioms VFit.noN_S5
#print axioms VFit.noA2_S5
"""
PIN = "4e6a9a11eb1dd5fc9f887e870d9d46e1b3378e75659f110a5f3328388924e132"

import hashlib, json, os, shutil, subprocess, sys
CLASSES=['K','T','D','B','K4','KB','KD45','S4','S5']
AX=['A1a','A1b','A2','H','N']
FULL=29  # A1a+A2+H+N
# ---------------- Lean ----------------
def find_lean():
    for c in [shutil.which('lean'), os.path.expanduser('~/.elan/bin/lean'), '/opt/elan/bin/lean', '/usr/local/bin/lean']:
        if c and os.path.exists(c): return c
    raise SystemExit('lean not found')
assert 'sorry' not in LEAN and '\naxiom ' not in LEAN
r=subprocess.run([find_lean(),'--stdin'],input=LEAN,capture_output=True,text=True,timeout=100)
print(r.stdout); print(r.stderr)
assert r.returncode==0, 'lean failed'
assert 'error' not in r.stdout.lower()
STD={'propext','Classical.choice','Quot.sound'}
THMS=['god_nonempty','haec_ess','god_exists_succ','NE_iff','refl_god','T_god','T_box','eucl_box','noN_S5','noA2_S5']
for t in THMS:
    line=[l for l in r.stdout.splitlines() if f"'VFit.{t}'" in l]
    assert len(line)==1, t
    l=line[0]
    if 'does not depend on any axioms' in l: continue
    deps={a.strip() for a in l.split('[')[1].split(']')[0].split(',')}
    assert deps<=STD, (t,deps)
for t in ['noN_S5','noA2_S5','haec_ess','NE_iff','god_exists_succ']:
    assert any(f"'VFit.{t}' does not depend on any axioms" in l for l in r.stdout.splitlines()), t
# ---------------- frames ----------------
def classes_of(R,n):
    W=range(n)
    refl=all(R[w][w] for w in W); sym=all(R[w][v]==R[v][w] for w in W for v in W)
    ser=all(any(R[w]) for w in W)
    tr=all(not(R[w][u] and R[u][v]) or R[w][v] for w in W for u in W for v in W)
    eu=all(not(R[w][u] and R[w][v]) or R[u][v] for w in W for u in W for v in W)
    d={'K':True,'T':refl,'D':ser,'B':refl and sym,'K4':tr,'KB':sym,'KD45':ser and tr and eu,
       'S4':refl and tr,'S5':refl and sym and tr}
    return [c for c in CLASSES if d[c]]
# ---------------- fast search (per-world signature cache) ----------------
cache={}
def local(nd,S,succE,Ew):
    key=(nd,S,succE,Ew)
    if key in cache: return cache[key]
    ne=1<<nd; allx=(1<<nd)-1
    NEx=0
    for x in range(nd):
        ok=True
        for Y in range(ne):
            if not (Y>>x)&1: continue
            ess=all(((Y&S)&~Z)==0 for Z in range(ne) if (Z>>x)&1)
            if ess and not all(Y&Eu for Eu in succE): ok=False;break
        if ok: NEx|=1<<x
    res={}
    for F in range(1<<ne):
        Ys=[Y for Y in range(ne) if (F>>Y)&1]
        a1a=all(not (F>>(allx&~Y))&1 for Y in Ys)
        a1b=all((F>>Y)&1 or (F>>(allx&~Y))&1 for Y in range(ne))
        a2=all((F>>Z)&1 for Y in Ys for Z in range(ne) if ((Y&S)&~Z)==0)
        G=allx
        for Y in Ys: G&=Y
        bits=int(a1a)|(int(a1b)<<1)|(int(a2)<<2)|(int((F>>G)&1==1)<<3)|(int((F>>NEx)&1==1)<<4)
        res[F]=(bits,(G&Ew)!=0)
    out={}
    for m in range(32):
        okF=[F for F,(b,e) in res.items() if b&m==m]
        t=[F for F in okF if res[F][1]]; f=[F for F in okF if not res[F][1]]
        out[m]=(t[0] if t else None, f[0] if f else None)
    cache[key]=out
    return out
def search(sizes,mode):
    cells={(m,c):{} for m in range(32) for c in CLASSES}
    for n,nd in sizes:
        for rb in range(1<<(n*n)):
            R=[[bool(rb>>(w*n+v)&1) for v in range(n)] for w in range(n)]
            cl=classes_of(R,n)
            noncol=any(R[w][v] for w in range(n) for v in range(n) if w!=v)
            for Eb in range(1<<(n*nd)):
                E=[(Eb>>(w*nd))&((1<<nd)-1) for w in range(n)]
                if mode in('nonempty','every') and not all(E): continue
                if mode=='every':
                    u=0
                    for e in E: u|=e
                    if u!=(1<<nd)-1: continue
                if mode=='const' and any(e!=(1<<nd)-1 for e in E): continue
                locs=[]
                for w in range(n):
                    succ=[v for v in range(n) if R[w][v]]
                    S=0
                    for v in succ: S|=E[v]
                    locs.append(local(nd,S,tuple(E[v] for v in succ),E[w]))
                for m in range(32):
                    opts=[locs[w][m] for w in range(n)]
                    if any(t is None and f is None for t,f in opts): continue
                    base=[t if t is not None else f for t,f in opts]
                    mk=lambda Fs,w=None:{'n':n,'nd':nd,'R':R,'E':E,'P':list(Fs),'mask':m,'w':w}
                    for c in cl:
                        d=cells[(m,c)]
                        if 'cons' not in d: d['cons']=mk(base)
                        if noncol and 'noncol' not in d: d['noncol']=mk(base)
                        if 'exF' not in d:
                            for w in range(n):
                                if opts[w][1] is not None:
                                    Fs=list(base);Fs[w]=opts[w][1];d['exF']=mk(Fs,w);break
                        if 'boxF' not in d:
                            for w in range(n):
                                hit=[v for v in range(n) if R[w][v] and opts[v][1] is not None]
                                if hit:
                                    Fs=list(base);Fs[hit[0]]=opts[hit[0]][1];d['boxF']=mk(Fs,w);break
    return cells
# ---------------- independent direct evaluator (definitions verbatim, no caching) ----------------
def evaluate(M):
    n,nd,R,E,P=M['n'],M['nd'],M['R'],M['E'],M['P']
    Wr=range(n); Dr=range(nd); exts=range(1<<nd)
    mem=lambda Y,x:(Y>>x)&1==1
    pos=lambda Y,w:(P[w]>>Y)&1==1
    neg=lambda Y:sum(1<<x for x in Dr if not mem(Y,x))
    ext_of=lambda f:sum(1<<x for x in Dr if f(x))
    ex=lambda x,w:(E[w]>>x)&1==1
    ent=lambda Y,Z,w:all(not ex(x,v) or not mem(Y,x) or mem(Z,x) for v in Wr if R[w][v] for x in Dr)
    god=lambda w,x:all(mem(Y,x) for Y in exts if pos(Y,w))
    ess=lambda Y,x,w:mem(Y,x) and all(ent(Y,Z,w) for Z in exts if mem(Z,x))
    NE=lambda w,x:all(all(any(ex(z,v) and mem(Y,z) for z in Dr) for v in Wr if R[w][v]) for Y in exts if ess(Y,x,w))
    for w in Wr:
        for x in Dr:  # Lean NE_iff sanity
            assert NE(w,x)==all(ex(x,v) for v in Wr if R[w][v])
    ax={'A1a':all(not(pos(neg(Y),w) and pos(Y,w)) for Y in exts for w in Wr),
        'A1b':all(pos(Y,w) or pos(neg(Y),w) for Y in exts for w in Wr),
        'A2':all(not pos(Y,w) or not ent(Y,Z,w) or pos(Z,w) for Y in exts for Z in exts for w in Wr),
        'H':all(pos(ext_of(lambda x:god(w,x)),w) for w in Wr),
        'N':all(pos(ext_of(lambda x:NE(w,x)),w) for w in Wr)}
    exG=[any(ex(x,w) and god(w,x) for x in Dr) for w in Wr]
    box=[all(exG[v] for v in Wr if R[w][v]) for w in Wr]
    noncol=any(R[w][v] for w in Wr for v in Wr if w!=v)
    return ax,exG,box,noncol
def check_cert(M,m,c,kind):
    ax,exG,box,noncol=evaluate(M)
    assert all(ax[a] for i,a in enumerate(AX) if m>>i&1), (m,c,kind,ax)
    assert c in classes_of(M['R'],M['n']), (m,c,kind)
    if kind=='noncol': assert noncol
    if kind=='exF': assert not exG[M['w']]
    if kind=='boxF': assert not box[M['w']]
SIZES=[(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)]
def proved(m,c,o):
    if m&FULL!=FULL: return None
    if o=='ex' and c in('T','B','S4','S5'): return 'T_god'
    if o=='box' and c in('T','B','S4','S5'): return 'T_box'
    if o=='box' and c=='KD45': return 'eucl_box'
    return None
tables={}
for mode in ['all','nonempty','every','const']:
    cells=search(SIZES,mode)
    tab={}
    ncert=0
    for (m,c),d in cells.items():
        for kind,M in d.items(): check_cert(M,m,c,kind); ncert+=1
        row={'cons':'cons' in d,'noncol':'noncol' in d}
        for o,k in [('ex','exF'),('box','boxF')]:
            th=proved(m,c,o)
            if k in d:
                assert th is None or mode=='const', ('countermodel contradicts Lean',m,c,o,mode)
                row[o]='refuted'
            elif th is not None: row[o]='proved:'+th
            else: row[o]='OPEN'
        tab[f'{m}/{c}']=row
    tables[mode]=tab
    print(mode,'certificates re-evaluated:',ncert)
# assertions: varying-domain modes
for mode in ['all','nonempty','every']:
    tab=tables[mode]
    for m in range(32):
        for c in CLASSES:
            row=tab[f'{m}/{c}']
            assert row['cons'] and row['noncol'], (mode,m,c)
            for o in ['ex','box']:
                th=proved(m,c,o)
                assert row[o]==('proved:'+th if th else 'refuted'), (mode,m,c,o,row)
assert tables['all']==tables['nonempty']==tables['every']
# constant-domain calibration against K13: valid iff superset of {A1a,A2,H} or {A1a,H,N}, every frame
for m in range(32):
    for c in CLASSES:
        row=tables['const'][f'{m}/{c}']
        k13=(m&13==13) or (m&25==25)
        assert row['cons'] and row['noncol']
        for o in ['ex','box']:
            assert (row[o]!='refuted')==k13, ('K13 calibration',m,c,o,row)
blob=json.dumps(tables['all'],sort_keys=True).encode()
h=hashlib.sha256(blob).hexdigest(); print('table sha256',h)
assert h==PIN, h
print('PASS: varying-domain Fitting 288 cells; no OPEN cell')
