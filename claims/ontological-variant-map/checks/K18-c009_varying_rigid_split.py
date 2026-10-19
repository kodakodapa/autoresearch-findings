"""C009 varying-domain (actualist) rigid-property Scott/Goedel slice: 64 subsets of A1a,A1b,A2..A5 x
Scott/Goedel essence x 9 classes. Definitions in LEAN header. Countermodels from exhaustive search
over (|W|,|D|) in (1,1..3),(2,1..3),(3,1..2), re-evaluated by a direct evaluator; positive cells by
Lean theorems (axiom monotonicity: theorem hypotheses are a subset of the cell axioms)."""
LEAN = r"""/- Varying-domain rigid-property Scott/Gödel: properties are rigid extensions D → Prop,
   positivity is world-indexed, E x w = x exists at w (domains may be empty). Entailment and
   NE are guarded by E. A1 is split: A1a = P(¬Y) → ¬P(Y), A1b = ¬P(Y) → P(¬Y); A3 = P(G_w) at w; A4 =
   positivity persists to successors; A5 = P(NE_w) at w. Essence: Scott (with Y x) or Gödel. -/
namespace VRig
variable {W D : Type}
abbrev Ext (D : Type) := D → Prop
def ent (R : W → W → Prop) (E : D → W → Prop) (Y Z : Ext D) (w : W) : Prop :=
  ∀ v, R w v → ∀ x, E x v → Y x → Z x
def God (P : Ext D → W → Prop) (w : W) : Ext D := fun x => ∀ Y, P Y w → Y x
def EssS (R : W → W → Prop) (E : D → W → Prop) (Y : Ext D) (x : D) (w : W) : Prop :=
  Y x ∧ ∀ Z : Ext D, Z x → ent R E Y Z w
def EssG (R : W → W → Prop) (E : D → W → Prop) (Y : Ext D) (x : D) (w : W) : Prop :=
  ∀ Z : Ext D, Z x → ent R E Y Z w
def NE (Ess : Ext D → D → W → Prop) (R : W → W → Prop) (E : D → W → Prop) (w : W) : Ext D :=
  fun x => ∀ Y, Ess Y x w → ∀ v, R w v → ∃ z, E z v ∧ Y z
def A1 (P : Ext D → W → Prop) : Prop := ∀ (Y : Ext D) w, P (fun x => ¬ Y x) w ↔ ¬ P Y w
def A1a (P : Ext D → W → Prop) : Prop := ∀ (Y : Ext D) w, P (fun x => ¬ Y x) w → ¬ P Y w
def A1b (P : Ext D → W → Prop) : Prop := ∀ (Y : Ext D) w, ¬ P Y w → P (fun x => ¬ Y x) w
def A2 (R : W → W → Prop) (E : D → W → Prop) (P : Ext D → W → Prop) : Prop :=
  ∀ Y Z w, P Y w → ent R E Y Z w → P Z w
def A3 (P : Ext D → W → Prop) : Prop := ∀ w, P (God P w) w
def A4 (R : W → W → Prop) (P : Ext D → W → Prop) : Prop := ∀ Y w v, P Y w → R w v → P Y v
def A5 (Ess : Ext D → D → W → Prop) (R : W → W → Prop) (E : D → W → Prop)
    (P : Ext D → W → Prop) : Prop := ∀ w, P (NE Ess R E w) w
def ExG (E : D → W → Prop) (P : Ext D → W → Prop) (w : W) : Prop := ∃ x, E x w ∧ God P w x

section
variable {R : W → W → Prop} {E : D → W → Prop} {P : Ext D → W → Prop}

theorem A1_A1a (h : A1 P) : A1a P := fun Y w hn hp => (h Y w).mp hn hp
theorem A1_A1b (h : A1 P) : A1b P := fun Y w hn => (h Y w).mpr hn

/-- A1a + A2 + A3: G_w is nonempty and w has a successor. -/
theorem god_nonempty (h1 : A1a P) (h2 : A2 R E P) (h3 : A3 P) (w : W) : ∃ x, God P w x :=
  Classical.byContradiction fun hn =>
    h1 _ w (h2 _ _ w (h3 w) (fun _ _ x _ hg => absurd ⟨x, hg⟩ hn)) (h3 w)

theorem serial (h1 : A1a P) (h2 : A2 R E P) (h3 : A3 P) (w : W) : ∃ v, R w v :=
  Classical.byContradiction fun hn =>
    h1 _ w (h2 _ _ w (h3 w) (fun v hv => absurd ⟨v, hv⟩ hn)) (h3 w)

theorem haec_ess (x : D) (w : W) : EssS R E (fun z => z = x) x w :=
  ⟨rfl, fun _ hz _ _ _ _ he => he ▸ hz⟩

/-- Scott essence: NE(x) at w is exactly existence at all successors. -/
theorem NE_iff (x : D) (w : W) : NE (EssS R E) R E w x ↔ ∀ v, R w v → E x v :=
  ⟨fun h v hv => let ⟨_, hz, he⟩ := h _ (haec_ess x w) v hv; he ▸ hz,
   fun h _ hY v hv => ⟨x, h v hv, hY.1⟩⟩

theorem god_exists_succ (h5 : A5 (EssS R E) R E P) {x : D} {w : W} (hg : God P w x) :
    ∀ v, R w v → E x v := (NE_iff x w).mp (hg _ (h5 w))

theorem T_god (hr : ∀ w, R w w) (h1 : A1a P) (h2 : A2 R E P) (h3 : A3 P)
    (h5 : A5 (EssS R E) R E P) (w : W) : ExG E P w :=
  let ⟨x, hg⟩ := god_nonempty h1 h2 h3 w
  ⟨x, god_exists_succ h5 hg w (hr w), hg⟩

theorem T_box (hr : ∀ w, R w w) (h1 : A1a P) (h2 : A2 R E P) (h3 : A3 P)
    (h5 : A5 (EssS R E) R E P) (w : W) : ∀ v, R w v → ExG E P v :=
  fun v _ => T_god hr h1 h2 h3 h5 v

theorem eucl_box (he : ∀ w u v, R w u → R w v → R u v) (h1 : A1a P) (h2 : A2 R E P)
    (h3 : A3 P) (h5 : A5 (EssS R E) R E P) (w : W) : ∀ v, R w v → ExG E P v :=
  fun v hv =>
    let ⟨x, hg⟩ := god_nonempty h1 h2 h3 v
    ⟨x, god_exists_succ h5 hg v (he w v v hv hv), hg⟩

/-- A4 alone makes G at a successor a subset of G at w. -/
theorem A4_god_back (h4 : A4 R P) {w v : W} (hv : R w v) {x : D} (hg : God P v x) :
    God P w x := fun Y hY => hg Y (h4 Y w v hY hv)

/-- A1a, A2, A3, A4, A5 (Scott essence, no A1b): necessary existence on every frame.
    Take x God-like at the successor v; by A4 it is God-like at w, so NE_w puts it in v. -/
theorem A4_box (h1 : A1a P) (h2 : A2 R E P) (h3 : A3 P) (h4 : A4 R P)
    (h5 : A5 (EssS R E) R E P) (w : W) : ∀ v, R w v → ExG E P v := fun v hv =>
  let ⟨x, hg⟩ := god_nonempty h1 h2 h3 v
  ⟨x, god_exists_succ h5 (A4_god_back h4 hv hg) v hv, hg⟩

/-- A1a, A2, A3, A4, A5 (Scott essence, no A1b): actual existence on every symmetric frame. -/
theorem sym_A4_god (hs : ∀ w v, R w v → R v w) (h1 : A1a P) (h2 : A2 R E P) (h3 : A3 P)
    (h4 : A4 R P) (h5 : A5 (EssS R E) R E P) (w : W) : ExG E P w :=
  let ⟨v, hv⟩ := serial h1 h2 h3 w
  let ⟨x, hg⟩ := god_nonempty h1 h2 h3 v
  ⟨x, god_exists_succ h5 hg w (hs w v hv), A4_god_back h4 hv hg⟩

/-- Gödel essence: A1a, A2, A5 have no world. -/
theorem godel_no_world (h1 : A1a P) (h2 : A2 R E P) (h5 : A5 (EssG R E) R E P) (w : W) :
    False :=
  have hent : ∀ Z, ent R E (NE (EssG R E) R E w) Z w := fun _ v hv _ _ hne =>
    let ⟨_, _, hf⟩ := hne (fun _ => False) (fun _ _ _ _ _ _ h => h.elim) v hv
    hf.elim
  h1 _ w (h2 _ _ w (h5 w) (hent _)) (h5 w)
end

/-- Headline 1: two-world KD45 frame (both worlds see `true`), one individual existing only
    at `true`, positivity P Y := Y (). All of A1–A5 (Scott) hold, but at `false` the God-like
    individual does not exist; the frame is non-reflexive at `false`. -/
theorem kd45_A4 :
    let R : Bool → Bool → Prop := fun _ v => v = true
    let E : Unit → Bool → Prop := fun _ w => w = true
    let P : Ext Unit → Bool → Prop := fun Y _ => Y ()
    A1 P ∧ A2 R E P ∧ A3 P ∧ A4 R P ∧ A5 (EssS R E) R E P ∧ ¬ ExG E P false := by
  intro R E P
  refine ⟨fun Y _ => Iff.rfl, ?_, fun _ _ h => h, fun _ _ _ h _ => h, ?_, ?_⟩
  · intro Y Z w hY he; exact he true rfl () rfl hY
  · intro w; exact (NE_iff (R := R) (E := E) () w).mpr (fun v hv => hv)
  · rintro ⟨_, hx, _⟩; exact Bool.noConfusion hx

/-- Headline 2 (no A4): symmetric irreflexive two-world frame, D = W = Bool, x exists at w
    iff x ≠ w, positivity P Y w := Y w. A1, A2, A3, A5 (Scott) hold; at each world the only
    God-like individual is the world's own name, which does not exist there; A4 fails. -/
theorem kb_noA4 :
    let R : Bool → Bool → Prop := fun w v => w ≠ v
    let E : Bool → Bool → Prop := fun x w => x ≠ w
    let P : Ext Bool → Bool → Prop := fun Y w => Y w
    A1 P ∧ A2 R E P ∧ A3 P ∧ A5 (EssS R E) R E P ∧ (∀ w v, R w v → R v w) ∧
      (∀ w, ¬ ExG E P w) ∧ ¬ A4 R P := by
  intro R E P
  refine ⟨fun Y _ => Iff.rfl, ?_, fun _ _ h => h, ?_, fun _ _ h => Ne.symm h, ?_, ?_⟩
  · intro Y Z w hY he
    cases w
    · exact he true (by decide) false (by decide) hY
    · exact he false (by decide) true (by decide) hY
  · intro w
    refine (NE_iff (R := R) (E := E) w w).mpr ?_
    intro v hv; exact hv
  · rintro w ⟨x, hx, hg⟩
    exact hx (hg (fun z => z = w) rfl)
  · intro h4
    have := h4 (fun z => z = false) false true rfl (by decide)
    exact Bool.noConfusion this
end VRig
#print axioms VRig.god_nonempty
#print axioms VRig.serial
#print axioms VRig.haec_ess
#print axioms VRig.NE_iff
#print axioms VRig.god_exists_succ
#print axioms VRig.T_god
#print axioms VRig.T_box
#print axioms VRig.eucl_box
#print axioms VRig.A4_god_back
#print axioms VRig.A4_box
#print axioms VRig.sym_A4_god
#print axioms VRig.godel_no_world
#print axioms VRig.kd45_A4
#print axioms VRig.kb_noA4
"""
PIN = "70aa8973c32cf13b9dc4571e1f8e55c913b047737b09e48de4bb856fae12bbff"
import hashlib, json, os, shutil, subprocess, sys
CLASSES=['K','T','D','B','K4','KB','KD45','S4','S5']
AX=['A1a','A1b','A2','A3','A4','A5']
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
THMS=['god_nonempty','serial','haec_ess','NE_iff','god_exists_succ','T_god','T_box','eucl_box',
      'A4_god_back','A4_box','sym_A4_god','godel_no_world','kd45_A4','kb_noA4']
for t in THMS:
    line=[l for l in r.stdout.splitlines() if f"'VRig.{t}'" in l]
    assert len(line)==1, t
    l=line[0]
    if 'does not depend on any axioms' in l: continue
    deps={a.strip() for a in l.split('[')[1].split(']')[0].split(',')}
    assert deps<=STD, (t,deps)
for t in ['haec_ess','NE_iff','god_exists_succ','A4_god_back','godel_no_world','kd45_A4','kb_noA4']:
    assert any(f"'VRig.{t}' does not depend on any axioms" in l for l in r.stdout.splitlines()), t
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
# ---------------- search (per-world local options; A4 enforced across worlds by DFS) ----------------
cache={}
def local(nd,S,succE,Ew,ess):
    key=(nd,S,succE,Ew,ess)
    if key in cache: return cache[key]
    ne=1<<nd; allx=(1<<nd)-1
    NEx=0
    for x in range(nd):
        ok=True
        for Y in range(ne):
            if ess=='S' and not (Y>>x)&1: continue
            isess=all(((Y&S)&~Z)==0 for Z in range(ne) if (Z>>x)&1)
            if isess and not all(Y&Eu for Eu in succE): ok=False;break
        if ok: NEx|=1<<x
    out={m:[] for m in range(64)}
    for F in range(1<<ne):
        Ys=[Y for Y in range(ne) if (F>>Y)&1]
        a1a=all(not((F>>Y)&1 and (F>>(allx&~Y))&1) for Y in range(ne))
        a1b=all((F>>Y)&1 or (F>>(allx&~Y))&1 for Y in range(ne))
        a2=all((F>>Z)&1 for Y in Ys for Z in range(ne) if ((Y&S)&~Z)==0)
        G=allx
        for Y in Ys: G&=Y
        bits=int(a1a)|(int(a1b)<<1)|(int(a2)<<2)|(int((F>>G)&1==1)<<3)|(int((F>>NEx)&1==1)<<5)
        for m in range(64):
            if (bits|16)&m==m: out[m].append((F,(G&Ew)!=0))
    cache[key]=out
    return out
def dfs(opts,R,n,a4,force=None):
    asg=[None]*n
    def go(i):
        if i==n: return True
        for F,ex in opts[i]:
            if force==i and ex: continue
            if a4 and any((R[j][i] and (asg[j]&~F)) or (R[i][j] and (F&~asg[j])) for j in range(i)): continue
            asg[i]=F
            if go(i+1): return True
        asg[i]=None
        return False
    return list(asg) if go(0) else None
def search(sizes,mode):
    cells={(e,m,c):{} for e in 'SG' for m in range(64) for c in CLASSES}
    for n,nd in sizes:
        for rb in range(1<<(n*n)):
            R=[[bool(rb>>(w*n+v)&1) for v in range(n)] for w in range(n)]
            cl=classes_of(R,n)
            noncol=any(R[w][v] for w in range(n) for v in range(n) if w!=v)
            for Eb in range(1<<(n*nd)):
                E=[(Eb>>(w*nd))&((1<<nd)-1) for w in range(n)]
                if mode=='nonempty' and not all(E): continue
                if mode=='const' and any(e!=(1<<nd)-1 for e in E): continue
                for ess in 'SG':
                    locs=[]
                    for w in range(n):
                        succ=[v for v in range(n) if R[w][v]]
                        S=0
                        for v in succ: S|=E[v]
                        locs.append(local(nd,S,tuple(E[v] for v in succ),E[w],ess))
                    for m in range(64):
                        ds=[cells[(ess,m,c)] for c in cl]
                        need_c=any('cons' not in d or (noncol and 'noncol' not in d) for d in ds)
                        need_e=any('exF' not in d or 'boxF' not in d for d in ds)
                        if not(need_c or need_e): continue
                        opts=[locs[w][m] for w in range(n)]
                        if any(not o for o in opts): continue
                        a4=bool(m&16)
                        mk=lambda Fs,w=None:{'n':n,'nd':nd,'R':R,'E':E,'P':list(Fs),'ess':ess,'mask':m,'w':w}
                        base=dfs(opts,R,n,a4)
                        if base is None: continue
                        for d in ds:
                            if 'cons' not in d: d['cons']=mk(base)
                            if noncol and 'noncol' not in d: d['noncol']=mk(base)
                        if need_e:
                            for w in range(n):
                                if not any(not ex for F,ex in opts[w]): continue
                                Fs=dfs(opts,R,n,a4,force=w)
                                if Fs is None: continue
                                for d in ds:
                                    if 'exF' not in d: d['exF']=mk(Fs,w)
                                    if 'boxF' not in d:
                                        u=[u for u in range(n) if R[u][w]]
                                        if u: d['boxF']=mk(Fs,u[0])
    return cells
# ---------------- independent direct evaluator (definitions verbatim, no caching) ----------------
def evaluate(M):
    n,nd,R,E,P,essk=M['n'],M['nd'],M['R'],M['E'],M['P'],M['ess']
    Wr=range(n); Dr=range(nd); exts=range(1<<nd)
    mem=lambda Y,x:(Y>>x)&1==1
    pos=lambda Y,w:(P[w]>>Y)&1==1
    neg=lambda Y:sum(1<<x for x in Dr if not mem(Y,x))
    ext_of=lambda f:sum(1<<x for x in Dr if f(x))
    ex=lambda x,w:(E[w]>>x)&1==1
    ent=lambda Y,Z,w:all(not ex(x,v) or not mem(Y,x) or mem(Z,x) for v in Wr if R[w][v] for x in Dr)
    god=lambda w,x:all(mem(Y,x) for Y in exts if pos(Y,w))
    if essk=='S': ess=lambda Y,x,w:mem(Y,x) and all(ent(Y,Z,w) for Z in exts if mem(Z,x))
    else: ess=lambda Y,x,w:all(ent(Y,Z,w) for Z in exts if mem(Z,x))
    NE=lambda w,x:all(all(any(ex(z,v) and mem(Y,z) for z in Dr) for v in Wr if R[w][v]) for Y in exts if ess(Y,x,w))
    if essk=='S':
        for w in Wr:
            for x in Dr: assert NE(w,x)==all(ex(x,v) for v in Wr if R[w][v])  # Lean NE_iff
    ax={'A1a':all(not(pos(neg(Y),w) and pos(Y,w)) for Y in exts for w in Wr),
        'A1b':all(pos(neg(Y),w) or pos(Y,w) for Y in exts for w in Wr),
        'A2':all(not pos(Y,w) or not ent(Y,Z,w) or pos(Z,w) for Y in exts for Z in exts for w in Wr),
        'A3':all(pos(ext_of(lambda x:god(w,x)),w) for w in Wr),
        'A4':all(not pos(Y,w) or pos(Y,v) for Y in exts for w in Wr for v in Wr if R[w][v]),
        'A5':all(pos(ext_of(lambda x:NE(w,x)),w) for w in Wr)}
    exG=[any(ex(x,w) and god(w,x) for x in Dr) for w in Wr]
    box=[all(exG[v] for v in Wr if R[w][v]) for w in Wr]
    noncol=any(R[w][v] for w in Wr for v in Wr if w!=v)
    return ax,exG,box,noncol
def check_cert(M,e,m,c,kind):
    ax,exG,box,noncol=evaluate(M)
    assert M['ess']==e and all(ax[a] for i,a in enumerate(AX) if m>>i&1), (e,m,c,kind,ax)
    assert c in classes_of(M['R'],M['n']), (e,m,c,kind)
    if kind=='noncol': assert noncol
    if kind=='exF': assert not exG[M['w']]
    if kind=='boxF': assert not box[M['w']]
# Headline Lean countermodels re-evaluated in Python as well
kd={'n':2,'nd':1,'R':[[False,True],[False,True]],'E':[0,1],'P':[2,2],'ess':'S','w':0}
ax,exG,box,nc=evaluate(kd); assert all(ax.values()) and not exG[0] and all(box) and nc and 'KD45' in classes_of(kd['R'],2) and 'D' in classes_of(kd['R'],2)
kb={'n':2,'nd':2,'R':[[False,True],[True,False]],'E':[2,1],'P':[0b1010,0b1100],'ess':'S','w':0}
ax,exG,box,nc=evaluate(kb); assert ax['A1a'] and ax['A1b'] and ax['A2'] and ax['A3'] and ax['A5'] and not ax['A4'] and not any(exG) and 'KB' in classes_of(kb['R'],2)
SIZES=[(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)]
SCOTT=45  # A1a+A2+A3+A5 (A1b=2, A4=16)
GOD=37    # A1a+A2+A5
def proved(e,m,c,o):
    if e=='G' and m&GOD==GOD: return 'godel_no_world'
    if e=='S' and m&SCOTT==SCOTT:
        if o=='ex':
            if c in('T','B','S4','S5'): return 'T_god'
            if m&16 and c=='KB': return 'sym_A4_god'
        if o=='box':
            if c in('T','B','S4','S5'): return 'T_box'
            if c=='KD45': return 'eucl_box'
            if m&16: return 'A4_box'
    return None
tables={}
for mode in ['all','nonempty','const']:
    cells=search(SIZES,mode)
    tab={}; ncert=0
    for (e,m,c),d in cells.items():
        for kind,M in d.items(): check_cert(M,e,m,c,kind); ncert+=1
        row={'cons':'cons' in d,'noncol':'noncol' in d}
        for o,k in [('ex','exF'),('box','boxF')]:
            th=proved(e,m,c,o)
            if k in d:
                assert th is None or mode=='const', ('countermodel contradicts Lean',e,m,c,o,mode)
                row[o]='refuted'
            elif th is not None and mode!='const': row[o]='proved:'+th
            else: row[o]='OPEN' if mode!='const' else 'unrefuted'
        tab[f'{e}/{m}/{c}']=row
    tables[mode]=tab
    print(mode,'certificates re-evaluated:',ncert)
for mode in ['all','nonempty']:
    tab=tables[mode]
    for e in 'SG':
        for m in range(64):
            for c in CLASSES:
                row=tab[f'{e}/{m}/{c}']
                incons=(e=='G' and m&GOD==GOD)
                assert row['cons']==(not incons) and row['noncol']==(not incons), (mode,e,m,c)
                for o in ['ex','box']:
                    th=proved(e,m,c,o)
                    assert row[o]==('proved:'+th if th else 'refuted'), (mode,e,m,c,o,row)
assert tables['all']==tables['nonempty']
# constant-domain calibration against K7/K13 (split A1): unrefuted iff >= {A1a,A2,A3} or (Scott) >= {A1a,A3,A5}, every frame
for e in 'SG':
    for m in range(64):
        for c in CLASSES:
            row=tables['const'][f'{e}/{m}/{c}']
            incons=(e=='G' and m&GOD==GOD)
            assert row['cons']==(not incons) and row['noncol']==(not incons)
            k7=(m&13==13) or (e=='S' and m&41==41)
            for o in ['ex','box']:
                assert (row[o]!='refuted')==(k7 or incons), ('K7 calibration',e,m,c,o,row)
blob=json.dumps(tables['all'],sort_keys=True).encode()
h=hashlib.sha256(blob).hexdigest(); print('table sha256',h)
assert h==PIN, h
print('PASS: varying-domain rigid Scott/Goedel split-A1 1152 cells; A1b never needed; no OPEN cell')
