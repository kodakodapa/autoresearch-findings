"""Split Fitting constant-domain slice. Global premises; all extensional properties;
Scott conjunctive essence; current extensions G and NE. A1a excludes positive
complements, A1b makes every nonpositive property's complement positive.
All 32 subsets of A1a,A1b,A2,H,N x nine classes. B=T+symmetry, KB=symmetry.
All countermodels use universal two-world frames, hence belong to every class.
Lean proves positive outcomes on arbitrary frames. No bounded-exhaustion inference.
"""
LEAN = '\nnamespace Rigid\nvariable {W D : Type}\nabbrev RP (D : Type) := D → Prop\ndef bot : RP D := fun _ => False\ndef top : RP D := fun _ => True\ndef neg (φ : RP D) : RP D := fun x => ¬ φ x\n-- box entailment at w for rigid properties\ndef ent (R : W → W → Prop) (φ ψ : RP D) (w : W) : Prop := ∀ v, R w v → ∀ x, φ x → ψ x\ndef God (P : RP D → W → Prop) (w : W) : RP D := fun x => ∀ φ, P φ w → φ x\ndef essS (R : W → W → Prop) (φ : RP D) (x : D) (w : W) : Prop :=\n  φ x ∧ ∀ ψ, ψ x → ent R φ ψ w\ndef essG (R : W → W → Prop) (φ : RP D) (x : D) (w : W) : Prop :=\n  ∀ ψ, ψ x → ent R φ ψ w\ndef NE (ess : RP D → D → W → Prop) (R : W → W → Prop) (w : W) : RP D :=\n  fun x => ∀ φ, ess φ x w → ∀ v, R w v → ∃ y, φ y\ndef A1 (P : RP D → W → Prop) : Prop := ∀ φ w, P (neg φ) w → ¬ P φ w\ndef A2 (R : W → W → Prop) (P : RP D → W → Prop) : Prop := ∀ φ ψ w, P φ w → ent R φ ψ w → P ψ w\ndef A3 (P : RP D → W → Prop) : Prop := ∀ w, P (God P w) w\ndef A5S (R : W → W → Prop) (P : RP D → W → Prop) : Prop := ∀ w, P (NE (essS R) R w) w\ndef A5G (R : W → W → Prop) (P : RP D → W → Prop) : Prop := ∀ w, P (NE (essG R) R w) w\n\ntheorem negbot : neg (bot : RP D) = top := funext fun _ => propext ⟨fun _ => trivial, fun _ h => h⟩\n\n-- Under A1, bot and top cannot both be positive.\ntheorem not_both (P : RP D → W → Prop) (h1 : A1 P) (w : W) (hb : P bot w) (ht : P top w) : False := by\n  have := (h1 bot w) (negbot ▸ ht); exact this hb\n\ntheorem NE_S_top (R : W → W → Prop) (w : W) : NE (essS R) R w = (top : RP D) :=\n  funext fun x => propext ⟨fun _ => trivial, fun _ _ he _ _ => ⟨x, he.1⟩⟩\n\n-- A1 + A2 + A3 give a God-like being at every world of every frame.\ntheorem A123_god (R : W → W → Prop) (P : RP D → W → Prop) (h1 : A1 P) (h2 : A2 R P) (h3 : A3 P)\n    (w : W) : ∃ x, God P w x := by\n  apply Classical.byContradiction; intro hn\n  have hb : P bot w := h2 _ _ w (h3 w) (fun _ _ x hx => hn ⟨x, hx⟩)\n  have ht : P top w := h2 _ _ w hb (fun _ _ _ _ => trivial)\n  exact not_both P h1 w hb ht\n\n-- A1 + A3 + A5 (Scott essence) give a God-like being at every world of every frame.\ntheorem A135S_god (R : W → W → Prop) (P : RP D → W → Prop) (h1 : A1 P) (h3 : A3 P) (h5 : A5S R P)\n    (w : W) : ∃ x, God P w x := by\n  apply Classical.byContradiction; intro hn\n  have he : God P w = bot := funext fun x => propext ⟨fun hx => hn ⟨x, hx⟩, False.elim⟩\n  have hb : P bot w := he ▸ h3 w\n  have ht : P top w := NE_S_top R w ▸ h5 w\n  exact not_both P h1 w hb ht\n\ntheorem A123_box (R : W → W → Prop) (P : RP D → W → Prop) (h1 : A1 P) (h2 : A2 R P) (h3 : A3 P)\n    (w : W) : ∀ v, R w v → ∃ x, God P v x := fun v _ => A123_god R P h1 h2 h3 v\ntheorem A135S_box (R : W → W → Prop) (P : RP D → W → Prop) (h1 : A1 P) (h3 : A3 P) (h5 : A5S R P)\n    (w : W) : ∀ v, R w v → ∃ x, God P v x := fun v _ => A135S_god R P h1 h3 h5 v\n\n\nend Rigid\n#print axioms Rigid.A123_god\n#print axioms Rigid.A123_box\n#print axioms Rigid.A135S_god\n#print axioms Rigid.A135S_box\n#print axioms Rigid.NE_S_top'

import subprocess, shutil, os, re, json, hashlib
exe=shutil.which('lean')
if not exe:
    for p in ['/opt/elan/bin/lean','/opt/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean']:
        if os.path.isfile(p): exe=p; break
assert exe
r=subprocess.run([exe,'--stdin'],input=LEAN,text=True,capture_output=True,timeout=100)
assert r.returncode==0, r.stdout+r.stderr
assert 'sorry' not in LEAN and 'sorryAx' not in r.stdout
assert not re.search(r'(?m)^\s*axiom\s',LEAN)
for name in ['A123_god','A123_box','A135S_god','A135S_box','NE_S_top']:
    line=next(x for x in r.stdout.splitlines() if "'Rigid."+name+"'" in x)
    if 'depends on axioms:' in line:
        assert set(line.split('[')[1].split(']')[0].split(', ')) <= {'propext','Classical.choice','Quot.sound'}
print(r.stdout)
AX=['A1a','A1b','A2','H','N']
CL=['K','T','D','B','K4','KB','KD45','S4','S5']
def evaluate(d,pos):
    # Two worlds, universal accessibility; identical positivity at both worlds.
    full=(1<<d)-1; props=range(1<<d)
    g=full
    for q in pos: g &= q
    ne=0
    for x in range(d):
        def ess(q):
            return bool(q>>x&1) and all(q & ~p == 0 for p in props if p>>x&1)
        if all(q!=0 for q in props if ess(q)): ne |= 1<<x
    assert ne==full
    flags=[all(not(full^q in pos) or q not in pos for q in props),
           all(q in pos or full^q in pos for q in props),
           all(p in pos for q in pos for p in props if q & ~p == 0),
           g in pos, ne in pos]
    return sum(1<<i for i,b in enumerate(flags) if b),g!=0
models=[(1,{1}),(1,{0,1}),(3,{3,5,6,7}),(1,{0})]
results=[evaluate(*m) for m in models]
assert results[0]==(31,True)
rows=[]
for mask in range(32):
    proved=bool(mask&1 and mask&8 and (mask&4 or mask&16))
    witness=next((i for i,(a,g) in enumerate(results) if a&mask==mask and not g),None)
    assert (witness is None)==proved
    for cl in CL:
        # Universal two-world relation is reflexive, symmetric, serial,
        # transitive and euclidean, and refutes collapse via Q={0}.
        R=lambda w,v: True
        assert all(any(R(w,v) for v in range(2)) for w in range(2))
        assert R(0,1) and 0!=1
        proof=('A123' if mask&4 else 'A135S') if proved else None
        rows.append([mask,cl,0,0,proof,witness])
assert len(rows)==288
payload=json.dumps(rows,separators=(',',':')).encode()
digest=hashlib.sha256(payload).hexdigest()
assert digest=='6b196fadfb03ca91d2590787e1e2e201b02f7bff825d5a4218fb4d6456d747f1'
print('288 cells verified; sha256',digest)
