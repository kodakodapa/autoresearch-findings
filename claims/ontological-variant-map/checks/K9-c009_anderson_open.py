"""C009 cross-review of r2's K8 (Anderson census): closes its 32 OPEN existence outcomes.
Semantics exactly as r2's anderson_census.py: constant nonempty domain D, all intensional properties
D -> W -> Prop, world-dependent positivity P, global axioms, necessary entailment over R-successors.
  God_A(x,w) := forall Y, P(Y,w) <-> box Y(x) at w
  Ess_A(Y,x,w) := forall Z, box Z(x) <-> box (forall z, Y z -> Z z)        NE_A(x) := forall Y, Ess_A(Y,x) -> box exists Y
  A1a: not (P Y and P notY); A2: necessary-entailment closure; H: P(God_A); A4: P Y -> box P Y; A5: P(NE_A).
Lean 4 core (lean --stdin), no sorry, no axiom declarations:
  NE_univ: NE_A holds of every individual (take Z := Y); A2H_A5: A2 and H imply A5.
  poss: A1a, A2, H give a possible God-like being at every world of every frame.
  sym_god / sym_box: on symmetric frames A1a, A2, H give exists God_A and box exists God_A everywhere.
  eucl_box: on euclidean frames A1a, A2, H give box exists God_A.
  eucl_A4_god: on euclidean frames A1a, A2, H, A4 give exists God_A (uniqueness via haecceity z = x).
  kd45_countermodel: 3-world KD45 frame r->a, r->b, {a,b} universal, one individual,
     P(Y,r) := Y(a), P(Y,a) = P(Y,b) := Y(a) and Y(b); A1a, A2, H, A5 hold, no God-like being at r, A4 fails.
The same countermodel is re-evaluated by r2's brute-force evaluator (copied verbatim from
agents/r2/checks/anderson_census.py), giving axiom mask 23 = {A1a,A2,H,A5}, exists false, box-exists true.
Resulting cells for r2's 16 open cells (masks 7,15,23,31 x B,KB,KD45,S5):
  B, KB, S5: exists and box-exists valid for all four masks (sym_god/sym_box; B, S5 are symmetric).
  KD45: box-exists valid for all four (eucl_box); exists valid for masks 15, 31 (eucl_A4_god),
        refuted for masks 7, 23 (kd45_countermodel)."""
import os, re, shutil, subprocess, itertools
LEAN = r"""
namespace And
variable {W D : Type}
abbrev Prp (W D : Type) := D → W → Prop
def box (R : W → W → Prop) (p : W → Prop) (w : W) : Prop := ∀ v, R w v → p v
def God (R : W → W → Prop) (P : Prp W D → W → Prop) : Prp W D :=
  fun x w => ∀ Y, P Y w ↔ box R (Y x) w
def Ess (R : W → W → Prop) (Y : Prp W D) (x : D) (w : W) : Prop :=
  ∀ Z : Prp W D, box R (Z x) w ↔ box R (fun v => ∀ z, Y z v → Z z v) w
def NE (R : W → W → Prop) : Prp W D :=
  fun x w => ∀ Y, Ess R Y x w → box R (fun v => ∃ z, Y z v) w
def A1a (P : Prp W D → W → Prop) : Prop := ∀ Y w, ¬ (P Y w ∧ P (fun x v => ¬ Y x v) w)
def A2 (R : W → W → Prop) (P : Prp W D → W → Prop) : Prop :=
  ∀ Y Z w, P Y w → box R (fun v => ∀ x, Y x v → Z x v) w → P Z w
def H (R : W → W → Prop) (P : Prp W D → W → Prop) : Prop := ∀ w, P (God R P) w
def A4 (R : W → W → Prop) (P : Prp W D → W → Prop) : Prop := ∀ Y w, P Y w → box R (P Y) w
def A5 (R : W → W → Prop) (P : Prp W D → W → Prop) : Prop := ∀ w, P (NE R) w

/-- Anderson essence implies necessary exemplification, so NE holds of everything. -/
theorem NE_univ (R : W → W → Prop) (x : D) (w : W) : NE R x w :=
  fun Y hE v hv => ⟨x, (hE Y).mpr (fun _ _ _ hz => hz) v hv⟩

/-- A2 and H give A5, so A5 is redundant in the presence of A2 and H. -/
theorem A2H_A5 (R : W → W → Prop) (P : Prp W D → W → Prop) (h2 : A2 R P) (hH : H R P) : A5 R P :=
  fun w => h2 _ _ w (hH w) (fun v _ y _ => NE_univ R y v)

/-- A1a, A2, H: a God-like being is possible at every world (no frame condition). -/
theorem poss (R : W → W → Prop) (P : Prp W D → W → Prop) (h1 : A1a P) (h2 : A2 R P) (hH : H R P)
    (w : W) : ∃ v x, R w v ∧ God R P x v :=
  Classical.byContradiction fun h =>
    h1 _ w ⟨hH w, h2 _ _ w (hH w) (fun v hv x hx _ => h ⟨v, x, hv, hx⟩)⟩

theorem god_box (R : W → W → Prop) (P : Prp W D → W → Prop) (hH : H R P) (x : D) (v : W)
    (hg : God R P x v) : box R (God R P x) v := (hg _).mp (hH v)

theorem sym_god (R : W → W → Prop) (P : Prp W D → W → Prop) (hs : ∀ w v, R w v → R v w)
    (h1 : A1a P) (h2 : A2 R P) (hH : H R P) (w : W) : ∃ x, God R P x w :=
  let ⟨v, x, hv, hg⟩ := poss R P h1 h2 hH w
  ⟨x, god_box R P hH x v hg w (hs w v hv)⟩

theorem sym_box (R : W → W → Prop) (P : Prp W D → W → Prop) (hs : ∀ w v, R w v → R v w)
    (h1 : A1a P) (h2 : A2 R P) (hH : H R P) (w : W) : box R (fun u => ∃ x, God R P x u) w :=
  fun u _ => sym_god R P hs h1 h2 hH u

theorem eucl_box (R : W → W → Prop) (P : Prp W D → W → Prop)
    (he : ∀ w u v, R w u → R w v → R u v)
    (h1 : A1a P) (h2 : A2 R P) (hH : H R P) (w : W) : box R (fun u => ∃ x, God R P x u) w :=
  fun u hu =>
    let ⟨v, x, hv, hg⟩ := poss R P h1 h2 hH w
    ⟨x, god_box R P hH x v hg u (he w v u hv hu)⟩

theorem eucl_A4_god (R : W → W → Prop) (P : Prp W D → W → Prop)
    (he : ∀ w u v, R w u → R w v → R u v)
    (h1 : A1a P) (h2 : A2 R P) (hH : H R P) (h4 : A4 R P) (w : W) : ∃ x, God R P x w := by
  obtain ⟨v, x, hv, hg⟩ := poss R P h1 h2 hH w
  have hb := god_box R P hH x v hg
  refine ⟨x, fun Y => ⟨fun hY u hu => ?_, fun hY => ?_⟩⟩
  · exact (hg Y).mp (h4 Y w hY v hv) u (he w v u hv hu)
  · refine h2 _ _ w (hH w) (fun u hu y hy => ?_)
    have hxu : God R P x u := hb u (he w v u hv hu)
    have huu : R u u := he w u u hu hu
    have hpos : P (fun z _ => z = x) u := (hxu _).mpr (fun _ _ => rfl)
    have hyx : y = x := (hy _).mp hpos u huu
    exact hyx ▸ hY u hu

/- Countermodel: KD45 frame r → a, r → b, {a,b} universal; one individual. -/
inductive Wd | r | a | b
open Wd
def Rk : Wd → Wd → Prop
  | r, r => False
  | r, _ => True
  | _, r => False
  | _, _ => True
def Pk : Prp Wd Unit → Wd → Prop
  | Y, r => Y () a
  | Y, _ => Y () a ∧ Y () b

theorem god_a : God Rk Pk () a := fun Y =>
  ⟨fun ⟨ha, hb⟩ v _ => by cases v <;> first | exact ha | exact hb | contradiction,
   fun h => ⟨h a trivial, h b trivial⟩⟩
theorem god_b : God Rk Pk () b := fun Y =>
  ⟨fun ⟨ha, hb⟩ v _ => by cases v <;> first | exact ha | exact hb | contradiction,
   fun h => ⟨h a trivial, h b trivial⟩⟩
theorem not_god_r : ¬ God Rk Pk () r := fun h =>
  Wd.noConfusion ((h (fun _ v => v = a)).mp rfl b trivial)

theorem kd45_countermodel :
    (∀ w, ∃ v, Rk w v) ∧ (∀ w v u, Rk w v → Rk v u → Rk w u) ∧
    (∀ w u v, Rk w u → Rk w v → Rk u v) ∧ ¬ Rk r r ∧
    A1a Pk ∧ A2 Rk Pk ∧ H Rk Pk ∧ A5 Rk Pk ∧ ¬ (∃ x, God Rk Pk x r) ∧ ¬ A4 Rk Pk := by
  have hH : H Rk Pk := by
    intro w; cases w
    · exact god_a
    · exact ⟨god_a, god_b⟩
    · exact ⟨god_a, god_b⟩
  have h2 : A2 Rk Pk := by
    intro Y Z w hY he; cases w
    · exact he a trivial () hY
    · exact ⟨he a trivial () hY.1, he b trivial () hY.2⟩
    · exact ⟨he a trivial () hY.1, he b trivial () hY.2⟩
  refine ⟨?_, ?_, ?_, fun h => h, ?_, h2, hH, A2H_A5 Rk Pk h2 hH, ?_, ?_⟩
  · intro w; cases w <;> exact ⟨a, trivial⟩
  · intro w v u h1 h2; cases w <;> cases v <;> cases u <;> first | trivial | contradiction
  · intro w u v h1 h2; cases w <;> cases u <;> cases v <;> first | trivial | contradiction
  · intro Y w ⟨h, h'⟩; cases w
    · exact h' h
    · exact h'.1 h.1
    · exact h'.1 h.1
  · intro ⟨x, hx⟩; cases x; exact not_god_r hx
  · intro h4
    have : Pk (fun _ v => v = a) b := h4 (fun _ v => v = a) r rfl b trivial
    exact Wd.noConfusion this.2
end And
#print axioms And.NE_univ
#print axioms And.A2H_A5
#print axioms And.poss
#print axioms And.sym_god
#print axioms And.sym_box
#print axioms And.eucl_box
#print axioms And.eucl_A4_god
#print axioms And.kd45_countermodel
"""
NAMES = ['And.NE_univ', 'And.A2H_A5', 'And.poss', 'And.sym_god', 'And.sym_box', 'And.eucl_box',
         'And.eucl_A4_god', 'And.kd45_countermodel']
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
assert "sorry" not in LEAN and "sorryAx" not in out
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

# ---- r2's evaluator, verbatim from agents/r2/checks/anderson_census.py ----
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

# countermodel: worlds 0=r, 1=a, 2=b; one individual; property q = bitmask over worlds
n, d = 3, 1
R = sum(1 << (w*n+v) for (w, v) in [(0,1),(0,2),(1,1),(1,2),(2,1),(2,2)])
Pr = sum(1 << q for q in range(8) if q & 2)               # P(Y,r) := Y(a)
Pab = sum(1 << q for q in range(8) if q & 2 and q & 4)    # P(Y,a) = P(Y,b) := Y(a) and Y(b)
mask, eg, beg, mc = evaluate(n, d, R, [Pr, Pab, Pab])
assert 'KD45' in classes(n, R) and 'KB' not in classes(n, R) and 'T' not in classes(n, R)
assert mask == 1 | 2 | 4 | 16, mask        # A1a, A2, H, A5 hold; A4 fails
assert eg is False and beg is True          # no God-like being at r; box-exists holds everywhere
assert mc is False                          # collapse fails too

# NE_A universal, checked by brute force on every model of r2's bound (independent of Lean)
cnt = 0
for nn, dd in ((1,1),(1,2),(2,1)):
    for r in range(1 << (nn*nn)):
        for p in itertools.product(range(1 << (1 << (nn*dd))), repeat=nn):
            m = evaluate(nn, dd, r, p)[0]
            assert not (m & 2 and m & 4) or m & 16   # A2 and H imply A5
            cnt += 1
assert cnt == 4136

# cell resolution for r2's 16 open cells
res = {}
for f in ('B', 'KB', 'KD45', 'S5'):
    for s in (7, 15, 23, 31):
        if f in ('B', 'KB', 'S5'):
            res[f, s] = ('valid:sym_god', 'valid:sym_box')
        elif s & 8:
            res[f, s] = ('valid:eucl_A4_god', 'valid:eucl_box')
        else:
            res[f, s] = ('refuted:kd45_countermodel', 'valid:eucl_box')
assert len(res) == 16
for (f, s), v in sorted(res.items()):
    print(f, s, v)
print("PASS: %d theorems, countermodel re-evaluated, 16 open cells resolved" % len(NAMES))
