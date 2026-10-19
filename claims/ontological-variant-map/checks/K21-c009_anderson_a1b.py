"""C009 Anderson slice with Scott A1b column: 64 subsets of A1a,A1b,A2,H,A4,A5 x 9 classes x
constant / varying (actualist, E-guarded entailment and NE) domains, full intensional properties.
Countermodels: exhaustive |W||D|<=2 with every existence pattern plus five named models, re-evaluated
by a direct evaluator; positive cells by Lean theorems (hypotheses a subset of the cell axioms)."""
LEAN = r"""/- Varying-domain Anderson with the A1b column: E x w = x exists at w; domains may be empty.
   Entailment (A2, essence) and the NE exemplification are guarded by E; property
   quantifiers and the box in God_A / essence range over all D → W → Prop. -/
namespace VAndB
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
def A1b (P : Prp W D → W → Prop) : Prop := ∀ Y w, ¬ P Y w → P (fun x v => ¬ Y x v) w
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

/-- A1b alone: a God-like being at w makes all successors of w equal. -/
theorem god_det (h1b : A1b P) {x : D} {w : W} (hg : God R P x w) :
    ∀ u v, R w u → R w v → u = v := by
  intro u v hu hv
  apply Classical.byContradiction
  intro hne
  by_cases hp : P (fun _ t => t = u) w
  · exact hne ((hg _).mp hp v hv).symm
  · exact ((hg _).mp (h1b _ w hp) u hu) rfl

theorem god_unique {x y : D} {v : W} (hvv : R v v) (hx : God R P x v) (hy : God R P y v) :
    y = x :=
  (hy _).mp ((hx (fun z _ => z = x)).mpr (fun _ _ => rfl)) v hvv

/-- Euclidean frames: A1a, A1b, A2, H give a God-like individual at every world. -/
theorem eucl_A1b_godlike (he : ∀ w u v, R w u → R w v → R u v) (h1 : A1a P) (h1b : A1b P)
    (h2 : A2 E R P) (hH : H R P) (w : W) : ∃ x, God R P x w := by
  obtain ⟨v, x, hv, _, hg⟩ := poss h1 h2 hH w
  have hvv : R v v := he w v v hv hv
  have hR : ∀ u, R w u → u = v := fun u hu => god_det h1b hg u v (he w v u hv hu) hvv
  refine ⟨x, fun Y => ⟨fun hY u hu => ?_, fun hY => ?_⟩⟩
  · have huv := hR u hu
    subst huv
    apply Classical.byContradiction
    intro hn
    have hneg : P (fun z t => ¬ Y z t) w :=
      h2 _ _ w (hH w) (fun t ht y _ hy => by
        have htv := hR t ht
        subst htv
        rw [god_unique hvv hg hy]; exact hn)
    exact h1 _ w ⟨hY, hneg⟩
  · exact h2 _ _ w (hH w) (fun t ht y _ hy => by
      have htv := hR t ht
      subst htv
      rw [god_unique hvv hg hy]; exact hY t ht)

/-- K9's euclidean A4 lemma, varying-domain form (God-like, not necessarily existent). -/
theorem eucl_A4_godlike (he : ∀ w u v, R w u → R w v → R u v) (h1 : A1a P) (h2 : A2 E R P)
    (hH : H R P) (h4 : A4 R P) (w : W) : ∃ x, God R P x w := by
  obtain ⟨v, x, hv, _, hg⟩ := poss h1 h2 hH w
  have hb := god_box hH hg
  refine ⟨x, fun Y => ⟨fun hY u hu => ?_, fun hY => ?_⟩⟩
  · exact (hg Y).mp (h4 Y w hY v hv) u (he w v u hv hu)
  · refine h2 _ _ w (hH w) (fun u hu y _ hy => ?_)
    have hxu : God R P x u := hb u (he w v u hv hu)
    have huu : R u u := he w u u hu hu
    rw [god_unique huu hxu hy]; exact hY u hu

/-- With all individuals existing everywhere, a God-like individual is an existent one. -/
theorem const_ex {R : W → W → Prop} {P : Prp W D → W → Prop} {w : W}
    (h : ∃ x, God R P x w) : ExG (fun _ _ => True) R P w :=
  let ⟨x, hx⟩ := h; ⟨x, trivial, hx⟩

/-- B frames (reflexive, symmetric): A1a, A1b, A2, H force R w v ↔ v = w (collapse). -/
theorem refl_sym_collapse (hr : ∀ w, R w w) (hs : ∀ w v, R w v → R v w) (h1 : A1a P)
    (h1b : A1b P) (h2 : A2 E R P) (hH : H R P) : ∀ w v, R w v → v = w := fun w v hv =>
  let ⟨_, _, hg⟩ := sym_god hs h1 h2 hH w
  god_det h1b hg v w hv (hr w)

/-- Symmetric frames: adding A4 forces the same isolation. -/
theorem sym_A4_collapse (hs : ∀ w v, R w v → R v w) (h1 : A1a P) (h1b : A1b P)
    (h2 : A2 E R P) (hH : H R P) (h4 : A4 R P) : ∀ w v, R w v → v = w := fun w v hv => by
  obtain ⟨_, _, hgw⟩ := sym_god hs h1 h2 hH w
  obtain ⟨_, _, hgv⟩ := sym_god hs h1 h2 hH v
  have hY : P (fun _ t => t = v) w := (hgw _).mpr (fun u hu => god_det h1b hgw u v hu hv)
  exact ((hgv _).mp (h4 _ w hY v hv) w (hs w v hv)).symm
end

/- Countermodel 1 (KB, constant domain): two worlds seeing only each other, one individual,
   P(Y, w) := Y () (!w). A1a, A1b, A2, H, A5 hold; A4 and collapse fail. -/
abbrev Rc : Bool → Bool → Prop := fun w v => w ≠ v
def Pc : Prp Bool Unit → Bool → Prop := fun Y w => Y () (!w)
theorem boxc (p : Bool → Prop) (w : Bool) : box Rc p w ↔ p (!w) := by
  constructor
  · intro h; exact h (!w) (by cases w <;> decide)
  · intro h v hv; cases w <;> cases v <;> first | exact h | exact absurd rfl hv
theorem godc (w : Bool) : God Rc Pc () w := fun Y => (boxc (Y ()) w).symm
theorem kb_cycle :
    (∀ w v, Rc w v → Rc v w) ∧ A1a Pc ∧ A1b Pc ∧ A2 (fun _ _ => True) Rc Pc ∧ H Rc Pc ∧
    A5 (fun _ _ => True) Rc Pc ∧ ExG (fun _ _ => True) Rc Pc true ∧ ¬ A4 Rc Pc ∧
    Rc true false := by
  have h2 : A2 (fun _ _ => True) Rc Pc := fun Y Z w hY he =>
    (boxc _ w).mp he () trivial hY
  have hH : H Rc Pc := fun w => godc (!w)
  refine ⟨fun w v h => Ne.symm h, fun Y w ⟨h, h'⟩ => h' h, fun Y w h => h, h2, hH,
    A2H_A5 h2 hH, ⟨(), trivial, godc true⟩, fun h4 => ?_, by decide⟩
  have := h4 (fun _ t => t = false) true rfl false (by decide)
  exact Bool.noConfusion this

/- Countermodel 2 (KD45, varying domain): r → v, v → v; g exists only at v, o only at r;
   P(Y, t) := Y g v. All six axioms; g is God-like at r but does not exist there. -/
inductive Wk | r | v
inductive Dk | g | o
open Wk Dk
def Rk : Wk → Wk → Prop := fun _ u => u = v
def Ek : Prp Wk Dk
  | g, v => True
  | o, r => True
  | _, _ => False
def Pk : Prp Wk Dk → Wk → Prop := fun Y _ => Y g v
theorem boxk (p : Wk → Prop) (w : Wk) : box Rk p w ↔ p v :=
  ⟨fun h => h v rfl, fun h _ hu => hu ▸ h⟩
theorem godk (w : Wk) : God Rk Pk g w := fun Y => (boxk (Y g) w).symm
theorem kd45_A1b :
    (∀ w, ∃ u, Rk w u) ∧ (∀ w u t, Rk w u → Rk u t → Rk w t) ∧
    (∀ w u t, Rk w u → Rk w t → Rk u t) ∧ ¬ Rk r r ∧ (∀ w, ∃ x, Ek x w) ∧
    A1a Pk ∧ A1b Pk ∧ A2 Ek Rk Pk ∧ H Rk Pk ∧ A4 Rk Pk ∧ A5 Ek Rk Pk ∧
    ¬ ExG Ek Rk Pk r ∧ box Rk (ExG Ek Rk Pk) r ∧ Rk r v := by
  have h2 : A2 Ek Rk Pk := fun Y Z w hY he => (boxk _ w).mp he g trivial hY
  have hH : H Rk Pk := fun _ => godk v
  refine ⟨fun _ => ⟨v, rfl⟩, fun _ _ _ _ h => h, fun _ _ _ _ h => h, Wk.noConfusion, ?_,
    fun Y w ⟨h, h'⟩ => h' h, fun Y w h => h, h2, hH, fun Y w h u _ => h, A2H_A5 h2 hH, ?_, ?_, rfl⟩
  · intro w; cases w
    · exact ⟨o, trivial⟩
    · exact ⟨g, trivial⟩
  · intro ⟨x, hx, hg⟩; cases x
    · exact hx
    · exact Dk.noConfusion ((boxk _ r).mp ((hg (fun z _ => z = g)).mp rfl))
  · intro u hu; subst hu; exact ⟨g, trivial, godk v⟩

/-- With E universal the guarded notions coincide with the constant-domain ones. -/
theorem entails_top (R : W → W → Prop) (Y Z : Prp W D) (w : W) :
    entails (fun _ _ => True) R Y Z w ↔ box R (fun v => ∀ x, Y x v → Z x v) w :=
  ⟨fun h v hv x hy => h v hv x trivial hy, fun h v hv x _ hy => h v hv x hy⟩
end VAndB
#print axioms VAndB.god_exists_succ
#print axioms VAndB.poss
#print axioms VAndB.god_box
#print axioms VAndB.sym_god
#print axioms VAndB.sym_box
#print axioms VAndB.eucl_box
#print axioms VAndB.A2H_A5
#print axioms VAndB.god_det
#print axioms VAndB.god_unique
#print axioms VAndB.eucl_A1b_godlike
#print axioms VAndB.eucl_A4_godlike
#print axioms VAndB.const_ex
#print axioms VAndB.refl_sym_collapse
#print axioms VAndB.sym_A4_collapse
#print axioms VAndB.kb_cycle
#print axioms VAndB.kd45_A1b
#print axioms VAndB.entails_top
"""
PIN = "08d76079aa3a81893c9709a6fee5bbc484377c33d9cb72a0079b63b81b654168"
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
NAMES = ['god_exists_succ','poss','god_box','sym_god','sym_box','eucl_box','A2H_A5','god_det','god_unique',
 'eucl_A1b_godlike','eucl_A4_godlike','const_ex','refl_sym_collapse','sym_A4_collapse','kb_cycle','kd45_A1b','entails_top']
def axioms(name):
    name = 'VAndB.' + name
    if re.search(r"'" + re.escape(name) + r"' does not depend on any axioms", out):
        return set()
    m = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", out)
    assert m, "no #print axioms line for " + name
    return {a.strip() for a in m.group(1).split(",")}
for n in NAMES:
    assert axioms(n) <= STD, n


FRAMES = ('K', 'T', 'D', 'B', 'K4', 'KB', 'KD45', 'S4', 'S5')
def classes(n, r):
    e = lambda w, v: (r >> (w*n+v)) & 1 == 1
    ws = range(n)
    ref = all(e(w, w) for w in ws)
    sym = all(not e(w, v) or e(v, w) for w in ws for v in ws)
    ser = all(any(e(w, v) for v in ws) for w in ws)
    tr = all(not (e(w, v) and e(v, u)) or e(w, u) for w in ws for v in ws for u in ws)
    eu = all(not (e(w, v) and e(w, u)) or e(v, u) for w in ws for v in ws for u in ws)
    fl = (True, ref, ser, ref and sym, tr, sym, ser and tr and eu, ref and tr, ref and sym and tr)
    return [f for f, b in zip(FRAMES, fl) if b]

def ev(n, d, r, p, e):
    """Anderson, full intensional properties q (bitmask over (w,x)), existence bitmask e.
    Bits: 1 A1a, 2 A1b, 4 A2, 8 H, 16 A4, 32 A5. Entailment and NE exemplification E-guarded."""
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
          all(pos(q, w) or pos(top ^ q, w) for w in ws for q in ps),
          all(not (pos(q, w) and ent(q, z, w)) or pos(z, w) for w in ws for q in ps for z in ps),
          all(pos(god, w) for w in ws),
          all(not pos(q, w) or all(pos(q, v) for v in succ[w]) for w in ws for q in ps),
          all(pos(ne, w) for w in ws)]
    eg = [any(ex(x, w) and has(god, x, w) for x in xs) for w in ws]
    mask = sum(1 << i for i, a in enumerate(ax) if a)
    collapse = all(succ[w] in ([], [w]) for w in ws)       # full-property collapse <=> R(w) within {w}
    return mask, all(eg), all(all(eg[v] for v in succ[w]) for w in ws), collapse, god, succ

pool = []   # (mask, ex, box, collapse, classes, constant?, tag)
def add(n, d, edges, P, e, tag):
    r = sum(1 << (w*n+v) for w, v in edges)
    m, a, b, c, god, succ = ev(n, d, r, P, e)
    pool.append((m, a, b, c, classes(n, r), e == (1 << (n*d)) - 1, tag))
    return m, a, b, c, classes(n, r), god

# (1) exhaustive bound |W||D| <= 2: every frame, positivity family and existence pattern
for nn, dd in ((1, 1), (1, 2), (2, 1)):
    for r in range(1 << (nn*nn)):
        cl = classes(nn, r)
        for p in itertools.product(range(1 << (1 << (nn*dd))), repeat=nn):
            for e in range(1 << (nn*dd)):
                m, a, b, c, god, succ = ev(nn, dd, r, p, e)
                pool.append((m, a, b, c, cl, e == (1 << (nn*dd)) - 1, ('bound', nn, dd, r, p, e)))
assert len(pool) == 16528
full = lambda n, d: (1 << (n*d)) - 1
props = lambda n, d, f: sum(1 << q for q in range(1 << (n*d)) if f(q))
bit = lambda q, i: (q >> i) & 1 == 1
# (2) kb_cycle (Lean): worlds 0,1 seeing only each other; P(Y,w) = Y at the other world
m, a, b, c, cl, _ = add(2, 1, [(0, 1), (1, 0)], [props(2, 1, lambda q: bit(q, 1)), props(2, 1, lambda q: bit(q, 0))], 3, 'kb_cycle')
assert m == 1 | 2 | 4 | 8 | 32 and a and b and not c and 'KB' in cl and 'B' not in cl
# (3) S5 with clusters {u},{w,v}, one individual, P(Y,t) = Y at u: A2 fails, all others hold
m, a, b, c, cl, _ = add(3, 1, [(0, 0), (1, 1), (1, 2), (2, 1), (2, 2)], [props(3, 1, lambda q: bit(q, 0))]*3, 7, 'cluster3')
assert m == 1 | 2 | 8 | 16 | 32 and not a and not b and not c and 'S5' in cl
# (4) K9 constant KD45 model: r -> a,b; {a,b} cluster; P(Y,r) = Y a, P(Y,a/b) = Y a and Y b
Pr = props(3, 1, lambda q: bit(q, 1)); Pab = props(3, 1, lambda q: bit(q, 1) and bit(q, 2))
m, a, b, c, cl, _ = add(3, 1, [(0, 1), (0, 2), (1, 1), (1, 2), (2, 1), (2, 2)], [Pr, Pab, Pab], 7, 'k9_kd45')
assert m == 1 | 4 | 8 | 32 and not a and b and 'KD45' in cl
# (5) K15 varying KD45 model: g exists at a,b; o at r; P(Y,t) = Y g a and Y g b
E15 = sum(1 << (w*2+x) for (x, w) in [(0, 1), (0, 2), (1, 0)])
P15 = props(3, 2, lambda q: bit(q, 1*2+0) and bit(q, 2*2+0))
m, a, b, c, cl, _ = add(3, 2, [(0, 1), (0, 2), (1, 1), (1, 2), (2, 1), (2, 2)], [P15]*3, E15, 'k15_kd45')
assert m == 1 | 4 | 8 | 16 | 32 and not a and b and 'KD45' in cl
# (6) kd45_A1b (Lean): r -> v, v -> v; g exists at v, o at r; P(Y,t) = Y g v
EB = sum(1 << (w*2+x) for (x, w) in [(0, 1), (1, 0)])
m, a, b, c, cl, god = add(2, 2, [(0, 1), (1, 1)], [props(2, 2, lambda q: bit(q, 1*2+0))]*2, EB, 'kd45_A1b')
assert m == 63 and not a and b and not c and 'KD45' in cl and god == (1 << 0) | (1 << 2)

# (7) table: 64 subsets x 9 classes x {const, var}; positive cells by Lean theorems
SYM = ('B', 'KB', 'S5'); EUC = ('B', 'KB', 'KD45', 'S5'); REFSYM = ('B', 'S5')
def has_(s, t): return s & t == t
table = {}
for mode in ('const', 'var'):
    for s in range(64):
        for f in FRAMES:
            ms = [x for x in pool if has_(x[0], s) and f in x[4] and (mode == 'var' or x[5])]
            cons = bool(ms)
            exv = None
            if has_(s, 13) and f in SYM: exv = 'sym_god'
            elif mode == 'const' and f == 'KD45' and has_(s, 15): exv = 'eucl_A1b_godlike+const_ex'
            elif mode == 'const' and f == 'KD45' and has_(s, 29): exv = 'eucl_A4_godlike+const_ex'
            bxv = ('sym_box' if f in SYM else 'eucl_box') if has_(s, 13) and f in EUC else None
            cov = None
            if has_(s, 15) and f in REFSYM: cov = 'refl_sym_collapse'
            elif has_(s, 31) and f in SYM: cov = 'sym_A4_collapse'
            out = []
            for k, th in ((1, exv), (2, bxv), (3, cov)):
                bad = any(not x[k] for x in ms)
                if th: assert not bad, (mode, s, f, k)
                out.append('valid:' + th if th else ('refuted' if bad else 'OPEN'))
            table['%s/%d/%s' % (mode, s, f)] = [cons] + out
assert len(table) == 1152
assert not any('OPEN' in v for v in table.values()), [k for k, v in table.items() if 'OPEN' in v]
assert all(v[0] for v in table.values())                          # every cell consistent
for k, v in table.items():
    mode, s, f = k.split('/'); s = int(s)
    assert v[1].startswith('valid') == (has_(s, 13) and (f in SYM or (mode == 'const' and f == 'KD45' and (has_(s, 2) or has_(s, 16))))), k
    assert v[2].startswith('valid') == (has_(s, 13) and f in EUC), k
    assert v[3].startswith('valid') == (has_(s, 15) and (f in REFSYM or (f == 'KB' and has_(s, 16)))), k
# A1b-free rows reproduce K9 (constant) and K15 (varying) for existence and box
blob = json.dumps(table, sort_keys=True).encode()
h = hashlib.sha256(blob).hexdigest()
print("table sha256", h)
assert h == PIN, h
print("PASS: %d theorems, 1152 Anderson+A1b cells certified (const and varying), no OPEN" % len(NAMES))
