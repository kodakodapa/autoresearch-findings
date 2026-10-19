"""C009 rigid-property slice: Scott A1-A5 subsets x {Scott, Goedel-1970 essence} x 9 frame classes.
Semantics (constant domain D, properties RIGID: subsets of D; positivity P(phi,w) world-dependent;
axioms asserted globally, at every world):
  ent(w,phi,psi)  := for all v with R w v, phi subset psi   (vacuous at dead ends)
  G_w             := {x : x in phi for every phi positive at w}   (G read at w as a rigid property)
  essS(phi,x,w)   := x in phi and for all psi containing x, ent(w,phi,psi);  essG drops 'x in phi'
  NE_w            := {x : every essence phi of x at w is nonempty at each successor of w}
  A1: P(not phi,w) <-> not P(phi,w);  A2: P(phi,w) and ent(w,phi,psi) -> P(psi,w);  A3: P(G_w,w)
  A4: P(phi,w) and R w v -> P(phi,v);  A5: P(NE_w,w).
Outcomes per cell: cons (some model with a world), concl (exists x G at every world of every model),
box (box exists x G everywhere), collapse (every model has R w v -> v = w; all propositions W->Prop
exist, so collapse fails exactly when some R w v with v != w, witness proposition {w}).
Certificates: every 'fails' cell gets an explicit finite model from the enumerated pool, re-evaluated here
by brute force; every 'holds' cell names a Lean 4 core theorem (embedded, run with lean --stdin, no sorry,
no axiom decls, #print axioms within propext/Classical.choice/Quot.sound) whose hypotheses are a subset
of the cell's axioms; theorems hold on every frame so cover all classes. No monotone inference used.
Sanity: no pool model contradicts a Lean-proved cell. Pool: 1 world |D|<=3 (reflexive or dead end),
2 worlds |D|<=2 all 16 relations, and 2-world universal copies of the 1-world |D|=3 models.
Asserts the pattern: consistent unless Goedel essence and A1,A2,A5 present; concl/box hold iff
superset of {A1,A2,A3}, or of {A1,A3,A5} with Scott essence (or inconsistent); collapse never forced on a
consistent cell; Scott A5 is derivable from A1+A2 (Lean A12_A5S)."""
LEAN = r"""
namespace Rigid
variable {W D : Type}
abbrev RP (D : Type) := D → Prop
def bot : RP D := fun _ => False
def top : RP D := fun _ => True
def neg (φ : RP D) : RP D := fun x => ¬ φ x
-- box entailment at w for rigid properties
def ent (R : W → W → Prop) (φ ψ : RP D) (w : W) : Prop := ∀ v, R w v → ∀ x, φ x → ψ x
def God (P : RP D → W → Prop) (w : W) : RP D := fun x => ∀ φ, P φ w → φ x
def essS (R : W → W → Prop) (φ : RP D) (x : D) (w : W) : Prop :=
  φ x ∧ ∀ ψ, ψ x → ent R φ ψ w
def essG (R : W → W → Prop) (φ : RP D) (x : D) (w : W) : Prop :=
  ∀ ψ, ψ x → ent R φ ψ w
def NE (ess : RP D → D → W → Prop) (R : W → W → Prop) (w : W) : RP D :=
  fun x => ∀ φ, ess φ x w → ∀ v, R w v → ∃ y, φ y
def A1 (P : RP D → W → Prop) : Prop := ∀ φ w, P (neg φ) w ↔ ¬ P φ w
def A2 (R : W → W → Prop) (P : RP D → W → Prop) : Prop := ∀ φ ψ w, P φ w → ent R φ ψ w → P ψ w
def A3 (P : RP D → W → Prop) : Prop := ∀ w, P (God P w) w
def A5S (R : W → W → Prop) (P : RP D → W → Prop) : Prop := ∀ w, P (NE (essS R) R w) w
def A5G (R : W → W → Prop) (P : RP D → W → Prop) : Prop := ∀ w, P (NE (essG R) R w) w

theorem negbot : neg (bot : RP D) = top := funext fun _ => propext ⟨fun _ => trivial, fun _ h => h⟩

-- Under A1, bot and top cannot both be positive.
theorem not_both (P : RP D → W → Prop) (h1 : A1 P) (w : W) (hb : P bot w) (ht : P top w) : False := by
  have := (h1 bot w).mp (negbot ▸ ht); exact this hb

theorem NE_S_top (R : W → W → Prop) (w : W) : NE (essS R) R w = (top : RP D) :=
  funext fun x => propext ⟨fun _ => trivial, fun _ _ he _ _ => ⟨x, he.1⟩⟩

-- A1 + A2 + A3 give a God-like being at every world of every frame.
theorem A123_god (R : W → W → Prop) (P : RP D → W → Prop) (h1 : A1 P) (h2 : A2 R P) (h3 : A3 P)
    (w : W) : ∃ x, God P w x := by
  apply Classical.byContradiction; intro hn
  have hb : P bot w := h2 _ _ w (h3 w) (fun _ _ x hx => hn ⟨x, hx⟩)
  have ht : P top w := h2 _ _ w hb (fun _ _ _ _ => trivial)
  exact not_both P h1 w hb ht

-- A1 + A3 + A5 (Scott essence) give a God-like being at every world of every frame.
theorem A135S_god (R : W → W → Prop) (P : RP D → W → Prop) (h1 : A1 P) (h3 : A3 P) (h5 : A5S R P)
    (w : W) : ∃ x, God P w x := by
  apply Classical.byContradiction; intro hn
  have he : God P w = bot := funext fun x => propext ⟨fun hx => hn ⟨x, hx⟩, False.elim⟩
  have hb : P bot w := he ▸ h3 w
  have ht : P top w := NE_S_top R w ▸ h5 w
  exact not_both P h1 w hb ht

theorem A123_box (R : W → W → Prop) (P : RP D → W → Prop) (h1 : A1 P) (h2 : A2 R P) (h3 : A3 P)
    (w : W) : ∀ v, R w v → ∃ x, God P v x := fun v _ => A123_god R P h1 h2 h3 v
theorem A135S_box (R : W → W → Prop) (P : RP D → W → Prop) (h1 : A1 P) (h3 : A3 P) (h5 : A5S R P)
    (w : W) : ∀ v, R w v → ∃ x, God P v x := fun v _ => A135S_god R P h1 h3 h5 v

-- Scott A5 is redundant given A1 + A2 in the rigid slice.
theorem A12_A5S (R : W → W → Prop) (P : RP D → W → Prop) (h1 : A1 P) (h2 : A2 R P) : A5S R P := by
  intro w
  rw [NE_S_top R w]
  by_cases hb : P bot w
  · exact h2 _ _ w hb (fun _ _ _ _ => trivial)
  · have : P (neg bot) w := (h1 bot w).mpr hb
    exact h2 _ _ w this (fun _ _ _ _ => trivial)

-- Goedel (Nachlass) essence: A1, A2, A5 have no model with a world, on any frame.
theorem A125G_no_world (R : W → W → Prop) (P : RP D → W → Prop) (h1 : A1 P) (h2 : A2 R P)
    (h5 : A5G R P) (w : W) : False := by
  by_cases hs : ∃ v, R w v
  · obtain ⟨v, hv⟩ := hs
    have he : NE (essG R) R w = (bot : RP D) := funext fun x => propext
      ⟨fun hx => by
          obtain ⟨y, hy⟩ := hx bot (fun _ _ _ _ _ hy => False.elim hy) v hv
          exact hy,
       False.elim⟩
    have hb : P bot w := he ▸ h5 w
    exact not_both P h1 w hb (h2 _ _ w hb (fun _ _ _ _ => trivial))
  · have hd : ∀ φ ψ : RP D, ent R φ ψ w := fun _ _ v hv => False.elim (hs ⟨v, hv⟩)
    by_cases hb : P bot w
    · exact not_both P h1 w hb (h2 _ _ w hb (hd _ _))
    · have hn : P (neg bot) w := (h1 bot w).mpr hb
      exact hb (h2 _ _ w hn (hd _ _))

-- Noncollapse model of all of Scott A1-A5 (rigid) on the universal two-world frame:
-- W = Bool, D = Unit, P φ w := φ ().
def Ru : Bool → Bool → Prop := fun _ _ => True
def Pu : RP Unit → Bool → Prop := fun φ _ => φ ()
theorem scott_rigid_noncollapse :
    (∀ w, Ru w w) ∧ (∀ w v, Ru w v → Ru v w) ∧ (∀ w v u, Ru w v → Ru v u → Ru w u) ∧
    A1 Pu ∧ A2 Ru Pu ∧ A3 Pu ∧ (∀ φ w v, Ru w v → Pu φ w → Pu φ v) ∧ A5S Ru Pu ∧
    (∀ w, ∃ x, God Pu w x) ∧ ¬ (∀ v, Ru false v → v = false) := by
  refine ⟨fun _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ _ => trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ w; exact Iff.rfl
  · intro φ ψ w hp he; exact he true trivial () hp
  · intro w φ hφ; exact hφ
  · intro φ w v _ h; exact h
  · intro w φ he v _; exact ⟨(), he.1⟩
  · intro w; exact ⟨(), fun φ h => h⟩
  · intro h; exact Bool.noConfusion (h true trivial)
end Rigid
#print axioms Rigid.A123_god
#print axioms Rigid.A123_box
#print axioms Rigid.A135S_god
#print axioms Rigid.A135S_box
#print axioms Rigid.A12_A5S
#print axioms Rigid.A125G_no_world
#print axioms Rigid.scott_rigid_noncollapse
"""
import itertools, os, re, shutil, subprocess

CLASSES = {'K': [], 'D': ['serial'], 'T': ['refl'], 'B': ['refl', 'sym'], 'K4': ['trans'],
           'KB': ['sym'], 'KD45': ['serial', 'trans', 'eucl'], 'S4': ['refl', 'trans'],
           'S5': ['refl', 'sym', 'trans']}
AX = ['A1', 'A2', 'A3', 'A4', 'A5']

def fprops(n, R):
    W = range(n)
    return dict(refl=all((w, w) in R for w in W), sym=all((v, w) in R for (w, v) in R),
                trans=all((w, u) in R for (w, v) in R for (v2, u) in R if v == v2),
                serial=all(any((w, v) in R for v in W) for w in W),
                eucl=all((v, u) in R for (w, v) in R for (w2, u) in R if w == w2))

def evaluate(n, m, R, pos, ess):
    """pos[w] = frozenset of masks over D (bit x = individual x). Returns (set of axioms true, flags)."""
    full = (1 << m) - 1; props = range(1 << m)
    succ = [[v for v in range(n) if (w, v) in R] for w in range(n)]
    def ent(w, a, b): return (not succ[w]) or (a & ~b) == 0
    def G(w):
        g = full
        for a in pos[w]: g &= a
        return g
    def essf(a, x, w):
        if ess == 'S' and not a >> x & 1: return False
        return all(ent(w, a, b) for b in props if b >> x & 1)
    def NE(w):
        return sum(1 << x for x in range(m)
                   if all(all(a != 0 for v in succ[w]) for a in props if essf(a, x, w)))
    ok = {k: True for k in AX}
    for w in range(n):
        for a in props:
            pa = a in pos[w]
            if (full ^ a in pos[w]) == pa: ok['A1'] = False
            if pa and any(ent(w, a, b) and b not in pos[w] for b in props): ok['A2'] = False
            if pa and any(a not in pos[v] for v in succ[w]): ok['A4'] = False
        if G(w) not in pos[w]: ok['A3'] = False
        if NE(w) not in pos[w]: ok['A5'] = False
    concl = all(G(w) != 0 for w in range(n))
    box = all(G(v) != 0 for w in range(n) for v in succ[w])
    collapse = all(w == v for (w, v) in R)
    return {k for k in AX if ok[k]}, dict(concl=concl, box=box, collapse=collapse)

def pool():
    for m in (1, 2, 3):
        fam = range(1 << (1 << m))
        for R in (frozenset({(0, 0)}), frozenset()):
            for s in fam:
                yield (1, m, R, (frozenset(a for a in range(1 << m) if s >> a & 1),))
    pairs = [(w, v) for w in range(2) for v in range(2)]
    for m in (1, 2):
        fam = [frozenset(a for a in range(1 << m) if s >> a & 1) for s in range(1 << (1 << m))]
        for bits in range(16):
            R = frozenset(p for i, p in enumerate(pairs) if bits >> i & 1)
            for p0 in fam:
                for p1 in fam:
                    yield (2, m, R, (p0, p1))
    U = frozenset(pairs)
    for s in range(256):
        p = frozenset(a for a in range(8) if s >> a & 1)
        yield (2, 3, U, (p, p))

# Lean theorems: name -> (essence or None, hypotheses, outcomes proved)
THMS = {'Rigid.A123_god': (None, {'A1', 'A2', 'A3'}, {'concl'}),
        'Rigid.A123_box': (None, {'A1', 'A2', 'A3'}, {'box'}),
        'Rigid.A135S_god': ('S', {'A1', 'A3', 'A5'}, {'concl'}),
        'Rigid.A135S_box': ('S', {'A1', 'A3', 'A5'}, {'box'}),
        'Rigid.A125G_no_world': ('G', {'A1', 'A2', 'A5'}, {'inconsistent'})}

# ---- run Lean ----
exe = shutil.which("lean")
if exe is None:
    for c in ("/opt/elan/bin/lean", "/opt/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"):
        if os.path.isfile(c): exe = c; break
assert exe, "lean not found"
pr = subprocess.run([exe, "--stdin"], input=LEAN, capture_output=True, text=True, timeout=100)
out = pr.stdout + pr.stderr
print(out)
assert pr.returncode == 0 and "error" not in out
assert "sorry" not in LEAN and "sorryAx" not in out
assert not re.search(r"(?m)^\s*axiom\s", LEAN)
STD = {"propext", "Classical.choice", "Quot.sound"}
def axioms(name):
    if re.search(r"'" + re.escape(name) + r"' does not depend on any axioms", out): return set()
    mm = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", out)
    assert mm, name
    return {a.strip() for a in mm.group(1).split(",")}
for nm in list(THMS) + ['Rigid.A12_A5S', 'Rigid.scott_rigid_noncollapse']:
    assert axioms(nm) <= STD, nm

# ---- evaluate pool ----
models = []
for (n, m, R, pos) in pool():
    pr_ = fprops(n, R)
    cls = {c for c in CLASSES if all(pr_[k] for k in CLASSES[c])}
    for ess in ('S', 'G'):
        sat, fl = evaluate(n, m, R, pos, ess)
        models.append((ess, frozenset(sat), cls, fl, (n, m, sorted(R), [sorted(p) for p in pos])))
print("pool models:", len(models) // 2)

subsets = [frozenset(c) for k in range(6) for c in itertools.combinations(AX, k)]
table = {}; nproof = nmodel = 0
for sub in subsets:
    for ess in ('S', 'G'):
        for cls in CLASSES:
            cands = [md for md in models if md[0] == ess and sub <= md[1] and cls in md[2]]
            cell = {}
            incons = [t for t, (e, h, o) in THMS.items() if 'inconsistent' in o and e in (None, ess) and h <= sub]
            for goal in ('cons', 'concl', 'box', 'collapse'):
                if goal == 'cons':
                    wit = cands[0] if cands else None
                    if wit: cell[goal] = ('model', wit[4]); nmodel += 1
                else:
                    wit = next((md for md in cands if not md[3][goal]), None)
                    if wit: cell[goal] = ('model', wit[4]); nmodel += 1
                thm = incons or [t for t, (e, h, o) in THMS.items() if goal in o and e in (None, ess) and h <= sub]
                if thm:
                    assert goal not in cell, ("pool model contradicts Lean theorem", sub, ess, cls, goal)
                    cell[goal] = ('lean', thm[0]); nproof += 1
                assert goal in cell, ("OPEN cell", sorted(sub), ess, cls, goal)
            table[(sub, ess, cls)] = cell
assert len(table) == 32 * 2 * 9
print("cells:", len(table), "model certs:", nmodel, "lean certs:", nproof)

# ---- pattern assertions ----
for (sub, ess, cls), cell in table.items():
    inc = ess == 'G' and {'A1', 'A2', 'A5'} <= sub
    holds = lambda g: cell[g][0] == 'lean'
    assert holds('cons') == inc, (sub, ess, cls)  # 'cons' lean cert means inconsistent
    prove = inc or {'A1', 'A2', 'A3'} <= sub or (ess == 'S' and {'A1', 'A3', 'A5'} <= sub)
    assert holds('concl') == prove and holds('box') == prove, (sorted(sub), ess, cls)
    assert holds('collapse') == inc, (sorted(sub), ess, cls)
# noncollapse witnesses of consistent cells lie on frames with a non-loop edge
print("PASS: rigid slice, 576 cells certified (models or Lean), pattern asserted")
