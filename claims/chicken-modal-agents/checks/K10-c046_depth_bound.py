"""C046 r1 (round 3): modal-depth bound for graded FairBots, any 2-action game.
Language L: atoms p (opponent plays action 1 against me), q (opponent plays action 1 against the
constant action-2 bot); constant F; ~,&,|,[]; agents guarded (every atom under a box).
True = action 1 (swerve / cooperate / stag). md = modal depth (nesting of []).
Theorem (Lean 4 core, embedded, all formulas): if a guarded agent A goes straight (action 2) against
SwerveBot (constant action 1) at all large heights, then for every j >= md(A) the graded FairBot
F_j = []^j p plays action 2 against A at every height >= md(A)+j; so A and F_j never reach mutual
action 1. Lemmas: locality of guarded formulas; constant inputs => value constant from height md.
Asserts:
 (1) Lean proves depth_bound (no sorryAx); two weakened variants (j >= md-1, height md+j-1) fail;
 (2) census of guarded classes up to size 10 (7561 classes, Moore-machine engine copied from
     c046_chicken_q.py): every class is constant vs SwerveBot from height md; 3102 go straight vs
     SwerveBot; for all of them and j = max(1,md)..md+3 (12407 pairs) F_j is straight from md+j;
     the bound is attained (CC with F_{md-1}) by 92 classes, the smallest []([]F|~q) (size 6, md 2);
 (3) direct height evaluation: []([]F|~q) vs []p is CC, vs [][]p F_2 goes straight from height 4.
Height semantics: box phi holds at h iff phi holds at all g < h (Boolos ch. 7); tail = standard value.
"""
import sys, time, os, shutil, subprocess
from collections import deque, Counter
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

def is_moore(m):
    return all(len(set(r)) == 1 for r in m[1])

def enumerate_classes(N, log=True):
    """U[n]: classes first reached at size n by any formula; G[n]: by guarded formula.
    first[cls] = (size, formula string) of a smallest realiser (guarded for G)."""
    U = {}; G = {}           # size -> list of classes (new at that size)
    firstU = {}; firstG = {}
    def addU(n, c, s):
        if c not in firstU: firstU[c] = (n, s); U[n].append(c)
    def addG(n, c, s):
        if c not in firstG: firstG[c] = (n, s); G[n].append(c)
    for n in range(1, N+1):
        t0 = time.time()
        U[n] = []; G[n] = []
        if n == 1:
            addU(1, BOT, 'F'); addU(1, P, 'p'); addU(1, Q, 'q'); addG(1, BOT, 'F')
        else:
            # unary
            for c in U[n-1]:
                s = firstU[c][1]
                addU(n, neg(c), '~' + s)
                b = box(c); addU(n, b, '[]' + s); addG(n, b, '[]' + s)
            for c in G[n-1]:
                addG(n, neg(c), '~' + firstG[c][1])
            # binary: sizes i + j = n-1
            for i in range(1, n-1):
                j = n - 1 - i
                if i > j: break
                for (pool, first, add) in ((U, firstU, addU), (G, firstG, addG)):
                    for ai, a in enumerate(pool[i]):
                        sa = first[a][1]
                        for bi, b in enumerate(pool[j]):
                            if i == j and bi < ai: continue
                            sb = first[b][1]
                            add(n, AND(a, b), '(' + sa + '&' + sb + ')')
                            add(n, OR(a, b), '(' + sa + '|' + sb + ')')
        # guarded classes must also enter U pool (they're formulas too)
        for c in G[n]:
            addU(n, c, firstG[c][1])
        if log:
            print(f'size {n}: new U {len(U[n])} (tot {len(firstU)}), new G {len(G[n])} (tot {len(firstG)}), {time.time()-t0:.1f}s', flush=True)
    return U, G, firstU, firstG




def mdepth(s):
    d = m = 0; i = 0
    # modal depth of a formula string: max nesting of [] (brackets scope via parse)
    def p(i):
        c = s[i]
        if c in 'Fpq': return 0, i + 1
        if c == '~': return p(i + 1)
        if s.startswith('[]', i): d, j = p(i + 2); return d + 1, j
        a, j = p(i + 1); b, k = p(j + 1); assert s[k] == ')'
        return max(a, b), k + 1
    d, j = p(0); assert j == len(s); return d

def run_vs(m, opp, H):
    """m: guarded Moore machine; opp(h, xs) -> (y_h, z_h) inputs at height h. returns own trace"""
    T, O = m; s = 0; xs = []
    for h in range(H):
        xs.append(O[s][0])
        y, z = opp(h, xs)
        s = T[s][y + 2 * z]
    return xs

def census_check(N):
    U, G, fU, fG = enumerate_classes(N, log=False)
    cls = sorted(fG, key=lambda c: fG[c])
    stats = Counter(); tight = []
    for c in cls:
        n, s = fG[c]; d = mdepth(s); H = 3 * d + 30
        xs = run_vs(c, lambda h, xs: (1, 1), H)
        assert len(set(xs[d:])) == 1, s           # stabilisation from height d (lemma stab)
        if xs[-1]: continue                        # swerves vs SwerveBot: theorem says nothing
        stats['straight_vs_SB'] += 1
        best = 0
        for j in range(1, d + 4):
            ys = []
            def opp(h, xs, j=j):
                y = int(all(xs[g] for g in range(h - j + 1)))
                ys.append(y); return y, int(h < j)
            xs2 = run_vs(c, opp, d + j + 25)
            if j >= d:   # theorem: F_j plays action 2 at every height >= d + j
                assert not any(ys[d + j:]), (s, j)
                stats['pairs_checked'] += 1
            if xs2[-1] and ys[-1]: best = j
        assert best < max(d, 1), s
        if d >= 2 and best == d - 1: tight.append((n, s))
        stats['cc_any'] += best > 0
    return len(cls), stats, tight

LEAN_SRC = "/-! Depth bound: an agent of modal depth d that goes straight (defects) against the constant\n    action-1 bot cannot reach mutual action 1 with F_j = box^j p for any j ≥ d.\n    Height semantics: box φ holds at h iff φ holds at every g < h. -/\ninductive Fm where\n  | bot | p | q\n  | neg (a : Fm)\n  | and (a b : Fm)\n  | or (a b : Fm)\n  | box (a : Fm)\n\ndef ev (P Q : Nat → Prop) : Fm → Nat → Prop\n  | .bot, _ => False\n  | .p, h => P h\n  | .q, h => Q h\n  | .neg a, h => ¬ ev P Q a h\n  | .and a b, h => ev P Q a h ∧ ev P Q b h\n  | .or a b, h => ev P Q a h ∨ ev P Q b h\n  | .box a, h => ∀ g, g < h → ev P Q a g\n\ndef md : Fm → Nat\n  | .bot => 0\n  | .p => 0\n  | .q => 0\n  | .neg a => md a\n  | .and a b => max (md a) (md b)\n  | .or a b => max (md a) (md b)\n  | .box a => md a + 1\n\n/-- every atom occurrence lies under a box -/\ndef guarded : Fm → Prop\n  | .bot => True\n  | .p => False\n  | .q => False\n  | .neg a => guarded a\n  | .and a b => guarded a ∧ guarded b\n  | .or a b => guarded a ∧ guarded b\n  | .box _ => True\n\ntheorem local_lt (φ : Fm) (H : Nat) (P Q P' Q' : Nat → Prop)\n    (hP : ∀ g, g < H → (P g ↔ P' g)) (hQ : ∀ g, g < H → (Q g ↔ Q' g)) :\n    ∀ h, h < H → (ev P Q φ h ↔ ev P' Q' φ h) := by\n  induction φ with\n  | bot => intro h _; exact Iff.rfl\n  | p => intro h hh; exact hP h hh\n  | q => intro h hh; exact hQ h hh\n  | neg a ia => intro h hh; exact not_congr (ia h hh)\n  | and a b ia ib => intro h hh; exact and_congr (ia h hh) (ib h hh)\n  | or a b ia ib => intro h hh; exact or_congr (ia h hh) (ib h hh)\n  | box a ia =>\n    intro h hh\n    exact ⟨fun K g hg => (ia g (by omega)).1 (K g hg), fun K g hg => (ia g (by omega)).2 (K g hg)⟩\n\ntheorem local_guarded (φ : Fm) (hg : guarded φ) (H : Nat) (P Q P' Q' : Nat → Prop)\n    (hP : ∀ g, g < H → (P g ↔ P' g)) (hQ : ∀ g, g < H → (Q g ↔ Q' g)) :\n    ev P Q φ H ↔ ev P' Q' φ H := by\n  induction φ with\n  | bot => exact Iff.rfl\n  | p => exact absurd hg id\n  | q => exact absurd hg id\n  | neg a ia => exact not_congr (ia hg)\n  | and a b ia ib => exact and_congr (ia hg.1) (ib hg.2)\n  | or a b ia ib => exact or_congr (ia hg.1) (ib hg.2)\n  | box a _ =>\n    have L := local_lt a H P Q P' Q' hP hQ\n    exact ⟨fun K g hg' => (L g hg').1 (K g hg'), fun K g hg' => (L g hg').2 (K g hg')⟩\n\ndef T : Nat → Prop := fun _ => True\n\n/-- against constant inputs (opponent always plays action 1), a formula of depth d is\n    constant from height d on -/\ntheorem stab (φ : Fm) : ∀ h h', md φ ≤ h → md φ ≤ h' → (ev T T φ h ↔ ev T T φ h') := by\n  induction φ with\n  | bot => intros; exact Iff.rfl\n  | p => intros; exact Iff.rfl\n  | q => intros; exact Iff.rfl\n  | neg a ia => intro h h' a1 a2; exact not_congr (ia h h' a1 a2)\n  | and a b ia ib =>\n    intro h h' a1 a2; simp only [md] at a1 a2\n    exact and_congr (ia h h' (by omega) (by omega)) (ib h h' (by omega) (by omega))\n  | or a b ia ib =>\n    intro h h' a1 a2; simp only [md] at a1 a2\n    exact or_congr (ia h h' (by omega) (by omega)) (ib h h' (by omega) (by omega))\n  | box a ia =>\n    intro h h' a1 a2; simp only [md] at a1 a2\n    have one : ∀ u v, md a + 1 ≤ u → md a + 1 ≤ v →\n        (∀ g, g < u → ev T T a g) → ∀ g, g < v → ev T T a g := by\n      intro u v hu hv K g hg\n      by_cases hgu : g < u\n      · exact K g hgu\n      · exact (ia (md a) g (Nat.le_refl _) (by omega)).1 (K (md a) (by omega))\n    exact ⟨one h h' a1 a2, one h' h a2 a1⟩\n\n/-- Main theorem. A: guarded agent of depth d = md A that goes straight against SwerveBot\n    (inputs p = q = True) at all large heights. Opponent F_j = box^j p, written as its height\n    law; its NerveBot trace z solves z h ↔ ∀ g, g + j ≤ h → False. Then F_j plays action 2\n    at every height ≥ d + j, so the pair never reaches mutual action 1. -/\ntheorem depth_bound (A : Fm) (hA : guarded A) (j : Nat) (hdj : md A ≤ j)\n    (hsb : ∃ H, ∀ h, H ≤ h → ¬ ev T T A h)\n    (x y z : Nat → Prop) (hz : ∀ h, z h ↔ ∀ g, g + j ≤ h → False)\n    (hx : ∀ h, x h ↔ ev y z A h) (hy : ∀ h, y h ↔ ∀ g, g + j ≤ h → x g) :\n    ∀ h, md A + j ≤ h → ¬ y h := by\n  obtain ⟨H, hH⟩ := hsb\n  have n0 : ¬ ev T T A (md A) := fun e =>\n    hH (H + md A) (by omega) ((stab A (md A) (H + md A) (Nat.le_refl _) (by omega)).1 e)\n  have yl : ∀ g, g < md A → (y g ↔ T g) :=\n    fun g hg => ⟨fun _ => trivial, fun _ => (hy g).2 (fun t ht => by omega)⟩\n  have zl : ∀ g, g < md A → (z g ↔ T g) :=\n    fun g hg => ⟨fun _ => trivial, fun _ => (hz g).2 (fun t ht => by omega)⟩\n  have nx : ¬ x (md A) := fun xd =>\n    n0 ((local_guarded A hA (md A) y z T T yl zl).1 ((hx (md A)).1 xd))\n  intro h hh yh\n  exact nx ((hy h).1 yh (md A) hh)\n\n#print axioms depth_bound\n"

def lean():
    for c in (shutil.which('lean'), '/opt/elan/bin/lean', os.path.expanduser('~/.elan/bin/lean')):
        if c and os.path.exists(c): return c
    raise AssertionError('lean binary not found')
def run(s):
    r = subprocess.run([lean(), '--stdin'], input=s, capture_output=True, text=True, timeout=100)
    return r.returncode, r.stdout + r.stderr

def main():
    t0 = time.time()
    rc, out = run(LEAN_SRC)
    assert rc == 0 and 'sorryAx' not in out and 'error' not in out and 'depends on axioms' in out, out
    for a, b in (('(hdj : md A ≤ j)', '(hdj : md A ≤ j + 1)'),
                 ('∀ h, md A + j ≤ h → ¬ y h := by', '∀ h, md A + j ≤ h + 1 → ¬ y h := by')):
        assert a in LEAN_SRC
        rc2, out2 = run(LEAN_SRC.replace(a, b))
        assert rc2 != 0 or 'sorryAx' in out2, 'weakened variant accepted: ' + b
    print('(1) Lean depth_bound proved; weakened variants rejected', flush=True)
    n, st, tight = census_check(10)
    assert n == 7561 and st['straight_vs_SB'] == 3102 and st['pairs_checked'] == 12407, (n, st)
    assert len(tight) == 92 and min(tight) == (6, '[]([]F|~q)'), (len(tight), min(tight))
    print('(2) census', n, dict(st), 'tight', len(tight), min(tight), flush=True)
    # (3) explicit: A(h) = forall g<h: (g<1 or not q(g)), q = opponent vs NerveBot
    H = 30
    def play(j):
        x, y = [], []
        z = [h < j for h in range(H)]           # F_j vs NerveBot
        for h in range(H):
            x.append(all(g < 1 or not z[g] for g in range(h)))
            y.append(all(x[g] for g in range(h - j + 1)))
        return x, y
    x1, y1 = play(1); assert all(x1) and all(y1)
    x2, y2 = play(2); assert x2[3] is False and not any(y2[4:]) and all(y2[:4])
    sb = [all(g < 1 or not True for g in range(h)) for h in range(H)]
    assert sb[:2] == [True, True] and not any(sb[2:])
    print('(3) explicit cells ok')
    print('PASS', round(time.time() - t0, 1), 's')

main()
