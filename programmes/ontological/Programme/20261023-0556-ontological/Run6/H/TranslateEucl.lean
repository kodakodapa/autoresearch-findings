import Lean
import OpenQuestions.Ax1GenTwoVariant2
import Programme.«20261022-1724-ontological».Run3.WitnessDeep

/-! # Thread H (run 6, pr): Th3 of `Ax1GenTwoVariant2` on Euclidean frames (th's P95)

Self-contained file as `TranslateKB.lean`: the library's `WitnessDeep.lean` verbatim, then the
meta-program, then the translation of th's `Th3_eucl` (P95, `agents/th/lean/Programme/Run6/ThH10.lean`,
proof copied verbatim): `◇∃ᴱG → □∃ᴱG` from the frame hypothesis
`eucl : ∀ x y z, x 𝗿 y → x 𝗿 z → y 𝗿 z`, using the module's `Th2` (Ax3, Ax2a, Ax2b).
The hypothesis is read as the closed frame formula `∀x y z. R x y → R x z → R y z` (C7), so
`Th3E.validF : ValidV4Fs Th3E.Fs Th3E.T Th3E.φ`, and `Th3E.of_struct` re-proves the module-level
statement through the structural checks (C8).  Together with K7 (symmetry) and K10 (reflexive +
transitive does not suffice): symmetry is sufficient for Th3 but not necessary.

Also a laundering probe (th P96, sk plan P91): an existential witness
`fun z u => existsAt z u ∧ u = w` must be refused as a whole-term violation. -/


/-! Verbatim copy of the library's `Programme/20261022-1724-ontological/Run3/WitnessDeep.lean` (run 4: `DG`, `DW`,
`sound_v4_wt`), minus its `#print`s; the library's `Programme` modules are not prebuilt. -/

/-! # WitnessDeep.lean (th, run 3, round 10): target C (d) in deep form

Lines after this header: pr's `SepLS.lean` (K14 evidence; contains K8's `sep_not_valid_v4` and K12/K13's
`Canon`/`LS`) minus its final `#print`, then th's `WholeTerm.lean` section `Programme.ThWhole` (round 9:
`DG`, `DW`, `sound_v4_wt`, `of_DC`) minus `#print`s, both verbatim; then section `Programme.ThWit`:
the witness-only calculus `DG3` derives v4's separating sentence from every theory. -/

-- [cleanup 2026-10-23] shared block (7898 lines) now imported from Programme.«20261022-1724-ontological».Run3.WitnessDeep





/-! ## Tool part `Core` -/
section

/-! # Thread H (run 6, pr): object-level helpers and the meta-level mirror of run 4's deep syntax

`Lctx`/`Lproj` read the `𝓛`-part of a HOL context; `cert_L` certifies `emb (Lproj Γ) s`.  The
`wt_*` lemmas build whole-term proofs constructor by constructor.  Meta side: `FT`/`HT`/`DT`/`LT`
mirror `FTy`/`HTy`/`HTerm`/`Tm` (de Bruijn indices), with substitution, `βη`-normalisation, the
meta `emb`, and two read-backs from `HTerm`s to `𝓛`-terms (exact, and modulo `βη`). -/

open Lean Meta
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
  Programme.«20261022-1724-ontological».ThWhole

namespace Programme.H

/-! ## Object level -/

/-- The `𝓛`-types of a HOL context, innermost first. -/
def Lctx : List HTy → List FTy
  | [] => []
  | .L t :: Γ => t :: Lctx Γ
  | .w :: Γ => Lctx Γ
  | .o :: Γ => Lctx Γ

/-- The renaming that reads the `𝓛`-variables of `Lctx Γ` as variables of `Γ`. -/
def Lproj : (Γ : List HTy) → LRen (Lctx Γ) Γ
  | [] => nilR
  | .L _ :: Γ => liftL (Lproj Γ)
  | .w :: Γ => shL (Lproj Γ)
  | .o :: Γ => shL (Lproj Γ)

theorem cert_L (Γ : List HTy) (t : FTy) (s : Tm (Lctx Γ) t) : Cert (.L t) (emb (Lproj Γ) s) :=
  ⟨_, s, Lproj Γ, rfl⟩
theorem cert_w (Γ : List HTy) (x : HTerm Γ .w) : Cert .w x := trivial
theorem cert_o (Γ : List HTy) (x : HTerm Γ .o) : Cert .o x := trivial

theorem leibOK_plain (Γ : List HTy) (a : HTy) (h : plain a = true) (φ : HTerm (a :: Γ) .o)
    (s t : HTerm Γ a) : LeibOK a φ s t := Or.inl h
theorem leibOK_wt (Γ : List HTy) (a : HTy) (φ : HTerm (a :: Γ) .o) (s t : HTerm Γ a)
    (h : WT φ) (hs : Cert a s) (ht : Cert a t) : LeibOK a φ s t := Or.inr ⟨h, hs, ht⟩

theorem wt_var (Γ : List HTy) (a : HTy) (v : HVar Γ a) : WT (HTerm.var v) := trivial
theorem wt_appL (Γ : List HTy) (a b : FTy) (f : HTerm Γ (.L (.arr a b))) (x : HTerm Γ (.L a))
    (hf : WT f) (hx : Cert _ x) : WT (HTerm.appL f x) := ⟨hf, hx⟩
theorem wt_lamL (Γ : List HTy) (a b : FTy) (body : HTerm (.L a :: Γ) (.L b)) (h : WT body) :
    WT (HTerm.lamL body) := h
theorem wt_pos (Γ : List HTy) : WT (HTerm.pos (Γ := Γ)) := trivial
theorem wt_wabs (Γ : List HTy) (φ : HTerm (.w :: Γ) .o) (h : WT φ) : WT (HTerm.wabs φ) := h
theorem wt_holds (Γ : List HTy) (p : HTerm Γ (.L .s)) (i : HTerm Γ .w) (hp : WT p) (hi : WT i) :
    WT (HTerm.holds p i) := ⟨hp, hi⟩
theorem wt_rel (Γ : List HTy) (i j : HTerm Γ .w) (hi : WT i) (hj : WT j) : WT (HTerm.rel i j) :=
  ⟨hi, hj⟩
theorem wt_act (Γ : List HTy) (x : HTerm Γ (.L .e)) (i : HTerm Γ .w) (hx : WT x) (hi : WT i) :
    WT (HTerm.act x i) := ⟨hx, hi⟩
theorem wt_bot (Γ : List HTy) : WT (HTerm.bot (Γ := Γ)) := trivial
theorem wt_imp (Γ : List HTy) (p q : HTerm Γ .o) (hp : WT p) (hq : WT q) : WT (HTerm.imp p q) :=
  ⟨hp, hq⟩
theorem wt_and (Γ : List HTy) (p q : HTerm Γ .o) (hp : WT p) (hq : WT q) : WT (HTerm.and p q) :=
  ⟨hp, hq⟩
theorem wt_or (Γ : List HTy) (p q : HTerm Γ .o) (hp : WT p) (hq : WT q) : WT (HTerm.or p q) :=
  ⟨hp, hq⟩
theorem wt_all (Γ : List HTy) (a : HTy) (p : HTerm (a :: Γ) .o) (h : WT p) : WT (HTerm.all a p) := h
theorem wt_ex (Γ : List HTy) (a : HTy) (p : HTerm (a :: Γ) .o) (h : WT p) : WT (HTerm.ex a p) := h
theorem wt_eq (Γ : List HTy) (a : HTy) (s t : HTerm Γ a) (hs : WT s) (ht : WT t) :
    WT (HTerm.eq a s t) := ⟨hs, ht⟩

/-! ## Meta level: types, HOL terms, `𝓛`-terms -/

inductive FT | e | s | arr (a b : FT)
  deriving BEq, Inhabited, Repr, Hashable

inductive HT | L (t : FT) | w | o
  deriving BEq, Inhabited, Repr, Hashable

def FT.plain : FT → Bool
  | .e => true
  | .s => true
  | .arr .e b => b.plain
  | .arr _ _ => false

def HT.plain : HT → Bool
  | .L t => t.plain
  | _ => true

def FT.tp : FT := .arr .e .s
def FT.th : FT := .arr FT.tp .s

def FT.toString : FT → String
  | .e => "e" | .s => "σ" | .arr a b => s!"({a.toString} → {b.toString})"
def HT.toString : HT → String
  | .L t => t.toString | .w => "w" | .o => "o"
instance : ToString FT := ⟨FT.toString⟩
instance : ToString HT := ⟨HT.toString⟩

/-- Meta mirror of `HTerm` (de Bruijn; `lamL` records its domain). -/
inductive DT where
  | var (n : Nat)
  | appL (f x : DT)
  | lamL (a : FT) (b : DT)
  | pos
  | wabs (b : DT)
  | holds (p i : DT)
  | rel (i j : DT)
  | act (x i : DT)
  | bot
  | imp (p q : DT)
  | and (p q : DT)
  | or (p q : DT)
  | all (a : HT) (b : DT)
  | ex (a : HT) (b : DT)
  | eq (a : HT) (s t : DT)
  deriving BEq, Inhabited, Repr, Hashable

/-- Meta mirror of `Tm`. -/
inductive LT where
  | var (n : Nat)
  | app (f x : LT)
  | lam (a : FT) (b : LT)
  | top | bot
  | neg (x : LT)
  | and (x y : LT) | or (x y : LT) | imp (x y : LT)
  | box (x : LT)
  | all (a : FT) (b : LT) | ex (a : FT) (b : LT)
  | allE (b : LT) | exE (b : LT)
  | eq (a : FT) (x y : LT)
  | pos
  deriving BEq, Inhabited, Repr

namespace DT

def shift (d : Nat) (c : Nat := 0) : DT → DT
  | var n => if n ≥ c then var (n + d) else var n
  | appL f x => appL (f.shift d c) (x.shift d c)
  | lamL a b => lamL a (b.shift d (c + 1))
  | pos => pos
  | wabs b => wabs (b.shift d (c + 1))
  | holds p i => holds (p.shift d c) (i.shift d c)
  | rel i j => rel (i.shift d c) (j.shift d c)
  | act x i => act (x.shift d c) (i.shift d c)
  | bot => bot
  | imp p q => imp (p.shift d c) (q.shift d c)
  | and p q => and (p.shift d c) (q.shift d c)
  | or p q => or (p.shift d c) (q.shift d c)
  | all a b => all a (b.shift d (c + 1))
  | ex a b => ex a (b.shift d (c + 1))
  | eq a s t => eq a (s.shift d c) (t.shift d c)

/-- Substitute `s` for variable `j` (and lower the variables above `j`), as `HOLX.subst`. -/
def subst (j : Nat) (s : DT) : DT → DT
  | var n => if n == j then s.shift j 0 else if n > j then var (n - 1) else var n
  | appL f x => appL (subst j s f) (subst j s x)
  | lamL a b => lamL a (subst (j + 1) s b)
  | pos => pos
  | wabs b => wabs (subst (j + 1) s b)
  | holds p i => holds (subst j s p) (subst j s i)
  | rel i k => rel (subst j s i) (subst j s k)
  | act x i => act (subst j s x) (subst j s i)
  | bot => bot
  | imp p q => imp (subst j s p) (subst j s q)
  | and p q => and (subst j s p) (subst j s q)
  | or p q => or (subst j s p) (subst j s q)
  | all a b => all a (subst (j + 1) s b)
  | ex a b => ex a (subst (j + 1) s b)
  | eq a x y => eq a (subst j s x) (subst j s y)

/-- `HOLX.inst`. -/
def inst (b t : DT) : DT := subst 0 t b

def hasVar (j : Nat) : DT → Bool
  | var n => n == j
  | appL f x => f.hasVar j || x.hasVar j
  | lamL _ b => b.hasVar (j + 1)
  | pos => false
  | wabs b => b.hasVar (j + 1)
  | holds p i => p.hasVar j || i.hasVar j
  | rel i k => i.hasVar j || k.hasVar j
  | act x i => x.hasVar j || i.hasVar j
  | bot => false
  | imp p q | and p q | or p q => p.hasVar j || q.hasVar j
  | all _ b | ex _ b => b.hasVar (j + 1)
  | eq _ x y => x.hasVar j || y.hasVar j

/-- Lower all variables by one (variable `0` must not occur). -/
def down (x : DT) : DT := x.inst (var 0)

/-- `βη`-normal form (β at `𝓛`-application and at world application, η at both). -/
partial def nf : DT → DT
  | var n => var n
  | appL f x =>
      match nf f with
      | lamL _ b => nf (b.inst (nf x))
      | f' => appL f' (nf x)
  | lamL a b =>
      let b' := nf b
      match b' with
      | appL f (var 0) => if f.hasVar 0 then lamL a b' else f.down
      | _ => lamL a b'
  | pos => pos
  | wabs b =>
      let b' := nf b
      match b' with
      | holds p (var 0) => if p.hasVar 0 then wabs b' else p.down
      | _ => wabs b'
  | holds p i =>
      match nf p with
      | wabs b => nf (b.inst (nf i))
      | p' => holds p' (nf i)
  | rel i j => rel (nf i) (nf j)
  | act x i => act (nf x) (nf i)
  | bot => bot
  | imp p q => imp (nf p) (nf q)
  | and p q => and (nf p) (nf q)
  | or p q => or (nf p) (nf q)
  | all a b => all a (nf b)
  | ex a b =>
      -- `◇`: `∃v. R i v ∧ B` is read as `¬∀v. R i v → ¬B` (`Translate.eqNF0` derives the equation)
      match a, nf b with
      | .w, and (rel i (var 0)) B => imp (all .w (imp (rel i (var 0)) (imp B bot))) bot
      -- `∃x. x @ w` is read as `∃ᴱx. ⊤`
      | .L .e, act (var 0) i => ex (.L .e) (and (act (var 0) i) (imp bot bot))
      | _, b' => ex a b'
  | eq a s t => eq a (nf s) (nf t)

/-- Head `β`-reduction only (world and `𝓛` application). -/
partial def hnf : DT → DT
  | holds p i => match hnf p with
    | wabs b => hnf (b.inst i)
    | p' => holds p' i
  | appL f x => match hnf f with
    | lamL _ b => hnf (b.inst x)
    | f' => appL f' x
  | x => x

partial def toStr : DT → String
  | var n => s!"#{n}"
  | appL f x => s!"({f.toStr} {x.toStr})"
  | lamL a b => s!"(λ:{a}. {b.toStr})"
  | pos => "P"
  | wabs b => s!"(λw. {b.toStr})"
  | holds p i => s!"{p.toStr}@{i.toStr}"
  | rel i j => s!"R {i.toStr} {j.toStr}"
  | act x i => s!"act {x.toStr} {i.toStr}"
  | bot => "⊥"
  | imp p q => s!"({p.toStr} → {q.toStr})"
  | and p q => s!"({p.toStr} ∧ {q.toStr})"
  | or p q => s!"({p.toStr} ∨ {q.toStr})"
  | all a b => s!"(∀:{a}. {b.toStr})"
  | ex a b => s!"(∃:{a}. {b.toStr})"
  | eq a s t => s!"({s.toStr} =[{a}] {t.toStr})"

instance : ToString DT := ⟨toStr⟩

end DT

/-- Type of a meta HOL term in a context (head = variable `0`). -/
partial def DT.ty (ctx : List HT) : DT → Except String HT
  | .var n => match ctx[n]? with
      | some a => pure a
      | none => throw s!"unbound variable #{n}"
  | .appL f _ => do
      match ← DT.ty ctx f with
      | .L (.arr _ b) => pure (.L b)
      | a => throw s!"appL head of type {a}"
  | .lamL a b => do
      match ← DT.ty (.L a :: ctx) b with
      | .L t => pure (.L (.arr a t))
      | t => throw s!"lamL body of type {t}"
  | .pos => pure (.L FT.th)
  | .wabs _ => pure (.L .s)
  | _ => pure .o

/-- Index among the `𝓛`-variables of the context of HOL variable `n` (if it is one). -/
def lidx (ctx : List HT) (n : Nat) : Option Nat := Id.run do
  let mut k := 0
  for j in [0:n] do
    if let some (.L _) := ctx[j]? then k := k + 1
  match ctx[n]? with
  | some (.L _) => return some k
  | _ => return none

/-- `Lproj ctx` as a list: `𝓛`-index ↦ HOL index. -/
def lprojL (ctx : List HT) : List Nat := Id.run do
  let mut out := #[]
  for j in [0:ctx.length] do
    if let some (.L _) := ctx[j]? then out := out.push j
  return out.toList

def lctxL (ctx : List HT) : List FT :=
  ctx.filterMap fun | .L t => some t | _ => none

/-- Meta `emb`. -/
def embD (r : List Nat) : LT → DT
  | .var j => .var (r.getD j 0)
  | .app F x => .appL (embD r F) (embD r x)
  | .lam a b => .lamL a (embD (0 :: r.map (· + 1)) b)
  | .top => .wabs (.imp .bot .bot)
  | .bot => .wabs .bot
  | .neg x => .wabs (.imp (.holds (embD (r.map (· + 1)) x) (.var 0)) .bot)
  | .and x y => .wabs (.and (.holds (embD (r.map (· + 1)) x) (.var 0)) (.holds (embD (r.map (· + 1)) y) (.var 0)))
  | .or x y => .wabs (.or (.holds (embD (r.map (· + 1)) x) (.var 0)) (.holds (embD (r.map (· + 1)) y) (.var 0)))
  | .imp x y => .wabs (.imp (.holds (embD (r.map (· + 1)) x) (.var 0)) (.holds (embD (r.map (· + 1)) y) (.var 0)))
  | .box x => .wabs (.all .w (.imp (.rel (.var 1) (.var 0)) (.holds (embD (r.map (· + 2)) x) (.var 0))))
  | .all a b => .wabs (.all (.L a) (.holds (embD (0 :: r.map (· + 2)) b) (.var 1)))
  | .ex a b => .wabs (.ex (.L a) (.holds (embD (0 :: r.map (· + 2)) b) (.var 1)))
  | .allE b => .wabs (.all (.L .e) (.imp (.act (.var 0) (.var 1)) (.holds (embD (0 :: r.map (· + 2)) b) (.var 1))))
  | .exE b => .wabs (.ex (.L .e) (.and (.act (.var 0) (.var 1)) (.holds (embD (0 :: r.map (· + 2)) b) (.var 1))))
  | .eq a x y => .wabs (.eq (.L a) (embD (r.map (· + 1)) x) (embD (r.map (· + 1)) y))
  | .pos => .pos

/-- Exact inverse of `emb (Lproj ctx)`: `rbE ctx x = some s` iff `x = emb (Lproj ctx) s`. -/
partial def rbE (ctx : List HT) : DT → Option LT
  | .var n => (lidx ctx n).map LT.var
  | .appL f x => LT.app <$> rbE ctx f <*> rbE ctx x
  | .lamL a b => LT.lam a <$> rbE (.L a :: ctx) b
  | .pos => some .pos
  | .wabs b =>
      let c1 := HT.w :: ctx
      match b with
      | .imp .bot .bot => some .top
      | .bot => some .bot
      | .imp (.holds x (.var 0)) .bot => LT.neg <$> rbE c1 x
      | .and (.holds x (.var 0)) (.holds y (.var 0)) => LT.and <$> rbE c1 x <*> rbE c1 y
      | .or (.holds x (.var 0)) (.holds y (.var 0)) => LT.or <$> rbE c1 x <*> rbE c1 y
      | .imp (.holds x (.var 0)) (.holds y (.var 0)) => LT.imp <$> rbE c1 x <*> rbE c1 y
      | .all .w (.imp (.rel (.var 1) (.var 0)) (.holds x (.var 0))) => LT.box <$> rbE (.w :: c1) x
      | .all (.L .e) (.imp (.act (.var 0) (.var 1)) (.holds x (.var 1))) =>
          LT.allE <$> rbE (.L .e :: c1) x
      | .ex (.L .e) (.and (.act (.var 0) (.var 1)) (.holds x (.var 1))) =>
          LT.exE <$> rbE (.L .e :: c1) x
      | .all (.L a) (.holds x (.var 1)) => LT.all a <$> rbE (.L a :: c1) x
      | .ex (.L a) (.holds x (.var 1)) => LT.ex a <$> rbE (.L a :: c1) x
      | .eq (.L a) x y => LT.eq a <$> rbE c1 x <*> rbE c1 y
      | _ => none
  | _ => none

mutual
/-- Read-back of a `βη`-normal term at a type of `𝓛`. -/
partial def rbT (ctx : List HT) : DT → Option LT
  | .var n => (lidx ctx n).map LT.var
  | .appL f x => LT.app <$> rbT ctx f <*> rbT ctx x
  | .lamL a b => LT.lam a <$> rbT (.L a :: ctx) b
  | .pos => some .pos
  | .wabs b => rbF (.w :: ctx) 0 b
  | _ => none
/-- Read-back of a `βη`-normal formula as an `𝓛`-sentence at the world variable `wi`. -/
partial def rbF (ctx : List HT) (wi : Nat) : DT → Option LT
  | .bot => some .bot
  | .imp .bot .bot => some .top
  | .imp a .bot => LT.neg <$> rbF ctx wi a
  | .imp a b => LT.imp <$> rbF ctx wi a <*> rbF ctx wi b
  | .and a b => LT.and <$> rbF ctx wi a <*> rbF ctx wi b
  | .or a b => LT.or <$> rbF ctx wi a <*> rbF ctx wi b
  | .all (.L .e) (.imp (.act (.var 0) (.var k)) b) =>
      if k == wi + 1 then LT.allE <$> rbF (.L .e :: ctx) (wi + 1) b
      else LT.all .e <$> rbF (.L .e :: ctx) (wi + 1) (.imp (.act (.var 0) (.var k)) b)
  | .ex (.L .e) (.and (.act (.var 0) (.var k)) b) =>
      if k == wi + 1 then LT.exE <$> rbF (.L .e :: ctx) (wi + 1) b
      else none
  | .all (.L a) b => LT.all a <$> rbF (.L a :: ctx) (wi + 1) b
  | .ex (.L a) b => LT.ex a <$> rbF (.L a :: ctx) (wi + 1) b
  | .all .w (.imp (.rel (.var k) (.var 0)) b) =>
      if k == wi + 1 then LT.box <$> rbF (.w :: ctx) 0 b else none
  | .eq (.L a) x y => LT.eq a <$> rbT ctx x <*> rbT ctx y
  | .holds x (.var k) => if k == wi then rbT ctx x else none
  | _ => none
end

/-- Canonical certified form of a term at a type of `𝓛`: `emb (Lproj ctx)` of the read-back of its
`βη`-normal form. -/
def canonL (ctx : List HT) (x : DT) : Option (LT × DT) := do
  let tm ← rbT ctx x.nf
  let x' := embD (lprojL ctx) tm
  if x'.nf == x.nf then some (tm, x') else none

/-- Read-back of a closed formula at the world variable `wi` as an `𝓛`-sentence (modulo `βη`). -/
def sentenceOf (ctx : List HT) (wi : Nat) (φ : DT) : Option LT := rbF ctx wi φ.nf

partial def LT.toStr : LT → String
  | .var n => s!"v{n}"
  | .app f x => s!"({f.toStr} {x.toStr})"
  | .lam a b => s!"(λ:{a}. {b.toStr})"
  | .top => "⊤" | .bot => "⊥"
  | .neg x => s!"¬{x.toStr}"
  | .and x y => s!"({x.toStr} ∧ {y.toStr})"
  | .or x y => s!"({x.toStr} ∨ {y.toStr})"
  | .imp x y => s!"({x.toStr} → {y.toStr})"
  | .box x => s!"□{x.toStr}"
  | .all a b => s!"(∀:{a}. {b.toStr})"
  | .ex a b => s!"(∃:{a}. {b.toStr})"
  | .allE b => s!"(∀ᴱ. {b.toStr})"
  | .exE b => s!"(∃ᴱ. {b.toStr})"
  | .eq a x y => s!"({x.toStr} =[{a}] {y.toStr})"
  | .pos => "P"

/-! ## Emission of object-level terms -/

def mkFTy : FT → Expr
  | .e => mkConst ``FTy.e
  | .s => mkConst ``FTy.s
  | .arr a b => mkApp2 (mkConst ``FTy.arr) (mkFTy a) (mkFTy b)

def mkHTy : HT → Expr
  | .L t => mkApp (mkConst ``HTy.L) (mkFTy t)
  | .w => mkConst ``HTy.w
  | .o => mkConst ``HTy.o

def mkListE (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc)
    (mkApp (mkConst ``List.nil [Level.zero]) ty)

def mkCtx (ctx : List HT) : Expr := mkListE (mkConst ``HTy) (ctx.map mkHTy)
def mkLCtx (ctx : List FT) : Expr := mkListE (mkConst ``FTy) (ctx.map mkFTy)

def mkHVar : List HT → Nat → Except String Expr
  | a :: Γ, 0 => pure (mkApp2 (mkConst ``HVar.zero) (mkCtx Γ) (mkHTy a))
  | b :: Γ, n + 1 => do
      let some a := Γ[n]? | throw "mkHVar: out of range"
      pure (mkApp4 (mkConst ``HVar.succ) (mkCtx Γ) (mkHTy a) (mkHTy b) (← mkHVar Γ n))
  | [], _ => throw "mkHVar: empty context"

partial def mkHTerm (ctx : List HT) (x : DT) : Except String Expr := do
  let Γ := mkCtx ctx
  match x with
  | .var n =>
      let some a := ctx[n]? | throw s!"mkHTerm: unbound #{n}"
      pure (mkApp3 (mkConst ``HTerm.var) Γ (mkHTy a) (← mkHVar ctx n))
  | .appL f y =>
      match ← DT.ty ctx f with
      | .L (.arr a b) =>
          pure (mkApp5 (mkConst ``HTerm.appL) Γ (mkFTy a) (mkFTy b) (← mkHTerm ctx f) (← mkHTerm ctx y))
      | _ => throw "mkHTerm: appL"
  | .lamL a b =>
      match ← DT.ty (.L a :: ctx) b with
      | .L t => pure (mkApp4 (mkConst ``HTerm.lamL) Γ (mkFTy a) (mkFTy t) (← mkHTerm (.L a :: ctx) b))
      | _ => throw "mkHTerm: lamL"
  | .pos => pure (mkApp (mkConst ``HTerm.pos) Γ)
  | .wabs b => pure (mkApp2 (mkConst ``HTerm.wabs) Γ (← mkHTerm (.w :: ctx) b))
  | .holds p i => pure (mkApp3 (mkConst ``HTerm.holds) Γ (← mkHTerm ctx p) (← mkHTerm ctx i))
  | .rel i j => pure (mkApp3 (mkConst ``HTerm.rel) Γ (← mkHTerm ctx i) (← mkHTerm ctx j))
  | .act y i => pure (mkApp3 (mkConst ``HTerm.act) Γ (← mkHTerm ctx y) (← mkHTerm ctx i))
  | .bot => pure (mkApp (mkConst ``HTerm.bot) Γ)
  | .imp p q => pure (mkApp3 (mkConst ``HTerm.imp) Γ (← mkHTerm ctx p) (← mkHTerm ctx q))
  | .and p q => pure (mkApp3 (mkConst ``HTerm.and) Γ (← mkHTerm ctx p) (← mkHTerm ctx q))
  | .or p q => pure (mkApp3 (mkConst ``HTerm.or) Γ (← mkHTerm ctx p) (← mkHTerm ctx q))
  | .all a b => pure (mkApp3 (mkConst ``HTerm.all) Γ (mkHTy a) (← mkHTerm (a :: ctx) b))
  | .ex a b => pure (mkApp3 (mkConst ``HTerm.ex) Γ (mkHTy a) (← mkHTerm (a :: ctx) b))
  | .eq a s t => pure (mkApp4 (mkConst ``HTerm.eq) Γ (mkHTy a) (← mkHTerm ctx s) (← mkHTerm ctx t))

def mkLVar : List FT → Nat → Except String Expr
  | t :: Γ, 0 => pure (mkApp2 (mkConst ``Var.zero) (mkLCtx Γ) (mkFTy t))
  | u :: Γ, n + 1 => do
      let some t := Γ[n]? | throw "mkLVar: out of range"
      pure (mkApp4 (mkConst ``Var.succ) (mkLCtx Γ) (mkFTy t) (mkFTy u) (← mkLVar Γ n))
  | [], _ => throw "mkLVar: empty context"

partial def LT.ty (ctx : List FT) : LT → Except String FT
  | .var n => match ctx[n]? with | some t => pure t | none => throw "LT.ty: unbound"
  | .app f _ => do match ← LT.ty ctx f with | .arr _ b => pure b | _ => throw "LT.ty: app"
  | .lam a b => do pure (.arr a (← LT.ty (a :: ctx) b))
  | .pos => pure FT.th
  | _ => pure .s

partial def mkTm (ctx : List FT) (x : LT) : Except String Expr := do
  let Γ := mkLCtx ctx
  match x with
  | .var n =>
      let some t := ctx[n]? | throw "mkTm: unbound"
      pure (mkApp3 (mkConst ``Tm.var) Γ (mkFTy t) (← mkLVar ctx n))
  | .app f y =>
      match ← LT.ty ctx f with
      | .arr a b => pure (mkApp5 (mkConst ``Tm.app) Γ (mkFTy a) (mkFTy b) (← mkTm ctx f) (← mkTm ctx y))
      | _ => throw "mkTm: app"
  | .lam a b => do
      let t ← LT.ty (a :: ctx) b
      pure (mkApp4 (mkConst ``Tm.lam) Γ (mkFTy a) (mkFTy t) (← mkTm (a :: ctx) b))
  | .top => pure (mkApp (mkConst ``Tm.top) Γ)
  | .bot => pure (mkApp (mkConst ``Tm.bot) Γ)
  | .neg y => pure (mkApp2 (mkConst ``Tm.neg) Γ (← mkTm ctx y))
  | .and y z => pure (mkApp3 (mkConst ``Tm.and) Γ (← mkTm ctx y) (← mkTm ctx z))
  | .or y z => pure (mkApp3 (mkConst ``Tm.or) Γ (← mkTm ctx y) (← mkTm ctx z))
  | .imp y z => pure (mkApp3 (mkConst ``Tm.imp) Γ (← mkTm ctx y) (← mkTm ctx z))
  | .box y => pure (mkApp2 (mkConst ``Tm.box) Γ (← mkTm ctx y))
  | .all a b => pure (mkApp3 (mkConst ``Tm.all) Γ (mkFTy a) (← mkTm (a :: ctx) b))
  | .ex a b => pure (mkApp3 (mkConst ``Tm.ex) Γ (mkFTy a) (← mkTm (a :: ctx) b))
  | .allE b => pure (mkApp2 (mkConst ``Tm.allE) Γ (← mkTm (.e :: ctx) b))
  | .exE b => pure (mkApp2 (mkConst ``Tm.exE) Γ (← mkTm (.e :: ctx) b))
  | .eq a y z => pure (mkApp4 (mkConst ``Tm.eq) Γ (mkFTy a) (← mkTm ctx y) (← mkTm ctx z))
  | .pos => pure (mkApp (mkConst ``Tm.pos) Γ)

end Programme.H

namespace Programme.H
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
  Programme.«20261022-1724-ontological».ThWhole

/-- Weakening of the hypotheses of a `DG` derivation (as `Deriv.weaken`). -/
theorem DG.weakenH {T : Tm [] .s → Prop} {ok : ∀ {Γ : List HTy} (a : HTy), HTerm Γ a → Prop}
    {okL : ∀ {Γ : List HTy} (a : HTy), HTerm (a :: Γ) .o → HTerm Γ a → HTerm Γ a → Prop} :
    ∀ {Γ hs φ}, DG T ok okL Γ hs φ → ∀ {hs'}, (∀ h, h ∈ hs → h ∈ hs') → DG T ok okL Γ hs' φ := by
  intro Γ hs φ d
  induction d with
  | hyp m => exact fun hsub => .hyp (hsub _ m)
  | ax φ i h => exact fun _ => .ax φ i h
  | impI _ ih => exact fun hsub => .impI (ih (cons_sub hsub _))
  | impE _ _ ih1 ih2 => exact fun hsub => .impE (ih1 hsub) (ih2 hsub)
  | byContra _ ih => exact fun hsub => .byContra (ih (cons_sub hsub _))
  | andI _ _ ih1 ih2 => exact fun hsub => .andI (ih1 hsub) (ih2 hsub)
  | andL _ ih => exact fun hsub => .andL (ih hsub)
  | andR _ ih => exact fun hsub => .andR (ih hsub)
  | orL _ ih => exact fun hsub => .orL (ih hsub)
  | orR _ ih => exact fun hsub => .orR (ih hsub)
  | orE _ _ _ ih ih1 ih2 => exact fun hsub => .orE (ih hsub) (ih1 (cons_sub hsub _)) (ih2 (cons_sub hsub _))
  | allI a _ ih => exact fun hsub => .allI a (ih (map_sub hsub))
  | allE a t _ hok ih => exact fun hsub => .allE a t (ih hsub) hok
  | exI a t hok _ ih => exact fun hsub => .exI a t hok (ih hsub)
  | exE a _ _ ih1 ih2 => exact fun hsub => .exE a (ih1 hsub) (ih2 (cons_sub (map_sub hsub) _))
  | refl a t => exact fun _ => .refl a t
  | symm a _ ih => exact fun hsub => .symm a (ih hsub)
  | trans a _ _ ih1 ih2 => exact fun hsub => .trans a (ih1 hsub) (ih2 hsub)
  | leibG a φ hok _ _ ih1 ih2 => exact fun hsub => .leibG a φ hok (ih1 hsub) (ih2 hsub)
  | funExt _ ih => exact fun hsub => .funExt (ih hsub)
  | funApp _ ih => exact fun hsub => .funApp (ih hsub)
  | wExt _ ih => exact fun hsub => .wExt (ih hsub)
  | wApp _ ih => exact fun hsub => .wApp (ih hsub)
  | propExt _ _ ih1 ih2 => exact fun hsub => .propExt (ih1 (cons_sub hsub _)) (ih2 (cons_sub hsub _))
  | betaL body x => exact fun _ => .betaL body x
  | betaWI φ i _ ih => exact fun hsub => .betaWI φ i (ih hsub)
  | betaWE φ i _ ih => exact fun hsub => .betaWE φ i (ih hsub)

/-- A derivation from no hypotheses holds under any. -/
theorem DG.ofNil {T : Tm [] .s → Prop} {ok : ∀ {Γ : List HTy} (a : HTy), HTerm Γ a → Prop}
    {okL : ∀ {Γ : List HTy} (a : HTy), HTerm (a :: Γ) .o → HTerm Γ a → HTerm Γ a → Prop}
    {Γ : List HTy} (hs : List (HTerm Γ .o)) {φ : HTerm Γ .o} (d : DG T ok okL Γ [] φ) :
    DG T ok okL Γ hs φ :=
  Programme.H.DG.weakenH d fun _ m => absurd m (List.not_mem_nil)

/-! ## Lemmas: derivations that use earlier lemmas as sentences of the theory (a semantic cut) -/

/-- A list of sentences, newest first, each an axiom (`A`) or valid over the sentences before it. -/
inductive Good (A : Tm [] .s → Prop) : List (Tm [] .s) → Prop
  | nil : Good A []
  | axm {s : Tm [] .s} {L : List (Tm [] .s)} : A s → Good A L → Good A (s :: L)
  | lem {s : Tm [] .s} {L : List (Tm [] .s)} : ValidV4 (fun φ => φ ∈ L) s → Good A L →
      Good A (s :: L)

/-- Cut: what is valid over a good list of lemmas is valid over the axioms alone. -/
theorem Good.valid {A : Tm [] .s → Prop} {L : List (Tm [] .s)} {χ : Tm [] .s} (g : Good A L)
    (h : ValidV4 (fun φ => φ ∈ L) χ) : ValidV4 A χ := by
  intro W M Lg hne hA
  apply h W M Lg hne
  clear h
  induction g with
  | nil => intro ψ hψ; cases hψ
  | axm hs _ ih =>
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hA _ hs
      · exact ih ψ hψ
  | lem hv _ ih =>
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hv W M Lg hne ih
      · exact ih ψ hψ

end Programme.H

end


/-! ## Tool part `Emit` -/
section

/-! # Thread H: meta derivations (`Der`) and their emission as `DW` proof terms

`Der` mirrors the rules of run 4's `DG` with every formula the rule needs recorded explicitly;
`emit` turns a `Der` into a term of type `DG T ok okL Γ hs φ` (with `ok`, `okL` the whole-term side
conditions of `DW`), recomputing each conclusion on the meta level and checking it against the
premises.  Side conditions are discharged by `cert_L`/`cert_w`/`cert_o` and `leibOK_plain`/
`leibOK_wt`; a failing side condition is an error naming the rule. -/

open Lean Meta
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
  Programme.«20261022-1724-ontological».ThWhole

namespace Programme.H

inductive Der where
  | hyp (k : Nat)
  | ax (idx : Nat) (i : DT)
  | impI (A : DT) (d : Der)
  | impE (d1 d2 : Der)
  | byContra (A : DT) (d : Der)
  | andI (d1 d2 : Der)
  | andL (d : Der)
  | andR (d : Der)
  | orL (B : DT) (d : Der)
  | orR (A : DT) (d : Der)
  | orE (d d1 d2 : Der)
  | allI (a : HT) (d : Der)
  | allE (t : DT) (d : Der)
  | exI (a : HT) (φ t : DT) (d : Der)
  | exE (d d2 : Der) (χ : DT)
  | refl (a : HT) (t : DT)
  | symm (d : Der)
  | trans (d1 d2 : Der)
  | leib (a : HT) (φ s t : DT) (deq d : Der)
  | funExt (d : Der)
  | funApp (d : Der)
  | wExt (d : Der)
  | wApp (d : Der)
  | propExt (φ ψ : DT) (d1 d2 : Der)
  | betaL (body x : DT)
  | betaWI (φ i : DT) (d : Der)
  | betaWE (d : Der)
  deriving Inhabited

/-- What the emitter needs: the theory (as an expression and as a list of sentences), `ok`, `okL`. -/
structure EmitEnv where
  T : Expr
  sentences : Array LT
  sentenceExprs : Array Expr
  ok : Expr
  okL : Expr

structure EmitCache where
  ctxs : Std.HashMap (List HT) Expr := {}
  terms : Std.HashMap (List HT × DT) Expr := {}
  lists : Std.HashMap (List HT × List DT) Expr := {}

abbrev EmitM := ReaderT EmitEnv (StateRefT EmitCache MetaM)

def ctxC (ctx : List HT) : EmitM Expr := do
  if let some e := (← get).ctxs[ctx]? then return e
  let e ← match ctx with
    | [] => pure (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``HTy))
    | a :: rest => do pure (mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``HTy) (mkHTy a) (← ctxC rest))
  modify fun c => { c with ctxs := c.ctxs.insert ctx e }
  pure e

def hvarC : List HT → Nat → EmitM Expr
  | a :: Γ, 0 => do pure (mkApp2 (mkConst ``HVar.zero) (← ctxC Γ) (mkHTy a))
  | b :: Γ, n + 1 => do
      let some a := Γ[n]? | throwError "hvarC: out of range"
      pure (mkApp4 (mkConst ``HVar.succ) (← ctxC Γ) (mkHTy a) (mkHTy b) (← hvarC Γ n))
  | [], _ => throwError "hvarC: empty context"

partial def tmC (ctx : List HT) (x : DT) : EmitM Expr := do
  if let some e := (← get).terms[(ctx, x)]? then return e
  let Γ ← ctxC ctx
  let ty (y : DT) (c : List HT) : EmitM HT := match DT.ty c y with
    | .ok t => pure t
    | .error m => throwError m
  let e ← match x with
    | .var n =>
        let some a := ctx[n]? | throwError s!"tmC: unbound #{n}"
        pure (mkApp3 (mkConst ``HTerm.var) Γ (mkHTy a) (← hvarC ctx n))
    | .appL f y =>
        match ← ty f ctx with
        | .L (.arr a b) => pure (mkApp5 (mkConst ``HTerm.appL) Γ (mkFTy a) (mkFTy b) (← tmC ctx f) (← tmC ctx y))
        | _ => throwError "tmC: appL"
    | .lamL a b =>
        match ← ty b (.L a :: ctx) with
        | .L t => pure (mkApp4 (mkConst ``HTerm.lamL) Γ (mkFTy a) (mkFTy t) (← tmC (.L a :: ctx) b))
        | _ => throwError "tmC: lamL"
    | .pos => pure (mkApp (mkConst ``HTerm.pos) Γ)
    | .wabs b => do pure (mkApp2 (mkConst ``HTerm.wabs) Γ (← tmC (.w :: ctx) b))
    | .holds p i => do pure (mkApp3 (mkConst ``HTerm.holds) Γ (← tmC ctx p) (← tmC ctx i))
    | .rel i j => do pure (mkApp3 (mkConst ``HTerm.rel) Γ (← tmC ctx i) (← tmC ctx j))
    | .act y i => do pure (mkApp3 (mkConst ``HTerm.act) Γ (← tmC ctx y) (← tmC ctx i))
    | .bot => pure (mkApp (mkConst ``HTerm.bot) Γ)
    | .imp p q => do pure (mkApp3 (mkConst ``HTerm.imp) Γ (← tmC ctx p) (← tmC ctx q))
    | .and p q => do pure (mkApp3 (mkConst ``HTerm.and) Γ (← tmC ctx p) (← tmC ctx q))
    | .or p q => do pure (mkApp3 (mkConst ``HTerm.or) Γ (← tmC ctx p) (← tmC ctx q))
    | .all a b => do pure (mkApp3 (mkConst ``HTerm.all) Γ (mkHTy a) (← tmC (a :: ctx) b))
    | .ex a b => do pure (mkApp3 (mkConst ``HTerm.ex) Γ (mkHTy a) (← tmC (a :: ctx) b))
    | .eq a s t => do pure (mkApp4 (mkConst ``HTerm.eq) Γ (mkHTy a) (← tmC ctx s) (← tmC ctx t))
  modify fun c => { c with terms := c.terms.insert (ctx, x) e }
  pure e

/-- The hypothesis list as an expression (shared tails). -/
partial def listC (ctx : List HT) (hs : List DT) : EmitM Expr := do
  if let some e := (← get).lists[(ctx, hs)]? then return e
  let Γ ← ctxC ctx
  let ety := mkApp2 (mkConst ``HTerm) Γ (mkHTy .o)
  let e ← match hs with
    | [] => pure (mkApp (mkConst ``List.nil [Level.zero]) ety)
    | h :: rest => do pure (mkApp3 (mkConst ``List.cons [Level.zero]) ety (← tmC ctx h) (← listC ctx rest))
  modify fun c => { c with lists := c.lists.insert (ctx, hs) e }
  pure e

/-- Proof of `hs[k] ∈ hs` (shared). -/
def memC (ctx : List HT) (hs : List DT) (k : Nat) : EmitM Expr := do
  let Γ ← ctxC ctx
  let ety := mkApp2 (mkConst ``HTerm) Γ (mkHTy .o)
  match hs, k with
  | x :: rest, 0 => pure (mkApp3 (mkConst ``List.Mem.head [Level.zero]) ety (← tmC ctx x) (← listC ctx rest))
  | y :: rest, n + 1 => do
      let some a := rest[n]? | throwError "memC: out of range"
      let h ← memC ctx rest n
      pure (mkApp5 (mkConst ``List.Mem.tail [Level.zero]) ety (← tmC ctx a) (← tmC ctx y) (← listC ctx rest) h)
  | [], _ => throwError "memC: empty"

def liftE {α} (x : Except String α) : EmitM α := do
  match x with
  | .ok a => pure a
  | .error e => throwError e

def hTermTy (Γ : Expr) : Expr := mkApp2 (mkConst ``HTerm) Γ (mkHTy .o)

/-- Proof of `hs[k] ∈ hs`. -/
def memProof (elemTy : Expr) (xs : List Expr) (k : Nat) : Except String Expr := do
  match xs, k with
  | x :: rest, 0 => pure (mkApp3 (mkConst ``List.Mem.head [Level.zero]) elemTy x (mkListE elemTy rest))
  | y :: rest, n + 1 => do
      let some a := rest[n]? | throw "memProof: out of range"
      let h ← memProof elemTy rest n
      pure (mkApp5 (mkConst ``List.Mem.tail [Level.zero]) elemTy a y (mkListE elemTy rest) h)
  | [], _ => throw "memProof: empty"

/-- Proof of `Cert a x`. -/
def certProof (ctx : List HT) (a : HT) (x : DT) : Except String Expr := do
  let Γ := mkCtx ctx
  match a with
  | .w => pure (mkApp2 (mkConst ``cert_w) Γ (← mkHTerm ctx x))
  | .o => pure (mkApp2 (mkConst ``cert_o) Γ (← mkHTerm ctx x))
  | .L t =>
      match rbE ctx x with
      | some tm =>
          if embD (lprojL ctx) tm == x then
            pure (mkApp3 (mkConst ``cert_L) Γ (mkFTy t) (← mkTm (lctxL ctx) tm))
          else throw s!"not a term of 𝓛 (whole-term condition): {x}"
      | none => throw s!"not a term of 𝓛 (whole-term condition): {x}"

/-- Proof of `WT x`. -/
partial def wtProof (ctx : List HT) (x : DT) : Except String Expr := do
  let Γ := mkCtx ctx
  match x with
  | .var n =>
      let some a := ctx[n]? | throw "wtProof: unbound"
      pure (mkApp3 (mkConst ``wt_var) Γ (mkHTy a) (← mkHVar ctx n))
  | .appL f y =>
      match ← DT.ty ctx f with
      | .L (.arr a b) =>
          pure (mkAppN (mkConst ``wt_appL) #[Γ, mkFTy a, mkFTy b, ← mkHTerm ctx f, ← mkHTerm ctx y,
            ← wtProof ctx f, ← certProof ctx (.L a) y])
      | _ => throw "wtProof: appL"
  | .lamL a b =>
      match ← DT.ty (.L a :: ctx) b with
      | .L t => pure (mkAppN (mkConst ``wt_lamL) #[Γ, mkFTy a, mkFTy t, ← mkHTerm (.L a :: ctx) b,
          ← wtProof (.L a :: ctx) b])
      | _ => throw "wtProof: lamL"
  | .pos => pure (mkApp (mkConst ``wt_pos) Γ)
  | .wabs b => pure (mkApp3 (mkConst ``wt_wabs) Γ (← mkHTerm (.w :: ctx) b) (← wtProof (.w :: ctx) b))
  | .holds p i => pure (mkAppN (mkConst ``wt_holds) #[Γ, ← mkHTerm ctx p, ← mkHTerm ctx i,
      ← wtProof ctx p, ← wtProof ctx i])
  | .rel i j => pure (mkAppN (mkConst ``wt_rel) #[Γ, ← mkHTerm ctx i, ← mkHTerm ctx j,
      ← wtProof ctx i, ← wtProof ctx j])
  | .act y i => pure (mkAppN (mkConst ``wt_act) #[Γ, ← mkHTerm ctx y, ← mkHTerm ctx i,
      ← wtProof ctx y, ← wtProof ctx i])
  | .bot => pure (mkApp (mkConst ``wt_bot) Γ)
  | .imp p q => pure (mkAppN (mkConst ``wt_imp) #[Γ, ← mkHTerm ctx p, ← mkHTerm ctx q,
      ← wtProof ctx p, ← wtProof ctx q])
  | .and p q => pure (mkAppN (mkConst ``wt_and) #[Γ, ← mkHTerm ctx p, ← mkHTerm ctx q,
      ← wtProof ctx p, ← wtProof ctx q])
  | .or p q => pure (mkAppN (mkConst ``wt_or) #[Γ, ← mkHTerm ctx p, ← mkHTerm ctx q,
      ← wtProof ctx p, ← wtProof ctx q])
  | .all a b => pure (mkAppN (mkConst ``wt_all) #[Γ, mkHTy a, ← mkHTerm (a :: ctx) b,
      ← wtProof (a :: ctx) b])
  | .ex a b => pure (mkAppN (mkConst ``wt_ex) #[Γ, mkHTy a, ← mkHTerm (a :: ctx) b,
      ← wtProof (a :: ctx) b])
  | .eq a s t => pure (mkAppN (mkConst ``wt_eq) #[Γ, mkHTy a, ← mkHTerm ctx s, ← mkHTerm ctx t,
      ← wtProof ctx s, ← wtProof ctx t])

/-- Proof of `LeibOK a φ s t`. -/
def leibOKProof (ctx : List HT) (a : HT) (φ s t : DT) : Except String Expr := do
  let Γ := mkCtx ctx
  if a.plain then
    pure (mkAppN (mkConst ``leibOK_plain) #[Γ, mkHTy a, mkApp2 (mkConst ``Eq.refl [Level.one])
      (mkConst ``Bool) (mkConst ``Bool.true), ← mkHTerm (a :: ctx) φ, ← mkHTerm ctx s, ← mkHTerm ctx t])
  else
    let wt ← match wtProof (a :: ctx) φ with
      | .ok p => pure p
      | .error e => throw s!"Leibniz at {a}: motive not whole-term ({e}); motive {φ}"
    pure (mkAppN (mkConst ``leibOK_wt) #[Γ, mkHTy a, ← mkHTerm (a :: ctx) φ, ← mkHTerm ctx s,
      ← mkHTerm ctx t, wt, ← certProof ctx a s, ← certProof ctx a t])

def chkEq (what : String) (x y : DT) : EmitM Unit :=
  unless x == y do throwError s!"emit ({what}): expected {y}, got {x}"

/-- Emit a derivation in context `ctx` under hypotheses `hs`; returns the proof and its conclusion. -/
partial def emit (ctx : List HT) (hs : List DT) (d : Der) : EmitM (Expr × DT) := do
  let env ← read
  let Γ ← ctxC ctx
  let HS ← listC ctx hs
  let pre (c : Name) : Expr := mkAppN (mkConst c) #[env.T, env.ok, env.okL, Γ, HS]
  let tm (x : DT) : EmitM Expr := tmC ctx x
  match d with
  | .hyp k =>
      let some φ := hs[k]? | throwError s!"emit: hyp {k} out of range"
      let mp ← memC ctx hs k
      pure (mkAppN (pre ``DG.hyp) #[← tm φ, mp], φ)
  | .ax idx i =>
      let some s := env.sentences[idx]? | throwError "emit: axiom index"
      let some sE := env.sentenceExprs[idx]? | throwError "emit: axiom index"
      let sentTy := mkApp2 (mkConst ``Tm) (mkLCtx []) (mkFTy .s)
      -- the theory lists its sentences newest first
      let mp ← liftE (memProof sentTy env.sentenceExprs.toList.reverse (env.sentenceExprs.size - 1 - idx))
      pure (mkAppN (pre ``DG.ax) #[sE, ← tm i, mp], .holds (embD [] s) i)
  | .impI A d =>
      let (D, B) ← emit ctx (A :: hs) d
      pure (mkAppN (pre ``DG.impI) #[← tm A, ← tm B, D], .imp A B)
  | .impE d1 d2 =>
      let (D1, X) ← emit ctx hs d1
      let .imp A B := X | throwError s!"emit impE: not an implication: {X}"
      let (D2, A') ← emit ctx hs d2
      chkEq "impE" A' A
      pure (mkAppN (pre ``DG.impE) #[← tm A, ← tm B, D1, D2], B)
  | .byContra A d =>
      let (D, X) ← emit ctx (.imp A .bot :: hs) d
      chkEq "byContra" X .bot
      pure (mkAppN (pre ``DG.byContra) #[← tm A, D], A)
  | .andI d1 d2 =>
      let (D1, A) ← emit ctx hs d1
      let (D2, B) ← emit ctx hs d2
      pure (mkAppN (pre ``DG.andI) #[← tm A, ← tm B, D1, D2], .and A B)
  | .andL d =>
      let (D, X) ← emit ctx hs d
      let .and A B := X | throwError s!"emit andL: {X}"
      pure (mkAppN (pre ``DG.andL) #[← tm A, ← tm B, D], A)
  | .andR d =>
      let (D, X) ← emit ctx hs d
      let .and A B := X | throwError s!"emit andR: {X}"
      pure (mkAppN (pre ``DG.andR) #[← tm A, ← tm B, D], B)
  | .orL B d =>
      let (D, A) ← emit ctx hs d
      pure (mkAppN (pre ``DG.orL) #[← tm A, ← tm B, D], .or A B)
  | .orR A d =>
      let (D, B) ← emit ctx hs d
      pure (mkAppN (pre ``DG.orR) #[← tm A, ← tm B, D], .or A B)
  | .orE d d1 d2 =>
      let (D, X) ← emit ctx hs d
      let .or A B := X | throwError s!"emit orE: {X}"
      let (D1, C) ← emit ctx (A :: hs) d1
      let (D2, C') ← emit ctx (B :: hs) d2
      chkEq "orE" C' C
      pure (mkAppN (pre ``DG.orE) #[← tm A, ← tm B, ← tm C, D, D1, D2], C)
  | .allI a d =>
      let (D, B) ← emit (a :: ctx) (hs.map (·.shift 1)) d
      pure (mkAppN (pre ``DG.allI) #[mkHTy a, ← tmC (a :: ctx) B, D], .all a B)
  | .allE t d =>
      let (D, X) ← emit ctx hs d
      let .all a B := X | throwError s!"emit allE: {X}"
      let okP ← match a with
        | .w => pure (mkApp2 (mkConst ``cert_w) Γ (← tm t))
        | .o => pure (mkApp2 (mkConst ``cert_o) Γ (← tm t))
        | _ => match certProof ctx a t with
          | .ok p => pure p
          | .error e => throwError s!"∀E instance at {a}: {e}"
      pure (mkAppN (pre ``DG.allE) #[mkHTy a, ← tmC (a :: ctx) B, ← tm t, D, okP],
        B.inst t)
  | .exI a φ t d =>
      let (D, X) ← emit ctx hs d
      chkEq "exI" X (φ.inst t)
      let okP ← match certProof ctx a t with
        | .ok p => pure p
        | .error e => throwError s!"∃I witness at {a}: {e}"
      pure (mkAppN (pre ``DG.exI) #[mkHTy a, ← tmC (a :: ctx) φ, ← tm t, okP, D],
        .ex a φ)
  | .exE d d2 χ =>
      let (D, X) ← emit ctx hs d
      let .ex a φ := X | throwError s!"emit exE: {X}"
      let (D2, Y) ← emit (a :: ctx) (φ :: hs.map (·.shift 1)) d2
      chkEq "exE" Y (χ.shift 1)
      pure (mkAppN (pre ``DG.exE) #[mkHTy a, ← tmC (a :: ctx) φ, ← tm χ, D, D2], χ)
  | .refl a t => pure (mkAppN (pre ``DG.refl) #[mkHTy a, ← tm t], .eq a t t)
  | .symm d =>
      let (D, X) ← emit ctx hs d
      let .eq a s t := X | throwError s!"emit symm: {X}"
      pure (mkAppN (pre ``DG.symm) #[mkHTy a, ← tm s, ← tm t, D], .eq a t s)
  | .trans d1 d2 =>
      let (D1, X) ← emit ctx hs d1
      let .eq a s t := X | throwError s!"emit trans: {X}"
      let (D2, Y) ← emit ctx hs d2
      let .eq a' t' u := Y | throwError s!"emit trans: {Y}"
      unless a == a' do throwError "emit trans: types differ"
      chkEq "trans middle" t' t
      pure (mkAppN (pre ``DG.trans) #[mkHTy a, ← tm s, ← tm t, ← tm u, D1, D2], .eq a s u)
  | .leib a φ s t deq d =>
      let (Deq, X) ← emit ctx hs deq
      chkEq "leib equation" X (.eq a s t)
      let (Dd, Y) ← emit ctx hs d
      chkEq "leib premise" Y (φ.inst s)
      let okP ← if a.plain then
          pure (mkAppN (mkConst ``leibOK_plain) #[Γ, mkHTy a, mkApp2 (mkConst ``Eq.refl [Level.one])
            (mkConst ``Bool) (mkConst ``Bool.true), ← tmC (a :: ctx) φ, ← tm s, ← tm t])
        else liftE (leibOKProof ctx a φ s t)
      pure (mkAppN (pre ``DG.leibG) #[mkHTy a, ← tm s, ← tm t, ← tmC (a :: ctx) φ, okP,
        Deq, Dd], φ.inst t)
  | .funExt d =>
      let (D, X) ← emit ctx hs d
      let .all (.L a) (.eq (.L b) (.appL f' (.var 0)) (.appL g' (.var 0))) := X
        | throwError s!"emit funExt: {X}"
      let f := f'.down
      let g := g'.down
      chkEq "funExt f" (f.shift 1) f'
      chkEq "funExt g" (g.shift 1) g'
      pure (mkAppN (pre ``DG.funExt) #[mkFTy a, mkFTy b, ← tm f, ← tm g, D], .eq (.L (.arr a b)) f g)
  | .funApp d =>
      let (D, X) ← emit ctx hs d
      let .eq (.L (.arr a b)) f g := X | throwError s!"emit funApp: {X}"
      pure (mkAppN (pre ``DG.funApp) #[mkFTy a, mkFTy b, ← tm f, ← tm g, D],
        .all (.L a) (.eq (.L b) (.appL (f.shift 1) (.var 0)) (.appL (g.shift 1) (.var 0))))
  | .wExt d =>
      let (D, X) ← emit ctx hs d
      let .all .w (.eq .o (.holds p' (.var 0)) (.holds q' (.var 0))) := X | throwError s!"emit wExt: {X}"
      let p := p'.down
      let q := q'.down
      chkEq "wExt p" (p.shift 1) p'
      chkEq "wExt q" (q.shift 1) q'
      pure (mkAppN (pre ``DG.wExt) #[← tm p, ← tm q, D], .eq (.L .s) p q)
  | .wApp d =>
      let (D, X) ← emit ctx hs d
      let .eq (.L .s) p q := X | throwError s!"emit wApp: {X}"
      pure (mkAppN (pre ``DG.wApp) #[← tm p, ← tm q, D],
        .all .w (.eq .o (.holds (p.shift 1) (.var 0)) (.holds (q.shift 1) (.var 0))))
  | .propExt φ ψ d1 d2 =>
      let (D1, X) ← emit ctx (φ :: hs) d1
      chkEq "propExt 1" X ψ
      let (D2, Y) ← emit ctx (ψ :: hs) d2
      chkEq "propExt 2" Y φ
      pure (mkAppN (pre ``DG.propExt) #[← tm φ, ← tm ψ, D1, D2], .eq .o φ ψ)
  | .betaL body x =>
      let .L a ← liftE (DT.ty ctx x) | throwError "emit betaL: argument type"
      let .L b ← liftE (DT.ty (.L a :: ctx) body) | throwError "emit betaL: body type"
      pure (mkAppN (pre ``DG.betaL) #[mkFTy a, mkFTy b, ← tmC (.L a :: ctx) body, ← tm x],
        .eq (.L b) (.appL (.lamL a body) x) (body.inst x))
  | .betaWI φ i d =>
      let (D, X) ← emit ctx hs d
      chkEq "betaWI" X (φ.inst i)
      pure (mkAppN (pre ``DG.betaWI) #[← tmC (.w :: ctx) φ, ← tm i, D], .holds (.wabs φ) i)
  | .betaWE d =>
      let (D, X) ← emit ctx hs d
      let .holds (.wabs φ) i := X | throwError s!"emit betaWE: {X}"
      pure (mkAppN (pre ``DG.betaWE) #[← tmC (.w :: ctx) φ, ← tm i, D], φ.inst i)

end Programme.H

end


/-! ## Tool part `Translate` -/
section

/-! # Thread H: from shallow Lean proofs to run 4's deep derivations

`#deep_translate thm as Name` reads the statement and the proof term of `thm` (a theorem of a
shallow `OpenQuestions` module, or a proof of one of its statements), and

* computes the deep image: an `𝓛`-sentence `φ` (read back from the statement), and a theory `T`
  (the module's axioms the proof uses, the statement's hypotheses, and instances of hypothesis
  schemas, each read back as an `𝓛`-sentence);
* translates the proof term, step by step, into a derivation of run 4's calculus `DG` with the
  whole-term side conditions of `DW`;
* adds `Name.T`, `Name.φ`, `Name.deep : DW Name.T [.w] [] (.holds (emb nilR Name.φ) var0)` and
  `Name.valid : ValidV4 Name.T Name.φ` (by `sound_v4_wt`), all kernel-checked.

A step outside the fragment, or an `∀E`/`∃I` instance or a Leibniz step that violates the
whole-term condition, stops the translation with an error naming it.  The fragment:
`fun`/application (→I/→E, ∀I/∀E at the types of `𝓛`, worlds and `Prop`), `And`/`Or`/`Iff`/
`Exists`/`True`/`False`/`Not`/`Ne` introduction and elimination (including `casesOn`/`rec` and the
matchers built from them), `Classical.byContradiction`/`byCases`/`em`, `dite`/`Decidable.byCases`
on `Classical.propDecidable`, `Eq.refl`/`symm`/`trans`/`mp`/`mpr`/`ndrec`/`rec`/`subst`, `congrArg`,
`congrFun`, `funext`, `propext`, `of_eq_true`/`eq_true`/`eq_self`, `β`/`η` (as derivations), and
unfolding of definitions and of the proofs of theorems (the module's and Lean's own), which are then
translated in turn. -/

open Lean Meta Elab Command Term
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
  Programme.«20261022-1724-ontological».ThWhole

namespace Programme.H

/-! ## Translation state -/

/-- A hypothesis of the statement that is read as a sentence (or a schema of sentences) of `T`. -/
structure FactVar where
  fvar : FVarId
  name : String

structure TState where
  sentences : Array LT := #[]
  sentenceNames : Array String := #[]
  /-- Which constant/hypothesis each sentence comes from (for reporting). -/
  usedConsts : Array Name := #[]
  depth : Nat := 0
  steps : Nat := 0
  /-- The deep variable standing for `Classical.ofNonempty : e`, if enabled. -/
  nonemptyVar : Option FVarId := none
  nonemptyUsed : Bool := false
  /-- The statement's world variable: `Classical.ofNonempty : i` stands for it (r1/th rule 3). -/
  worldVar : Option FVarId := none
  /-- Whether the last statement translated by `goalCore` had no world binder (read at a fresh world). -/
  lastWorldFree : Bool := false
  /-- Module frame axioms (e.g. `Rrefl`): name, the local hypothesis standing for it, its closed
  frame-formula image.  Every derivation (lemmas included) has them as hypotheses. -/
  modFrames : Array (Name × FVarId × DT) := #[]
  /-- The proof term being translated (for error messages). -/
  current : Expr := .bvar 0
  /-- The theorems whose proofs are being unfolded, innermost first. -/
  stack : List Name := []
  /-- Replacement proofs: constant ↦ theorem with the identical statement. -/
  replace : List (Name × Name) := []
  /-- Memo for the conversion engine (derivations there use no outer hypotheses). -/
  eqCache : Std.HashMap (List HT × HT × DT) (DT × Der) := {}
  /-- Theorems translated once and used as lemmas: name ↦ index of their sentence. -/
  lemmaIdx : Std.HashMap Name Nat := {}
  /-- Theorems whose statement is not a validity of an `𝓛`-sentence (unfolded at each use). -/
  noLemma : Std.HashSet Name := {}
  /-- The lemma derivations: sentence index, theorem, derivation (in `[.w]`), its target. -/
  lemmas : Array (Nat × Name × Der × DT) := #[]
  /-- Translate theorems as lemmas (otherwise unfold their proofs at each use). -/
  useLemmas : Bool := true
  /-- For sentences read off an instance of a statement hypothesis: the instance's Lean type and
  `fun h => h args` (closed), for the structural check. -/
  factTys : Std.HashMap Nat (Expr × Expr) := {}
  /-- Statement hypotheses read as closed frame formulas (C7): fact index and image, in the order
  of the derivation's hypothesis list (newest first). -/
  frames : List (Nat × DT) := []

/-- The translation context: deep variables (outermost first), hypotheses (most recent first). -/
structure TCtx where
  vars : Array (FVarId × HT) := #[]
  hyps : List (Option FVarId × DT) := []
  facts : Array FactVar := #[]

abbrev TM := StateRefT TState MetaM

def TCtx.deep (c : TCtx) : List HT := c.vars.toList.reverse.map (·.2)

def TCtx.idx? (c : TCtx) (id : FVarId) : Option Nat := do
  let pos ← c.vars.findIdx? (·.1 == id)
  pure (c.vars.size - 1 - pos)

def TCtx.pushVar (c : TCtx) (id : FVarId) (a : HT) : TCtx :=
  { c with vars := c.vars.push (id, a), hyps := c.hyps.map fun (h, A) => (h, A.shift 1) }

def TCtx.pushHyp (c : TCtx) (h : Option FVarId) (A : DT) : TCtx :=
  { c with hyps := (h, A) :: c.hyps }

def TCtx.hypIdx? (c : TCtx) (id : FVarId) : Option (Nat × DT) := Id.run do
  let mut k := 0
  for (h, A) in c.hyps do
    if h == some id then return some (k, A)
    k := k + 1
  return none

def TCtx.isFact (c : TCtx) (id : FVarId) : Bool := c.facts.any (·.fvar == id)

/-- Progress log, only if the environment variable `DEEP_LOG` names a file. -/
def dbg (s : String) : TM Unit := do
  if let some f ← IO.getEnv "DEEP_LOG" then
    let h ← IO.FS.Handle.mk f .append
    h.putStrLn s
    h.flush

def outside {α} (what : MessageData) : TM α := do
  let cur := (← get).current
  let stk := (← get).stack
  throwError m!"[deep_translate] outside the fragment: {what}\n  in the step: {cur}\n  inside the proof of: {stk}"

def wtFail {α} (what : MessageData) : TM α := do
  let cur := (← get).current
  let stk := (← get).stack
  throwError m!"[deep_translate] whole-term condition violated: {what}\n  in the step: {cur}\n  inside the proof of: {stk}"

/-! ## Types -/

/-- Module names of the shallow embedding (all modules share them). -/
def isWorldTy (e : Expr) : Bool := e.isConstOf `i
def isEntTy (e : Expr) : Bool := e.isConstOf `e

partial def ftOf (ty : Expr) : MetaM (Option FT) := do
  let ty ← whnfR ty
  if isEntTy ty then return some .e
  match ty with
  | .forallE _ dom cod _ =>
      if cod.hasLooseBVars then return none
      let dom' ← whnfR dom
      if isWorldTy dom' then
        let cod' ← whnfR cod
        if cod'.isProp then return some .s else return none
      let some a ← ftOf dom | return none
      let some b ← ftOf cod | return none
      return some (.arr a b)
  | _ => return none

def htOf? (ty : Expr) : MetaM (Option HT) := do
  let ty' ← whnfR ty
  if isWorldTy ty' then return some .w
  if ty'.isProp then return some .o
  return (← ftOf ty).map HT.L

def htOf (ty : Expr) : TM HT := do
  match ← htOf? ty with
  | some a => pure a
  | none => outside m!"type {← ppExpr ty} is not a type of 𝓛, the world type or Prop"

/-! ## Unfolding -/

/-- Constants never unfolded: the signature of the embedding and the logical constants. -/
def primitiveConsts : List Name :=
  [`i, `e, `R, `existsAt, `P, ``True, ``False, ``Not, ``And, ``Or, ``Iff, ``Exists, ``Eq, ``Ne,
   ``Classical.ofNonempty, ``Classical.choice]

/-- Unfold a constant application `c args` (definition or theorem value), `β`-reducing. -/
def unfoldApp? (e : Expr) : MetaM (Option Expr) := do
  let .const c lvls := e.getAppFn | return none
  if primitiveConsts.contains c then return none
  let info ← getConstInfo c
  let v ← match info with
    | .defnInfo d => pure d.value
    | .thmInfo t => pure t.value
    | _ => return none
  if info.levelParams.length != lvls.length then return none
  let v := v.instantiateLevelParams info.levelParams lvls
  return some (v.beta e.getAppArgs)

/-! ## Terms and formulas: the image `img` -/

mutual
/-- Image of a Lean term (of a type of `𝓛`, the world type or `Prop`) in the current context;
definitions unfolded, `β`-reduced, `η`-reduced. -/
partial def img (c : TCtx) (e : Expr) : TM DT := do
  let x ← img0 c e
  pure x.nf

partial def img0 (c : TCtx) (e : Expr) : TM DT := do
  match e with
  | .mdata _ b => img0 c b
  | .letE _ _ v b _ => img0 c (b.instantiate1 v)
  | .fvar id =>
      match c.idx? id with
      | some k => pure (.var k)
      | none =>
          if (← get).nonemptyVar == some id then
            match c.idx? id with
            | some k => pure (.var k)
            | none => outside "nonempty witness out of scope"
          else outside s!"free variable {(← id.getDecl).userName} is not a deep variable"
  | .lam n ty b bi =>
      let some a ← htOf? ty | outside s!"λ over a type outside 𝓛: {← ppExpr ty}"
      if (← htOf? (← inferType e)).isNone then
        outside m!"the term {← ppExpr e} has type {← ppExpr (← inferType e)}, not a type of 𝓛 or the world type"
      withLocalDecl n bi ty fun x => do
        let c' := c.pushVar x.fvarId! a
        let body ← img0 c' (b.instantiate1 x)
        match a with
        | .L t => pure (.lamL t body)
        | .w => pure (.wabs body)
        | .o => outside "λ over Prop"
  | .forallE n ty b bi =>
      if (← isProp ty) && !b.hasLooseBVars then
        pure (.imp (← img0 c ty) (← img0 c b))
      else if (← isProp ty) then
        -- a motive applied to the proof: β-reduce, then it must not depend on it
        withLocalDecl n bi ty fun h => do
          let body ← Core.betaReduce (b.instantiate1 h)
          if body.containsFVar h.fvarId! then outside m!"dependent implication {← ppExpr e}"
          pure (.imp (← img0 c ty) (← img0 c body))
      else
        let some a ← htOf? ty | outside s!"∀ over a type outside 𝓛: {← ppExpr ty}"
        withLocalDecl n bi ty fun x => do
          pure (.all a (← img0 (c.pushVar x.fvarId! a) (b.instantiate1 x)))
  | .app .. | .const .. => imgApp c e
  | .proj .. => outside s!"projection in a term: {← ppExpr e}"
  | _ => outside s!"term {← ppExpr e}"

partial def imgApp (c : TCtx) (e : Expr) : TM DT := do
  let f := e.getAppFn
  let args := e.getAppArgs
  if f.isLambda then return ← img0 c e.headBeta
  if let .mdata _ f' := f then return ← img0 c (mkAppN f' args)
  if let .letE _ _ v b _ := f then return ← img0 c (mkAppN (b.instantiate1 v) args)
  if let .const n _ := f then
    let arity : Option Nat := match n with
      | ``Not => some 1 | ``And => some 2 | ``Or => some 2 | ``Iff => some 2 | ``Exists => some 2
      | ``Eq => some 3 | ``Ne => some 3 | `R => some 2 | `existsAt => some 2 | _ => none
    if let some k := arity then
      if args.size < k then
        -- an under-applied connective (e.g. the nominal `Eq w`): η-expand first
        return ← img0 c (← etaExpand e)
  match f with
  | .const n _ =>
      match n, args.size with
      | ``False, 0 => pure .bot
      | ``True, 0 => pure (.imp .bot .bot)
      | ``Not, 1 => pure (.imp (← img0 c args[0]!) .bot)
      | ``And, 2 => pure (.and (← img0 c args[0]!) (← img0 c args[1]!))
      | ``Or, 2 => pure (.or (← img0 c args[0]!) (← img0 c args[1]!))
      | ``Iff, 2 =>
          let a ← img0 c args[0]!
          let b ← img0 c args[1]!
          pure (.and (.imp a b) (.imp b a))
      | ``Exists, 2 =>
          let some a ← htOf? args[0]! | outside s!"∃ over {← ppExpr args[0]!}"
          let p := args[1]!
          withLocalDecl `x .default args[0]! fun x => do
            pure (.ex a (← img0 (c.pushVar x.fvarId! a) (mkApp p x).headBeta))
      | ``Eq, 3 =>
          let some a ← htOf? args[0]! | outside s!"= at {← ppExpr args[0]!}"
          pure (.eq a (← img0 c args[1]!) (← img0 c args[2]!))
      | ``Ne, 3 =>
          let some a ← htOf? args[0]! | outside s!"≠ at {← ppExpr args[0]!}"
          pure (.imp (.eq a (← img0 c args[1]!) (← img0 c args[2]!)) .bot)
      | `R, 2 => pure (.rel (← img0 c args[0]!) (← img0 c args[1]!))
      | `existsAt, 2 => pure (.act (← img0 c args[0]!) (← img0 c args[1]!))
      | `P, _ => imgSpine c .pos (.L FT.th) args
      | ``Classical.ofNonempty, 2 | ``Classical.choice, 2 =>
          -- `ofNonempty` is `choice inferInstance`; both are the one entity `c₀` (proof irrelevance)
          if isWorldTy (← whnfR args[0]!) then
            -- a world: the statement's own world variable (`Cert .w = True`; worlds are only variables)
            match (← get).worldVar with
            | some id =>
                match c.idx? id with
                | some k => return ← imgSpine c (.var k) .w args[2:].toArray
                | none => outside "world witness out of scope"
            | none => outside "Classical.ofNonempty : i with no world variable in scope"
          unless isEntTy (← whnfR args[0]!) do outside "Classical.ofNonempty at a type other than e"
          match (← get).nonemptyVar with
          | some id =>
              modify fun s => { s with nonemptyUsed := true }
              match c.idx? id with
              | some k => imgSpine c (.var k) (.L .e) args[2:].toArray
              | none => outside "nonempty witness out of scope"
          | none => throwError "[deep_translate] needs-nonempty"
      | _, _ =>
          match ← unfoldApp? e with
          | some e' => img0 c e'
          | none => outside s!"constant {n} (no definition to unfold)"
  | .fvar id =>
      match c.idx? id with
      | some k =>
          let some a := c.deep[k]? | outside "variable"
          imgSpine c (.var k) a args
      | none => outside s!"application of {(← id.getDecl).userName}, not a deep variable"
  | _ => outside s!"application head {← ppExpr f}"

partial def imgSpine (c : TCtx) (hd : DT) (a : HT) (args : Array Expr) : TM DT := do
  let mut x := hd
  let mut ty := a
  for arg in args do
    match ty with
    | .L (.arr _ b) =>
        x := .appL x (← img0 c arg)
        ty := .L b
    | .L .s =>
        x := .holds x (← img0 c arg)
        ty := .o
    | _ => outside "over-applied term"
  pure x
end

/-! ## Conversion: `βη` as derivations -/

def liftEx {α} (x : Except String α) : TM α := do
  match x with
  | .ok a => pure a
  | .error e => throwError e

/-- `eq o (holds (wabs φ) i) (φ[i])`. -/
def betaWEq (φ i : DT) : Der :=
  .propExt (.holds (.wabs φ) i) (φ.inst i) (.betaWE (.hyp 0)) (.betaWI φ i (.hyp 0))

/-- Can Leibniz at `a` with this motive and sides be emitted? -/
def leibOk (ctx : List HT) (a : HT) (φ s t : DT) : Bool :=
  a.plain || ((wtProof (a :: ctx) φ).toOption.isSome && (certProof ctx a s).toOption.isSome &&
    (certProof ctx a t).toOption.isSome)

/-- From `d : eq a X Y` and a context `C[·]` (a formula/term with hole `var 0` of type `a` in
`a :: ctx`, of type `b`), derive `eq b C[X] C[Y]` (Leibniz on the motive `C[X] = C[·]`). -/
def congrD (ctx : List HT) (a b : HT) (C : DT) (X Y : DT) (d : Der) : TM Der := do
  let CX := C.inst X
  let motive := DT.eq b (CX.shift 1) C
  unless leibOk ctx a motive X Y do
    wtFail s!"congruence at {a} needs Leibniz with motive {motive}, sides {X}, {Y}"
  pure (.leib a motive X Y d (.refl b CX))

mutual
/-- `eqNF ctx a X = (N, d)`: `N = X.nf` and `d` derives `eq a X N`. -/
partial def eqNF (ctx : List HT) (a : HT) (X : DT) : TM (DT × Der) := do
  if let some r := (← get).eqCache[(ctx, a, X)]? then return r
  let r ← eqNF0 ctx a X
  modify fun s => { s with eqCache := s.eqCache.insert (ctx, a, X) r }
  pure r

partial def eqNF0 (ctx : List HT) (a : HT) (X : DT) : TM (DT × Der) := do
  let N := X.nf
  if N == X then return (X, .refl a X)
  match X with
  | .appL f x =>
      let .L (.arr ta tb) ← liftEx (DT.ty ctx f) | throwError "eqNF appL"
      match f with
      | .lamL _ body =>
          let r := body.inst x
          let (N', dr) ← eqNF ctx (.L tb) r
          let db : Der := .betaL body x
          pure (N', if N' == r then db else .trans db dr)
      | _ =>
        let (f', df) ← eqNF ctx (.L (.arr ta tb)) f
        if f' == f then
          let (x', dx) ← eqNF ctx (.L ta) x
          if x' == x then return (X, .refl a X)
          let C := DT.appL (f.shift 1) (.var 0)
          pure (.appL f x', ← congrD ctx (.L ta) (.L tb) C x x' dx)
        else
          -- the function changes: `funApp` at a certified argument
          let some (_, xs) := canonL ctx x
            | do
              -- no certified form: Leibniz on the function
              let C := DT.appL (.var 0) (x.shift 1)
              let d1 ← congrD ctx (.L (.arr ta tb)) (.L tb) C f f' df
              let Y := DT.appL f' x
              let (N', dY) ← eqNF ctx (.L tb) Y
              return (N', if N' == Y then d1 else .trans d1 dY)
          let mut d : Der := .refl (.L tb) X
          let mut first := true
          if xs != x then
            let (xn, dxn) ← eqNF ctx (.L ta) x
            let (_, dxs) ← eqNF ctx (.L ta) xs
            -- x = xs  via their common normal form
            let dxx : Der := .trans dxn (.symm dxs)
            let _ := xn
            d ← congrD ctx (.L ta) (.L tb) (.appL (f.shift 1) (.var 0)) x xs dxx
            first := false
          let step : Der := .allE xs (.funApp df)
          d := if first then step else .trans d step
          let Y := DT.appL f' xs
          let (N', dY) ← eqNF ctx (.L tb) Y
          pure (N', if N' == Y then d else .trans d dY)
  | .lamL ta body =>
      let .L tb ← liftEx (DT.ty (.L ta :: ctx) body) | throwError "eqNF lamL"
      let (body', db) ← eqNF (.L ta :: ctx) (.L tb) body
      let X' := DT.lamL ta body'
      let d ← if body' == body then pure (Der.refl a X) else do
        -- funExt: ∀z. (λ body) z = (λ body') z
        let b1 := body.shift 1 1
        let b2 := body'.shift 1 1
        let inner : Der := .trans (.trans (.betaL b1 (.var 0)) db) (.symm (.betaL b2 (.var 0)))
        pure (.funExt (.allI (.L ta) inner))
      -- η
      match body' with
      | .appL g (.var 0) =>
          if !g.hasVar 0 then
            let g0 := g.down
            let de : Der := .funExt (.allI (.L ta) (.betaL (body'.shift 1 1) (.var 0)))
            let d' := if body' == body then de else .trans d de
            let (N', dn) ← eqNF ctx a g0
            pure (N', if N' == g0 then d' else .trans d' dn)
          else pure (X', d)
      | _ => pure (X', d)
  | .wabs body =>
      let (body', db) ← eqNF (.w :: ctx) .o body
      let X' := DT.wabs body'
      let d ← if body' == body then pure (Der.refl a X) else do
        let b1 := body.shift 1 1
        let b2 := body'.shift 1 1
        let inner : Der := .trans (.trans (betaWEq b1 (.var 0)) db) (.symm (betaWEq b2 (.var 0)))
        pure (.wExt (.allI .w inner))
      match body' with
      | .holds p (.var 0) =>
          if !p.hasVar 0 then
            let p0 := p.down
            let de : Der := .wExt (.allI .w (betaWEq (body'.shift 1 1) (.var 0)))
            let d' := if body' == body then de else .trans d de
            let (N', dn) ← eqNF ctx a p0
            pure (N', if N' == p0 then d' else .trans d' dn)
          else pure (X', d)
      | _ => pure (X', d)
  | .holds p i =>
      let (p', dp) ← eqNF ctx (.L .s) p
      let d0 ← if p' == p then pure (Der.refl .o X) else
        congrD ctx (.L .s) .o (.holds (.var 0) (i.shift 1)) p p' dp
      match p' with
      | .wabs body =>
          let r := body.inst i
          let (N', dr) ← eqNF ctx .o r
          let d1 : Der := if p' == p then betaWEq body i else .trans d0 (betaWEq body i)
          pure (N', if N' == r then d1 else .trans d1 dr)
      | _ => pure (.holds p' i, d0)
  | .act x i =>
      let (x', dx) ← eqNF ctx (.L .e) x
      pure (.act x' i, ← congrD ctx (.L .e) .o (.act (.var 0) (i.shift 1)) x x' dx)
  | .imp p q => binO ctx X .imp p q
  | .and p q => binO ctx X .and p q
  | .or p q => binO ctx X .or p q
  | .all b body =>
      let (body', db) ← eqNF (b :: ctx) .o body
      let X' := DT.all b body'
      -- all b body ⊢ all b body' and back
      let fwd : Der := .allI b (.leib .o (.var 0) body body' db (.allE (.var 0) (.hyp 0)))
      let bwd : Der := .allI b (.leib .o (.var 0) body' body (.symm db) (.allE (.var 0) (.hyp 0)))
      pure (X', .propExt X X' fwd bwd)
  | .ex .w (.and (.rel I (.var 0)) B) =>
      -- `◇`, classically: `(∃v. R I v ∧ B) = ¬∀v. R I v → ¬B'`
      let (B', dB) ← eqNF (.w :: ctx) .o B
      let A := DT.all .w (.imp (.rel I (.var 0)) (.imp B' .bot))
      let X' := DT.imp A .bot
      let fwd : Der := .impI A (.exE (.hyp 1)
        (.impE (.impE (.allE (.var 0) (.hyp 1)) (.andL (.hyp 0)))
          (.leib .o (.var 0) B B' dB (.andR (.hyp 0)))) .bot)
      let body := DT.and (.rel I (.var 0)) B
      let fwd := if B' == B then .impI A (.exE (.hyp 1)
        (.impE (.impE (.allE (.var 0) (.hyp 1)) (.andL (.hyp 0))) (.andR (.hyp 0))) .bot) else fwd
      let toB : Der := if B' == B then .hyp 0 else .leib .o (.var 0) B' B (.symm dB) (.hyp 0)
      let bwd : Der := .byContra X (.impE (.hyp 1) (.allI .w (.impI (.rel I (.var 0)) (.impI B'
        (.impE (.hyp 2) (.exI .w (body.shift 1 1) (.var 0) (.andI (.hyp 1) toB)))))))
      pure (X', .propExt X X' fwd bwd)
  | .ex (.L .e) (.act (.var 0) I) =>
      -- `(∃x. x @ I) = (∃x. x @ I ∧ ⊤)`
      let body' := DT.and (.act (.var 0) I) (.imp .bot .bot)
      let X' := DT.ex (.L .e) body'
      let fwd : Der := .exE (.hyp 0) (.exI (.L .e) (body'.shift 1 1) (.var 0)
        (.andI (.hyp 0) (.impI .bot (.hyp 0)))) X'
      let bwd : Der := .exE (.hyp 0) (.exI (.L .e) ((DT.act (.var 0) I).shift 1 1) (.var 0)
        (.andL (.hyp 0))) X
      pure (X', .propExt X X' fwd bwd)
  | .ex b body =>
      let (body', db) ← eqNF (b :: ctx) .o body
      let X' := DT.ex b body'
      let fwd : Der := .exE (.hyp 0) (.exI b (body'.shift 1 1) (.var 0)
        (.leib .o (.var 0) body body' db (.hyp 0))) X'
      let bwd : Der := .exE (.hyp 0) (.exI b (body.shift 1 1) (.var 0)
        (.leib .o (.var 0) body' body (.symm db) (.hyp 0))) X
      pure (X', .propExt X X' fwd bwd)
  | .eq b s t =>
      let (s', ds) ← eqNF ctx b s
      let (t', dt) ← eqNF ctx b t
      let X' := DT.eq b s' t'
      -- s = t ⊢ s' = t' : trans (symm ds) (trans h dt); and back
      let fwd : Der := .trans (.trans (.symm ds) (.hyp 0)) dt
      let bwd : Der := .trans (.trans ds (.hyp 0)) (.symm dt)
      let fwd := if s' == s then (if t' == t then Der.hyp 0 else .trans (.hyp 0) dt) else fwd
      let bwd := if s' == s then (if t' == t then Der.hyp 0 else .trans (.hyp 0) (.symm dt)) else bwd
      pure (X', .propExt X X' fwd bwd)
  | _ => throwError s!"eqNF: unexpected {X}"

partial def binO (ctx : List HT) (X : DT) (mk : DT → DT → DT) (p q : DT) : TM (DT × Der) := do
  let (p', dp) ← eqNF ctx .o p
  let (q', dq) ← eqNF ctx .o q
  let mut d : Der := .refl .o X
  let mut first := true
  if p' != p then
    d ← congrD ctx .o .o (mk (.var 0) (q.shift 1)) p p' dp
    first := false
  if q' != q then
    let s ← congrD ctx .o .o (mk (p'.shift 1) (.var 0)) q q' dq
    d := if first then s else .trans d s
  pure (mk p' q', d)
end

/-- Turn a derivation of `X` into one of `Y`, for `βη`-equal `X`, `Y` (formulas). -/
def conv (ctx : List HT) (d : Der) (X Y : DT) : TM Der := do
  if X == Y then return d
  -- cheap cases: world β at the top
  if let .holds (.wabs φ) i := X then
    if φ.inst i == Y then return .betaWE d
  if let .holds (.wabs φ) i := Y then
    if φ.inst i == X then return .betaWI φ i d
  let (nX, dX) ← eqNF ctx .o X
  let (nY, dY) ← eqNF ctx .o Y
  unless nX == nY do
    throwError m!"[deep_translate] not convertible:\n  {X}\n  {Y}\n(normal forms\n  {nX}\n  {nY})"
  let deq : Der := if nY == Y then dX else .trans dX (.symm dY)
  pure (.leib .o (.var 0) X Y deq d)

/-- Expose an implication/quantifier/conjunction/... at the head of a conclusion. -/
def expose (ctx : List HT) (d : Der) (X : DT) : TM (Der × DT) := do
  match X with
  | .imp .. | .all .. | .and .. | .or .. | .ex .. | .eq .. | .bot => pure (d, X)
  | _ =>
      -- a `◇` at the head stays an `∃` over worlds (its `nf` is `¬□¬`)
      if let h@(.ex .w (.and (.rel _ (.var 0)) _)) := X.hnf then
        return (← conv ctx d X h, h)
      let N := X.nf
      pure (← conv ctx d X N, N)

end Programme.H

end


/-! ## Tool part `Prf` -/
section

/-! # Thread H: the proof-term walker -/

open Lean Meta Elab Command Term
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
  Programme.«20261022-1724-ontological».ThWhole

namespace Programme.H

/-- The canonical certified form of an `∀E`/`∃I` instance (`emb` of an `𝓛`-term). -/
def canonInst (c : TCtx) (a : HT) (arg : Expr) : TM DT := do
  let x ← img c arg
  match a with
  | .L _ =>
      match canonL c.deep x with
      | some (_, x') => pure x'
      | none => wtFail m!"instance {← ppExpr arg} is not a term of 𝓛 (image {x})"
  | _ => pure x

/-! ### Existence outside the guards (v4: `E` is definable as `∃ᴱy. y = z`)

An instance whose image has `act s u` outside a quantifier guard is not an `𝓛`-term.  It is the
instance `M[E₀]` of a context `M` with hole at type `e → σ`, where `E₀ = λz w. act z w`; the term
`M[E₁]`, with `E₁ = λz. ∃ᴱy. y = z` (an `𝓛`-term), is certified.  `E₁ = E₀` is derived (funext,
world extensionality, propext); `e → σ` is a plain type, so Leibniz with the motive `B[M[·]]` is
allowed.  The instance step is taken at the certified `M[E₁]`. -/

def actE0 : DT := .lamL .e (.wabs (.act (.var 1) (.var 0)))
def actE1 : DT := .lamL .e (.wabs (.ex (.L .e) (.and (.act (.var 0) (.var 1)) (.eq (.L .e) (.var 0) (.var 2)))))
def actHT : HT := .L FT.tp

/-- Replace unguarded `act s u` (in a term shifted by one) by `holds (appL hole s) u`. -/
partial def actHole (d : Nat) : DT → DT
  | .act s u => .holds (.appL (.var d) (actHole d s)) (actHole d u)
  | .ex (.L .e) (.and (.act (.var 0) k) b) => .ex (.L .e) (.and (.act (.var 0) k) (actHole (d + 1) b))
  | .all (.L .e) (.imp (.act (.var 0) k) b) => .all (.L .e) (.imp (.act (.var 0) k) (actHole (d + 1) b))
  | .lamL a b => .lamL a (actHole (d + 1) b)
  | .wabs b => .wabs (actHole (d + 1) b)
  | .all a b => .all a (actHole (d + 1) b)
  | .ex a b => .ex a (actHole (d + 1) b)
  | .appL f x => .appL (actHole d f) (actHole d x)
  | .holds p i => .holds (actHole d p) (actHole d i)
  | .imp p q => .imp (actHole d p) (actHole d q)
  | .and p q => .and (actHole d p) (actHole d q)
  | .or p q => .or (actHole d p) (actHole d q)
  | .eq a p q => .eq a (actHole d p) (actHole d q)
  | x => x

/-- A derivation of `eq (e → σ) E₁ E₀` (closed terms, any context). -/
def actEq : Der :=
  let body1 := match actE1 with | .lamL _ b => b | x => x
  let body0 := match actE0 with | .lamL _ b => b | x => x
  let W1 := body1.shift 1
  let W0 := body0.shift 1
  let b1 := match W1 with | .wabs b => b | x => x
  let b0 := match W0 with | .wabs b => b | x => x
  let P0 := b0.inst (.var 0)
  let Bx := match b1.inst (.var 0) with | .ex _ b => b | x => x
  -- ∃y. act y w ∧ y = z  ⊢  act z w
  let inner1 : Der := .leib (.L .e) (.act (.var 0) (.var 2)) (.var 0) (.var 2) (.andR (.hyp 0)) (.andL (.hyp 0))
  let d1 : Der := .betaWI b0 (.var 0) (.exE (.betaWE (.hyp 0)) inner1 P0)
  -- act z w  ⊢  ∃y. act y w ∧ y = z
  let d2 : Der := .betaWI b1 (.var 0) (.exI (.L .e) Bx (.var 1) (.andI (.betaWE (.hyp 0)) (.refl (.L .e) (.var 1))))
  let mid : Der := .wExt (.allI .w (.propExt (.holds W1 (.var 0)) (.holds W0 (.var 0)) d1 d2))
  let inner : Der := .trans (.betaL (body1.shift 1 1) (.var 0)) (.trans mid (.symm (.betaL (body0.shift 1 1) (.var 0))))
  .funExt (.allI (.L .e) inner)

/-- For an uncertified instance `x`: its certified form `M[E₁]` and the context `M` (if `act`
occurs outside the guards and `M[E₁]` is an `𝓛`-term). -/
def actFix (ctx : List HT) (x : DT) : Option (DT × DT) := do
  let x1 := x.shift 1
  let M := actHole 0 x1
  if M == x1 then none
  let (_, x'') ← canonL ctx (M.inst actE1)
  pure (x'', M)

/-- Replace every argument of an `𝓛`-application by its canonical certified form (if it has one). -/
partial def certify (ctx : List HT) : DT → DT
  | .appL f y =>
      let y' := match canonL ctx y with | some (_, z) => z | none => certify ctx y
      .appL (certify ctx f) y'
  | .lamL a b => .lamL a (certify (.L a :: ctx) b)
  | .wabs b => .wabs (certify (.w :: ctx) b)
  | .holds p i => .holds (certify ctx p) i
  | .act x i => .act (certify ctx x) i
  | .imp p q => .imp (certify ctx p) (certify ctx q)
  | .and p q => .and (certify ctx p) (certify ctx q)
  | .or p q => .or (certify ctx p) (certify ctx q)
  | .all a b => .all a (certify (a :: ctx) b)
  | .ex a b => .ex a (certify (a :: ctx) b)
  | .eq a s t => .eq a (certify ctx s) (certify ctx t)
  | x => x

def addSentence (S : LT) (src : String) : TM Nat := do
  let st ← get
  match st.sentences.findIdx? (· == S) with
  | some k => pure k
  | none =>
      set { st with sentences := st.sentences.push S, sentenceNames := st.sentenceNames.push src }
      pure st.sentences.size

/-- Peel exactly `n` quantifiers (fewer if there are not so many). -/
def peelN : Nat → DT → List HT × DT
  | n + 1, .all a b => let (bs, body) := peelN n b; (a :: bs, body)
  | _, x => ([], x)

/-- Peel a prefix of quantifiers. -/
def peelAll : DT → List HT × DT
  | .all a b => let (bs, body) := peelAll b; (a :: bs, body)
  | x => ([], x)

/-- A validity fact `∀ x₁ … w … xₙ, body` (one world binder, the others at types of `𝓛`): its
`𝓛`-sentence `∀x₁…xₙ. body` joins `T` (its index is supplied by `getIdx`), and the derivation of
its image is returned. -/
def factDerWith (c : TCtx) (src : String) (ty : Expr) (getIdx : LT → TM Nat) : TM (Der × DT) := do
  let F ← img c ty
  let (bs, body) := peelAll F
  let wposs := (List.range bs.length).filter fun j => bs[j]? == some HT.w
  let [wpos] := wposs | outside m!"{src}: not a validity statement with one world quantifier: {F}"
  let n := bs.length
  let ctx' := bs.reverse ++ c.deep
  let wi := n - 1 - wpos
  let some S := sentenceOf ctx' wi body
    | outside m!"{src}: the statement is not an 𝓛-sentence: {body}"
  -- the `𝓛`-binders, outermost first, with their indices in `ctx'`
  let lbs := (List.range n).filterMap fun j =>
    match bs[j]? with | some (HT.L t) => some (t, n - 1 - j) | _ => none
  let nl := lbs.length
  -- closedness: no `𝓛`-variable beyond the binders
  let rec maxVar : LT → Nat → Bool
    | .var k, d => k < d
    | .app f x, d => maxVar f d && maxVar x d
    | .lam _ b, d => maxVar b (d + 1)
    | .neg x, d | .box x, d => maxVar x d
    | .and x y, d | .or x y, d | .imp x y, d | .eq _ x y, d => maxVar x d && maxVar y d
    | .all _ b, d | .ex _ b, d | .allE b, d | .exE b, d => maxVar b (d + 1)
    | _, _ => true
  unless maxVar S nl do outside m!"{src}: the statement has free parameters"
  let S' := lbs.reverse.foldl (fun acc (t, _) => LT.all t acc) S
  let idx ← getIdx S'
  let mut d : Der := .ax idx (.var wi)
  let mut X : DT := .holds (embD [] S') (.var wi)
  for (_, k) in lbs do
    let (d', X') ← expose ctx' d X
    let .all _ B := X' | throwError m!"factDer: expected ∀, got {X'}"
    d := .allE (.var k) d'
    X := B.inst (.var k)
  d ← conv ctx' d X body
  for b in bs.reverse do
    d := .allI b d
  pure (d, F)

def factDer (c : TCtx) (src : String) (ty : Expr) : TM (Der × DT) :=
  factDerWith c src ty fun S => addSentence S src

def isFactAxiom (n : Name) : MetaM Bool := do
  let info ← getConstInfo n
  let .axiomInfo _ := info | return false
  if [``propext, ``Classical.choice, ``Quot.sound, `iNonempty, `eNonempty].contains n then return false
  isProp info.type

def specialNames : List Name :=
  [``And.casesOn, ``And.intro, ``And.left, ``And.rec, ``And.right, ``Classical.byCases,
   ``Classical.byContradiction, ``Classical.em, ``Decidable.byCases, ``Eq.mp, ``Eq.mpr, ``Eq.ndrec,
   ``Eq.rec, ``Eq.refl, ``Eq.subst, ``Eq.symm, ``Eq.trans, ``Exists.casesOn, ``Exists.elim,
   ``Exists.intro, ``Exists.rec, ``False.casesOn, ``False.elim, ``False.rec, ``Iff.intro, ``Iff.mp,
   ``Iff.mpr, ``Iff.refl, ``Iff.rfl, ``Or.casesOn, ``Or.elim, ``Or.inl, ``Or.inr, ``Or.rec,
   ``absurd, ``cast, ``congrArg, ``congrFun, ``congrFun', ``forall_congr, `congr, ``eq_self, ``eq_true, ``funext, ``id,
   ``letFun, ``of_eq_true, ``propext, ``rfl]

def trivD : Der := .impI .bot (.hyp 0)
def topD : DT := .imp .bot .bot

/-- Peel the `𝓛`/world binders of a goal (unfolding `Mvalid`). -/
partial def peelVars {α} (ty : Expr) (xs : Array Expr) (k : Array Expr → Expr → TM α) : TM α := do
  let ty' ← whnf ty
  match ty' with
  | .forallE n dom body bi =>
      let seenW ← xs.anyM fun x => return isWorldTy (← whnfR (← inferType x))
      if seenW && isWorldTy (← whnfR dom) then k xs ty  -- a second world binder: the body's `□`
      else if (← htOf? dom).isSome && !(← isProp dom) then
        withLocalDecl n bi dom fun x => peelVars (body.instantiate1 x) (xs.push x) k
      else k xs ty
  | _ => k xs ty

def needsNonempty (ex : Exception) : TM Bool := do
  return (← ex.toMessageData.toString).startsWith "[deep_translate] needs-nonempty"

/-- A closed frame formula (C7): `rel` between bound world variables, `⊥`, connectives, world
quantifiers, equality of bound world variables. -/
def DT.frameOK : DT → Nat → Bool
  | .rel (.var i) (.var j), d => i < d && j < d
  | .eq .w (.var i) (.var j), d => i < d && j < d
  | .bot, _ => true
  | .imp p q, d | .and p q, d | .or p q, d => DT.frameOK p d && DT.frameOK q d
  | .all .w b, d | .ex .w b, d => DT.frameOK b (d + 1)
  | _, _ => false

mutual

partial def chk (c : TCtx) (e : Expr) (A : DT) : TM Der := do
  let (d, X) ← prf c e
  conv c.deep d X A

partial def prf (c : TCtx) (e : Expr) : TM (Der × DT) := do
  modify fun s => { s with steps := s.steps + 1, current := e }
  if (← get).steps > 400000 then outside m!"step limit at {← ppExpr e}"
  if (← get).steps % 500 == 0 then dbg (s!"[deep] step {(← get).steps}, depth {(← get).depth} {(← get).stack.take 3}")
  match e with
  | .mdata _ b => prf c b
  | .letE n ty v b _ =>
      if ← isProp ty then
        let (dv, A) ← prf c v
        withLocalDecl n .default ty fun h => do
          let (db, B) ← prf (c.pushHyp h.fvarId! A) (b.instantiate1 h)
          pure (.impE (.impI A db) dv, B)
      else prf c (b.instantiate1 v)
  | .fvar id =>
      if let some (k, A) := c.hypIdx? id then return (.hyp k, A)
      if c.isFact id then
        return ← factDer c s!"{(← id.getDecl).userName}" (← id.getType)
      outside m!"proof variable {(← id.getDecl).userName} is not a hypothesis"
  | .lam n ty b bi =>
      if ← isProp ty then
        let A ← img c ty
        withLocalDecl n bi ty fun h => do
          let (d, B) ← prf (c.pushHyp h.fvarId! A) (b.instantiate1 h)
          pure (.impI A d, .imp A B)
      else
        let a ← htOf ty
        withLocalDecl n bi ty fun x => do
          let (d, B) ← prf (c.pushVar x.fvarId! a) (b.instantiate1 x)
          pure (.allI a d, .all a B)
  | .app .. | .const .. => prfApp c e
  | .proj s i h =>
      let (d, X) ← prf c h
      let (d, X) ← expose c.deep d X
      match s, i, X with
      | ``And, 0, .and A _ => pure (.andL d, A)
      | ``And, 1, .and _ B => pure (.andR d, B)
      | ``Iff, 0, .and A _ => pure (.andL d, A)
      | ``Iff, 1, .and _ B => pure (.andR d, B)
      | _, _, _ => outside m!"projection {s}.{i} of {X}"
  | _ => outside m!"proof term {← ppExpr e}"

partial def applyArgs (c : TCtx) (d0 : Der) (X0 : DT) (args : Array Expr) : TM (Der × DT) := do
  let mut d := d0
  let mut X := X0
  for arg in args do
    let (d', X') ← expose c.deep d X
    match X' with
    | .imp A B =>
        let da ← chk c arg A
        d := .impE d' da
        X := B
    | .all a B =>
        let x ← img c arg
        if let .L _ := a then
          if (canonL c.deep x).isNone then
            if let some (x'', M) := actFix c.deep x then
              let φ := (B.shift 1 1).inst M
              let d2 ← conv c.deep (.allE x'' d') (B.inst x'') (φ.inst actE1)
              d ← conv c.deep (.leib actHT φ actE1 actE0 actEq d2) (φ.inst actE0) (B.inst x)
              X := B.inst x
              continue
        let t ← canonInst c a arg
        d := .allE t d'
        X := B.inst t
    | _ => outside m!"argument {← ppExpr arg} applied to a proof of {X'}"
  pure (d, X)

/-- A goal `∀ x… w …, body` (statement hypotheses `facts` already in scope) with proof `pf`: its
`𝓛`-sentence `φ`, a derivation of `holds (emb φ) w` in `[.w]` and that target.  With `withNE`,
`Classical.ofNonempty : e` is a variable taken from the sentence `∃x.⊤` of `T`. -/
partial def goalCore (facts : Array FactVar) (goalTy pf : Expr) (withNE : Bool) :
    TM (LT × Der × DT) := do
  let savedNE := (← get).nonemptyVar
  let savedW := (← get).worldVar
  modify fun s => { s with nonemptyVar := none }
  let r ← peelVars goalTy #[] fun xs body => do
    let ws ← xs.filterM fun x => do return isWorldTy (← whnfR (← inferType x))
    -- a world-free statement (e.g. `G ≠ fun _ => ⊥ᵐ`): a rigid sentence, read at a fresh world
    let withW (k : Expr → Array Expr → Expr → TM (LT × Der × DT)) : TM (LT × Der × DT) := do
      match ws with
      | #[w0] =>
          let ls := xs.filter (· != w0)
          let r ← k w0 ls (← mkLambdaFVars ls (mkAppN pf xs))
          modify fun s => { s with lastWorldFree := false }
          pure r
      | #[] =>
          withLocalDecl `w₀ .default (mkConst `i) fun w0 => do
            let r ← k w0 xs (← mkLambdaFVars xs (mkAppN pf xs))
            modify fun s => { s with lastWorldFree := true }
            pure r
      | _ => outside m!"statement {← ppExpr goalTy} is not a validity (one world binder)"
    withW fun w0 ls q => do
      let mut c0 : TCtx := { vars := #[(w0.fvarId!, .w)], facts := facts }
      modify fun s => { s with worldVar := some w0.fvarId! }
      -- module frame axioms: hypotheses of every derivation (pushed first: the tail of `hs`)
      for (_, fv, F) in (← get).modFrames do c0 := c0.pushHyp (some fv) F
      -- C7: hypotheses whose image is a closed frame formula go into the hypothesis list
      if facts.size > 0 then
        let mut frames : List (Nat × DT) := []
        let mut rest : Array FactVar := #[]
        let mut k := 0
        for f in facts do
          let F? ← try some <$> img c0 (← instantiateMVars (← f.fvar.getType)) catch _ => pure none
          match F? with
          | some F =>
              if DT.frameOK F 0 then
                frames := (k, F) :: frames
                c0 := c0.pushHyp (some f.fvar) F
              else rest := rest.push f
          | none => rest := rest.push f
          k := k + 1
        c0 := { c0 with facts := rest }
        modify fun s => { s with frames := frames }
      let Fimg ← img c0 (← mkForallFVars ls body)
      let (bs, fbody) := peelN ls.size Fimg
      let ctx' := bs.reverse ++ c0.deep
      let some S := sentenceOf ctx' bs.length fbody
        | outside m!"the statement is not an 𝓛-sentence: {fbody}"
      let φ := bs.reverse.foldl (fun acc b => match b with | .L t => LT.all t acc | _ => acc) S
      let target := DT.holds (embD [] φ) (.var 0)
      if withNE then
        withLocalDecl `c₀ .default (mkConst `e) fun cv => do
          modify fun s => { s with nonemptyVar := some cv.fvarId! }
          let neIdx ← addSentence (.ex .e .top) "NonEmpty"
          let c1 : TCtx := (c0.pushVar cv.fvarId! (.L .e)).pushHyp none (.imp .bot .bot)
          let (d, X) ← prf c1 q
          let d ← conv c1.deep d X (target.shift 1)
          let dNE0 : Der := .ax neIdx (.var 0)
          let XNE := DT.holds (embD [] (.ex .e .top)) (.var 0)
          let (dNE, XNE') ← expose c0.deep dNE0 XNE
          unless XNE' == DT.ex (.L .e) (.imp .bot .bot) do throwError m!"NonEmpty: {XNE'}"
          pure (φ, Der.exE dNE d target, target)
      else
        let (d, X) ← prf c0 q
        let d ← conv c0.deep d X target
        pure (φ, d, target)
  modify fun s => { s with nonemptyVar := savedNE, worldVar := savedW }
  pure r

/-- A theorem whose statement is a validity of a closed `𝓛`-sentence is translated once (from the
theory so far) and then used as a sentence of the theory: a lemma.  Otherwise `none` (unfold). -/
partial def lemmaApp (c : TCtx) (n : Name) (args : Array Expr) : TM (Option (Der × DT)) := do
  unless (← get).useLemmas do return none
  if (← get).noLemma.contains n then return none
  let info ← getConstInfo n
  let .thmInfo tv := info | return none
  unless info.levelParams.isEmpty do return none
  let idx ← match (← get).lemmaIdx[n]? with
    | some k => pure k
    | none =>
      let st ← get
      let ref ← IO.mkRef (none : Option LT)
      let ok ← try
          let _ ← factDerWith c (toString n) info.type fun S => do ref.set (some S); pure 0
          pure true
        catch _ => pure false
      set st
      let some S ← ref.get | do
        modify fun s => { s with noLemma := s.noLemma.insert n }
        return none
      unless ok do
        modify fun s => { s with noLemma := s.noLemma.insert n }
        return none
      let enter : TM Unit := modify fun s => { s with stack := n :: s.stack, depth := s.depth + 1 }
      enter
      let (φ, d, target) ← try goalCore #[] info.type tv.value false catch ex => do
        unless ← needsNonempty ex do throw ex
        set st
        enter
        goalCore #[] info.type tv.value true
      unless φ == S do outside m!"lemma {n}: sentence mismatch {φ.toStr} vs {S.toStr}"
      let k ← match (← get).sentences.findIdx? (· == S) with
        | some k => pure k
        | none => do
            let k := (← get).sentences.size
            modify fun s => { s with sentences := s.sentences.push S,
                                     sentenceNames := s.sentenceNames.push s!"lemma {n}",
                                     lemmas := s.lemmas.push (k, n, d, target) }
            pure k
      modify fun s => { s with lemmaIdx := s.lemmaIdx.insert n k, stack := s.stack.tail,
                               depth := s.depth - 1 }
      pure k
  let (d, X) ← factDerWith c (toString n) info.type fun _ => pure idx
  return some (← applyArgs c d X args)

partial def prfApp (c : TCtx) (e : Expr) : TM (Der × DT) := do
  let f := e.getAppFn
  let args := e.getAppArgs
  if f.isLambda then return ← prf c e.headBeta
  if let .mdata _ f' := f then return ← prf c (mkAppN f' args)
  if let .letE _ _ v b _ := f then return ← prf c (mkAppN (b.instantiate1 v) args)
  match f with
  | .const n _ =>
      if let some r ← special c n args then return r
      if specialNames.contains n then
        -- partially applied logical constant: η-expand
        let e' ← etaExpand e
        if e'.isLambda then return ← prf c e'
        outside m!"{n} applied to too few arguments"
      if let some (_, fv, _) := (← get).modFrames.find? (·.1 == n) then
        return ← prf c (mkAppN (mkFVar fv) args)
      if ← isFactAxiom n then
        let (d, X) ← factDer c s!"{n}" (← inferType f)
        return ← applyArgs c d X args
      let e ← match (← get).replace.lookup n with
        | some n' => pure (mkAppN (mkConst n' (f.constLevels!)) args)
        | none => pure e
      if let some r ← lemmaApp c e.getAppFn.constName! args then return r
      match ← unfoldApp? e with
      | some e' =>
          let st ← get
          if st.depth > 400 then outside m!"unfolding depth exceeded at {n}"
          modify fun s => { s with depth := s.depth + 1, stack := n :: s.stack }
          let r ← prf c e'
          modify fun s => { s with depth := s.depth - 1, stack := s.stack.tail }
          pure r
      | none => outside m!"constant {n}"
  | .fvar id =>
      if let some (k, A) := c.hypIdx? id then return ← applyArgs c (.hyp k) A args
      if c.isFact id then return ← factApp c id args
      outside m!"application of {(← id.getDecl).userName}, which is not a hypothesis"
  | .proj .. =>
      let (d, X) ← prf c f
      applyArgs c d X args
  | _ => outside m!"application head {← ppExpr f}"

/-- A hypothesis of the statement applied to arguments.  Leading arguments at types outside `𝓛`
(a schema, as `Ax1GenR`'s set of properties) are substituted into the statement first; the instance
must again be an `𝓛`-sentence. -/
partial def factApp (c : TCtx) (id : FVarId) (args : Array Expr) : TM (Der × DT) := do
  let name := s!"{(← id.getDecl).userName}"
  let mut ty ← instantiateMVars (← id.getType)
  let mut k := 0
  -- schema arguments
  repeat
    let ty' ← whnf ty
    let .forallE _ dom _ _ := ty' | break
    if (← htOf? dom).isSome || (← isProp dom) then break
    let some arg := args[k]? | outside m!"{name}: schema used without an instance"
    ty := ty'.bindingBody!.instantiate1 arg
    k := k + 1
  let src := if k == 0 then name else s!"{name} (instance)"
  let instFn ← mkLambdaFVars #[mkFVar id] (mkAppN (mkFVar id) (args.extract 0 k))
  let (d, X) ← factDerWith c src ty fun S => do
    let i ← addSentence S src
    if !ty.hasFVar && !instFn.hasFVar && !(← get).factTys.contains i then
      modify fun st => { st with factTys := st.factTys.insert i (ty, instFn) }
    pure i
  applyArgs c d X args[k:].toArray

/-- Leibniz substitution along `h : a = b` of type `α`, with Lean motive `mot x` (a `Prop`). -/
partial def leibCase (c : TCtx) (α aE bE : Expr) (mot : Expr → Expr) (m h : Expr) :
    TM (Der × DT) := do
  let ta ← htOf α
  let φ ← withLocalDecl `x .default α fun x => do img (c.pushVar x.fvarId! ta) (mot x)
  if ta.plain then
    let s ← img c aE
    let t ← img c bE
    let dh ← chk c h (.eq ta s t)
    let dm ← chk c m (φ.inst s)
    pure (.leib ta φ s t dh dm, φ.inst t)
  else
    let s ← canonInst c ta aE
    let t ← canonInst c ta bE
    let φ' := certify (ta :: c.deep) φ
    unless leibOk c.deep ta φ' s t do
      wtFail m!"Leibniz step at {ta} with motive {φ'} (sides {s}, {t})"
    let dh ← chk c h (.eq ta s t)
    let dm ← chk c m (φ'.inst s)
    pure (.leib ta φ' s t dh dm, φ'.inst t)

/-- Classical case split on `p` for the goal `q`. -/
partial def caseSplit (c : TCtx) (p q : Expr) (f1 f2 : Expr → Expr) : TM (Der × DT) := do
  let P ← img c p
  let Q ← img c q
  let c1 := c.pushHyp none (.imp Q .bot)
  let d1 ← withLocalDecl `h .default p fun h => chk (c1.pushHyp h.fvarId! P) (f1 h).headBeta Q
  let d2 ← withLocalDecl `h .default (mkNot p) fun h =>
    chk (c1.pushHyp h.fvarId! (.imp P .bot)) (f2 h).headBeta Q
  let dNotP : Der := .impI P (.impE (.hyp 1) d1)
  let dQ : Der := .impE (.impI (.imp P .bot) d2) dNotP
  pure (.byContra Q (.impE (.hyp 0) dQ), Q)

partial def orCase (c : TCtx) (a b : Expr) (h f g : Expr) (C : DT) : TM (Der × DT) := do
  let (dh, X) ← prf c h
  let (dh, X) ← expose c.deep dh X
  let .or A B := X | outside m!"∨-elimination of {X}"
  let d1 ← withLocalDecl `h .default a fun x => chk (c.pushHyp x.fvarId! A) (mkApp f x).headBeta C
  let d2 ← withLocalDecl `h .default b fun x => chk (c.pushHyp x.fvarId! B) (mkApp g x).headBeta C
  pure (.orE dh d1 d2, C)

partial def exCase (c : TCtx) (α p h f : Expr) (C : DT) : TM (Der × DT) := do
  let (dh, X) ← prf c h
  let (dh, X) ← expose c.deep dh X
  -- a `◇` already read as `¬□¬`: back to `∃v. R I v ∧ B` (`conv`: equal normal forms)
  let (dh, X) ← match X with
    | .imp (.all .w (.imp (.rel I (.var 0)) (.imp B .bot))) .bot =>
        let Y := DT.ex .w (.and (.rel I (.var 0)) B)
        pure (← conv c.deep dh X Y, Y)
    | _ => pure (dh, X)
  let .ex a φ := X | outside m!"∃-elimination of {X}"
  let d2 ← withLocalDecl `x .default α fun x => do
    let c1 := c.pushVar x.fvarId! a
    withLocalDecl `hx .default (mkApp p x).headBeta fun hx => do
      -- `∃x. x @ w` read as `∃ᴱx. ⊤`: the body is `x @ w ∧ ⊤`, the Lean hypothesis is `x @ w`
      if let .and B0 (.imp .bot .bot) := φ then
        let B ← img c1 (mkApp p x).headBeta
        if B.nf != φ.nf then
          let d ← chk ((c1.pushHyp none φ).pushHyp hx.fvarId! B) (mkApp2 f x hx).headBeta (C.shift 1)
          return .impE (.impI B d) (← conv c1.deep (.andL (.hyp 0)) B0 B)
      chk (c1.pushHyp hx.fvarId! φ) (mkApp2 f x hx).headBeta (C.shift 1)
  pure (.exE dh d2 C, C)

partial def andCase (c : TCtx) (a b h f : Expr) (C : DT) : TM (Der × DT) := do
  let (dh, X) ← prf c h
  let (dh, X) ← expose c.deep dh X
  let .and A B := X | outside m!"∧-elimination of {X}"
  let d ← withLocalDecl `ha .default a fun ha => withLocalDecl `hb .default b fun hb =>
    chk ((c.pushHyp ha.fvarId! A).pushHyp hb.fvarId! B) (mkApp2 f ha hb).headBeta C
  pure (.impE (.impE (.impI A (.impI B d)) (.andL dh)) (.andR dh), C)

/-- The motive of a non-dependent eliminator, applied to the major premise. -/
partial def motiveAt (c : TCtx) (motive major : Expr) : TM DT := do
  img c (mkApp motive major).headBeta

/-- Handlers for the logical constants; `none` if `n` is not one of them. -/
partial def special (c : TCtx) (n : Name) (args : Array Expr) : TM (Option (Der × DT)) := do
  let k := args.size
  let rest (m : Nat) : Array Expr := args[m:].toArray
  let fin (m : Nat) (r : Der × DT) : TM (Option (Der × DT)) := do
    if k == m then pure (some r) else some <$> applyArgs c r.1 r.2 (rest m)
  match n with
  | ``And.intro => do
      if k < 4 then return none
      let A ← img c args[0]!
      let B ← img c args[1]!
      let da ← chk c args[2]! A
      let db ← chk c args[3]! B
      fin 4 (.andI da db, .and A B)
  | ``And.left | ``And.right => do
      if k < 3 then return none
      let (d, X) ← prf c args[2]!
      let (d, X) ← expose c.deep d X
      let .and A B := X | outside m!"{n} of {X}"
      fin 3 (if n == ``And.left then (.andL d, A) else (.andR d, B))
  | ``And.casesOn => do
      if k < 5 then return none
      fin 5 (← andCase c args[0]! args[1]! args[3]! args[4]! (← motiveAt c args[2]! args[3]!))
  | ``And.rec => do
      if k < 5 then return none
      fin 5 (← andCase c args[0]! args[1]! args[4]! args[3]! (← motiveAt c args[2]! args[4]!))
  | ``Or.inl => do
      if k < 3 then return none
      let (d, A) ← prf c args[2]!
      let B ← img c args[1]!
      fin 3 (.orL B d, .or A B)
  | ``Or.inr => do
      if k < 3 then return none
      let (d, B) ← prf c args[2]!
      let A ← img c args[0]!
      fin 3 (.orR A d, .or A B)
  | ``Or.elim => do
      if k < 6 then return none
      fin 6 (← orCase c args[0]! args[1]! args[3]! args[4]! args[5]! (← img c args[2]!))
  | ``Or.casesOn => do
      if k < 6 then return none
      fin 6 (← orCase c args[0]! args[1]! args[3]! args[4]! args[5]! (← motiveAt c args[2]! args[3]!))
  | ``Or.rec => do
      if k < 6 then return none
      fin 6 (← orCase c args[0]! args[1]! args[5]! args[3]! args[4]! (← motiveAt c args[2]! args[5]!))
  | ``Exists.intro => do
      if k < 4 then return none
      let a ← htOf args[0]!
      let φ ← withLocalDecl `x .default args[0]! fun x => do
        img (c.pushVar x.fvarId! a) (mkApp args[1]! x).headBeta
      let x ← img c args[2]!
      if let .L _ := a then
        if (canonL c.deep x).isNone then
          if let some (x'', M) := actFix c.deep x then
            let ψ := (φ.shift 1 1).inst M
            let dh0 ← chk c args[3]! (φ.inst x)
            let d2 ← conv c.deep dh0 (φ.inst x) (ψ.inst actE0)
            let d3 ← conv c.deep (.leib actHT ψ actE0 actE1 (.symm actEq) d2) (ψ.inst actE1) (φ.inst x'')
            return ← fin 4 (.exI a φ x'' d3, .ex a φ)
      let t ← canonInst c a args[2]!
      let dh ← chk c args[3]! (φ.inst t)
      fin 4 (.exI a φ t dh, .ex a φ)
  | ``Exists.elim => do
      if k < 5 then return none
      fin 5 (← exCase c args[0]! args[1]! args[3]! args[4]! (← img c args[2]!))
  | ``Exists.casesOn => do
      if k < 5 then return none
      fin 5 (← exCase c args[0]! args[1]! args[3]! args[4]! (← motiveAt c args[2]! args[3]!))
  | ``Exists.rec => do
      if k < 5 then return none
      fin 5 (← exCase c args[0]! args[1]! args[4]! args[3]! (← motiveAt c args[2]! args[4]!))
  | ``False.elim => do
      if k < 2 then return none
      let C ← img c args[0]!
      let d ← chk (c.pushHyp none (.imp C .bot)) args[1]! .bot
      fin 2 (.byContra C d, C)
  | ``False.rec | ``False.casesOn => do
      if k < 2 then return none
      let C ← motiveAt c args[0]! args[1]!
      let d ← chk (c.pushHyp none (.imp C .bot)) args[1]! .bot
      fin 2 (.byContra C d, C)
  | ``absurd => do
      if k < 4 then return none
      let A ← img c args[0]!
      let B ← img c args[1]!
      let c' := c.pushHyp none (.imp B .bot)
      let d1 ← chk c' args[2]! A
      let d2 ← chk c' args[3]! (.imp A .bot)
      fin 4 (.byContra B (.impE d2 d1), B)
  | ``Classical.byContradiction => do
      if k < 2 then return none
      let P ← img c args[0]!
      let d ← withLocalDecl `hn .default (mkNot args[0]!) fun hn =>
        chk (c.pushHyp hn.fvarId! (.imp P .bot)) (mkApp args[1]! hn).headBeta .bot
      fin 2 (.byContra P d, P)
  | ``Classical.byCases => do
      if k < 4 then return none
      fin 4 (← caseSplit c args[0]! args[1]! (mkApp args[2]!) (mkApp args[3]!))
  | ``Decidable.byCases => do
      if k < 5 then return none
      fin 5 (← caseSplit c args[0]! args[1]! (mkApp args[3]!) (mkApp args[4]!))
  | ``dite => do
      if k < 5 then return none
      unless ← isProp args[0]! do return none
      fin 5 (← caseSplit c args[1]! args[0]! (mkApp args[3]!) (mkApp args[4]!))
  | ``ite => do
      if k < 5 then return none
      unless ← isProp args[0]! do return none
      fin 5 (← caseSplit c args[1]! args[0]! (fun _ => args[3]!) (fun _ => args[4]!))
  | ``Classical.em => do
      if k < 1 then return none
      let P ← img c args[0]!
      let X := DT.or P (.imp P .bot)
      let inner : Der := .impI P (.impE (.hyp 1) (.orL (.imp P .bot) (.hyp 0)))
      fin 1 (.byContra X (.impE (.hyp 0) (.orR P inner)), X)
  | ``Iff.intro => do
      if k < 4 then return none
      let A ← img c args[0]!
      let B ← img c args[1]!
      let d1 ← chk c args[2]! (.imp A B)
      let d2 ← chk c args[3]! (.imp B A)
      fin 4 (.andI d1 d2, .and (.imp A B) (.imp B A))
  | ``Iff.mp | ``Iff.mpr => do
      if k < 3 then return none
      let (d, X) ← prf c args[2]!
      let (d, X) ← expose c.deep d X
      let .and L R := X | outside m!"{n} of {X}"
      fin 3 (if n == ``Iff.mp then (.andL d, L) else (.andR d, R))
  | ``Iff.rfl | ``Iff.refl => do
      if k < 1 then return none
      let A ← img c args[0]!
      let d : Der := .impI A (.hyp 0)
      fin 1 (.andI d d, .and (.imp A A) (.imp A A))
  | ``id => do
      if k < 2 then return none
      let (d, X) ← prf c args[1]!
      fin 2 (d, X)
  | ``True.intro | ``trivial => fin 0 (trivD, topD)
  | ``Eq.refl | ``rfl => do
      if k < 2 then return none
      let a ← htOf args[0]!
      let t ← img c args[1]!
      fin 2 (.refl a t, .eq a t t)
  | ``Eq.symm => do
      if k < 4 then return none
      let (d, X) ← prf c args[3]!
      let (d, X) ← expose c.deep d X
      let .eq a s t := X | outside m!"Eq.symm of {X}"
      fin 4 (.symm d, .eq a t s)
  | ``Eq.trans => do
      if k < 6 then return none
      let (d1, X) ← prf c args[4]!
      let (d1, X) ← expose c.deep d1 X
      let .eq a s t := X | outside m!"Eq.trans of {X}"
      let u ← img c args[3]!
      let d2 ← chk c args[5]! (.eq a t u)
      fin 6 (.trans d1 d2, .eq a s u)
  | ``Eq.mpr => do
      if k < 4 then return none
      let A ← img c args[0]!
      let B ← img c args[1]!
      let dh ← chk c args[2]! (.eq .o A B)
      let db ← chk c args[3]! B
      fin 4 (.leib .o (.var 0) B A (.symm dh) db, A)
  | ``Eq.mp | ``cast => do
      if k < 4 then return none
      let A ← img c args[0]!
      let B ← img c args[1]!
      let dh ← chk c args[2]! (.eq .o A B)
      let da ← chk c args[3]! A
      fin 4 (.leib .o (.var 0) A B dh da, B)
  | ``Eq.ndrec => do
      if k < 6 then return none
      fin 6 (← leibCase c args[0]! args[1]! args[4]! (fun x => (mkApp args[2]! x).headBeta)
        args[3]! args[5]!)
  | ``Eq.rec => do
      if k < 6 then return none
      let mot := args[2]!
      let .lam _ _ (.lam _ _ body _) _ := mot | outside "Eq.rec with a motive that is not λ x h"
      if body.hasLooseBVar 0 then outside "Eq.rec with a motive depending on the proof"
      fin 6 (← leibCase c args[0]! args[1]! args[4]! (fun x => (body.lowerLooseBVars 1 1).instantiate1 x)
        args[3]! args[5]!)
  | ``Eq.subst => do
      if k < 6 then return none
      fin 6 (← leibCase c args[0]! args[2]! args[3]! (fun x => (mkApp args[1]! x).headBeta)
        args[5]! args[4]!)
  | ``congrArg => do
      if k < 6 then return none
      let α := args[0]!
      let a1 := args[2]!
      let a2 := args[3]!
      let f := args[4]!
      let fa1 := (mkApp f a1).headBeta
      let lv ← getLevel' args[1]!
      let mot (x : Expr) : Expr := mkApp3 (mkConst ``Eq [lv]) args[1]! fa1 (mkApp f x).headBeta
      let m := mkApp2 (mkConst ``Eq.refl [lv]) args[1]! fa1
      let _ := α
      fin 6 (← leibCase c α a1 a2 mot m args[5]!)
  | `congr => do
      -- `congr h₁ h₂ : f₁ a₁ = f₂ a₂` as `(congrFun h₁ a₁).trans (congrArg f₂ h₂)`
      if k < 8 then return none
      let e' ← mkEqTrans (← mkCongrFun args[6]! args[4]!) (← mkCongrArg args[3]! args[7]!)
      fin 8 (← prf c e')
  | ``forall_congr => do
      -- `forall_congr h : (∀a, p a) = (∀a, q a)` as `propext ⟨λ hp a. (h a) ▸ hp a, λ hq a. (h a) ▸ hq a⟩`
      -- (core's own proof is `funext h ▸ rfl`, `funext` at `α → Prop`)
      if k < 4 then return none
      let α := args[0]!
      let p := args[1]!
      let q := args[2]!
      let h := args[3]!
      let allP ← withLocalDecl `a .default α fun a => mkForallFVars #[a] (mkApp p a).headBeta
      let allQ ← withLocalDecl `a .default α fun a => mkForallFVars #[a] (mkApp q a).headBeta
      let fwd ← withLocalDecl `hp .default allP fun hp => withLocalDecl `a .default α fun a => do
        mkLambdaFVars #[hp, a] (← mkEqMP (mkApp h a) (mkApp hp a))
      let bwd ← withLocalDecl `hq .default allQ fun hq => withLocalDecl `a .default α fun a => do
        mkLambdaFVars #[hq, a] (← mkEqMPR (mkApp h a) (mkApp hq a))
      let e' := mkApp3 (mkConst ``propext) allP allQ (mkApp4 (mkConst ``Iff.intro) allP allQ fwd bwd)
      fin 4 (← prf c e')
  | ``congrFun | ``congrFun' => do
      if k < 6 then return none
      -- `congrFun (congrArg f h) x` is `congrArg (λy. f y x) h` (no equation between functions)
      let h4 := args[4]!
      if h4.isAppOfArity ``congrArg 6 then
        let x := args[5]!
        let f := h4.appFn!.appArg!
        let fnew ← withLocalDecl `y .default h4.getAppArgs[0]! fun y =>
          mkLambdaFVars #[y] (mkApp (mkApp f y).headBeta x).headBeta
        return ← fin 6 (← prf c (← mkCongrArg fnew h4.appArg!))
      let ta ← htOf args[0]!
      let F ← img c args[2]!
      let G ← img c args[3]!
      match ta with
      | .L t =>
          let .L (.arr _ tb) ← liftEx (DT.ty c.deep F) | outside "congrFun type"
          let x ← canonInst c ta args[5]!
          let dh ← chk c args[4]! (.eq (.L (.arr t tb)) F G)
          fin 6 (.allE x (.funApp dh), .eq (.L tb) (.appL F x) (.appL G x))
      | .w =>
          let dh ← chk c args[4]! (.eq (.L .s) F G)
          let i ← img c args[5]!
          fin 6 (.allE i (.wApp dh), .eq .o (.holds F i) (.holds G i))
      | _ => outside "congrFun over Prop"
  | ``funext => do
      if k < 5 then return none
      let ta ← htOf args[0]!
      let F ← img c args[2]!
      let G ← img c args[3]!
      match ta with
      | .L t =>
          let .L (.arr _ tb) ← liftEx (DT.ty c.deep F) | outside "funext type"
          let dh ← chk c args[4]! (.all (.L t) (.eq (.L tb) (.appL (F.shift 1) (.var 0))
            (.appL (G.shift 1) (.var 0))))
          fin 5 (.funExt dh, .eq (.L (.arr t tb)) F G)
      | .w =>
          let dh ← chk c args[4]! (.all .w (.eq .o (.holds (F.shift 1) (.var 0))
            (.holds (G.shift 1) (.var 0))))
          fin 5 (.wExt dh, .eq (.L .s) F G)
      | _ => outside "funext over Prop"
  | ``propext => do
      if k < 3 then return none
      let A ← img c args[0]!
      let B ← img c args[1]!
      let I := DT.and (.imp A B) (.imp B A)
      let dh1 ← chk (c.pushHyp none A) args[2]! I
      let dh2 ← chk (c.pushHyp none B) args[2]! I
      fin 3 (.propExt A B (.impE (.andL dh1) (.hyp 0)) (.impE (.andR dh2) (.hyp 0)), .eq .o A B)
  | ``of_eq_true => do
      if k < 2 then return none
      let P ← img c args[0]!
      let dh ← chk c args[1]! (.eq .o P topD)
      fin 2 (.leib .o (.var 0) topD P (.symm dh) trivD, P)
  | ``eq_true => do
      if k < 2 then return none
      let P ← img c args[0]!
      let d2 ← chk (c.pushHyp none topD) args[1]! P
      fin 2 (.propExt P topD trivD d2, .eq .o P topD)
  | ``eq_self => do
      if k < 2 then return none
      let a ← htOf args[0]!
      let t ← img c args[1]!
      let E := DT.eq a t t
      fin 2 (.propExt E topD trivD (.refl a t), .eq .o E topD)
  | ``letFun => do
      if k < 4 then return none
      if ← isProp args[0]! then
        let (dv, A) ← prf c args[2]!
        let (d, X) ← withLocalDecl `h .default args[0]! fun h => do
          let (db, B) ← prf (c.pushHyp h.fvarId! A) (mkApp args[3]! h).headBeta
          pure (Der.impE (.impI A db) dv, B)
        fin 4 (d, X)
      else
        let (d, X) ← prf c (mkApp args[3]! args[2]!).headBeta
        fin 4 (d, X)
  | _ => return none
where
  getLevel' (ty : Expr) : TM Level := do
    let l ← getLevel ty
    pure l

end

end Programme.H

end


/-! ## Tool part `Bridge` -/
section

/-! # Thread H: the bridge from the deep image back to the module's statement

After `#deep_translate X as N`, when every sentence of `N.T` comes from a module axiom (or is
`∃x.⊤`, from the module's `Nonempty e`) and `X` has no hypotheses read as facts, the command adds

* `N.bridge<k> : ∀ w, eval S N.ax<k> () w` for each axiom sentence, proved from the module axiom,
  where `S := fullStr R existsAt P` is the full structure on the module's own frame, actuality and
  positivity;
* `N.of_deep : type_of% @X`, the module's statement re-proved from `N.valid` (run 4's
  `valid_iff`, `full_closed_resp`) and the bridges.

Both are elaborated from source text and kernel-checked.  `N.of_deep` is the image check: had the
read-back misread a definition of the module, `N.φ` evaluated in the full structure would not give
back the module's statement, and `N.of_deep` would not build.  The proofs only unfold definitions
(`bridge_unfold`: the module's definitions and `N`'s sentences), normalise the full structure
(`bridge_simp`: `eval`, carriers `True`, primitive equality is identity, `↔` as two implications) and
then apply the module axiom (resp. `N.valid`'s instance) to hypotheses. -/

open Lean Meta Elab Tactic
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX

namespace Programme.H

theorem eqT_full_iff {W D : Type} (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) :
    ∀ (t : FTy) {x y : Den W D t}, eqT (fullStr R act P) t x y ↔ x = y
  | .e, _, _ => Iff.rfl
  | .s, _, _ => Iff.rfl
  | .arr _ b, _, _ => ⟨fun h => funext fun z => (eqT_full_iff R act P b).1 (h z trivial),
      fun h z _ => (eqT_full_iff R act P b).2 (congrFun h z)⟩

theorem fullStr_A {W D : Type} (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) (t x) :
    (fullStr R act P).A t x = True := rfl
theorem fullStr_R {W D : Type} (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) :
    (fullStr R act P).R = R := rfl
theorem fullStr_act {W D : Type} (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) :
    (fullStr R act P).act = act := rfl
theorem fullStr_P {W D : Type} (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) :
    (fullStr R act P).P = P := rfl

/-- Is `n` a definition to unfold for the bridge: a non-type definition of an `OpenQuestions` or
`Notes` module, or a declaration in the namespace `base` (the translation's sentences). -/
def bridgeUnfoldable (base : Name) (n : Name) : MetaM Bool := do
  if primitiveConsts.contains n then return false
  let env ← getEnv
  let some (.defnInfo d) := env.find? n | return false
  let inScope ← if base.isPrefixOf n then pure true else
    match env.getModuleIdxFor? n with
    | some idx =>
        let m := env.header.moduleNames[idx.toNat]!
        pure (m.getRoot == `OpenQuestions || m.getRoot == `Notes)
    | none => pure false
  if !inScope then return false
  return !(← forallTelescope d.type fun _ b => pure (b.isSort && !b.isProp))

/-- `bridge_unfold N`: δ-expand (and β-reduce) the module's definitions and `N`'s sentences in the
goal and in every hypothesis. -/
elab "bridge_unfold " base:ident : tactic => do
  let base := base.getId
  let names := (← getEnv).constants.fold (init := (#[] : Array Name)) fun acc n _ => acc.push n
  let mut ok : NameSet := {}
  for n in names do
    if ← bridgeUnfoldable base n then ok := ok.insert n
  let expand (e : Expr) : MetaM Expr := do
    let e ← deltaExpand e ok.contains
    Core.betaReduce e
  liftMetaTactic fun g => do
    let g ← g.change (← expand (← g.getType))
    let mut g := g
    for d in (← g.getDecl).lctx do
      if d.isImplementationDetail then continue
      g ← g.changeLocalDecl d.fvarId (← expand d.type)
    pure [g]

macro "bridge_simp" : tactic => `(tactic| simp only [eval, Var.get, fullStr_A, fullStr_R, fullStr_act,
  fullStr_P, eqT_full_iff, true_implies, forall_const, true_and, and_true, ne_eq,
  iff_iff_implies_and_implies, Classical.not_forall, Classical.not_imp, Classical.not_not, exists_prop] at *)

end Programme.H

end


/-! ## Tool part `Struct` -/
section

/-! # Thread H: the structural image check (th's C8, run 6 `Programme.Run6.ThH5`)

`of_deep` reads `N.T` and `N.φ` in the full structure, so it fixes them only up to full-structure
equivalence (th's `full_check_blind`: a reifier conjoining v4's `phiSep` would pass).  The
structural check is stronger: `shR` is the unguarded reading of an `𝓛`-term (one Lean connective
per constructor), and the tool emits, for each axiom sentence `N.ax<k>` read off module axiom `X`
with `n` outer binders, `N.struct<k> : type_of% @X = shV R existsAt P n N.ax<k> ()`, and the same
`N.struct_φ` for the statement.  These are proved by `rfl` after δ-unfolding the module side and at
most two rewrites, each an identity of Lean propositions: `(a ↔ b) = ((a → b) ∧ (b → a))` (the
module's `Mequiv`) and `(∃ v, R w v ∧ B v) = ¬∀ v, R w v → ¬B v` (the module's `Mdia`, C5), and `(∃ x, act x w) = (∃ x, act x w ∧ True)`.
No guard erasure, no `eqT`.  An extra conjunct, a dropped guard or a swapped quantifier fails.
`N.of_struct : type_of% @X` then re-proves the module statement from `N.valid` through th's
`of_valid_full` and `shV_iff` only.  `shR`, `eval_full_eq`, `shV`, `shV_iff`, `of_valid_full`
are th's (copied, renamed into `Programme.H`). -/

open Lean Meta Elab Tactic
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX

namespace Programme.H

variable {W D : Type}

/-- The structural, unguarded reading of an `𝓛`-term (th, C8). -/
def shR (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) :
    {Γ : List FTy} → {t : FTy} → Tm Γ t → Env W D Γ → Den W D t
  | _, _, .var i, ρ => i.get ρ
  | _, _, .app F x, ρ => shR R act P F ρ (shR R act P x ρ)
  | _, _, .lam b, ρ => fun z => shR R act P b (z, ρ)
  | _, _, .top, _ => fun _ => True
  | _, _, .bot, _ => fun _ => False
  | _, _, .neg a, ρ => fun w => ¬ shR R act P a ρ w
  | _, _, .and a b, ρ => fun w => shR R act P a ρ w ∧ shR R act P b ρ w
  | _, _, .or a b, ρ => fun w => shR R act P a ρ w ∨ shR R act P b ρ w
  | _, _, .imp a b, ρ => fun w => shR R act P a ρ w → shR R act P b ρ w
  | _, _, .box a, ρ => fun w => ∀ v, R w v → shR R act P a ρ v
  | _, _, .all _ b, ρ => fun w => ∀ x, shR R act P b (x, ρ) w
  | _, _, .ex _ b, ρ => fun w => ∃ x, shR R act P b (x, ρ) w
  | _, _, .allE b, ρ => fun w => ∀ y, act y w → shR R act P b (y, ρ) w
  | _, _, .exE b, ρ => fun w => ∃ y, act y w ∧ shR R act P b (y, ρ) w
  | _, _, .eq _ x y, ρ => fun _ => shR R act P x ρ = shR R act P y ρ
  | _, _, .pos, _ => P

theorem eqT_full_iff' (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th)
    (t : FTy) (x y : Den W D t) : eqT (fullStr R act P) t x y ↔ x = y :=
  ⟨eqT_full R act P t, fun h => h ▸ eqT_refl _ t x⟩

/-- In the full structure, evaluation is the structural reading (th, C8). -/
theorem eval_full_eq (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) :
    ∀ {Γ : List FTy} {t : FTy} (φ : Tm Γ t) (ρ : Env W D Γ),
      eval (fullStr R act P) φ ρ = shR R act P φ ρ := by
  intro Γ t φ
  induction φ with
  | var i => intro ρ; rfl
  | app F x ihF ihx => intro ρ; simp only [eval, shR, ihF, ihx]
  | lam b ih => intro ρ; funext z; simp only [eval, shR, ih]
  | top => intro ρ; rfl
  | bot => intro ρ; rfl
  | neg a ih => intro ρ; funext w; simp only [eval, shR, ih]
  | and a b iha ihb => intro ρ; funext w; simp only [eval, shR, iha, ihb]
  | or a b iha ihb => intro ρ; funext w; simp only [eval, shR, iha, ihb]
  | imp a b iha ihb => intro ρ; funext w; simp only [eval, shR, iha, ihb]
  | box a ih => intro ρ; funext w; simp only [eval, shR, ih]; rfl
  | all a b ih =>
      intro ρ; funext w
      exact propext ⟨fun h x => (ih (x, ρ)) ▸ h x trivial, fun h x _ => (ih (x, ρ)) ▸ h x⟩
  | ex a b ih =>
      intro ρ; funext w
      exact propext ⟨fun ⟨x, _, hx⟩ => ⟨x, (ih (x, ρ)) ▸ hx⟩,
        fun ⟨x, hx⟩ => ⟨x, trivial, (ih (x, ρ)).symm ▸ hx⟩⟩
  | allE b ih => intro ρ; funext w; simp only [eval, shR, ih]; rfl
  | exE b ih => intro ρ; funext w; simp only [eval, shR, ih]; rfl
  | eq a x y ihx ihy =>
      intro ρ; funext w
      simp only [eval, shR, ← ihx, ← ihy]
      exact propext (eqT_full_iff' R act P a _ _)
  | pos => intro ρ; rfl

/-- Validity reading with `n` leading object quantifiers pulled out (th, C8). -/
def shV (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) :
    Nat → {Γ : List FTy} → Tm Γ .s → Env W D Γ → Prop
  | 0, _, φ, ρ => ∀ w, shR R act P φ ρ w
  | n + 1, _, .all _ b, ρ => ∀ x, shV R act P n b (x, ρ)
  | _ + 1, _, φ, ρ => ∀ w, shR R act P φ ρ w

theorem shV_iff (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) :
    ∀ (n : Nat) {Γ : List FTy} (φ : Tm Γ .s) (ρ : Env W D Γ),
      shV R act P n φ ρ ↔ ∀ w, shR R act P φ ρ w
  | 0, _, _, _ => Iff.rfl
  | n + 1, _, φ, ρ => by
      cases φ with
      | all a b =>
          simp only [shV, shR]
          exact ⟨fun h w x => (shV_iff R act P n b (x, ρ)).1 (h x) w,
                 fun h x => (shV_iff R act P n b (x, ρ)).2 fun w => h w x⟩
      | _ => simp only [shV]

/-- A `ValidV4` certificate read in the full structure, structurally (th, C8). -/
theorem of_valid_full {T : Tm [] .s → Prop} {φ : Tm [] .s} (h : ValidV4 T φ)
    (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) [Nonempty D]
    (hT : ∀ ψ, T ψ → ∀ w, shR R act P ψ () w) : ∀ w, shR R act P φ () w := by
  intro w
  have hS := (valid_iff T φ).1 h W D (fullStr R act P) inferInstance (fun _ => trivial)
    (full_closed_resp R act P).1 (full_closed_resp R act P).2.1
    (fun ψ hψ w => by rw [eval_full_eq]; exact hT ψ hψ w) w
  rwa [eval_full_eq] at hS

/-- The two rewrites allowed on the module side: identities of Lean propositions. -/
theorem iff_nf (a b : Prop) : (a ↔ b) = ((a → b) ∧ (b → a)) :=
  propext ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
theorem dia_nf (r : W → W → Prop) (w : W) (b : W → Prop) :
    (∃ v, r w v ∧ b v) = ¬ ∀ v, r w v → ¬ b v :=
  propext ⟨fun ⟨v, hv, hb⟩ h => h v hv hb,
    fun h => Classical.byContradiction fun hn => h fun v hv hb => hn ⟨v, hv, hb⟩⟩

/-- Third allowed rewrite: the reifier reads `∃ x, x @ w` as `∃ᴱ x. ⊤`; an identity of Lean propositions. -/
theorem exAct_nf {D : Type} (act : D → W → Prop) (w : W) : (∃ x, act x w) = (∃ x, act x w ∧ True) :=
  propext ⟨fun ⟨x, hx⟩ => ⟨x, hx, trivial⟩, fun ⟨x, hx, _⟩ => ⟨x, hx⟩⟩

/-- `struct_unfold`: δ-expand (and β-reduce) the module's definitions (and `N`'s statement types) on the left-hand side of an
equation goal only. -/
elab "struct_unfold " base:ident : tactic => do
  let base := base.getId
  let names := (← getEnv).constants.fold (init := (#[] : Array Name)) fun acc n _ => acc.push n
  let mut ok : NameSet := {}
  for n in names do
    if ← bridgeUnfoldable base n then ok := ok.insert n
  let ok' := ok
  liftMetaTactic fun g => do
    let ty ← instantiateMVars (← g.getType)
    let some (_, l, r) := ty.eq? | throwError "struct_unfold: not an equation"
    let l ← Core.betaReduce (← deltaExpand l ok'.contains)
    let g ← g.change (← mkEq l r)
    pure [g]

end Programme.H

end


/-! ## Tool part `Frame` -/
section

/-! # Thread H: frame hypotheses (th's C7, run 6 `Programme.Run6.ThH6`)

A statement hypothesis such as `symm : ∀ x y, x 𝗿 y → y 𝗿 x` is not an `𝓛`-sentence, but its image
is a closed HOL formula built from `rel`, world variables, connectives and world quantifiers only
(`RelOnly`).  The tool keeps such hypotheses in the hypothesis list of the derivation (weakened into
the world context) and concludes `ValidV4Fs Fs T φ`: `φ` holds in every v4 `𝓛`-general model of
`T` whose frame satisfies every `F ∈ Fs`.  `RelW`, `RelOnly`, `relOnly_o`, `frameStr`,
`FrameHolds` and the proofs of `sound_v4_wt_frames` and `of_validFs_full` are th's (`ThH6`:
`sound_v4_wt_frame`, `of_validF_full`), generalised here from one formula to a list. -/

open Lean Meta Elab Tactic
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
  Programme.«20261022-1724-ontological».ThWhole

namespace Programme.H

variable {W D D' : Type}

inductive RelW : {Γ : List HTy} → HTerm Γ .w → Prop
  | var {Γ} (v : HVar Γ .w) : RelW (.var v)

/-- Frame formulas: only world variables, `rel`, equality at `w`, connectives, world quantifiers. -/
inductive RelOnly : {Γ : List HTy} → HTerm Γ .o → Prop
  | rel {Γ} {i j : HTerm Γ .w} : RelW i → RelW j → RelOnly (.rel i j)
  | bot {Γ} : RelOnly (Γ := Γ) .bot
  | imp {Γ} {p q : HTerm Γ .o} : RelOnly p → RelOnly q → RelOnly (.imp p q)
  | and {Γ} {p q : HTerm Γ .o} : RelOnly p → RelOnly q → RelOnly (.and p q)
  | or {Γ} {p q : HTerm Γ .o} : RelOnly p → RelOnly q → RelOnly (.or p q)
  | all {Γ} {p : HTerm (.w :: Γ) .o} : RelOnly p → RelOnly (.all .w p)
  | ex {Γ} {p : HTerm (.w :: Γ) .o} : RelOnly p → RelOnly (.ex .w p)
  | eq {Γ} {s u : HTerm Γ .w} : RelW s → RelW u → RelOnly (.eq .w s u)

theorem relOnly_w {Γ} (S : Str W D) (S' : Str W D')
    (ρ : HEnv W D Γ) (ρ' : HEnv W D' Γ) (hρ : ∀ v : HVar Γ .w, ρ v = ρ' v)
    {i : HTerm Γ .w} (h : RelW i) : heval S i ρ = heval S' i ρ' := by
  cases h with
  | var v => exact hρ v

theorem cons_w {Γ} {ρ : HEnv W D Γ} {ρ' : HEnv W D' Γ} (hρ : ∀ v : HVar Γ .w, ρ v = ρ' v) (u : W) :
    ∀ v : HVar (.w :: Γ) .w, cons (a := .w) u ρ v = cons (a := .w) u ρ' v
  | .zero => rfl
  | .succ v => hρ v

/-- Frame invariance (th): a frame formula has the same truth value in two structures on one frame. -/
theorem relOnly_o (S : Str W D) (S' : Str W D') (hS : S.R = S'.R) {Γ} {φ : HTerm Γ .o}
    (h : RelOnly φ) : ∀ (ρ : HEnv W D Γ) (ρ' : HEnv W D' Γ), (∀ v : HVar Γ .w, ρ v = ρ' v) →
      (heval S φ ρ ↔ heval S' φ ρ') := by
  induction h with
  | rel hi hj =>
      intro ρ ρ' hρ
      show S.R _ _ ↔ S'.R _ _
      rw [relOnly_w S S' ρ ρ' hρ hi, relOnly_w S S' ρ ρ' hρ hj, hS]
  | bot => intro _ _ _; exact Iff.rfl
  | imp _ _ ihp ihq => intro ρ ρ' hρ; exact imp_congr (ihp ρ ρ' hρ) (ihq ρ ρ' hρ)
  | and _ _ ihp ihq => intro ρ ρ' hρ; exact and_congr (ihp ρ ρ' hρ) (ihq ρ ρ' hρ)
  | or _ _ ihp ihq => intro ρ ρ' hρ; exact or_congr (ihp ρ ρ' hρ) (ihq ρ ρ' hρ)
  | all _ ih =>
      intro ρ ρ' hρ
      show (∀ u, True → _) ↔ (∀ u, True → _)
      exact forall_congr' fun u => imp_congr Iff.rfl (ih _ _ (cons_w hρ u))
  | ex _ ih =>
      intro ρ ρ' hρ
      show (∃ u, True ∧ _) ↔ (∃ u, True ∧ _)
      exact exists_congr fun u => and_congr Iff.rfl (ih _ _ (cons_w hρ u))
  | eq hs hu =>
      intro ρ ρ' hρ
      show _ = _ ↔ _ = _
      rw [relOnly_w S S' ρ ρ' hρ hs, relOnly_w S S' ρ ρ' hρ hu]

/-- The unit structure over a frame. -/
def frameStr (R : W → W → Prop) : Str W Unit := ⟨R, fun _ _ => True, fun _ _ => True, fun _ _ => True⟩

/-- The frame semantics of a closed frame formula. -/
def FrameHolds (R : W → W → Prop) (F : HTerm [] .o) : Prop :=
  heval (frameStr R) F emptyEnv

def AllRel : List (HTerm [] .o) → Prop
  | [] => True
  | F :: Fs => RelOnly F ∧ AllRel Fs

def FramesHold (R : W → W → Prop) : List (HTerm [] .o) → Prop
  | [] => True
  | F :: Fs => FrameHolds R F ∧ FramesHold R Fs

theorem AllRel.mem : ∀ {Fs : List (HTerm [] .o)}, AllRel Fs → ∀ F ∈ Fs, RelOnly F
  | _ :: _, ⟨h, _⟩, _, .head _ => h
  | _ :: _, ⟨_, hs⟩, F, .tail _ m => AllRel.mem hs F m

theorem FramesHold.mem {R : W → W → Prop} : ∀ {Fs : List (HTerm [] .o)}, FramesHold R Fs →
    ∀ F ∈ Fs, FrameHolds R F
  | _ :: _, ⟨h, _⟩, _, .head _ => h
  | _ :: _, ⟨_, hs⟩, F, .tail _ m => FramesHold.mem hs F m

/-- `ValidV4` over the v4 `𝓛`-general models whose frame satisfies every formula of `Fs`. -/
def ValidV4Fs (Fs : List (HTerm [] .o)) (T : Tm [] .s → Prop) (φ : Tm [] .s) : Prop :=
  ∀ (W : Type) (M : VM W) (L : LGen M), Nonempty (M.C .e) → FramesHold M.R Fs →
    (∀ ψ, T ψ → ∀ w, M.pr (L.ev ψ ()) w) → ∀ w, M.pr (L.ev φ ()) w

/-- **Soundness with frame hypotheses** (th's `sound_v4_wt_frame`, for a list). -/
theorem sound_v4_wt_frames {Fs : List (HTerm [] .o)} (hF : AllRel Fs) {T : Tm [] .s → Prop}
    {φ : Tm [] .s} (d : DW T [.w] (Fs.map (wk (b := .w))) (.holds (emb nilR φ) var0)) :
    ValidV4Fs Fs T φ := by
  intro W M L hne hFr hT w
  have hS := toStr_entities M hne
  have := sound_wt (toStr M hne) hS (toStr_closed M hne L) (toStr_resp M hne)
    (fun ψ hψ v => (toStr_truth M hne L ψ v).2 (hT ψ hψ v)) d (cons (a := .w) w emptyEnv)
    (admEnv_cons (a := .w) _ (fun v => by cases v) trivial) (fun h m => by
      obtain ⟨F, hFm, rfl⟩ := List.mem_map.1 m
      rw [heval_wk]
      exact (relOnly_o (frameStr M.R) (toStr M hne) rfl (hF.mem F hFm) emptyEnv emptyEnv
        (fun v => by cases v)).1 (hFr.mem F hFm))
  simp only [heval, heval_emb _ hS] at this
  exact (toStr_truth M hne L φ w).1 this

/-- Cut for `ValidV4Fs` (the lemmas are valid on all frames). -/
theorem Good.validFs {A : Tm [] .s → Prop} {L : List (Tm [] .s)} {χ : Tm [] .s} {Fs} (g : Good A L)
    (h : ValidV4Fs Fs (fun φ => φ ∈ L) χ) : ValidV4Fs Fs A χ := by
  intro W M Lg hne hF hA
  apply h W M Lg hne hF
  clear h
  induction g with
  | nil => intro ψ hψ; cases hψ
  | axm hs _ ih =>
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hA _ hs
      · exact ih ψ hψ
  | lem hv _ ih =>
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hv W M Lg hne ih
      · exact ih ψ hψ

/-- Lemmas under frame formulas (module frame axioms such as `Rrefl`): each lemma is valid over
the sentences before it on the frames satisfying `Fs`. -/
inductive GoodF (Fs : List (HTerm [] .o)) (A : Tm [] .s → Prop) : List (Tm [] .s) → Prop
  | nil : GoodF Fs A []
  | axm {s : Tm [] .s} {L : List (Tm [] .s)} : A s → GoodF Fs A L → GoodF Fs A (s :: L)
  | lem {s : Tm [] .s} {L : List (Tm [] .s)} : ValidV4Fs Fs (fun φ => φ ∈ L) s → GoodF Fs A L →
      GoodF Fs A (s :: L)

/-- Cut for `GoodF`. -/
theorem GoodF.validFs {A : Tm [] .s → Prop} {L : List (Tm [] .s)} {χ : Tm [] .s} {Fs}
    (g : GoodF Fs A L) (h : ValidV4Fs Fs (fun φ => φ ∈ L) χ) : ValidV4Fs Fs A χ := by
  intro W M Lg hne hF hA
  apply h W M Lg hne hF
  clear h
  induction g with
  | nil => intro ψ hψ; cases hψ
  | axm hs _ ih =>
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hA _ hs
      · exact ih ψ hψ
  | lem hv _ ih =>
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hv W M Lg hne hF ih
      · exact ih ψ hψ

theorem FramesHold.of_append {R : W → W → Prop} :
    ∀ (a : List (HTerm [] .o)) {b : List (HTerm [] .o)}, FramesHold R (a ++ b) → FramesHold R b
  | [], _, h => h
  | _ :: a, _, ⟨_, h⟩ => FramesHold.of_append a h

/-- A certificate on the frames of `b` holds on the frames of `a ++ b`. -/
theorem ValidV4Fs.append {b : List (HTerm [] .o)} {T : Tm [] .s → Prop} {φ : Tm [] .s}
    (a : List (HTerm [] .o)) (h : ValidV4Fs b T φ) : ValidV4Fs (a ++ b) T φ :=
  fun W M L hne hF hT => h W M L hne (FramesHold.of_append a hF) hT

theorem AllRel.append : ∀ {a b : List (HTerm [] .o)}, AllRel a → AllRel b → AllRel (a ++ b)
  | [], _, _, hb => hb
  | _ :: _, _, ⟨h, ha⟩, hb => ⟨h, AllRel.append ha hb⟩

/-- **Image bridge with frame formulas** (th's `of_validF_full`, for a list). -/
theorem of_validFs_full {Fs : List (HTerm [] .o)} {T : Tm [] .s → Prop} {φ : Tm [] .s}
    (h : ValidV4Fs Fs T φ)
    (R : W → W → Prop) (act : D → W → Prop) (P : Den W D th) [Nonempty D] (hF : FramesHold R Fs)
    (hT : ∀ ψ, T ψ → ∀ w, shR R act P ψ () w) : ∀ w, shR R act P φ () w := by
  intro w
  have hC : Closed (fullStr R act P) := (full_closed_resp R act P).1
  have hR : Resp (fullStr R act P) := (full_closed_resp R act P).2.1
  have hE : ∀ x, (fullStr R act P).A .e x := fun _ => trivial
  have hne : Nonempty ((ofStr (fullStr R act P) hC hR).C .e) :=
    let ⟨d⟩ := (inferInstance : Nonempty D); ⟨Quotient.mk (setoidT _ .e) ⟨d, hE d⟩⟩
  have := h W _ (ofStr_lgen _ hC hR hE) hne hF
    (fun ψ hψ v => (ofStr_truth _ hC hR hE ψ v).2 (by rw [eval_full_eq]; exact hT ψ hψ v)) w
  have := (ofStr_truth _ hC hR hE φ w).1 this
  rwa [eval_full_eq] at this

/-- Prove `RelOnly F` / `RelW i` for a concrete term by its constructors. -/
partial def solveRelOnly (g : MVarId) : MetaM Unit := do
  let ctors := [``RelOnly.rel, ``RelOnly.bot, ``RelOnly.imp, ``RelOnly.and, ``RelOnly.or,
    ``RelOnly.all, ``RelOnly.ex, ``RelOnly.eq, ``RelW.var]
  for c in ctors do
    let s ← saveState
    try
      let gs ← g.apply (← mkConstWithFreshMVarLevels c)
      for g' in gs do
        unless ← g'.isAssigned do solveRelOnly g'
      return
    catch _ => s.restore
  throwError m!"not a frame formula: {← g.getType}"

/-- `frame_hold h`: prove `FrameHolds R F` from the module's hypothesis `h`: introduce the world
binders and hypotheses of `F` (by `whnf`), then `apply h` and close its premises by assumption. -/
elab "frame_hold " h:term : tactic => do
  for _ in [0:64] do
    let g ← getMainGoal
    let t ← whnf (← g.getType)
    unless t.isForall do break
    let g ← g.change t
    let (_, g) ← g.intro1
    replaceMainGoal [g]
  evalTactic (← `(tactic| first | exact $h | (apply $h <;> assumption)))

end Programme.H

end


/-! ## Tool part `Cmd` -/
section

/-! # Thread H: the command `#deep_translate thm as Name` -/

open Lean Meta Elab Command Term
open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
  Programme.«20261022-1724-ontological».ThWhole

namespace Programme.H

partial def Der.size : Der → Nat
  | .hyp _ | .ax .. | .refl .. | .betaL .. => 1
  | .impI _ d | .byContra _ d | .andL d | .andR d | .orL _ d | .orR _ d | .allI _ d | .allE _ d
  | .exI _ _ _ d | .symm d | .funExt d | .funApp d | .wExt d | .wApp d | .betaWI _ _ d
  | .betaWE d => 1 + d.size
  | .impE d1 d2 | .andI d1 d2 | .trans d1 d2 | .leib _ _ _ _ d1 d2 | .propExt _ _ d1 d2
  | .exE d1 d2 _ => 1 + d1.size + d2.size
  | .orE d d1 d2 => 1 + d.size + d1.size + d2.size

/-- One goal of a statement: hypotheses read as facts, `𝓛`/world binders, the proof. -/
structure Goal where
  suffix : String
  ty : Expr
  proof : Expr

/-- Split `↔`/`∧` statements into goals. -/
partial def splitGoals (suffix : String) (ty prf : Expr) : MetaM (Array Goal) := do
  let ty' ← whnfR ty
  match ty'.getAppFn, ty'.getAppArgs with
  | .const ``Iff _, #[a, b] =>
      -- a proof `Iff.intro p q` is split into `p` and `q` (each direction from its own axioms)
      let (p1, p2) := if prf.isAppOfArity ``Iff.intro 4 then (prf.appFn!.appArg!, prf.appArg!)
        else (mkApp3 (mkConst ``Iff.mp) a b prf, mkApp3 (mkConst ``Iff.mpr) a b prf)
      let g1 ← splitGoals (suffix ++ "mp") (← mkArrow a b) p1
      let g2 ← splitGoals (suffix ++ "mpr") (← mkArrow b a) p2
      pure (g1 ++ g2)
  | .const ``And _, #[a, b] =>
      let (p1, p2) := if prf.isAppOfArity ``And.intro 4 then (prf.appFn!.appArg!, prf.appArg!)
        else (mkApp3 (mkConst ``And.left) a b prf, mkApp3 (mkConst ``And.right) a b prf)
      let g1 ← splitGoals (suffix ++ "left") a p1
      let g2 ← splitGoals (suffix ++ "right") b p2
      pure (g1 ++ g2)
  | _, _ => pure #[{ suffix, ty, proof := prf }]

structure Result where
  sentences : Array LT
  names : Array String
  phi : LT
  der : Der
  target : DT
  lemmas : Array (Nat × Name × Der × DT)
  facts : Array String := #[]
  factTys : Std.HashMap Nat (Expr × Expr) := {}
  frames : List (Nat × DT) := []
  worldFree : Bool := false
  /-- Module frame axioms, in the order pushed (the derivation's `hs` ends with their reverse). -/
  modFrames : List (Name × DT) := []

deriving instance Inhabited for Result

/-- The axioms a proof depends on (through the definitions and theorems outside `Init`/`Lean`/`Std`). -/
partial def usedAxioms (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let skip (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some mi =>
        let m := env.header.moduleNames[mi.toNat]!
        (`Init).isPrefixOf m || (`Lean).isPrefixOf m || (`Std).isPrefixOf m
    | none => false
  let mut todo := e.getUsedConstants.toList
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n || skip n then continue
    seen := seen.insert n
    match env.find? n with
    | some (.axiomInfo _) => out := out.push n
    | some (.thmInfo t) => todo := t.value.getUsedConstants.toList ++ t.type.getUsedConstants.toList ++ todo
    | some (.defnInfo d) => todo := d.value.getUsedConstants.toList ++ todo
    | _ => pure ()
  pure out

/-- Module frame axioms used by a proof: axioms whose statement is a closed frame formula (`Rrefl`,
`Rtrans`).  They become hypotheses of every derivation (C7 for module axioms). -/
def moduleFrames (pf : Expr) : TM (Array (Name × Expr × DT)) := do
  let mut out := #[]
  for n in ← usedAxioms pf do
    let ty := (← getConstInfo n).type
    unless ← isProp ty do continue
    let F? ← try some <$> img {} ty catch _ => pure none
    if let some F := F? then
      if DT.frameOK F 0 then out := out.push (n, ty, F)
  pure out

/-- Translate one goal: the sentences of `T` (axioms and lemmas), `φ`, the derivation. -/
partial def translateGoal (g : Goal) (withNE : Bool) : TM Result := do
  let mfs ← moduleFrames g.proof
  withLocalDeclsD (mfs.map fun (n, ty, _) => (n.appendAfter "_frame", fun _ => pure ty)) fun fvs => do
  modify fun s => { s with modFrames := (mfs.zip fvs).map fun ((n, _, F), fv) => (n, fv.fvarId!, F) }
  -- hypotheses: leading binders whose type is a `Prop` (facts / schemas)
  let rec peelFacts (ty prf : Expr) (facts : Array FactVar) (k : Array FactVar → Expr → TM Result) :
      TM Result := do
    let ty' ← whnfR ty
    match ty' with
    | .forallE n dom body bi =>
        if (← isProp dom) then
          withLocalDecl n bi dom fun h => do
            peelFacts (body.instantiate1 h) (mkApp prf h)
              (facts.push { fvar := h.fvarId!, name := n.toString }) k
        else k facts ty
    | _ => k facts ty
  peelFacts g.ty g.proof #[] fun facts goalTy => do
    let pf := mkAppN g.proof (facts.map (fun (f : FactVar) => mkFVar f.fvar))
    let (φ, d, target) ← goalCore facts goalTy pf withNE
    let st ← get
    pure { sentences := st.sentences, names := st.sentenceNames, phi := φ, der := d, target,
           lemmas := st.lemmas, facts := facts.map (·.name), factTys := st.factTys,
           frames := st.frames, worldFree := st.lastWorldFree,
           modFrames := st.modFrames.toList.map fun (n, _, F) => (n, F) }

def logF (s : String) : IO Unit := do
  if let some f ← IO.getEnv "DEEP_LOG" then
    let h ← IO.FS.Handle.mk f .append
    h.putStrLn s
    h.flush

def addDef (n : Name) (ty v : Expr) : CoreM Unit := do
  let dv : DefinitionVal := { name := n, levelParams := [], type := ty, value := v,
                              hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  addDecl (Declaration.defnDecl dv)

def addThm (n : Name) (ty v : Expr) : CoreM Unit := do
  let tv : TheoremVal := { name := n, levelParams := [], type := ty, value := v }
  addDecl (Declaration.thmDecl tv)

/-- The tactic script for `of_deep`: split `↔`/`∧` as `splitGoals` does, leaves from `leaves`. -/
partial def bridgeScript (leaves : Std.HashMap String String) (suffix : String) (ty : Expr) :
    MetaM (Option String) := do
  let ty' ← whnfR ty
  let indent (s : String) : String := "\n".intercalate ((s.splitOn "\n").map ("  " ++ ·))
  let two (a b : String) (ta tb : Expr) : MetaM (Option String) := do
    let some s1 ← bridgeScript leaves (suffix ++ a) ta | return none
    let some s2 ← bridgeScript leaves (suffix ++ b) tb | return none
    return some s!"constructor\n· {(indent s1).drop 2}\n· {(indent s2).drop 2}"
  match ty'.getAppFn, ty'.getAppArgs with
  | .const ``Iff _, #[a, b] => two "mp" "mpr" (← mkArrow a b) (← mkArrow b a)
  | .const ``And _, #[a, b] => two "left" "right" a b
  | _, _ => return leaves[suffix]?

/-! Term-mode proofs, inside the fragment, of core simp lemmas whose core proofs leave it
(`decide`, `funext` at `Prop → Prop`); the tool uses them in place of the core lemma. -/
namespace Rw
theorem not_true_eq_false : (¬True) = False := propext ⟨fun h => h trivial, False.elim⟩
theorem not_false_eq_true : (¬False) = True := propext ⟨fun _ => trivial, fun _ h => h⟩
example : type_of% @not_true_eq_false = type_of% @_root_.not_true_eq_false := rfl
example : type_of% @not_false_eq_true = type_of% @_root_.not_false_eq_true := rfl
end Rw

def builtinRepl : List (Name × Name) :=
  [(``_root_.not_true_eq_false, ``Rw.not_true_eq_false),
   (``_root_.not_false_eq_true, ``Rw.not_false_eq_true)]

/-- Give every node of a generated command the position of the `#deep_translate` command, so
that a failing bridge is reported there. -/
partial def relocate (info : SourceInfo) : Syntax → Syntax
  | .node _ k args => .node info k (args.map (relocate info))
  | .atom _ v => .atom info v
  | .ident _ raw v pre => .ident info raw v pre
  | .missing => .missing

/-- The number of leading object binders of a validity statement (after `whnf`, up to the world
binder): the `n` of `shV n`. -/
partial def nBindersM (e : Expr) : MetaM Nat := do
  let e ← whnf e
  match e with
  | .forallE n d b bi =>
      if isWorldTy (← whnfR d) then return 0
      withLocalDecl n bi d fun x => do return 1 + (← nBindersM (b.instantiate1 x))
  | _ => return 0

syntax (name := deepTranslate) "#deep_translate " ident " as " ident (" replacing " ident " by " ident)* : command

@[command_elab deepTranslate] def elabDeepTranslate : CommandElab := fun stx => do
  let src := stx[1]
  let dst := stx[3].getId
  let replStx : Array Syntax := stx[4].getArgs
  let bridges ← liftTermElabM do
    let mut bridges : Array String := #[]
    let mut repl : List (Name × Name) := builtinRepl
    for r in replStx do
      let a ← realizeGlobalConstNoOverloadWithInfo r[1]
      let b ← realizeGlobalConstNoOverloadWithInfo r[3]
      unless ← isDefEq (← getConstInfo a).type (← getConstInfo b).type do
        throwError m!"replacement {b} does not have the statement of {a}"
      repl := (a, b) :: repl
    let srcName ← realizeGlobalConstNoOverloadWithInfo src
    let info ← getConstInfo srcName
    let val ← match info with
      | .thmInfo t => pure t.value
      | .defnInfo d => pure d.value
      | _ => throwError "{srcName} has no proof term"
    let goals ← splitGoals "" info.type val
    let mut leaves : Std.HashMap String String := {}
    for g in goals do
      let base := if g.suffix == "" then dst else dst ++ Name.mkSimple g.suffix
      let r ← try (translateGoal g false).run' { replace := repl } catch ex =>
        if (← ex.toMessageData.toString).startsWith "[deep_translate] needs-nonempty" then
          (translateGoal g true).run' { replace := repl }
        else throw ex
      logF (s!"[deep] {← IO.monoMsNow} translated: {r.der.size} rules, {r.sentences.size} sentences")
      -- declarations: the sentences
      let sentTy := mkApp2 (mkConst ``Tm) (mkLCtx []) (mkFTy .s)
      let sentListTy := mkApp (mkConst ``List [Level.zero]) sentTy
      let mut sentConsts : Array Expr := #[]
      for k in [0:r.sentences.size] do
        let nm := base ++ Name.mkSimple s!"ax{k}"
        let some s := r.sentences[k]? | unreachable!
        let e ← match mkTm [] s with | .ok e => pure e | .error m => throwError m
        addDef nm sentTy e
        sentConsts := sentConsts.push (mkConst nm)
      let phiE ← match mkTm [] r.phi with | .ok e => pure e | .error m => throwError m
      addDef (base ++ `φ) sentTy phiE
      let memPred (lst : Expr) : MetaM Expr := withLocalDecl `φ .default sentTy fun x => do
        mkLambdaFVars #[x] (mkApp5 (mkConst ``Membership.mem [Level.zero, Level.zero]) sentTy
          sentListTy (mkApp (mkConst ``List.instMembership [Level.zero]) sentTy) lst x)
      -- the prefix theories: `Tpre j` = sentences `j-1, …, 0` (newest first)
      let preList (j : Nat) : Expr := mkListE sentTy (sentConsts.extract 0 j).toList.reverse
      let dwVal ← instantiateValueLevelParams (← getConstInfo ``DW) []
      let wCtx := mkCtx [.w]
      let dwTy (TE : Expr) (sE : Expr) : Expr := mkAppN (mkConst ``DW) #[TE, wCtx,
        mkListE (hTermTy wCtx) [],
        mkApp3 (mkConst ``HTerm.holds) wCtx
          (mkApp5 (mkConst ``emb) (mkLCtx []) wCtx (mkFTy .s) (mkApp (mkConst ``nilR) wCtx) sE)
          (mkApp2 (mkConst ``var0) (mkHTy .w) (mkListE (mkConst ``HTy) []))]
      let mut cache : EmitCache := {}
      let emitAt (TName : Name) (j : Nat) (d : Der) (tgt : DT) (cache : EmitCache) (hs : List DT := []) :
          TermElabM (Expr × EmitCache) := do
        let dwApp := (mkApp dwVal (mkConst TName)).headBeta
        let env : EmitEnv := { T := mkConst TName, sentences := r.sentences.extract 0 j,
                               sentenceExprs := sentConsts.extract 0 j,
                               ok := dwApp.getAppArgs[1]!, okL := dwApp.getAppArgs[2]! }
        let ((pf, concl), cache') ← ((emit [.w] hs d).run env).run cache
        unless concl == tgt do throwError m!"conclusion mismatch: {concl} vs {tgt}"
        pure (pf, cache')
      -- frame formulas (C7): closed images, `AllRel` proved constructor by constructor
      let hT0 := mkApp2 (mkConst ``HTerm) (mkCtx []) (mkHTy .o)
      let defFs (nm : Name) (L : List DT) : TermElabM Unit := do
        let envF : EmitEnv := { T := mkConst (base ++ `Tfull), sentences := #[], sentenceExprs := #[],
                                ok := .bvar 0, okL := .bvar 0 }
        let (FsL, _) ← ((L.mapM fun F => tmC [] F).run envF).run {}
        addDef nm (mkApp (mkConst ``List [Level.zero]) hT0) (mkListE hT0 FsL)
        let mut okE : Expr := mkConst ``True.intro
        let mut okTy : Expr := mkConst ``True
        for F in FsL.reverse do
          let goalTy := mkApp2 (mkConst ``RelOnly) (mkCtx []) F
          let g ← mkFreshExprMVar goalTy
          solveRelOnly g.mvarId!
          let p ← instantiateMVars g
          okE := mkApp4 (mkConst ``And.intro) goalTy okTy p okE
          okTy := mkApp2 (mkConst ``And) goalTy okTy
        addThm (nm.appendAfter "_ok") (mkApp (mkConst ``AllRel) (mkConst nm)) okE
      let wkFn ← withLocalDecl `t .default hT0 fun t => do
        mkLambdaFVars #[t] (mkApp4 (mkConst ``wk) (mkCtx []) (mkHTy .o) (mkHTy .w) t)
      let hsOf (nm : Name) : Expr := mkApp4 (mkConst ``List.map [Level.zero, Level.zero]) hT0
          (mkApp2 (mkConst ``HTerm) (mkCtx [.w]) (mkHTy .o)) wkFn (mkConst nm)
      let dwTyH (TE hsE sE : Expr) : Expr := mkAppN (mkConst ``DW) #[TE, wCtx, hsE,
          mkApp3 (mkConst ``HTerm.holds) wCtx
            (mkApp5 (mkConst ``emb) (mkLCtx []) wCtx (mkFTy .s) (mkApp (mkConst ``nilR) wCtx) sE)
            (mkApp2 (mkConst ``var0) (mkHTy .w) (mkListE (mkConst ``HTy) []))]
      let mfRev := r.modFrames.reverse.map (·.2)
      let hasMod := !mfRev.isEmpty
      let FsMName := base ++ `FsM
      if hasMod then defFs FsMName mfRev
      -- lemmas, each from the sentences before it
      let mut lemValid : Std.HashMap Nat Expr := {}
      for (j, ln, d, tgt) in r.lemmas do
        let TName := base ++ Name.mkSimple s!"T{j}"
        addDef TName (← mkArrow sentTy (mkSort Level.zero)) (← memPred (preList j))
        let (pf, cache') ← emitAt TName j d tgt cache mfRev
        cache := cache'
        let lname := base ++ Name.mkSimple s!"lem{j}"
        let vname := base ++ Name.mkSimple s!"lem{j}_valid"
        if hasMod then
          addThm lname (dwTyH (mkConst TName) (hsOf FsMName) sentConsts[j]!) pf
          addThm vname (mkApp3 (mkConst ``ValidV4Fs) (mkConst FsMName) (mkConst TName) sentConsts[j]!)
            (mkAppN (mkConst ``sound_v4_wt_frames) #[mkConst FsMName, mkConst (FsMName.appendAfter "_ok"),
              mkConst TName, sentConsts[j]!, mkConst lname])
        else
          addThm lname (dwTy (mkConst TName) sentConsts[j]!) pf
          addThm vname (mkApp2 (mkConst ``ValidV4) (mkConst TName) sentConsts[j]!)
            (mkApp3 (mkConst ``sound_v4_wt) (mkConst TName) sentConsts[j]! (mkConst lname))
        lemValid := lemValid.insert j (mkConst vname)
        logF s!"[deep] {← IO.monoMsNow} lemma {j} ({ln}) emitted"
      -- the main derivation, from all sentences
      let n := r.sentences.size
      let TfullName := base ++ `Tfull
      addDef TfullName (← mkArrow sentTy (mkSort Level.zero)) (← memPred (preList n))
      let frameHs := r.frames.map (·.2) ++ mfRev
      let (pf, _) ← emitAt TfullName n r.der r.target cache frameHs
      let hasFrames := !frameHs.isEmpty
      if hasMod && !r.frames.isEmpty then defFs (base ++ `FsS) (r.frames.map (·.2))
      if hasFrames then
        defFs (base ++ `Fs) frameHs
        addThm (base ++ `deep) (dwTyH (mkConst TfullName) (hsOf (base ++ `Fs)) (mkConst (base ++ `φ))) pf
      else
        addThm (base ++ `deep) (dwTy (mkConst TfullName) (mkConst (base ++ `φ))) pf
      logF (s!"[deep] {← IO.monoMsNow} main kernel-checked")
      -- `T`: the axioms (non-lemma sentences); the lemmas are cut by `Good.valid`
      let axIdx := (List.range n).filter fun j => !lemValid.contains j
      let axList := mkListE sentTy (axIdx.map fun j => sentConsts[j]!)
      let TName := base ++ `T
      addDef TName (← mkArrow sentTy (mkSort Level.zero)) (← memPred axList)
      let mut good : Expr := if hasMod then mkApp2 (mkConst ``GoodF.nil) (mkConst (base ++ `Fs)) (mkConst TName)
        else mkApp (mkConst ``Good.nil) (mkConst TName)
      for j in [0:n] do
        let L := preList j
        let sE := sentConsts[j]!
        match lemValid[j]? with
        | some v =>
            if hasMod then
              let v := if r.frames.isEmpty then v
                else mkAppN (mkConst ``ValidV4Fs.append) #[mkConst FsMName, mkConst (base ++ Name.mkSimple s!"T{j}"),
                  sE, mkConst (base ++ `FsS), v]
              good := mkAppN (mkConst ``GoodF.lem) #[mkConst (base ++ `Fs), mkConst TName, sE, L, v, good]
            else good := mkAppN (mkConst ``Good.lem) #[mkConst TName, sE, L, v, good]
        | none =>
            let some pos := axIdx.idxOf? j | unreachable!
            let mp ← liftM (m := TermElabM) <| match memProof sentTy (axIdx.map fun j => sentConsts[j]!) pos with
              | .ok e => pure e | .error m => throwError m
            good := if hasMod then mkAppN (mkConst ``GoodF.axm) #[mkConst (base ++ `Fs), mkConst TName, sE, L, mp, good]
              else mkAppN (mkConst ``Good.axm) #[mkConst TName, sE, L, mp, good]
      if hasMod then
        addThm (base ++ `good) (mkApp3 (mkConst ``GoodF) (mkConst (base ++ `Fs)) (mkConst TName) (preList n)) good
        let FsC : Expr := Lean.mkConst (base ++ `Fs)
        addThm (base ++ `validF) (mkApp3 (mkConst ``ValidV4Fs) FsC (mkConst TName) (mkConst (base ++ `φ)))
          (mkAppN (mkConst ``GoodF.validFs) #[mkConst TName, preList n, mkConst (base ++ `φ), FsC,
            mkConst (base ++ `good),
            mkAppN (mkConst ``sound_v4_wt_frames) #[FsC, mkConst (base ++ `Fs_ok), mkConst TfullName,
              mkConst (base ++ `φ), mkConst (base ++ `deep)]])
      if !hasMod then
       addThm (base ++ `good) (mkApp2 (mkConst ``Good) (mkConst TName) (preList n)) good
       if hasFrames then
         let FsC : Expr := Lean.mkConst (base ++ `Fs)
         addThm (base ++ `validF) (mkApp3 (mkConst ``ValidV4Fs) FsC (mkConst TName) (mkConst (base ++ `φ)))
           (mkAppN (mkConst ``Good.validFs) #[mkConst TName, preList n, mkConst (base ++ `φ), FsC,
             mkConst (base ++ `good),
             mkAppN (mkConst ``sound_v4_wt_frames) #[FsC, mkConst (base ++ `Fs_ok), mkConst TfullName,
               mkConst (base ++ `φ), mkConst (base ++ `deep)]])
       else
         addThm (base ++ `valid) (mkApp2 (mkConst ``ValidV4) (mkConst TName) (mkConst (base ++ `φ)))
           (mkAppN (mkConst ``Good.valid) #[mkConst TName, preList n, mkConst (base ++ `φ),
             mkConst (base ++ `good),
             mkApp3 (mkConst ``sound_v4_wt) (mkConst TfullName) (mkConst (base ++ `φ)) (mkConst (base ++ `deep))])
      let total := r.lemmas.foldl (fun acc (_, _, d, _) => acc + d.size) r.der.size
      let mut msg := m!"{base}: φ = {r.phi.toStr}\n  derivation: {r.der.size} rule applications, {r.lemmas.size} lemmas, {total} in all"
      for k in [0:r.sentences.size] do
        msg := msg ++ m!"\n  [{k}] ({r.names[k]!}) = {r.sentences[k]!.toStr}"
      logInfo msg
      -- the bridge back to the module's statement (see `Bridge`): every axiom sentence comes
      -- from a module axiom, from `NonEmpty`, or from a hypothesis of the statement (a fact)
      let env ← getEnv
      let factIdx (nm : String) : Option Nat :=
        let nm' := if nm.endsWith " (instance)" then String.ofList (nm.toList.take (nm.length - 11)) else nm
        r.facts.findIdx? (· == nm')
      let axSrc : List (Nat × Option Name × Option Nat) ← axIdx.mapM fun j => do
        let nm := r.names[j]!
        if nm == "NonEmpty" then return (j, none, none)
        if let some k := factIdx nm then return (j, none, some k)
        let c := nm.toName
        match env.find? c with
        | some (.axiomInfo _) => return (j, some c, none)
        | _ => return (j, some Name.anonymous, none)
      if axSrc.all (fun (_, c, _) => c != some Name.anonymous) then
        let S := "(fullStr _root_.R _root_.existsAt _root_.P)"
        let opn := "open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX Programme.H in\n"
        let mut cases := ""
        for (j, c, f) in axSrc do
          let ax := s!"{base ++ Name.mkSimple s!"ax{j}"}"
          let stmt := s!"∀ w, eval {S} {ax} () w"
          match c, f with
          | some c, _ =>
              let body := s!"  suffices H : type_of% @_root_.{c} → {stmt} from H @_root_.{c}\n  bridge_unfold {base}\n  try bridge_simp\n  first | done | (intro h; intros; apply h <;> assumption)"
              bridges := bridges.push (opn ++ s!"theorem {base ++ Name.mkSimple s!"bridge{j}"} : {stmt} := by\n{body}")
              cases := cases ++ s!"\n      · exact {base ++ Name.mkSimple s!"bridge{j}"}"
          | none, some k =>
              cases := cases ++ s!"\n      · bridge_unfold {base}\n        try bridge_simp\n        first | done | (intros; apply hf{k} <;> assumption)"
          | none, none =>
              let body := s!"  bridge_unfold {base}\n  try bridge_simp\n  first | done | exact ⟨Classical.ofNonempty, trivial⟩ | exact fun _ => ⟨Classical.ofNonempty, trivial⟩"
              bridges := bridges.push (opn ++ s!"theorem {base ++ Name.mkSimple s!"bridge{j}"} : {stmt} := by\n{body}")
              cases := cases ++ s!"\n      · exact {base ++ Name.mkSimple s!"bridge{j}"}"
        -- the structural image check (th's C8): `type_of% @X = shV .. n N.ax<k> ()` by `rfl`
        let shVs := "shV _root_.R _root_.existsAt _root_.P"
        let structTac := s!"  struct_unfold {base}\n  first\n  | rfl\n  | (simp only [Programme.H.iff_nf, Programme.H.dia_nf _root_.R, Programme.H.exAct_nf _root_.existsAt]; rfl)"

        let mut scases := ""
        let mut structOk := g.suffix == ""
        for (j, c, f) in axSrc do
          let ax := s!"{base ++ Name.mkSimple s!"ax{j}"}"
          let sn := base ++ Name.mkSimple s!"struct{j}"
          match c, f with
          | some c, _ =>
              let nb ← nBindersM (← getConstInfo c).type
              bridges := bridges.push (opn ++ s!"theorem {sn} : type_of% @_root_.{c} = {shVs} {nb} {ax} () := by\n{structTac}")
              scases := scases ++ s!"\n  · exact (shV_iff _root_.R _root_.existsAt _root_.P {nb} _ _).1 (cast {sn} @_root_.{c})"
          | none, none =>
              bridges := bridges.push (opn ++ s!"theorem {sn} : (∀ _ : _root_.i, ∃ _ : _root_.e, True) = {shVs} 0 {ax} () := rfl")
              scases := scases ++ s!"\n  · exact (shV_iff _root_.R _root_.existsAt _root_.P 0 _ _).1 (cast {sn} (fun _ => ⟨Classical.ofNonempty, trivial⟩))"
          | none, some k =>
              match r.factTys[j]? with
              | some (ty, fn) =>
                  let tn := base ++ Name.mkSimple s!"factTy{j}"
                  addDef tn (mkSort Level.zero) ty
                  let fnTy ← inferType fn
                  addDef (base ++ Name.mkSimple s!"factInst{j}") (.forallE `h fnTy.bindingDomain! (mkConst tn) .default) fn
                  let nb ← nBindersM ty
                  bridges := bridges.push (opn ++ s!"theorem {sn} : {tn} = {shVs} {nb} {ax} () := by\n{structTac}")
                  scases := scases ++ s!"\n  · exact (shV_iff _root_.R _root_.existsAt _root_.P {nb} _ _).1 (cast {sn} ({base ++ Name.mkSimple s!"factInst{j}"} hf{k}))"
              | none => structOk := false
        -- the statement after its hypotheses (non-dependent arrows only)
        let mut stmtBody := info.type
        for _ in [0:r.facts.size] do
          if stmtBody.isForall then stmtBody := stmtBody.bindingBody! else structOk := false
        if stmtBody.hasLooseBVars then structOk := false
        if structOk then
          let nb ← nBindersM stmtBody
          let intros := if r.facts.size == 0 then "" else
            "intro " ++ " ".intercalate ((List.range r.facts.size).map fun k => s!"hf{k}") ++ "\n  "
          let sφ := base ++ `struct_φ
          let lhs ← if r.facts.size == 0 then pure s!"type_of% @_root_.{srcName}" else do
            addDef (base ++ `goalTy) (mkSort Level.zero) stmtBody
            pure s!"{base ++ `goalTy}"
          let lhs := if r.worldFree then s!"(∀ _ : _root_.i, {lhs})" else lhs
          bridges := bridges.push (opn ++ s!"theorem {sφ} : {lhs} = {shVs} {nb} {base ++ `φ} () := by\n{structTac}")
          let memS := if axSrc.length == 0 then "  cases hψ"
            else s!"  simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ\n  rcases hψ with {" | ".intercalate (axSrc.map fun _ => "rfl")}{scases}"
          let certify := if r.frames.isEmpty && r.modFrames.isEmpty then s!"of_valid_full {base ++ `valid} _root_.R _root_.existsAt _root_.P ?_"
            else
              let labels := r.frames.map (fun (k, _) => s!"hf{k}") ++ r.modFrames.reverse.map (fun (n, _) => s!"@_root_.{n}")
              let hold := labels.foldr (fun l acc => s!"(And.intro (by frame_hold {l}) {acc})") "trivial"
              s!"of_validFs_full {base ++ `validF} _root_.R _root_.existsAt _root_.P {hold} ?_"
          logInfo m!"{dst}: of_struct emitted"
          bridges := bridges.push (opn ++ s!"/-- The module's statement from the deep certificate through the structural checks only (no `bridge_simp`). -/\ntheorem {dst ++ `of_struct} : type_of% @_root_.{srcName} := no_implicit_lambda% (by\n  {intros}{if r.worldFree then "refine (fun H => H Classical.ofNonempty) (@Eq.mpr _ _ " ++ toString sφ ++ " ?_)" else "refine @Eq.mpr _ _ " ++ toString sφ ++ " ?_"}\n  refine (shV_iff _root_.R _root_.existsAt _root_.P {nb} _ _).2 ({certify})\n  intro ψ hψ\n  delta {base ++ `T} at hψ\n{memS})")
        let pat := " | ".intercalate (axSrc.map fun _ => "rfl")
        let memT := if axSrc.length == 0 then "      cases hψ"
          else s!"      simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ\n      rcases hψ with {pat}{cases}"
        let intros := if r.facts.size == 0 then "" else
          "intro " ++ " ".intercalate ((List.range r.facts.size).map fun k => s!"hf{k}") ++ "\n"
        if r.frames.isEmpty && r.modFrames.isEmpty then
         leaves := leaves.insert g.suffix (intros ++ s!"have hfc := full_closed_resp _root_.R _root_.existsAt _root_.P
have hd := (valid_iff {base ++ `T} {base ++ `φ}).1 {base ++ `valid} _root_.i _root_.e {S} inferInstance hfc.2.2 hfc.1 hfc.2.1
  (fun ψ hψ => by
      delta {base ++ `T} at hψ
{memT})
clear hfc
revert hd
bridge_unfold {base}
try bridge_simp
first | done | trivial | (intro hd; intros; first | trivial | (apply hd <;> assumption) | exact hd _)")
      else
        logInfo m!"{base}: no bridge (a sentence not from a module axiom or hypothesis)"
    -- `dst.of_deep : type_of% @X`, split as the goals were
    let implicitHead := info.type.isForall && !info.type.bindingInfo!.isExplicit
    if implicitHead then logInfo m!"{dst}: no of_deep (implicit leading binder); of_struct is the image check"
    if let some sc ← (if implicitHead then pure none else bridgeScript leaves "" info.type) then
      let opn := "open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX Programme.H in\n"
      let ind := "\n".intercalate ((sc.splitOn "\n").map ("  " ++ ·))
      bridges := bridges.push (opn ++ s!"/-- The module's statement, re-proved from the deep certificates read in the full structure on the module's postulates: the image check. -/\ntheorem {dst ++ `of_deep} : type_of% @_root_.{srcName} := no_implicit_lambda% (by\n{ind})")
    pure bridges
  for b in bridges do
    match Parser.runParserCategory (← getEnv) `command b with
    | .ok bstx => withRef stx <| elabCommand (relocate (SourceInfo.fromRef stx) bstx)
    | .error err => throwError m!"[deep_translate] bridge does not parse: {err}\n{b}"

end Programme.H

end


open Programme.«20261022-1724-ontological».Run3.LX Programme.«20261022-1724-ontological».Run3.HOLX
  Programme.«20261022-1724-ontological».ThWhole

namespace Programme.Run6.H.Eucl
/-- th's ThH10.Th3_eucl (P95), proof verbatim. -/
theorem Th3_eucl (eucl : ∀ x y z, x 𝗿 y → x 𝗿 z → y 𝗿 z) :
    ⌊◇(∃ᴱ x, G x) →ᵐ □(∃ᴱ y, G y)⌋ := by
  have h1 : ⌊(∃ᴱ x, G x) →ᵐ □(∃ᴱ y, G y)⌋ := fun _ ⟨x, _, hG⟩ => Th2 x _ hG
  intro w ⟨v, hv, hex⟩ u hu
  exact h1 v hex u (eucl w v u hv hu)
/-- Laundering probe: the existential witness mentions `existsAt` and the nominal `w`. -/
theorem actNom : ⌊(∀ᵐ φ : e → σ, P φ) →ᵐ (∃ᵐ φ : e → σ, P φ)⌋ := fun w h =>
  ⟨fun z u => existsAt z u ∧ u = w, h _⟩
end Programme.Run6.H.Eucl
open Programme.Run6.H.Eucl

set_option maxHeartbeats 0 in
#deep_translate Th3_eucl as Programme.Run6.H.Th3E

/-- The frame formula read off `eucl` is `∀x y z. R x y → R x z → R y z`. -/
example : Programme.Run6.H.Th3E.Fs = [.all .w (.all .w (.all .w (.imp (.rel (.var (.succ (.succ .zero))) (.var (.succ .zero)))
    (.imp (.rel (.var (.succ (.succ .zero))) (.var .zero)) (.rel (.var (.succ .zero)) (.var .zero))))))] := rfl

/--
error: [deep_translate] whole-term condition violated: instance fun z u =>
  z @ᵐ u ∧ u = w is not a term of 𝓛 (image (λ:e. (λw. (act #1 #0 ∧ (#0 =[w] #2)))))
  in the step: Exists.intro (fun z u => z @ᵐ u ∧ u = w) (h fun z u => z @ᵐ u ∧ u = w)
  inside the proof of: []
-/
#guard_msgs in
#deep_translate actNom as Programme.Run6.H.ActNom

#print axioms Programme.Run6.H.Th3E.validF
#print axioms Programme.Run6.H.Th3E.of_struct
