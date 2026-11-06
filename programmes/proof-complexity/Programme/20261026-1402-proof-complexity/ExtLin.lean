import Programme.«20261026-1402-proof-complexity».ExtLemma

/-!
# Linearity of `Bal` and EXT from a spanning set; Lean statement of S2 (K19)

`Bal p n k y f e` is linear in the pair `(y, f)`, ignores multiples of `p` in `f`, and only reads
`f` at canonical `e`-matchings. So the set of `f` that have an extension `y` at level `e` is closed
under the span operations of `InSpan` (`ext_of_span`): to prove `EXT p n k d` it suffices to show
that every level-`(d-1)`-balanced `f` lies in the span of functions with known extensions
(`EXT_of_span`). This is the composition step of th's K14 route (L2 + L3 + L4 by linearity).

`S2 p n k`: every `f` on 2-matchings with zero edge links (`Bal p n k f 0 1`) is in the span of
products `r ⊗ r'` of disjoint `2 × 2` rectangles (`rprod`). This is the Lean statement of K19
against `Work.ExtLemma`; it is stated here, not proved.
-/

namespace Programme.«20261026-1402-proof-complexity».ExtLin

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr)
open Programme.«20261026-1402-proof-complexity».ExtLemma

variable {p n k : Nat}

theorem lineS_add (f f' : List Nat → Int) (g : List Nat) (v : Nat → Nat) (M : Nat) :
    lineS n k (fun h => f h + f' h) g v M = lineS n k f g v M + lineS n k f' g v M := by
  unfold lineS; rw [← rsum_add]; apply rsum_congr; intro t _; split <;> simp

theorem rsum_mul' (M : Nat) (f : Nat → Int) (c : Int) : rsum M (fun j => c * f j) = c * rsum M f := by
  induction M with
  | zero => simp [rsum]
  | succ M ih => simp only [rsum]; rw [ih, Int.mul_add]

theorem lineS_smul (a : Int) (f : List Nat → Int) (g : List Nat) (v : Nat → Nat) (M : Nat) :
    lineS n k (fun h => a * f h) g v M = a * lineS n k f g v M := by
  unfold lineS; rw [← rsum_mul']; apply rsum_congr; intro t _; split <;> simp

theorem Bal_add {e : Nat} {y y' f f' : List Nat → Int} (h : Bal p n k y f e) (h' : Bal p n k y' f' e) :
    Bal p n k (fun g => y g + y' g) (fun g => f g + f' g) e := by
  intro g hg hl
  obtain ⟨hr, hc⟩ := h g hg hl
  obtain ⟨hr', hc'⟩ := h' g hg hl
  refine ⟨fun i hi hf => ?_, fun j hj hf => ?_⟩
  · have := Int.dvd_add (hr i hi hf) (hr' i hi hf)
    unfold rowS at *; rw [lineS_add]; rw [show ∀ a b c d : Int, a + b - (c + d) = a - c + (b - d) by
      intros; omega]; exact this
  · have := Int.dvd_add (hc j hj hf) (hc' j hj hf)
    unfold colS at *; rw [lineS_add]; rw [show ∀ a b c d : Int, a + b - (c + d) = a - c + (b - d) by
      intros; omega]; exact this

theorem Bal_smul {e : Nat} (a : Int) {y f : List Nat → Int} (h : Bal p n k y f e) :
    Bal p n k (fun g => a * y g) (fun g => a * f g) e := by
  intro g hg hl
  obtain ⟨hr, hc⟩ := h g hg hl
  refine ⟨fun i hi hf => ?_, fun j hj hf => ?_⟩
  · have := Int.dvd_trans (hr i hi hf) (Int.dvd_mul_left a _)
    unfold rowS at *; rw [lineS_smul, ← Int.mul_sub]; exact this
  · have := Int.dvd_trans (hc j hj hf) (Int.dvd_mul_left a _)
    unfold colS at *; rw [lineS_smul, ← Int.mul_sub]; exact this

/-- `Bal` reads `f` only at canonical `e`-matchings, and only modulo `p`. -/
theorem Bal_congr {e : Nat} {y f f' : List Nat → Int} (h : Bal p n k y f e)
    (hf : ∀ g, CM n k g → g.length = e → (p : Int) ∣ f' g - f g) : Bal p n k y f' e := by
  intro g hg hl
  obtain ⟨hr, hc⟩ := h g hg hl
  have hd := hf g hg hl
  refine ⟨fun i hi hp => ?_, fun j hj hp => ?_⟩
  · have := Int.dvd_sub (hr i hi hp) hd
    rw [show ∀ a b c : Int, a - c - (b - c) = a - b by intros; omega] at this; exact this
  · have := Int.dvd_sub (hc j hj hp) hd
    rw [show ∀ a b c : Int, a - c - (b - c) = a - b by intros; omega] at this; exact this

/-- Span of a set `G` of functions, modulo `p` and up to values off canonical `e`-matchings. -/
inductive InSpan (p n k e : Nat) (G : (List Nat → Int) → Prop) : (List Nat → Int) → Prop
  | gen {f} : G f → InSpan p n k e G f
  | add {f f'} : InSpan p n k e G f → InSpan p n k e G f' → InSpan p n k e G (fun g => f g + f' g)
  | smul (a : Int) {f} : InSpan p n k e G f → InSpan p n k e G (fun g => a * f g)
  | congr {f f'} : InSpan p n k e G f → (∀ g, CM n k g → g.length = e → (p : Int) ∣ f' g - f g) →
      InSpan p n k e G f'

/-- Functions with an extension at level `e` are closed under the span operations. -/
theorem ext_of_span {e : Nat} {G : (List Nat → Int) → Prop} (hG : ∀ f, G f → ∃ y, Bal p n k y f e)
    {f : List Nat → Int} (hf : InSpan p n k e G f) : ∃ y, Bal p n k y f e := by
  induction hf with
  | gen h => exact hG _ h
  | add _ _ ih ih' =>
    obtain ⟨y, hy⟩ := ih; obtain ⟨y', hy'⟩ := ih'; exact ⟨_, Bal_add hy hy'⟩
  | smul a _ ih => obtain ⟨y, hy⟩ := ih; exact ⟨_, Bal_smul a hy⟩
  | congr _ hc ih => obtain ⟨y, hy⟩ := ih; exact ⟨y, Bal_congr hy hc⟩

/-- **EXT from a spanning set.** If every `f` balanced at level `d-1` lies in the span of
functions that have level-`d` extensions, then `EXT p n k d`. -/
theorem EXT_of_span {d : Nat} {G : (List Nat → Int) → Prop} (hG : ∀ f, G f → ∃ y, Bal p n k y f d)
    (hS : ∀ f c : List Nat → Int, (∀ e, e + 1 = d → Bal p n k f c e) → InSpan p n k d G f) :
    EXT p n k d :=
  fun f c hb => ext_of_span hG (hS f c hb)

/-! ## Statement of S2 (K19) -/

/-- The `2 × 2` rectangle `x_{ab} + x_{a'b'} - x_{ab'} - x_{a'b}` as a function on variables. -/
def rect (n a a' b b' : Nat) (v : Nat) : Int :=
  (if v = var n a b then 1 else 0) + (if v = var n a' b' then 1 else 0)
    - (if v = var n a b' then 1 else 0) - (if v = var n a' b then 1 else 0)

/-- Product `r ⊗ r'` on 2-element lists. -/
def tprod (r r' : Nat → Int) : List Nat → Int
  | [v, w] => r v * r' w + r w * r' v
  | _ => 0

/-- Products of two rectangles on disjoint pigeons and disjoint holes of `ontoFPHP n k`. -/
def RectProd (n k : Nat) (f : List Nat → Int) : Prop :=
  ∃ a a' c c' b b' d d', [a, a', c, c'].Nodup ∧ [b, b', d, d'].Nodup ∧
    (∀ i ∈ [a, a', c, c'], i < n + k) ∧ (∀ j ∈ [b, b', d, d'], j < n) ∧
    f = tprod (rect n a a' b b') (rect n c c' d d')

/-- **S2** (th, K19) as a Lean proposition: every `f` on 2-matchings whose link at each edge has
all free row and column sums `≡ 0` mod `p` is in the span of disjoint rectangle products. -/
def S2 (p n k : Nat) : Prop :=
  ∀ f : List Nat → Int, Bal p n k f (fun _ => 0) 1 → InSpan p n k 2 (RectProd n k) f

/-- S2 reduces extension of zero-link functions to extension of single rectangle products. -/
theorem ext_zero_link (hS2 : S2 p n k) (hR : ∀ f, RectProd n k f → ∃ y, Bal p n k y f 2)
    {f : List Nat → Int} (hf : Bal p n k f (fun _ => 0) 1) : ∃ y, Bal p n k y f 2 :=
  ext_of_span hR (hS2 f hf)

#print axioms Programme.«20261026-1402-proof-complexity».ExtLin.EXT_of_span
#print axioms Programme.«20261026-1402-proof-complexity».ExtLin.ext_zero_link

end Programme.«20261026-1402-proof-complexity».ExtLin
