import Programme.«20261027-0607-proof-complexity».SJ
import Programme.«20261026-1402-proof-complexity».ExtLin
import Programme.«20261026-1402-proof-complexity».RectExt

/-! # S2 for odd `p` (th's S_j at `j = 1`)

`ExtLin.S2 p n k` (stated, not proved, in the run-1402 library) holds for every odd `p` and `n ≥ 4`.
Proof: th's `SJ` at `j = 1` (`2! = 2` is a unit mod odd `p`) puts every zero-link `f` in the span
of the 2-fold rectangle products `RP n 2 P Q`; each of these agrees with
`tprod (rect ..) (rect ..)` on 2-element lists of distinct variables (`RP_two`), so it lies in the
span of `RectProd n k` (`InSpan` monotone in the generating set). -/

namespace Programme.«20261027-0607-proof-complexity».S2Odd

open Programme.«20261025-0459-proof-complexity».OntoFPHP (var)
open Programme.«20261025-1627-proof-complexity».MomGen (canon canon_nodup)
open Programme.«20261025-0459-proof-complexity».OntoSubst (var_div var_mod)
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin
open Programme.«20261027-0607-proof-complexity».LemK
open Programme.«20261027-0607-proof-complexity».SJ

/-- `InSpan` is monotone in the generating set. -/
theorem span_mono {p n k e : Nat} {G G' : (List Nat → Int) → Prop}
    (hG : ∀ h, G h → InSpan p n k e G' h) {f : List Nat → Int} (hf : InSpan p n k e G f) :
    InSpan p n k e G' f := by
  induction hf with
  | gen h => exact hG _ h
  | add _ _ ih ih' => exact InSpan.add ih ih'
  | smul a _ ih => exact InSpan.smul a ih
  | congr _ hc ih => exact InSpan.congr ih hc

theorem var_iff {n x y v : Nat} (hy : y < n) : v = var n x y ↔ v / n = x ∧ v % n = y := by
  constructor
  · rintro rfl; exact ⟨var_div n x y hy, var_mod n x y hy⟩
  · rintro ⟨h1, h2⟩
    unfold var; rw [← h1, ← h2, Nat.mul_comm]; exact (Nat.div_add_mod v n).symm

/-- A rectangle is the product of the pigeon and hole difference indicators. -/
theorem rect_eq {n a a' b b' : Nat} (hb : b < n) (hb' : b' < n) (v : Nat) :
    rect n a a' b b' v = dl (a, a') (v / n) * dl (b, b') (v % n) := by
  unfold rect dl
  simp only [var_iff hb, var_iff hb']
  generalize v / n = X; generalize v % n = Y
  by_cases h1 : X = a <;> by_cases h2 : X = a' <;> by_cases h3 : Y = b <;> by_cases h4 : Y = b' <;>
    (try subst h1) <;> (try subst h2) <;> (try subst h3) <;> (try subst h4) <;> simp_all

/-- On two distinct variables the permanent `jp 2` is the symmetric product. -/
theorem jp_two (r : Nat → Nat → Int) {v w : Nat} (hvw : v ≠ w) :
    jp 2 r [v, w] = r 0 v * r 1 w + r 0 w * r 1 v := by
  have : [v, w].erase w = [v] := by
    simp [hvw]
  simp [jp, ls, List.erase_cons_head, this]

/-- Every generator of th's span at `j = 1` is in the span of `RectProd`. -/
theorem RPGen_span {p n k : Nat} {h : List Nat → Int} (hh : RPGen n k 2 h) :
    InSpan p n k 2 (RectProd n k) h := by
  obtain ⟨P, Q, hP, hQ, rfl⟩ := hh
  obtain ⟨hP1, hP2⟩ := hP
  obtain ⟨hQ1, hQ2⟩ := hQ
  obtain ⟨p0a, -, p0b, -, p0c⟩ := hP1 0 (by omega)
  obtain ⟨p1a, -, p1b, -, p1c⟩ := hP1 1 (by omega)
  obtain ⟨q0a, -, q0b, -, q0c⟩ := hQ1 0 (by omega)
  obtain ⟨q1a, -, q1b, -, q1c⟩ := hQ1 1 (by omega)
  obtain ⟨pd1, pd2, pd3⟩ := hP2 0 (by omega) 1 (by omega) (by omega)
  obtain ⟨pd4, pd5, pd6⟩ := hP2 1 (by omega) 0 (by omega) (by omega)
  obtain ⟨qd1, qd2, qd3⟩ := hQ2 0 (by omega) 1 (by omega) (by omega)
  obtain ⟨qd4, qd5, qd6⟩ := hQ2 1 (by omega) 0 (by omega) (by omega)
  have hR : RectProd n k (tprod (rect n (P 0).1 (P 0).2 (Q 0).1 (Q 0).2)
      (rect n (P 1).1 (P 1).2 (Q 1).1 (Q 1).2)) := by
    refine ⟨(P 0).1, (P 0).2, (P 1).1, (P 1).2, (Q 0).1, (Q 0).2, (Q 1).1, (Q 1).2,
      ?_, ?_, ?_, ?_, rfl⟩
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        List.nodup_nil, or_false, not_or, not_false_eq_true, and_true]
      omega
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        List.nodup_nil, or_false, not_or, not_false_eq_true, and_true]
      omega
    · intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
    · intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      omega
  refine InSpan.congr (InSpan.gen hR) (fun g hg hl => ?_)
  have hnd : g.Nodup := by rw [← hg.1]; exact canon_nodup _ _
  match g, hl, hnd with
  | [v, w], _, hnd =>
    have hvw : v ≠ w := by
      intro e; subst e; simp at hnd
    unfold RP; rw [jp_two _ hvw]
    simp only [tprod, rect_eq q0a q0b, rect_eq q1a q1b]
    simp

/-- **S2 for odd `p`.** For odd `p` and `n ≥ 4`, every function on 2-matchings of `ontoFPHP n k`
with zero edge links is, mod `p` on canonical 2-matchings, in the span of disjoint rectangle
products (`ExtLin.S2`). -/
theorem S2_odd (p n k : Nat) (hp : p % 2 = 1) (hn : 4 ≤ n) : S2 p n k := by
  intro f hf
  have hu : ∃ e : Int, (p : Int) ∣ e * (fact (1 + 1) : Int) - 1 :=
    ⟨((p + 1) / 2 : Nat), ⟨1, by simp [fact]; omega⟩⟩
  exact span_mono (fun _ h => RPGen_span h) (SJ p n k 1 (by omega) hu f hf)

/-- **Zero-link extension at level 2 for odd `p`.** For odd `p`, `n ≥ 7` and `p ∣ k`, every
function on 2-matchings of `ontoFPHP n k` with zero edge links has a level-2 extension
(`RectExt.zero_link_ext` with its S2 hypothesis discharged by `S2_odd`). -/
theorem zero_link_ext_odd {p n k : Nat} (hp : p % 2 = 1) (hn : 7 ≤ n) (hk : (p : Int) ∣ k)
    {f : List Nat → Int} (hf : Bal p n k f (fun _ => 0) 1) : ∃ Y, Bal p n k Y f 2 :=
  Programme.«20261026-1402-proof-complexity».RectExt.zero_link_ext hn hk (S2_odd p n k hp (by omega)) hf

end Programme.«20261027-0607-proof-complexity».S2Odd

#print axioms Programme.«20261027-0607-proof-complexity».S2Odd.S2_odd
#print axioms Programme.«20261027-0607-proof-complexity».S2Odd.zero_link_ext_odd
