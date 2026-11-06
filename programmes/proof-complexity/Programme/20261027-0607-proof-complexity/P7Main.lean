import Programme.«20261027-0607-proof-complexity».P7Count
import Programme.«20261027-0607-proof-complexity».P7Check
import Programme.«20261027-0607-proof-complexity».PeelV

/-!
# Conjecture V at `p = 7`: onto-FPHP with `n + 49` pigeons has no degree-7 PC refutation over `Z/7`

Port of th's `D5Main` (p = 5) to `p = 7`, with pr's own data and chunked check.
`design7`: the class-code function `T tree` (`Work.P7Defs`, data `Work.P7Data0`–`Work.P7Data3`) is a unit degree-7
design of `ontoFPHP 13 49` over `Z/7`: `T tree [] = 1` and `Bal 7 13 49 (T tree) (T tree) e` for all
`e ≤ 6`. The kernel check `chk` (`Work.P7Check`, 64 chunks) verifies, at each state code of a matching of
size `≤ 6`, the reduced row and column equations and that every neighbour code is listed at the next level.
`row_formula`, `col_formula` and `regroup` turn these into the free row and column sums of `T tree`.

`no_deg7`: with `Work.PeelV.no_deg_p_of_design` (K20), for every `n ≥ 13`, `ontoFPHP n 49` has no
degree-7 `PPCRefutation 7`.
-/

namespace Programme.«20261027-0607-proof-complexity».P7

open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum var ontoFPHP PPCRefutation)
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr)
open Programme.«20261025-1627-proof-complexity».MomGen (canon mem_canon canon_nodup)
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».SymDesign (isMatch_cons)

/-! ## Reading the check -/

structure Spec (t : Tr) (k e : Nat) (S : List (Nat × Nat)) : Prop where
  ok : spOk 0 S = true
  kv : k = spv S
  row : ∀ p ∈ S, rc p.1 < Pi p.1 →
    ((List.range 3).foldr (fun d a => if csS S d < Hd d then ((Hd d : Int) - csS S d) * Gt t (nb k p.1 d) + a else a) 0
      - Gt t k) % 7 = 0
  clo : ∀ p ∈ S, rc p.1 < Pi p.1 → ∀ d < 3, csS S d < Hd d → e ≠ 6 →
    isIn t (nb k p.1 d) = true ∧ lev t (nb k p.1 d) = e + 1
  col : ∀ d < 3, csS S d < Hd d →
    (sps S (fun i => ((Pi i : Int) - rc i) * Gt t (nb k i d)) - Gt t k) % 7 = 0

theorem spec_of {t : Tr} {k e : Nat} {S : List (Nat × Nat)} (he : e ≤ 6) (h : okE t k e S = true) :
    Spec t k e S := by
  simp only [okE, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true,
    List.all_eq_true, beq_iff_eq, decide_eq_true_eq, List.mem_range] at h
  rcases h with h | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  · exact absurd he h
  refine ⟨h1, h2, fun p hp hr => ?_, fun p hp hr d hd hc he4 => ?_, fun d hd hc => ?_⟩
  · rcases h3 p hp with h | h
    · exact absurd hr h
    · exact h.1
  · rcases h3 p hp with h | h
    · exact absurd hr h
    · exact (h.2 d hd).elim (fun h' => h'.elim (fun h'' => absurd hc h'') (fun h'' => absurd h'' he4)) id
  · rcases h4 d hd with h | h
    · exact absurd hc h
    · exact h

theorem find_of_isIn {t : Tr} {x e : Nat} (h1 : isIn t x = true) (h2 : lev t x = e) :
    ∃ v S, find t x = some (v, e, S) := by
  unfold isIn at h1; unfold lev at h2
  revert h1 h2
  cases find t x with
  | none => intro h1; simp at h1
  | some q => intro _ h2; obtain ⟨v, e', S⟩ := q; simp at h2; exact ⟨v, S, by rw [h2]⟩

theorem okE_of {t : Tr} (ht : okT t = true) {x v e : Nat} {S : List (Nat × Nat)}
    (hf : find t x = some (v, e, S)) : okE t x e S = true := by
  have h : (toList t).all (fun q => okE t q.1 q.2.2.1 q.2.2.2) = true := ht
  exact List.all_eq_true.mp h (x, v, e, S) (find_mem t x v e S hf)

/-! ## Matchings -/

theorem mt_tail {x : Nat} {l : List Nat} (h : Mt (x :: l)) : Mt l :=
  ⟨(List.nodup_cons.mp h.nd).2, ((isMatch_cons 13 x l).mp h.im).1, fun v hv => h.lt v (by simp [hv])⟩

theorem mt_head {x : Nat} {l : List Nat} (h : Mt (x :: l)) : ∀ w ∈ l, w / 13 ≠ x / 13 ∧ w % 13 ≠ x % 13 := by
  intro w hw
  have h1 := ((isMatch_cons 13 x l).mp h.im).2 w hw
  have h2 : x ≠ w := fun e => (List.nodup_cons.mp h.nd).1 (e ▸ hw)
  simp [cfl, h2] at h1
  exact ⟨fun e => h1.1 e.symm, fun e => h1.2 e.symm⟩

theorem mt_of_cm {g : List Nat} (h : CM 13 49 g) : Mt g := by
  have hc : canon 806 g = g := h.1
  refine ⟨hc ▸ canon_nodup _ _, h.2, fun v hv => ?_⟩
  rw [← hc] at hv; exact ((mem_canon _ _ _).mp hv).2

theorem pig_lt {g : List Nat} (hm : Mt g) {i : Nat} (hi : i < 62) (hf : ∀ w ∈ g, w / 13 ≠ i) :
    rowc g ((i + 4) / 6) < Pc ((i + 4) / 6) := by
  have h := free_pigs hm (c := (i + 4) / 6) (by omega)
  have := rsum_ge_term (fun s => if (s + 4) / 6 = (i + 4) / 6 ∧ ∀ w ∈ g, w / 13 ≠ s then (1 : Int) else 0)
    (fun _ => by split <;> omega) 62 i hi
  rw [if_pos ⟨rfl, hf⟩] at this
  omega

theorem hole_lt {g : List Nat} (hm : Mt g) {j : Nat} (hj : j < 13) (hf : ∀ w ∈ g, w % 13 ≠ j) :
    csg g (j / 6) < Hd (j / 6) := by
  have h := free_holes hm (d := j / 6) (by omega)
  have := rsum_ge_term (fun t => if t / 6 = j / 6 ∧ ∀ w ∈ g, w % 13 ≠ t then (1 : Int) else 0)
    (fun _ => by split <;> omega) 13 j hj
  rw [if_pos ⟨rfl, hf⟩] at this
  omega

theorem csS_eq {g : List Nat} (hm : Mt g) {S : List (Nat × Nat)} (hS : spOk 0 S = true)
    (hk : kap g = spv S) {d : Nat} (hd : d < 3) : csS S d = csg g d := by
  unfold csS
  rw [← regroup (bd hm) hS hk, cs_cc g hm.lt d]
  apply rsum_congr; intro c hc; rw [dig_key (bd hm) hc hd]

/-! ## Reachability -/

theorem reach {t : Tr} (ht : okT t = true) (h0 : ∃ v S, find t (kap []) = some (v, 0, S)) :
    ∀ l : List Nat, Mt l → l.length ≤ 6 → ∃ v S, find t (kap l) = some (v, l.length, S)
  | [], _, _ => h0
  | x :: l, hm, hl => by
    have hm' := mt_tail hm
    obtain ⟨v, S, hf⟩ := reach ht h0 l hm' (by simp at hl; omega)
    have sp := spec_of (by simp at hl; omega) (okE_of ht hf)
    have hx := hm.lt x (by simp)
    have hfr := mt_head hm
    have hb := bd hm'
    obtain ⟨p, hp, hpk⟩ := key_mem hb sp.ok sp.kv (c := (x / 13 + 4) / 6) (by omega)
    have hr : rc p.1 < Pi p.1 := by
      rw [hpk, rc_key hb (by omega), Pi_key hb (by omega)]
      exact pig_lt hm' (i := x / 13) (by omega) (fun w hw => (hfr w hw).1)
    have hcs : csS S (x % 13 / 6) < Hd (x % 13 / 6) := by
      rw [csS_eq hm' sp.ok sp.kv (by omega)]
      exact_mod_cast hole_lt hm' (j := x % 13) (by omega) (fun w hw => (hfr w hw).2)
    obtain ⟨h1, h2⟩ := sp.clo p hp hr _ (by omega) hcs (by simp at hl; omega)
    obtain ⟨v', S', hf'⟩ := find_of_isIn h1 h2
    refine ⟨v', S', ?_⟩
    rw [kap_cons x l (by omega), ← hpk]
    simpa using hf'

/-! ## Balance -/

theorem fold3 (f : Nat → Int → Int) : (List.range 3).foldr f 0 = f 0 (f 1 (f 2 0)) := rfl

theorem bal {t : Tr} (ht : okT t = true) (h0 : ∃ v S, find t (kap []) = some (v, 0, S)) :
    ∀ e ≤ 6, Bal 7 13 49 (T t) (T t) e := by
  intro e he g hg hl
  have hm := mt_of_cm hg
  obtain ⟨v, S, hf⟩ := reach ht h0 g hm (by omega)
  rw [hl] at hf
  have sp := spec_of he (okE_of ht hf)
  have hb := bd hm
  refine ⟨fun i hi hfr => ?_, fun j hj hfr => ?_⟩
  · rw [row_formula t hm (by omega) hfr]
    obtain ⟨p, hp, hpk⟩ := key_mem hb sp.ok sp.kv (c := (i + 4) / 6) (by omega)
    have hr : rc p.1 < Pi p.1 := by
      rw [hpk, rc_key hb (by omega), Pi_key hb (by omega)]; exact pig_lt hm (by omega) hfr
    have h := sp.row p hp hr
    rw [fold3, hpk] at h
    have hc : ∀ d < 3, csS S d = csg g d := fun d hd => csS_eq hm sp.ok sp.kv hd
    rw [hc 0 (by omega), hc 1 (by omega), hc 2 (by omega)] at h
    have l0 := cs_le hm (d := 0) (by omega); have l1 := cs_le hm (d := 1) (by omega)
    have l2 := cs_le hm (d := 2) (by omega)
    apply Int.dvd_of_emod_eq_zero
    unfold T
    have e3 : ∀ F : Nat → Int, rsum 3 F = F 0 + (F 1 + (F 2 + 0)) := by
      intro F; simp [rsum]; omega
    rw [e3]
    revert h
    generalize Gt t (nb (kap g) (key g ((i + 4) / 6)) 0) = A0
    generalize Gt t (nb (kap g) (key g ((i + 4) / 6)) 1) = A1
    generalize Gt t (nb (kap g) (key g ((i + 4) / 6)) 2) = A2
    generalize Gt t (kap g) = B
    generalize csg g 0 = c0 at l0
    generalize csg g 1 = c1 at l1
    generalize csg g 2 = c2 at l2
    intro h
    have q0 : ((Hd 0 : Int) - c0) * A0 = if (c0 : Int) < Hd 0 then ((Hd 0 : Int) - c0) * A0 else 0 := by
      split
      · rfl
      · have : (c0 : Int) = Hd 0 := by omega
        rw [this, Int.sub_self, Int.zero_mul]
    have q1 : ((Hd 1 : Int) - c1) * A1 = if (c1 : Int) < Hd 1 then ((Hd 1 : Int) - c1) * A1 else 0 := by
      split
      · rfl
      · have : (c1 : Int) = Hd 1 := by omega
        rw [this, Int.sub_self, Int.zero_mul]
    have q2 : ((Hd 2 : Int) - c2) * A2 = if (c2 : Int) < Hd 2 then ((Hd 2 : Int) - c2) * A2 else 0 := by
      split
      · rfl
      · have : (c2 : Int) = Hd 2 := by omega
        rw [this, Int.sub_self, Int.zero_mul]
    rw [q0, q1, q2]
    revert h
    by_cases d0 : (c0 : Int) < Hd 0 <;> by_cases d1 : (c1 : Int) < Hd 1 <;> by_cases d2 : (c2 : Int) < Hd 2 <;>
      simp only [d0, d1, d2, if_true, if_false] <;> intro h <;> omega
  · rw [col_formula t hm hj hfr]
    have hd : j / 6 < 3 := by omega
    have hcs : csS S (j / 6) < Hd (j / 6) := by
      rw [csS_eq hm sp.ok sp.kv hd]; exact_mod_cast hole_lt hm hj hfr
    have h := sp.col (j / 6) hd hcs
    apply Int.dvd_of_emod_eq_zero
    unfold T
    have e : rsum 11 (fun c => ((Pc c : Int) - rowc g c) * Gt t (nb (kap g) (key g c) (j / 6))) =
        rsum 11 (fun c => (fun i => ((Pi i : Int) - rc i) * Gt t (nb (kap g) i (j / 6))) (key g c)) := by
      apply rsum_congr; intro c hc
      simp only; rw [Pi_key hb hc, rc_key hb hc]
    rw [e, regroup hb sp.ok sp.kv (fun i => ((Pi i : Int) - rc i) * Gt t (nb (kap g) i (j / 6)))]
    exact h

/-! ## The instance -/

theorem find0 : find tree (kap []) = some (1, 0, [(0, 1), (98, 6), (196, 4)]) := by decide +kernel

theorem T_nil : T tree [] = 1 := by decide +kernel

/-- **Unit degree-7 design** of `ontoFPHP 13 49` over `Z/7`. -/
theorem design7 : T tree [] = 1 ∧ ∀ e ≤ 6, Bal 7 13 49 (T tree) (T tree) e :=
  ⟨T_nil, bal chk ⟨_, _, find0⟩⟩

theorem prime7 : Programme.«20261027-0607-proof-complexity».Peel.IsPrime 7 := ⟨by decide, fun a ha => by
  have := Nat.le_of_dvd (by decide) ha
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 by omega) with
    h | h | h | h | h | h | h | h <;> subst h <;> simp_all <;> omega⟩

/-- **Conjecture V at `p = 7`.** For every `n ≥ 13`, onto-FPHP with `n + 49` pigeons and `n` holes
(functional encoding) has no degree-7 polynomial calculus refutation over `Z/7`. -/
theorem no_deg7 (n : Nat) (hn : 13 ≤ n) : ¬ PPCRefutation 7 (ontoFPHP n 49) 7 :=
  Programme.«20261027-0607-proof-complexity».PeelV.no_deg_p_of_design prime7 (by decide) (by decide) (fun e he => design7.2 e (by omega))
    (by rw [T_nil]; decide) n hn

end Programme.«20261027-0607-proof-complexity».P7

#print axioms Programme.«20261027-0607-proof-complexity».P7.design7
#print axioms Programme.«20261027-0607-proof-complexity».P7.no_deg7
