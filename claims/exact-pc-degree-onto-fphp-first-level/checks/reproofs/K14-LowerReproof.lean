import Work.Alias
import Peer.th.Peel
namespace Work.LowerReproof
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Peer.th.SJ
open Peer.th.Peel (IsPrime Units)

-- Construct a window representative directly by induction on the link depth.
-- Shared inputs: the author's rectangle-window and zero-link span lemmas.
-- Neither Peel.claim, ext_d, no_refutation_units nor pc_degree_ge_p is used.
theorem lift_flag {p n k H : Nat} (hk : (p : Int) ∣ k)
    (hn : 2 * H + 1 ≤ n) (hu : Units p (H + 1)) :
    ∀ d ≤ H, ∀ f, Peer.th.Peel.Adm p n k d f →
    ∃ T, (∀ e ≤ H, Bal p n k T T e) ∧
      ∀ g, CM n k g → g.length = d → (p : Int) ∣ f g - T g := by
  intro d hd
  induction d with
  | zero =>
    intro f _
    have hr : RPGen n k 0 (RP n 0 (fun _ => (0,0)) (fun _ => (0,0))) :=
      ⟨_, _, Peer.th.Peel.VP_zero _ _ _, Peer.th.Peel.VP_zero _ _ _, rfl⟩
    have hs := Peer.th.Peel.rp_span hk hn (Nat.zero_le H) hu hr
    obtain ⟨T, ht, he⟩ := Peer.th.Peel.span_rep (Nat.zero_le H) hs
    refine ⟨fun g => f [] * T g, fun e h => Bal_smul _ (ht e h), ?_⟩
    intro g hg hl
    have he := he g hg hl
    have hg0 : g = [] := List.eq_nil_of_length_eq_zero hl
    subst g
    simp [RP, jp] at he
    have hm : (p : Int) ∣ f [] * (1 - T []) := Int.dvd_mul_of_dvd_right he
    simpa only [Int.mul_sub, Int.mul_one] using hm
  | succ d ih =>
    intro f hf
    obtain ⟨c, hfc, hc⟩ := hf
    obtain ⟨T, ht, he⟩ := ih (by omega) c hc
    have hz : Bal p n k (fun g => f g + (-1) * T g) (fun _ => 0) d := by
      apply Bal_congr (Bal_add hfc (Bal_smul (-1) (ht d (by omega))))
      intro g hg hl
      have h := Int.dvd_neg.mpr (he g hg hl)
      rw [show (0 : Int) - (c g + -1 * T g) = -(c g - T g) by omega]
      exact h
    have hs := SJ p n k d (by omega) (Peer.th.Peel.fact_unit hu (d+1) (by omega)) _ hz
    have hw := Peer.th.Peel.span_mono
      (fun f' hf' => Peer.th.Peel.rp_span hk hn (by omega) hu hf') hs
    obtain ⟨U, hut, hue⟩ := Peer.th.Peel.span_rep (by omega) hw
    refine ⟨fun g => U g + T g, fun e h => Bal_add (hut e h) (ht e h), ?_⟩
    intro g hg hl
    have h := hue g hg hl
    rw [show f g - (U g + T g) = f g + -1 * T g - U g by omega]
    exact h

theorem bridge {p k : Nat} (hp : IsPrime p) (hk : p ∣ k) (n : Nat)
    (hn : 2 * p - 3 ≤ n) : ¬ PPCRefutation p (ontoFPHP n k) (p - 1) := by
  apply no_refutation_of_ext_ge (n0 := 2*p-3) (by have := hp.1; omega)
    (by have := hp.1; omega) (by have := hp.1; omega) _ n hn
  intro d hd f c hb
  have hun : Units p (d+1) := fun s h1 h2 => Peer.th.Peel.units_of_prime hp s h1 (by omega)
  have had : Peer.th.Peel.Adm p (2*p-3) k d f := by
    cases d with
    | zero => trivial
    | succ e => exact Peer.th.Peel.adm_of_bal e f c (hb e rfl)
  obtain ⟨T, ht, he⟩ := lift_flag (Int.natCast_dvd_natCast.mpr hk)
    (by omega) hun d (Nat.le_refl d) f had
  exact ⟨T, Bal_congr (ht d (Nat.le_refl d)) he⟩

example : type_of% @bridge = type_of% @Peer.th.Peel.pc_degree_ge_p := rfl
end Work.LowerReproof
#print axioms Work.LowerReproof.bridge

example : type_of% @Work.LowerReproof.bridge = type_of% @Work.Peel.pc_degree_ge_p := rfl
