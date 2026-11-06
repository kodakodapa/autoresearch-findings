import Programme.«20261027-1434-proof-complexity».Towers
import Programme.«20261027-1434-proof-complexity».L2Base
import Programme.«20261027-1434-proof-complexity».Peel

/-!
# The level-2 zero-link generators agree with self-balanced towers

`r0_cong`: the rectangle product `L2Base.R0` is `≡ RRM` mod 2 on every canonical 2-matching.
`t_cong`: `TExt.T 7` is `≡` the relabelling `relab πT ρT TB` (pigeons `0,1,2 ↔ 12,13,14`, holes
`0,1,2 ↔ 4,5,6`) on every canonical 2-matching. Both by kernel evaluation on all pairs `b < a < 105`
(seven chunks of `a`). `relab_cong`: such agreement survives relabelling.
-/

namespace Programme.«20261027-1434-proof-complexity».Cong

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».Relabel
open Programme.«20261027-1434-proof-complexity».PeelBase

def πT : Perm (7 + 8) := mkP 15 [(0, 12), (1, 13), (2, 14)]
def ρT : Perm 7 := mkP 7 [(0, 4), (1, 5), (2, 6)]

/-- Agreement mod 2 on canonical matchings of length `e`. -/
def Agree (e : Nat) (X Y : List Nat → Int) : Prop := ∀ g, CM 7 8 g → g.length = e → (2 : Int) ∣ X g - Y g

def chk2 (X Y : List Nat → Int) (lo n : Nat) : Bool :=
  (List.range' lo n).all fun a => (List.range a).all fun b => !(isMatch 7 [a, b]) || ((X [a, b] - Y [a, b]) % 2 == 0)

theorem agree_of_chk {X Y : List Nat → Int} (h : ∀ c < 7, chk2 X Y (15 * c) 15 = true) : Agree 2 X Y := by
  intro g hg hl
  obtain ⟨a, b, rfl, hba, ha, hm⟩ := CM_two hg hl
  have hc := h (a / 15) (by omega)
  unfold chk2 at hc
  rw [List.all_eq_true] at hc
  have h1 := hc a (List.mem_range'.mpr ⟨a % 15, by omega, by omega⟩)
  rw [List.all_eq_true] at h1
  have h2 := h1 b (List.mem_range.mpr hba)
  rw [hm] at h2
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at h2
  exact Int.dvd_of_emod_eq_zero h2

def TBi (m : List Nat) : Int := Programme.«20261027-1434-proof-complexity».Towers.TB (fcanon (m.map (phi πT ρT)))

theorem r0_0 : chk2 Programme.«20261027-1434-proof-complexity».L2Base.R0 Programme.«20261027-1434-proof-complexity».Towers.RRM 0 15 = true := by decide +kernel
theorem t_0 : chk2 (Programme.«20261026-1402-proof-complexity».TExt.T 7) TBi 0 15 = true := by decide +kernel
theorem r0_1 : chk2 Programme.«20261027-1434-proof-complexity».L2Base.R0 Programme.«20261027-1434-proof-complexity».Towers.RRM 15 15 = true := by decide +kernel
theorem t_1 : chk2 (Programme.«20261026-1402-proof-complexity».TExt.T 7) TBi 15 15 = true := by decide +kernel
theorem r0_2 : chk2 Programme.«20261027-1434-proof-complexity».L2Base.R0 Programme.«20261027-1434-proof-complexity».Towers.RRM 30 15 = true := by decide +kernel
theorem t_2 : chk2 (Programme.«20261026-1402-proof-complexity».TExt.T 7) TBi 30 15 = true := by decide +kernel
theorem r0_3 : chk2 Programme.«20261027-1434-proof-complexity».L2Base.R0 Programme.«20261027-1434-proof-complexity».Towers.RRM 45 15 = true := by decide +kernel
theorem t_3 : chk2 (Programme.«20261026-1402-proof-complexity».TExt.T 7) TBi 45 15 = true := by decide +kernel
theorem r0_4 : chk2 Programme.«20261027-1434-proof-complexity».L2Base.R0 Programme.«20261027-1434-proof-complexity».Towers.RRM 60 15 = true := by decide +kernel
theorem t_4 : chk2 (Programme.«20261026-1402-proof-complexity».TExt.T 7) TBi 60 15 = true := by decide +kernel
theorem r0_5 : chk2 Programme.«20261027-1434-proof-complexity».L2Base.R0 Programme.«20261027-1434-proof-complexity».Towers.RRM 75 15 = true := by decide +kernel
theorem t_5 : chk2 (Programme.«20261026-1402-proof-complexity».TExt.T 7) TBi 75 15 = true := by decide +kernel
theorem r0_6 : chk2 Programme.«20261027-1434-proof-complexity».L2Base.R0 Programme.«20261027-1434-proof-complexity».Towers.RRM 90 15 = true := by decide +kernel
theorem t_6 : chk2 (Programme.«20261026-1402-proof-complexity».TExt.T 7) TBi 90 15 = true := by decide +kernel

theorem r0_cong : Agree 2 Programme.«20261027-1434-proof-complexity».L2Base.R0 Programme.«20261027-1434-proof-complexity».Towers.RRM := agree_of_chk (fun c hc => by
  match c, hc with
  | 0, _ => exact r0_0 | 1, _ => exact r0_1 | 2, _ => exact r0_2 | 3, _ => exact r0_3
  | 4, _ => exact r0_4 | 5, _ => exact r0_5 | 6, _ => exact r0_6)

theorem relab_TBi {g : List Nat} (hg : CM 7 8 g) (hl : g.length = 2) : relab πT ρT Programme.«20261027-1434-proof-complexity».Towers.TB g = TBi g := by
  have hlt := fun x (hx : x ∈ g) => CM_lt hg hx
  unfold relab TBi
  rw [canon_short (fun x hx => by obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; exact phi_lt πT ρT (hlt v hv))
    (nodup_map_on _ (CM_nodup hg) (fun x hx y hy => phi_inj πT ρT (hlt x hx) (hlt y hy)))
    (by rw [List.length_map]; omega)]

theorem t_cong : Agree 2 (Programme.«20261026-1402-proof-complexity».TExt.T 7) (relab πT ρT Programme.«20261027-1434-proof-complexity».Towers.TB) := by
  intro g hg hl
  rw [relab_TBi hg hl]
  exact agree_of_chk (fun c hc => by
    match c, hc with
    | 0, _ => exact t_0 | 1, _ => exact t_1 | 2, _ => exact t_2 | 3, _ => exact t_3
    | 4, _ => exact t_4 | 5, _ => exact t_5 | 6, _ => exact t_6) g hg hl

theorem relab_cong (σ : Perm (7 + 8)) (τ : Perm 7) {e : Nat} {X Y : List Nat → Int} (h : Agree e X Y) :
    Agree e (relab σ τ X) (relab σ τ Y) := by
  intro g hg hl
  obtain ⟨hcm, hlen⟩ := CM_image σ τ hg
  exact h _ hcm (hlen.trans hl)

end Programme.«20261027-1434-proof-complexity».Cong
