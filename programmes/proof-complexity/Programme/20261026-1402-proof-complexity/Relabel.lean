import Programme.«20261026-1402-proof-complexity».ExtLemma

/-!
# Relabelling pigeons and holes preserves `Bal`

A permutation `σ` of the pigeons `[0, n+k)` and `τ` of the holes `[0, n)` (given with inverses)
act on variables by `φ (var n i j) = var n (σ i) (τ j)` and on functions of matchings by
`relab f g = f (canon N (g.map φ))`. `bal_relab`: if `Bal p n k Y f d` then
`Bal p n k (relab Y) (relab f) d`. So every pigeon/hole relabelling of a function with a
level-`d` extension again has one (used for the `S_P × S_H` images of `T`, K31/K32).
-/

namespace Programme.«20261026-1402-proof-complexity».Relabel

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt var_decode)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma

/-- A permutation of `[0, m)` with its inverse. -/
structure Perm (m : Nat) where
  f : Nat → Nat
  g : Nat → Nat
  f_lt : ∀ x < m, f x < m
  g_lt : ∀ x < m, g x < m
  gf : ∀ x < m, g (f x) = x
  fg : ∀ x < m, f (g x) = x

theorem Perm.inj {m : Nat} (σ : Perm m) {x y : Nat} (hx : x < m) (hy : y < m) (h : σ.f x = σ.f y) :
    x = y := by
  rw [← σ.gf x hx, ← σ.gf y hy, h]

/-! ## Reindexing sums -/

theorem rsum_list (m : Nat) (F : Nat → Int) : rsum m F = ((List.range m).map F).sum := by
  induction m with
  | zero => rfl
  | succ m ih => simp [rsum, ih, List.range_succ, List.sum_append]

theorem perm_sum {l l' : List Int} (h : l.Perm l') : l.sum = l'.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem nodup_map_on {l : List Nat} (f : Nat → Nat) (hl : l.Nodup)
    (hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ih hl.2 (fun x hx y hy => hf x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    rintro ⟨b, hb, he⟩
    have := hf b (List.mem_cons_of_mem _ hb) a List.mem_cons_self he
    subst this; exact hl.1 hb

theorem rsum_perm {m : Nat} (σ : Perm m) (F : Nat → Int) : rsum m (fun x => F (σ.f x)) = rsum m F := by
  rw [rsum_list, rsum_list]
  have hp : ((List.range m).map σ.f).Perm (List.range m) := by
    rw [List.perm_ext_iff_of_nodup (nodup_map_on _ List.nodup_range
      (fun x hx y hy h => σ.inj (List.mem_range.mp hx) (List.mem_range.mp hy) h)) List.nodup_range]
    intro a
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨b, hb, rfl⟩; exact σ.f_lt b hb
    · intro ha; exact ⟨σ.g a, σ.g_lt a ha, σ.fg a ha⟩
  have := perm_sum (hp.map F)
  rw [List.map_map] at this
  exact this

/-! ## The action on variables -/

variable {p n k : Nat}

/-- Action on variables. -/
def phi (σ : Perm (n + k)) (τ : Perm n) (v : Nat) : Nat := var n (σ.f (v / n)) (τ.f (v % n))

/-- Relabelled function of matchings. -/
def relab (σ : Perm (n + k)) (τ : Perm n) (f : List Nat → Int) (g : List Nat) : Int :=
  f (canon ((n + k) * n) (g.map (phi σ τ)))

theorem div_lt' {v : Nat} (hv : v < (n + k) * n) : v / n < n + k := by
  rw [Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (by rintro rfl; simp at hv))]; exact hv

theorem mod_lt' {v : Nat} (hv : v < (n + k) * n) : v % n < n :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hv))

theorem phi_div (σ : Perm (n + k)) (τ : Perm n) {v : Nat} (hv : v < (n + k) * n) :
    phi σ τ v / n = σ.f (v / n) := var_div _ _ _ (τ.f_lt _ (mod_lt' hv))

theorem phi_mod (σ : Perm (n + k)) (τ : Perm n) {v : Nat} (hv : v < (n + k) * n) :
    phi σ τ v % n = τ.f (v % n) := var_mod _ _ _ (τ.f_lt _ (mod_lt' hv))

theorem phi_lt (σ : Perm (n + k)) (τ : Perm n) {v : Nat} (hv : v < (n + k) * n) :
    phi σ τ v < (n + k) * n := var_lt _ _ _ _ (σ.f_lt _ (div_lt' hv)) (τ.f_lt _ (mod_lt' hv))

theorem phi_var (σ : Perm (n + k)) (τ : Perm n) {i j : Nat} (hi : i < n + k) (hj : j < n) :
    phi σ τ (var n i j) = var n (σ.f i) (τ.f j) := by
  have hv := var_lt n k i j hi hj
  unfold phi; rw [var_div _ _ _ hj, var_mod _ _ _ hj]

theorem phi_inj (σ : Perm (n + k)) (τ : Perm n) {v w : Nat} (hv : v < (n + k) * n) (hw : w < (n + k) * n)
    (h : phi σ τ v = phi σ τ w) : v = w := by
  have h1 : σ.f (v / n) = σ.f (w / n) := by rw [← phi_div σ τ hv, ← phi_div σ τ hw, h]
  have h2 : τ.f (v % n) = τ.f (w % n) := by rw [← phi_mod σ τ hv, ← phi_mod σ τ hw, h]
  have e1 := σ.inj (div_lt' hv) (div_lt' hw) h1
  have e2 := τ.inj (mod_lt' hv) (mod_lt' hw) h2
  rw [← var_decode n v, ← var_decode n w, e1, e2]

theorem cfl_phi (σ : Perm (n + k)) (τ : Perm n) {v w : Nat} (hv : v < (n + k) * n) (hw : w < (n + k) * n) :
    cfl n (phi σ τ v) (phi σ τ w) = cfl n v w := by
  have hd : (phi σ τ v / n == phi σ τ w / n) = (v / n == w / n) := by
    rw [phi_div σ τ hv, phi_div σ τ hw]
    apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
    exact ⟨σ.inj (div_lt' hv) (div_lt' hw), fun h => by rw [h]⟩
  have hm : (phi σ τ v % n == phi σ τ w % n) = (v % n == w % n) := by
    rw [phi_mod σ τ hv, phi_mod σ τ hw]
    apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
    exact ⟨τ.inj (mod_lt' hv) (mod_lt' hw), fun h => by rw [h]⟩
  have hn : (phi σ τ v != phi σ τ w) = (v != w) := by
    apply Bool.eq_iff_iff.mpr; simp only [bne_iff_ne, ne_eq]
    exact ⟨fun h e => h (by rw [e]), fun h e => h (phi_inj σ τ hv hw e)⟩
  unfold cfl; rw [hd, hm, hn]

theorem isMatch_map (σ : Perm (n + k)) (τ : Perm n) {l : List Nat} (hl : ∀ x ∈ l, x < (n + k) * n) :
    isMatch n (l.map (phi σ τ)) = isMatch n l := by
  apply Bool.eq_iff_iff.mpr
  rw [isMatch_iff, isMatch_iff]
  simp only [List.mem_map]
  constructor
  · intro h v hv w hw
    rw [← cfl_phi σ τ (hl v hv) (hl w hw)]; exact h _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
  · rintro h _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [cfl_phi σ τ (hl v hv) (hl w hw)]; exact h v hv w hw

theorem canon_map_canon (σ : Perm (n + k)) (τ : Perm n) (L : List Nat) :
    canon ((n + k) * n) ((canon ((n + k) * n) L).map (phi σ τ)) =
      canon ((n + k) * n) ((L.filter (· < (n + k) * n)).map (phi σ τ)) := by
  apply canon_congr
  intro x _
  simp only [List.mem_map, mem_canon, List.mem_filter, decide_eq_true_eq]

theorem filter_all {L : List Nat} (h : ∀ x ∈ L, x < (n + k) * n) : L.filter (· < (n + k) * n) = L :=
  List.filter_eq_self.mpr (fun x hx => by simpa using h x hx)

/-- The image of a canonical matching. -/
theorem CM_image (σ : Perm (n + k)) (τ : Perm n) {g : List Nat} (hg : CM n k g) :
    CM n k (canon ((n + k) * n) (g.map (phi σ τ))) ∧
      (canon ((n + k) * n) (g.map (phi σ τ))).length = g.length := by
  have hlt := fun x (hx : x ∈ g) => CM_lt hg hx
  have hmlt : ∀ x ∈ g.map (phi σ τ), x < (n + k) * n := by
    intro x hx; obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; exact phi_lt σ τ (hlt v hv)
  have hmem : ∀ x, x ∈ canon ((n + k) * n) (g.map (phi σ τ)) ↔ x ∈ g.map (phi σ τ) := by
    intro x; rw [mem_canon]; exact ⟨fun h => h.1, fun h => ⟨h, hmlt x h⟩⟩
  refine ⟨⟨canon_idem _, ?_⟩, ?_⟩
  · rw [isMatch_congr n _ _ hmem, isMatch_map σ τ hlt]; exact hg.2
  · rw [canon_len_eq (nodup_map_on _ (CM_nodup hg) (fun x hx y hy => phi_inj σ τ (hlt x hx) (hlt y hy)))
      hmlt, List.length_map]

/-- One relabelled line term equals the corresponding term at the image. -/
theorem term_eq (σ : Perm (n + k)) (τ : Perm n) (Y : List Nat → Int) {g : List Nat} (hg : CM n k g)
    {i j : Nat} (hi : i < n + k) (hj : j < n) :
    (if isMatch n (var n i j :: g) then relab σ τ Y (canon ((n + k) * n) (var n i j :: g)) else 0) =
      (if isMatch n (var n (σ.f i) (τ.f j) :: canon ((n + k) * n) (g.map (phi σ τ))) then
        Y (canon ((n + k) * n) (var n (σ.f i) (τ.f j) :: canon ((n + k) * n) (g.map (phi σ τ)))) else 0) := by
  have hl : ∀ x ∈ var n i j :: g, x < (n + k) * n := by
    intro x hx; rcases List.mem_cons.mp hx with rfl | hx
    · exact var_lt n k i j hi hj
    · exact CM_lt hg hx
  have hmlt : ∀ x ∈ g.map (phi σ τ), x < (n + k) * n := by
    intro x hx; obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; exact phi_lt σ τ (CM_lt hg hv)
  have hmem : ∀ x, x ∈ var n (σ.f i) (τ.f j) :: canon ((n + k) * n) (g.map (phi σ τ)) ↔
      x ∈ (var n i j :: g).map (phi σ τ) := by
    intro x
    simp only [List.map_cons, List.mem_cons, mem_canon, phi_var σ τ hi hj]
    constructor
    · rintro (h | h); exact Or.inl h; exact Or.inr h.1
    · rintro (h | h); exact Or.inl h; exact Or.inr ⟨h, hmlt x h⟩
  have hM : isMatch n (var n i j :: g) =
      isMatch n (var n (σ.f i) (τ.f j) :: canon ((n + k) * n) (g.map (phi σ τ))) := by
    rw [isMatch_congr n _ _ hmem, isMatch_map σ τ hl]
  rw [← hM]
  split
  · unfold relab
    rw [canon_map_canon, filter_all hl]
    congr 1
    apply canon_congr; intro x _; exact (hmem x).symm
  · rfl

theorem row_relab (σ : Perm (n + k)) (τ : Perm n) (Y : List Nat → Int) {g : List Nat} (hg : CM n k g)
    {i : Nat} (hi : i < n + k) :
    rowS n k (relab σ τ Y) g i = rowS n k Y (canon ((n + k) * n) (g.map (phi σ τ))) (σ.f i) := by
  unfold rowS lineS
  rw [rsum_congr n _ _ (fun j hj => term_eq σ τ Y hg hi hj)]
  exact rsum_perm τ (fun j => if isMatch n (var n (σ.f i) j :: canon ((n + k) * n) (g.map (phi σ τ)))
    then Y (canon ((n + k) * n) (var n (σ.f i) j :: canon ((n + k) * n) (g.map (phi σ τ)))) else 0)

theorem col_relab (σ : Perm (n + k)) (τ : Perm n) (Y : List Nat → Int) {g : List Nat} (hg : CM n k g)
    {j : Nat} (hj : j < n) :
    colS n k (relab σ τ Y) g j = colS n k Y (canon ((n + k) * n) (g.map (phi σ τ))) (τ.f j) := by
  unfold colS lineS
  rw [rsum_congr (n + k) _ _ (fun i hi => term_eq σ τ Y hg hi hj)]
  exact rsum_perm σ (fun i => if isMatch n (var n i (τ.f j) :: canon ((n + k) * n) (g.map (phi σ τ)))
    then Y (canon ((n + k) * n) (var n i (τ.f j) :: canon ((n + k) * n) (g.map (phi σ τ)))) else 0)

/-- **Relabelling lemma.** A pigeon/hole relabelling of a level-`d` balanced pair is balanced. -/
theorem bal_relab (σ : Perm (n + k)) (τ : Perm n) {Y f : List Nat → Int} {d : Nat}
    (h : Bal p n k Y f d) : Bal p n k (relab σ τ Y) (relab σ τ f) d := by
  intro g hg hlen
  obtain ⟨hcm, hl⟩ := CM_image σ τ hg
  obtain ⟨hr, hc⟩ := h _ hcm (hl.trans hlen)
  refine ⟨fun i hi hfree => ?_, fun j hj hfree => ?_⟩
  · rw [row_relab σ τ Y hg hi]
    refine hr _ (σ.f_lt i hi) ?_
    intro x hx
    obtain ⟨⟨v, hv, rfl⟩, -⟩ := (mem_canon _ _ _).mp hx |>.imp_left List.mem_map.mp
    rw [phi_div σ τ (CM_lt hg hv)]
    exact fun e => hfree v hv (σ.inj (div_lt' (CM_lt hg hv)) hi e)
  · rw [col_relab σ τ Y hg hj]
    refine hc _ (τ.f_lt j hj) ?_
    intro x hx
    obtain ⟨⟨v, hv, rfl⟩, -⟩ := (mem_canon _ _ _).mp hx |>.imp_left List.mem_map.mp
    rw [phi_mod σ τ (CM_lt hg hv)]
    exact fun e => hfree v hv (τ.inj (mod_lt' (CM_lt hg hv)) hj e)

/-- Every relabelling of a function with a level-`d` extension has one. -/
theorem ext_relab (σ : Perm (n + k)) (τ : Perm n) {f : List Nat → Int} {d : Nat}
    (h : ∃ Y, Bal p n k Y f d) : ∃ Y, Bal p n k Y (relab σ τ f) d := by
  obtain ⟨Y, hY⟩ := h
  exact ⟨relab σ τ Y, bal_relab σ τ hY⟩

end Programme.«20261026-1402-proof-complexity».Relabel

#print axioms Programme.«20261026-1402-proof-complexity».Relabel.bal_relab
#print axioms Programme.«20261026-1402-proof-complexity».Relabel.ext_relab
