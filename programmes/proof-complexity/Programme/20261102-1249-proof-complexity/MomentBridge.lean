import Programme.«20261026-1402-proof-complexity».ExtLemma
namespace Programme.«20261102-1249-proof-complexity».MomentBridge
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-1627-proof-complexity».DesignExt
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261025-1627-proof-complexity».OntoExt2 (SN var_lt)
open Programme.«20261026-1402-proof-complexity».ExtLemma

def ConflictZero (n k D : Nat) (W : List Nat → Int) : Prop :=
  ∀ g, canon ((n+k)*n) g = g → g.length ≤ D → isMatch n g = false → W g = 0
abbrev realize (p n k D : Nat) (W : List Nat → Int) := sumWFn p ((n+k)*n) D W

theorem conflict_kill {p n k D : Nat} {W : List Nat → Int}
    (hW : ConflictZero n k D W) (xs : List Nat) (hl : xs.length ≤ D)
    (u : Nat) (hu : u ∈ xs) (w : Nat) (hw : w ∈ xs) (hc : cfl n u w = true) :
    (p : Int) ∣ (realize p n k D W).E (fun a => monoEval a xs) := by
  rcases all_lt_or (N := (n+k)*n) xs with hx | ⟨x,hx,hN⟩
  · change (p : Int) ∣ sumW _ D W _
    rw [sumW_mono _ D W xs hx (Nat.le_trans (canon_length_le _ _) hl)]
    have hm : isMatch n (canon ((n+k)*n) xs) = false := by
      cases h : isMatch n (canon ((n+k)*n) xs)
      · rfl
      · have h' := (isMatch_iff _ _).mp h u ((mem_canon' hx u).mpr hu)
          w ((mem_canon' hx w).mpr hw)
        rw [hc] at h'; cases h'
    rw [hW _ (canon_idem _) (Nat.le_trans (canon_length_le _ _) hl) hm]
    exact ⟨0, by simp⟩
  · exact vanish0 _ xs x hx hN

theorem extends_iff {p n k D d : Nat} {U W : List Nat → Int} (hd : d ≤ D)
    (hU : ConflictZero n k D U) (hW : ConflictZero n k D W) :
    Extends d (realize p n k D U) (realize p n k D W) ↔
    ∀ g, CM n k g → g.length ≤ d → (p : Int) ∣ U g - W g := by
  constructor
  · intro h g hg hl
    have a := h g hl
    change (p : Int) ∣ sumW _ D U _ - sumW _ D W _ at a
    rw [sumW_mono _ D U g (fun x hx => CM_lt hg hx) (by rw [hg.1]; omega),
      sumW_mono _ D W g (fun x hx => CM_lt hg hx) (by rw [hg.1]; omega), hg.1] at a
    exact a
  · intro h xs hl
    change (p : Int) ∣ sumW _ D U _ - sumW _ D W _
    rcases all_lt_or (N := (n+k)*n) xs with hx | ⟨x,hx,hN⟩
    · rw [sumW_mono _ D U xs hx (by have := canon_length_le ((n+k)*n) xs; omega),
          sumW_mono _ D W xs hx (by have := canon_length_le ((n+k)*n) xs; omega)]
      cases hm : isMatch n (canon ((n+k)*n) xs)
      · rw [hU _ (canon_idem _) (by have := canon_length_le ((n+k)*n) xs; omega) hm,
            hW _ (canon_idem _) (by have := canon_length_le ((n+k)*n) xs; omega) hm]
        exact ⟨0, by simp⟩
      · exact h _ ⟨canon_idem _, hm⟩ (Nat.le_trans (canon_length_le _ _) hl)
    · exact Int.dvd_sub (vanish0 (realize p n k D U) xs x hx hN)
        (vanish0 (realize p n k D W) xs x hx hN)

theorem bal_of_design {p n k D : Nat} {W : List Nat → Int}
    (hW : ConflictZero n k D W)
    (hE : IsDesign (ontoFPHP n k) D (realize p n k D W)) :
    ∀ e < D, Bal p n k W W e := by
  intro e he g hg hgl
  have hK := fun xs (hl : xs.length ≤ e+1) u hu w hw hc =>
    conflict_kill (p := p) hW xs (by omega) u hu w hw hc
  have hV : ∀ xs : List Nat, (∀ x ∈ xs, x < (n+k)*n) → isMatch n xs = true →
      (canon ((n+k)*n) xs).length = e+1 →
      (realize p n k D W).E (fun a => monoEval a xs) = W (canon ((n+k)*n) xs) := by
    intro xs hx _ hl
    exact sumW_mono _ D W xs hx (by omega)
  have hgW : (realize p n k D W).E (fun a => monoEval a g) = W g := by
    change sumW _ D W _ = _
    rw [sumW_mono _ D W g (fun x hx => CM_lt hg hx) (by rw [hg.1]; omega), hg.1]
  constructor
  · intro i hi hf
    have h1 := line_bal hK hV hg hgl (fun j => var n i j) n
      (fun j hj => var_lt n k i j hi hj) (notin_of_pfree hf)
    have h2 := hE _ (Programme.«20261025-0459-proof-complexity».OntoSubst.mem_pig hi) g
      (by have := sumOne_deg (fun j => var n i j) n; omega)
    rw [hgW] at h1
    have h := Int.dvd_sub h2 h1
    refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp h
    exact ⟨0, by simp only [rowS]; omega⟩
  · intro j hj hf
    have h1 := line_bal hK hV hg hgl (fun i => var n i j) (n+k)
      (fun i hi => var_lt n k i j hi hj) (fun i _ => notin_of_hfree hf i hj)
    have h2 := hE _ (Programme.«20261025-0459-proof-complexity».OntoSubst.mem_hole hj) g
      (by have := sumOne_deg (fun i => var n i j) (n+k); omega)
    rw [hgW] at h1
    have h := Int.dvd_sub h2 h1
    refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp h
    exact ⟨0, by simp only [colS]; omega⟩

/-- All sum-axiom cases, including occupied and conflicting multipliers. -/
theorem line_of_bal {p n k D : Nat} {W : List Nat → Int}
    (hW : ConflictZero n k D W)
    (v : Nat → Nat) (M : Nat)
    (hvN : ∀ t < M, v t < (n+k)*n)
    (hvc : ∀ t < M, ∀ t' < M, t ≠ t' → cfl n (v t) (v t') = true)
    (hbal : ∀ g, CM n k g → g.length < D → (∀ t < M, v t ∉ g) →
      (p : Int) ∣ lineS n k W g v M - W g)
    (m : List Nat) (hm : m.length < D) :
    (p : Int) ∣ (realize p n k D W).E (fun a => monoEval a m * (sumOne v M).eval a) := by
  rcases all_lt_or (N := (n+k)*n) m with hx | ⟨x,hx,hN⟩
  case inr => exact vanish _ m x hx hN _
  let g := canon ((n+k)*n) m
  have hglen : g.length < D := Nat.lt_of_le_of_lt (canon_length_le _ _) hm
  have hsame : ∀ x, x ∈ m ↔ x ∈ g := fun x => (mem_canon' hx x).symm
  have eq : (fun a => monoEval a m * (sumOne v M).eval a) =
      (fun a => monoEval a g * (sumOne v M).eval a) := by
    funext a; rw [monoEval_congr a m g hsame]
  rw [eq]
  have hK := fun xs (hl : xs.length ≤ g.length+1) u hu w hw hc =>
    conflict_kill (p := p) hW xs (by omega) u hu w hw hc
  cases hmt : isMatch n g
  · obtain ⟨u,hu,w,hw,hc⟩ := not_match hmt
    exact line_conf hK u hu w hw hc v M
  have hg : CM n k g := ⟨canon_idem _, hmt⟩
  by_cases ho : ∃ t < M, v t ∈ g
  · obtain ⟨t,ht,hg0⟩ := ho
    exact line_occ hK v M t ht hg0 (fun s hs ne => hvc s hs t ht ne)
  have hf : ∀ t < M, v t ∉ g := fun t ht h => ho ⟨t,ht,h⟩
  have hV : ∀ xs : List Nat, (∀ x ∈ xs, x < (n+k)*n) → isMatch n xs = true →
      (canon ((n+k)*n) xs).length = g.length+1 →
      (realize p n k D W).E (fun a => monoEval a xs) = W (canon ((n+k)*n) xs) := by
    intro xs hxs _ hl
    exact sumW_mono _ D W xs hxs (by omega)
  have h1 := line_bal hK hV hg rfl v M hvN hf
  have h2 := hbal g hg hglen hf
  have hgW : (realize p n k D W).E (fun a => monoEval a g) = W g := by
    change sumW _ D W _ = _
    rw [sumW_mono _ D W g (fun x hx => CM_lt hg hx) (by rw [hg.1]; omega), hg.1]
  rw [hgW] at h1
  have h := Int.dvd_add h1 h2
  simpa only [Int.sub_add_cancel] using h

theorem design_of_bal {p n k D : Nat} {W : List Nat → Int}
    (hn : 0 < n) (hW : ConflictZero n k D W)
    (hB : ∀ e < D, Bal p n k W W e) :
    IsDesign (ontoFPHP n k) D (realize p n k D W) := by
  intro P hP m hm
  rcases Programme.«20261025-0459-proof-complexity».OntoSubst.mem_ontoFPHP hP with
    ⟨i,hi,rfl⟩ | ⟨j,hj,rfl⟩ | hc | hf
  · have hd := Programme.«20261025-1627-proof-complexity».OntoExt2.sumOne_deg_pos
      (fun j => var n i j) n hn
    apply line_of_bal hW (fun j => var n i j) n
      (fun j hj => var_lt n k i j hi hj) pig_cfl _ m (by omega)
    intro g hg hgl hfr
    exact (hB g.length hgl g hg rfl).1 i hi (pfree_of hn hfr)
  · have hd := Programme.«20261025-1627-proof-complexity».OntoExt2.sumOne_deg_pos
      (fun i => var n i j) (n+k) (by omega)
    apply line_of_bal hW (fun i => var n i j) (n+k)
      (fun i hi => var_lt n k i j hi hj) (hole_cfl hj) _ m (by omega)
    intro g hg hgl hfr
    exact (hB g.length hgl g hg rfl).2 j hj
      (hfree_of hn (fun x hx => CM_lt hg hx) hfr)
  · obtain ⟨j,i,i',hj,hi,hi',hii,rfl⟩ :=
      Programme.«20261025-0459-proof-complexity».OntoSubst.mem_collAx.mp hc
    rw [Programme.«20261025-0459-proof-complexity».OntoSubst.prod2_deg] at hm
    have eq : (fun a => monoEval a m * (prod2 (var n i j) (var n i' j)).eval a) =
        (fun a => monoEval a (m ++ [var n i j, var n i' j])) := by
      funext a
      rw [Programme.«20261025-0459-proof-complexity».OntoSubst.prod2_eval, monoEval_append]
      simp [monoEval, xv]
    rw [eq]
    exact conflict_kill hW _ (by simp; omega) (var n i j) (by simp)
      (var n i' j) (by simp) (hole_cfl (k := k) hj i hi i' hi' (by omega))
  · obtain ⟨i,j,j',hi,hj,hj',hjj,rfl⟩ :=
      Programme.«20261025-0459-proof-complexity».OntoSubst.mem_funcAx.mp hf
    rw [Programme.«20261025-0459-proof-complexity».OntoSubst.prod2_deg] at hm
    have eq : (fun a => monoEval a m * (prod2 (var n i j) (var n i j')).eval a) =
        (fun a => monoEval a (m ++ [var n i j, var n i j'])) := by
      funext a
      rw [Programme.«20261025-0459-proof-complexity».OntoSubst.prod2_eval, monoEval_append]
      simp [monoEval, xv]
    rw [eq]
    exact conflict_kill hW _ (by simp; omega) (var n i j) (by simp)
      (var n i j') (by simp) (pig_cfl (i := i) j hj j' hj' (by omega))

/-- P44's equivalence, with its zero-conflict hypothesis stated explicitly. -/
theorem design_iff {p n k D : Nat} {W : List Nat → Int}
    (hn : 0 < n) (hW : ConflictZero n k D W) :
    IsDesign (ontoFPHP n k) D (sumWFn p ((n+k)*n) D W) ↔
      ∀ e < D, Bal p n k W W e :=
  ⟨bal_of_design hW, design_of_bal hn hW⟩

/-- Finite matching-coordinate criterion for variable-conditioned closure. -/
theorem conditioned_extends_iff {p n k D d x : Nat} {U W : List Nat → Int}
    (hd : d+1 ≤ D) (hx : x < (n+k)*n)
    (hU : ConflictZero n k D U) (hW : ConflictZero n k D W) :
    Extends d (realize p n k D U) (xFn (realize p n k D W) x) ↔
    ∀ g, CM n k g → g.length ≤ d →
      (p : Int) ∣ U g - W (canon ((n+k)*n) (x :: g)) := by
  have read (g : List Nat) (hg : CM n k g) (hl : g.length ≤ d) :
      (realize p n k D U).E (fun a => monoEval a g) -
        (xFn (realize p n k D W) x).E (fun a => monoEval a g) =
        U g - W (canon ((n+k)*n) (x :: g)) := by
    change sumW _ D U _ - sumW _ D W _ = _
    rw [show (fun a => xv x a * monoEval a g) = (fun a => monoEval a (x::g)) from
      funext (fun a => (monoEval_cons x g a).symm)]
    rw [sumW_mono _ D U g (fun y hy => CM_lt hg hy) (by rw [hg.1]; omega), hg.1,
      sumW_mono _ D W (x::g) (by intro y hy; rcases List.mem_cons.mp hy with rfl | hy; exact hx; exact CM_lt hg hy)
        (by have := canon_length_le ((n+k)*n) (x::g); simp only [List.length_cons] at this; omega)]
  constructor
  · intro h g hg hl
    rw [← read g hg hl]
    exact h g hl
  · intro h t ht
    rcases all_lt_or (N := (n+k)*n) t with hlt | ⟨y,hy,hN⟩
    · let g := canon ((n+k)*n) t
      have hglen : g.length ≤ d := Nat.le_trans (canon_length_le _ _) ht
      have hs : ∀ y, y ∈ t ↔ y ∈ g := fun y => (mem_canon' hlt y).symm
      rw [Fm_congr (realize p n k D U) t g hs,
        Fm_congr (xFn (realize p n k D W) x) t g hs]
      cases hm : isMatch n g
      · obtain ⟨u,hu,w,hw,hc⟩ := not_match hm
        apply Int.dvd_sub
        · exact conflict_kill hU g (by omega) u hu w hw hc
        · change (p : Int) ∣ (realize p n k D W).E (fun a => xv x a * monoEval a g)
          rw [show (fun a => xv x a * monoEval a g) = (fun a => monoEval a (x::g)) from
            funext (fun a => (monoEval_cons x g a).symm)]
          exact conflict_kill hW (x::g) (by simp; omega) u (by simp [hu]) w (by simp [hw]) hc
      · rw [read g ⟨canon_idem _,hm⟩ hglen]
        exact h g ⟨canon_idem _,hm⟩ hglen
    · exact Int.dvd_sub (vanish0 _ t y hy hN) (vanish0 _ t y hy hN)
/-- Conditioning by a variable outside the board vanishes on every input. -/
theorem condition_outside {p n k D x : Nat} (W : List Nat → Int)
    (hx : (n+k)*n ≤ x) (f : (Nat → Bool) → Int) :
    (p : Int) ∣ (xFn (realize p n k D W) x).E f := by
  change (p : Int) ∣ (realize p n k D W).E (fun a => xv x a * f a)
  rw [(realize p n k D W).supp _ (fun _ => 0) (by
    intro a ha
    simp only [xv, ha x hx, Bool.false_eq_true, ↓reduceIte, Int.zero_mul])]
  exact (realize p n k D W).zero
end Programme.«20261102-1249-proof-complexity».MomentBridge
#print axioms Programme.«20261102-1249-proof-complexity».MomentBridge.extends_iff
#print axioms Programme.«20261102-1249-proof-complexity».MomentBridge.design_iff
#print axioms Programme.«20261102-1249-proof-complexity».MomentBridge.conditioned_extends_iff

#print axioms Programme.«20261102-1249-proof-complexity».MomentBridge.condition_outside
