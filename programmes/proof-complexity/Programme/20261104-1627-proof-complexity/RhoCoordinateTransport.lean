import Programme.«20261104-1627-proof-complexity».MixedRhoLowering
namespace Programme.«20261104-1627-proof-complexity».RhoCoordinateTransport
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-1627-proof-complexity».NoDrop
private theorem zeros (L : List Label) : (L.map (fun _ => (0 : Int))).sum = 0 := by
  induction L with
  | nil => rfl
  | cons x L ih => simpa using ih
private theorem dedup (L : List Label) : L.eraseDups.Nodup := by
  cases L with
  | nil => simp
  | cons x xs =>
    rw [List.eraseDups_cons, List.nodup_cons]
    constructor
    · simp only [List.mem_eraseDups, List.mem_filter]
      intro h
      simpa using h.2
    · exact dedup (xs.filter fun b => !b == x)
termination_by L.length
decreasing_by have := List.length_filter_le (fun b => !b == x) xs; simp_all; omega
private theorem delta_sum (L : List Label) (hL : L.Nodup) (g : Label)
    (hg : g ∈ L) (c : Int) (f : Label → Int) :
    (L.map (fun x => (if g = x then c else 0) * f x)).sum = c * f g := by
  induction L with
  | nil => simp at hg
  | cons x L ih =>
    obtain ⟨hx,hn⟩ := List.nodup_cons.mp hL
    by_cases he : g = x
    · subst g
      have hz : (L.map (fun y => (if x = y then c else 0) * f y)).sum = 0 := by
        have hm : L.map (fun y => (if x = y then c else 0) * f y) = L.map (fun _ => (0 : Int)) := by
          apply List.map_congr_left
          intro y hy
          have hxy : x ≠ y := by intro h; exact hx (h ▸ hy)
          simp [hxy]
        rw [hm, zeros]
      simp [hz]
    · have hg' : g ∈ L := (List.mem_cons.mp hg).resolve_left he
      simp only [List.map_cons,List.sum_cons,he,ite_false,Int.zero_mul,Int.zero_add]
      exact ih hn hg'
private theorem map_add_sum (L : List Label) (f g : Label → Int) :
    (L.map (fun x => f x + g x)).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => rfl
  | cons x L ih => simp only [List.map_cons,List.sum_cons,ih]; omega
/-- Aggregate coordinates determine every integer linear observable of raw labels. -/
theorem observable_group (v : Vector) (L : List Label) (hL : L.Nodup)
    (hv : ∀ a ∈ v, a.2 ∈ L) (f : Label → Int) :
    (v.map (fun a => a.1 * f a.2)).sum =
      (L.map (fun g => vectorCoeff v g * f g)).sum := by
  induction v with
  | nil => simp [vectorCoeff, zeros]
  | cons a v ih =>
    have hc (g : Label) : vectorCoeff (a::v) g =
        (if a.2 = g then a.1 else 0) + vectorCoeff v g := by
      by_cases h : a.2 = g <;> simp [vectorCoeff,h]
    simp only [List.map_cons,List.sum_cons]
    simp only [hc,Int.add_mul]
    rw [map_add_sum,delta_sum L hL a.2 (hv a (by simp)),
      ih (fun b hb => hv b (by simp [hb]))]
private theorem weighted_congr (p : Nat) (L : List Label) (f g w : Label → Int)
    (h : ∀ x ∈ L, (p : Int) ∣ f x - g x) :
    (p : Int) ∣ (L.map (fun x => f x*w x)).sum - (L.map (fun x => g x*w x)).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hx := Int.dvd_trans (h x (by simp)) (Int.dvd_mul_right _ (w x))
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons]
    have he : f x*w x + (L.map (fun x => f x*w x)).sum -
        (g x*w x + (L.map (fun x => g x*w x)).sum) =
        (f x-g x)*w x + ((L.map (fun x => f x*w x)).sum - (L.map (fun x => g x*w x)).sum) := by
      rw [Int.sub_mul]; omega
    rw [he]
    exact Int.dvd_add hx ht
/-- No validity or finite-board assumption is needed for rho transport. -/
theorem rho_congr {p n : Nat} {v w : Vector}
    (h : ∀ g, (p : Int) ∣ vectorCoeff v g - vectorCoeff w g) (a : Nat → Bool) :
    (p : Int) ∣ (rho n v).eval a - (rho n w).eval a := by
  let L := ((v.map (·.2)) ++ (w.map (·.2))).eraseDups
  have hL : L.Nodup := dedup _
  have hv : ∀ t ∈ v, t.2 ∈ L := by
    intro t ht
    simp only [L,List.mem_eraseDups,List.mem_append,List.mem_map]
    exact Or.inl ⟨t,ht,rfl⟩
  have hw : ∀ t ∈ w, t.2 ∈ L := by
    intro t ht
    simp only [L,List.mem_eraseDups,List.mem_append,List.mem_map]
    exact Or.inr ⟨t,ht,rfl⟩
  simp only [rho,Poly.eval,List.map_map,Function.comp_def]
  change (p : Int) ∣ (v.map (fun t => t.1 * monoEval a (mono n t.2.base))).sum -
    (w.map (fun t => t.1 * monoEval a (mono n t.2.base))).sum
  rw [observable_group v L hL hv (fun g => monoEval a (mono n g.base)),
    observable_group w L hL hw (fun g => monoEval a (mono n g.base))]
  exact weighted_congr p L _ _ _ (fun g _ => h g)
theorem lowering_transport {p n D : Nat} {A : List (Poly Nat)} {v w : Vector}
    (h : ∀ g, (p : Int) ∣ vectorCoeff v g - vectorCoeff w g)
    (hw : NSIn p A D (rho n w).eval) : NSIn p A D (rho n v).eval := by
  apply nsIn_congr hw
  exact rho_congr h
theorem combine_lowering {p n D : Nat} {A : List (Poly Nat)}
    (c : List (Int × Vector))
    (h : ∀ t ∈ c, NSIn p A D (rho n t.2).eval) :
    NSIn p A D (rho n (combine c)).eval := by
  induction c with
  | nil => exact ⟨[], by simp, by simp [combine,rho,Poly.eval]⟩
  | cons t c ih =>
    have hh := nsIn_lin t.1 1 (h t (by simp))
      (ih (fun u hu => h u (by simp [hu])))
    apply nsIn_congr hh
    intro a
    have hs (v : Vector) :
        ((v.map (fun b => t.1*b.1*monoEval a (mono n b.2.base)))).sum =
          t.1 * (v.map (fun b => b.1*monoEval a (mono n b.2.base))).sum := by
      induction v with
      | nil => simp
      | cons b v ih =>
        simp only [List.map_cons,List.sum_cons]
        rw [ih,Int.mul_add,Int.mul_assoc]
    simp only [combine,List.flatMap_cons,rho,Poly.eval,List.map_append,List.sum_append,
      List.map_map,Function.comp_def,Int.one_mul]
    rw [hs]
    simp

/-- Spanning becomes a lowering theorem only after every enumerated generator lowers. -/
theorem kernel_lowering_of_spanning {p m n d D : Nat} {A : List (Poly Nat)}
    (span : Spanning p m n d)
    (hlower : ∀ w ∈ syzygies m n d, NSIn p A D (rho n w).eval)
    {v : Vector} (hv : Kernel p m n d v) : NSIn p A D (rho n v).eval := by
  obtain ⟨c,hc,he⟩ := span v hv
  exact lowering_transport he (combine_lowering c (fun t ht => hlower t.2 (hc t ht)))
#print axioms rho_congr
#print axioms lowering_transport
#print axioms combine_lowering
#print axioms kernel_lowering_of_spanning
end Programme.«20261104-1627-proof-complexity».RhoCoordinateTransport
