import Programme.«20261104-1627-proof-complexity».ReconstructionSupport
namespace Programme.«20261104-1627-proof-complexity».BooleanReconstruction
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261104-1627-proof-complexity».OutsideDifference

def zeroPoly (x : Nat) (P : Poly Nat) : Poly Nat :=
  ⟨P.terms.filter (fun t => x ∉ t.2)⟩
theorem zeroPoly_eval (x : Nat) (P : Poly Nat) (a : Nat → Bool) :
    (zeroPoly x P).eval a = P.eval (set a x false) := by
  unfold zeroPoly Poly.eval
  generalize P.terms = T
  induction T with
  | nil => simp
  | cons t T ih =>
    by_cases hx : x ∈ t.2
    · simp only [List.filter_cons, hx, decide_false, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
      change _ = t.1 * monoEval (set a x false) t.2 + _
      rw [← ih]
      simp [mono_set, hx]
    · have hm : t.2.filter (fun y => y != x) = t.2 := by
        apply List.filter_eq_self.mpr
        intro y hy
        simp only [bne_iff_ne]
        intro he; subst y; exact hx hy
      simp only [List.filter_cons, hx, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons, List.sum_cons]
      rw [ih]
      simp [mono_set, hx, hm]

theorem zero_leaf (s : List Nat) :
    ∀ e ∈ expand s (fun _ => (0 : Int)), ∀ a, e.2 a = 0 := by
  induction s with
  | nil => intro e he; simp [expand] at he; subst e; simp
  | cons x xs ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact ih e he
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
      simpa using ih v (by simpa using hv)

/-- A termwise weighted bound treats empty polynomials without truncated subtraction. -/
theorem leaf_term_budget (s : List Nat) (P : Poly Nat) (d : Nat)
    (hP : ∀ t ∈ P.terms, t.2.length ≤ d) :
    ∀ e ∈ expand s P.eval, ∃ Q : Poly Nat,
      (∀ a, Q.eval a = e.2 a) ∧
      ∀ t ∈ Q.terms, t.2.length + e.1.length ≤ d := by
  induction s generalizing P d with
  | nil =>
    intro e he
    simp [expand] at he
    subst e
    exact ⟨P, fun _ => rfl, by simpa using hP⟩
  | cons x xs ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · have hz : (zeroPoly x P).eval = fun a => P.eval (set a x false) := by
        funext a; exact zeroPoly_eval x P a
      rw [← hz] at he
      exact ih (zeroPoly x P) d (by
        intro t ht; exact hP t (List.mem_filter.mp ht).1) e he
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
      have hd : (diff x P).eval = fun a => P.eval (set a x true) - P.eval (set a x false) := by
        funext a; exact diff_eval x P a
      rw [← hd] at hu
      by_cases hpos : 0 < d
      · obtain ⟨Q, hQ, hb⟩ := ih (diff x P) (d-1) (by
          intro t ht
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
          obtain ⟨hv, hx⟩ := List.mem_filter.mp hv
          have hl := erase_length x v.2 (by simpa using hx)
          have hp := hP v hv
          dsimp
          omega) u hu
        refine ⟨Q, hQ, ?_⟩
        intro t ht
        have hh := hb t ht
        simp only [List.length_cons]
        omega
      · have hempty : (diff x P).terms = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro t ht
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
          obtain ⟨hv, hx⟩ := List.mem_filter.mp hv
          have hl := erase_length x v.2 (by simpa using hx)
          have hp := hP v hv
          omega
        have hfun : (diff x P).eval = fun _ => 0 := by
          funext b; simp [Poly.eval, hempty]
        rw [hfun] at hu
        refine ⟨⟨[]⟩, ?_, ?_⟩
        · intro a; simpa [Poly.eval] using (zero_leaf xs u hu a).symm
        · simp

theorem leaf_degree_or_zero (s : List Nat) (P : Poly Nat)
    (e : List Nat × Fn) (he : e ∈ expand s P.eval) :
    ∃ Q : Poly Nat, (∀ a, Q.eval a = e.2 a) ∧
      (e.1.length ≤ P.deg → Q.deg + e.1.length ≤ P.deg) ∧
      (P.deg < e.1.length → Q.terms = []) := by
  obtain ⟨Q, hQ, hb⟩ := leaf_term_budget s P P.deg
    ((deg_le_iff P P.deg).mp (Nat.le_refl _)) e he
  refine ⟨Q, hQ, ?_, ?_⟩
  · intro hu
    have hd : Q.deg ≤ P.deg - e.1.length := by
      apply (deg_le_iff _ _).mpr
      intro t ht
      have hh := hb t ht
      omega
    omega
  · intro hu
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro t ht
    have hh := hb t ht
    omega

theorem leaf_vanish (s : List Nat) (P : Poly Nat)
    (e : List Nat × Fn) (he : e ∈ expand s P.eval)
    (hu : P.deg < e.1.length) : ∀ a, e.2 a = 0 := by
  obtain ⟨Q, hQ, _, hz⟩ := leaf_degree_or_zero s P e he
  intro a
  rw [← hQ, Poly.eval, hz hu]
  rfl
open Programme.«20261025-0459-proof-complexity».OntoSubst
open Programme.«20261104-1627-proof-complexity».SupportedCertificates Programme.«20261104-1627-proof-complexity».OffboardSections

theorem leaf_supported_degree (B : Nat → Bool) (s : List Nat) (P : Poly Nat)
    (hP : ∀ t ∈ P.terms, ∀ x ∈ t.2, B x = true ∨ x ∈ s)
    (e : List Nat × Fn) (he : e ∈ expand s P.eval)
    (hu : e.1.length ≤ P.deg) :
    ∃ Q : Poly Nat, Supported B Q ∧ (∀ a, Q.eval a = e.2 a) ∧
      Q.deg + e.1.length ≤ P.deg := by
  obtain ⟨Q, hQ, hd, _⟩ := leaf_degree_or_zero s P e he
  refine ⟨Poly.subst (sectionSubst B (fun _ => false)) Q,
    section_supported B _ Q, ?_, ?_⟩
  · intro a
    rw [subst_eval, hQ]
    have hf : ∀ a b, (∀ x, B x = true ∨ x ∈ s → a x = b x) → P.eval a = P.eval b := by
      intro a b hab
      apply eval_agree (B := fun x => decide (B x = true ∨ x ∈ s))
      · intro t ht x hx; simpa using hP t ht x hx
      · intro x hx; exact hab x (by simpa using hx)
    exact leaf_agree B s P.eval hf e he _ _ (by
      intro x hx; simp [pull_section, hx])
  · have hh := subst_deg (sectionSubst B (fun _ => false)) Q
    have hh' := hd hu
    omega
end Programme.«20261104-1627-proof-complexity».BooleanReconstruction
#print axioms Programme.«20261104-1627-proof-complexity».BooleanReconstruction.leaf_degree_or_zero
#print axioms Programme.«20261104-1627-proof-complexity».BooleanReconstruction.leaf_vanish

#print axioms Programme.«20261104-1627-proof-complexity».BooleanReconstruction.leaf_supported_degree
