import Programme.«20261025-0459b-proof-complexity».Indep

/-!
# Rise counting for the Hall plucks (M3 of P88)

Hall-violator test graphs are coded by one assignment `α : Nat → Bool` on vertex coordinates:
left `i ↦ 2i` (`α (2i)` = "`i ∈ S`"), right `j ↦ 2j+1` (`α (2j+1)` = "`j ∈ T`"); the edge `(i,j)`
of `negG α` is absent iff `i ∈ S` and `j ∉ T` (pr's `vG` with `S i = α (2i)`, `T j = α (2j+1)`).

A pluck event (pr's export in P101) gives petals with residual edge lists `Q_j` (`P_j \ I`) and
residues `R_j` (vertex coordinates of `P_j` outside the core), the residues disjoint and disjoint
from a `base` that holds all other coordinates of the petals. `hall_rise`: if each `Q_j` is a
matching with `≤ ℓ` edges and every edge of `Q_j` has an endpoint in `R_j`, at most a
`(1-2^{-ℓ})^p` fraction of the assignments on `base ++ R_1 ++ … ++ R_p` make no `Q_j` present.
-/

namespace Programme.«20261025-0459b-proof-complexity».HallRise

open Programme.«20261025-0459b-proof-complexity».Indep

/-- The Hall-violator graph of `α`: edge `(i,j)` absent iff `α (2i)` and not `α (2j+1)`. -/
def negG (α : Nat → Bool) (i j : Nat) : Bool := !(α (2 * i) && !α (2 * j + 1))

def pres (H : Nat → Nat → Bool) (P : List (Nat × Nat)) : Prop := ∀ e ∈ P, H e.1 e.2 = true

instance (H : Nat → Nat → Bool) (P : List (Nat × Nat)) : Decidable (pres H P) := by
  unfold pres; infer_instance

/-- A petal: residual edges `Q` and residue coordinates `R`. -/
structure Petal where
  Q : List (Nat × Nat)
  R : List Nat

/-- The petal's hypotheses: `Q` a duplicate-free matching with `≤ ℓ` edges, every endpoint in
`base ∪ R`, every edge with an endpoint in `R`. -/
def Ok (ℓ : Nat) (base : List Nat) (P : Petal) : Prop :=
  P.Q.Nodup ∧ P.R.Nodup ∧ P.Q.length ≤ ℓ ∧
  (∀ e ∈ P.Q, ∀ e' ∈ P.Q, e.1 = e'.1 → e = e') ∧ (∀ e ∈ P.Q, ∀ e' ∈ P.Q, e.2 = e'.2 → e = e') ∧
  (∀ e ∈ P.Q, (2 * e.1 ∈ base ∨ 2 * e.1 ∈ P.R) ∧ (2 * e.2 + 1 ∈ base ∨ 2 * e.2 + 1 ∈ P.R)) ∧
  (∀ e ∈ P.Q, 2 * e.1 ∈ P.R ∨ 2 * e.2 + 1 ∈ P.R)

def blk (P : Petal) : Blk := ⟨P.R, fun α => pres (negG α) P.Q, inferInstance⟩

/-- The coordinate fixed to force an edge present: its left endpoint (set to "not in `S`") if
that lies in `R`, else its right endpoint (set to "in `T`"). -/
def pick (R : List Nat) (e : Nat × Nat) : Nat := if 2 * e.1 ∈ R then 2 * e.1 else 2 * e.2 + 1

/-- Even coordinates false, odd ones true. -/
def good (y : Nat) : Bool := y % 2 == 1

theorem nodup_map_on {f : Nat × Nat → Nat} : ∀ {Q : List (Nat × Nat)}, Q.Nodup →
    (∀ e ∈ Q, ∀ e' ∈ Q, f e = f e' → e = e') → (Q.map f).Nodup
  | [], _, _ => List.nodup_nil
  | e :: Q, hQ, h => by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_on (List.nodup_cons.1 hQ).2
      (fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))⟩
    obtain ⟨e', he', hf⟩ := List.mem_map.1 hm
    have := h e (List.mem_cons_self ..) e' (List.mem_cons_of_mem _ he') hf.symm
    subst this; exact (List.nodup_cons.1 hQ).1 he'

theorem pick_nodup {R : List Nat} {Q : List (Nat × Nat)} (hQ : Q.Nodup)
    (h1 : ∀ e ∈ Q, ∀ e' ∈ Q, e.1 = e'.1 → e = e') (h2 : ∀ e ∈ Q, ∀ e' ∈ Q, e.2 = e'.2 → e = e') :
    (Q.map (pick R)).Nodup := by
  refine nodup_map_on hQ ?_
  intro e he e' he' h
  unfold pick at h
  split at h <;> split at h
  · exact h1 e he e' he' (by omega)
  · omega
  · omega
  · exact h2 e he e' he' (by omega)

theorem pick_mem {R : List Nat} {e : Nat × Nat} (h : 2 * e.1 ∈ R ∨ 2 * e.2 + 1 ∈ R) :
    pick R e ∈ R := by
  unfold pick; split
  · assumption
  · rcases h with h | h
    · contradiction
    · exact h

theorem pres_of_good {R : List Nat} {Q : List (Nat × Nat)} {α : Nat → Bool}
    (h : ∀ y ∈ Q.map (pick R), α y = good y) : pres (negG α) Q := by
  intro e he
  have hy := h (pick R e) (List.mem_map_of_mem he)
  unfold pick at hy; unfold negG
  split at hy
  · have : good (2 * e.1) = false := by simp [good]
    simp [this] at hy; simp [hy]
  · have : good (2 * e.2 + 1) = true := by simp [good]
    simp [this] at hy; simp [hy]

theorem fr (ℓ : Nat) (base : List Nat) (P : Petal) (hP : Ok ℓ base P) (a : Nat → Bool) :
    2 ^ P.R.length ≤ 2 ^ ℓ * cnt (ext P.R [a]) (fun α => pres (negG α) P.Q) := by
  obtain ⟨hQ, hR, hl, h1, h2, _, h4⟩ := hP
  have hD := fix_count good P.R (P.Q.map (pick P.R)) a hR (pick_nodup hQ h1 h2)
    (by intro y hy; obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy; exact pick_mem (h4 e he))
  have hm : cnt (ext P.R [a]) (fun α => ∀ y ∈ P.Q.map (pick P.R), α y = good y) ≤
      cnt (ext P.R [a]) (fun α => pres (negG α) P.Q) :=
    cnt_mono (fun α _ h => pres_of_good h)
  rw [List.length_map] at hD
  calc 2 ^ P.R.length ≤ 2 ^ P.Q.length * cnt (ext P.R [a]) _ := hD
    _ ≤ 2 ^ ℓ * cnt (ext P.R [a]) (fun α => pres (negG α) P.Q) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hl) hm

theorem dep (ℓ : Nat) (base : List Nat) (P : Petal) (hP : Ok ℓ base P) (α β : Nat → Bool)
    (h : ∀ y, (y ∈ base ∨ y ∈ P.R) → α y = β y) :
    pres (negG α) P.Q ↔ pres (negG β) P.Q := by
  have h3 := hP.2.2.2.2.2.1
  have key : ∀ e ∈ P.Q, negG α e.1 e.2 = negG β e.1 e.2 := by
    intro e he
    unfold negG; rw [h _ (h3 e he).1, h _ (h3 e he).2]
  exact ⟨fun hp e he => (key e he) ▸ hp e he, fun hp e he => (key e he).symm ▸ hp e he⟩

/-- **M3.** For petals satisfying `Ok ℓ base` with residues disjoint from each other and from
`base`: the assignments on `U = base ++ R_1 ++ … ++ R_p` under which no residual matching `Q_j` is
present in the Hall-violator graph number at most `2^|U| (1 - 2^{-ℓ})^p`. -/
theorem hall_rise (ℓ : Nat) (base : List Nat) (Ps : List Petal)
    (hnd : (base ++ Ps.flatMap Petal.R).Nodup) (hok : ∀ P ∈ Ps, Ok ℓ base P) :
    cnt (asg (base ++ Ps.flatMap Petal.R)) (fun α => ∀ P ∈ Ps, ¬pres (negG α) P.Q) *
        2 ^ (ℓ * Ps.length) ≤
      2 ^ (base ++ Ps.flatMap Petal.R).length * (2 ^ ℓ - 1) ^ Ps.length := by
  have hf : flat (Ps.map blk) = Ps.flatMap Petal.R := by
    simp [flat, blk, List.flatMap_map]
  have h := indep ℓ base (Ps.map blk) (by rw [hf]; exact hnd)
    (by
      intro b hb α β hαβ
      obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hb
      exact dep ℓ base P (hok P hP) α β hαβ)
    (by
      intro b hb a
      obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hb
      exact fr ℓ base P (hok P hP) a)
  rw [hf, List.length_map] at h
  rw [cnt_congr (Q := none (Ps.map blk))]
  · exact h
  · intro α _
    simp only [Indep.none, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rfl

end Programme.«20261025-0459b-proof-complexity».HallRise
