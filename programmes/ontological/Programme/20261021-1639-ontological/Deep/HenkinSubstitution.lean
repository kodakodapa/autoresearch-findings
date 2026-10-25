import Programme.«20261021-1639-ontological».Deep.Henkin

namespace Programme.«20261021-1639-ontological».Deep.Henkin

theorem push_liftRen (r : Ren Γ Δ) (ρ : Assignment h Δ) (x : h.D a) :
    (fun {b} (v : Var (a :: Γ) b) => push ρ x (liftRen r v)) =
    (fun {b} (v : Var (a :: Γ) b) => push (fun v => ρ (r v)) x v) := by
  funext b v
  cases v <;> rfl

theorem translate_rename (h : Frame W) (I : ∀ {a}, C a → h.D a)
    (t : Term C Γ a) (r : Ren Γ Δ) (ρ : Assignment h Δ) :
    translate h I (rename r t) ρ = translate h I t (fun v => ρ (r v)) := by
  induction t generalizing Δ with
  | var v => rfl
  | const c => rfl
  | app f x hf hx => simp only [rename, translate, hf, hx]
  | lam t ih => simp only [rename, translate, ih, push_liftRen]
  | falsum => rfl
  | imp p q hp hq => simp only [rename, translate, hp, hq]
  | box p hp => simp only [rename, translate, hp]
  | all p hp => simp only [rename, translate, hp, push_liftRen]
  | equal s t hs ht => simp only [rename, translate, hs, ht]

theorem translate_liftSub (h : Frame W) (I : ∀ {a}, C a → h.D a)
    (s : Sub C Γ Δ) (ρ : Assignment h Δ) (x : h.D a) :
    (fun {b} (v : Var (a :: Γ) b) => translate h I (liftSub s v) (push ρ x)) =
    (fun {b} (v : Var (a :: Γ) b) => push (fun u => translate h I (s u) ρ) x v) := by
  funext b v
  cases v with
  | here => rfl
  | there v => simp only [liftSub, translate_rename]; rfl

theorem translate_subst (h : Frame W) (I : ∀ {a}, C a → h.D a)
    (t : Term C Γ a) (s : Sub C Γ Δ) (ρ : Assignment h Δ) :
    translate h I (subst s t) ρ = translate h I t (fun v => translate h I (s v) ρ) := by
  induction t generalizing Δ with
  | var v => rfl
  | const c => rfl
  | app f x hf hx => simp only [subst, translate, hf, hx]
  | lam t ih => simp only [subst, translate, ih, translate_liftSub]
  | falsum => rfl
  | imp p q hp hq => simp only [subst, translate, hp, hq]
  | box p hp => simp only [subst, translate, hp]
  | all p hp => simp only [subst, translate, hp, translate_liftSub]
  | equal u v hu hv => simp only [subst, translate, hu, hv]

theorem denotes_iff_translate (m : Model C W) (ρ : Assignment m.frame Γ)
    (t : Term C Γ a) (v : m.frame.D a) :
    Denotes m.frame m.interp ρ t v ↔ translate m.frame m.interp t ρ = v := by
  constructor
  · exact agreement
  · intro hv
    rw [← hv]
    exact translate_denotes m ρ t

theorem denotes_rename (m : Model C W) (t : Term C Γ a)
    (r : Ren Γ Δ) (ρ : Assignment m.frame Δ) (v : m.frame.D a) :
    Denotes m.frame m.interp ρ (rename r t) v ↔
      Denotes m.frame m.interp (fun x => ρ (r x)) t v := by
  simp only [denotes_iff_translate, translate_rename]

theorem denotes_subst (m : Model C W) (t : Term C Γ a)
    (s : Sub C Γ Δ) (ρ : Assignment m.frame Δ) (v : m.frame.D a) :
    Denotes m.frame m.interp ρ (subst s t) v ↔
      Denotes m.frame m.interp (fun x => translate m.frame m.interp (s x) ρ) t v := by
  simp only [denotes_iff_translate, translate_subst]

#print axioms translate_rename
#print axioms translate_subst
#print axioms denotes_rename
#print axioms denotes_subst
end Programme.«20261021-1639-ontological».Deep.Henkin
