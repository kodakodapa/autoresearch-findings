import Programme.«20261101-0614-proof-complexity».Singleton
import Programme.«20261101-0614-proof-complexity».PairCode
namespace Programme.«20261101-0614-proof-complexity».SingletonBridge
open Programme.«20261031-2024-proof-complexity».NativeIter
namespace C
end C
open Programme.«20261101-0614-proof-complexity».Composition
noncomputable def unpair (q : Nat) : Nat × Nat := by
  classical
  exact if h : ∃ ab : Nat × Nat, pair ab.1 ab.2 = q then Classical.choose h else (0,0)
theorem unpair_pair (a b : Nat) : unpair (pair a b) = (a,b) := by
  have h : ∃ ab : Nat × Nat, pair ab.1 ab.2 = pair a b := ⟨(a,b),rfl⟩
  simp only [unpair, dite_eq_left h]
  have he := Classical.choose_spec h
  obtain ⟨ha,hb⟩ := pair_injective he
  exact Prod.ext ha hb
noncomputable def rho (L : Nat) (v : Var) : Var :=
  if v.1 = 0 then (0,(unpair v.2).2)
  else let yz := unpair v.2; let xz := unpair yz.2
       (yz.1+1,xz.1*L+xz.2)
@[simp] theorem rho_f (L y : Nat) : rho L (fVar 0 y) = (0,y) := by
  simp [rho, fVar, unpair_pair]
@[simp] theorem rho_s (L y x z : Nat) : rho L (sVar y x z) = Singleton.block L y (x,z) := by
  simp [rho, sVar, unpair_pair, Singleton.block]

theorem structural_mem (L x : Nat) (hx : x < L) :
    UnaryIter.row L x ∈ Singleton.structural L := by
  simp only [Singleton.structural, List.mem_flatMap]
  exact ⟨x,List.mem_range.mpr hx,by simp⟩

theorem row_image (L y x : Nat) :
    renameClause (rho L) ((List.range L).map (fun z => pos (sVar y x z))) =
      renameClause (Singleton.block L y) (UnaryIter.row L x) := by
  simp [renameClause, renameLit, UnaryIter.row, pos, List.map_map, Function.comp_def]

theorem single_not_structural (L x z : Nat) :
    [((x,z),false)] ∉ Singleton.structural L := by
  simp [Singleton.structural, UnaryIter.row, UnaryIter.minus,
    List.mem_flatMap, List.mem_map, List.mem_filter]
  intro u hu he
  have hh := congrArg (fun c : Clause => c.head?.map Prod.snd) he
  cases L with
  | zero => simp [UnaryIter.row] at hh
  | succ n => simp [UnaryIter.row, List.range_succ_eq_map] at hh

theorem cross_not_structural (L x z : Nat) (hxz : x < z) :
    [((x,z),false), ((z,z),false)] ∉ Singleton.structural L := by
  simp only [Singleton.structural, List.mem_flatMap, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_filter, List.mem_range]
  rintro ⟨u, hu, he | ⟨v,hv,t,ht,he⟩⟩
  · have hh := congrArg (fun c : Clause => c.head?.map Prod.snd) he
    cases L with
    | zero => simp [UnaryIter.row] at hh
    | succ n => simp [UnaryIter.row, List.range_succ_eq_map] at hh
  · simp [UnaryIter.minus] at he
    omega

theorem target_block (N L y : Nat) (hy : y < N) (c : Clause)
    (hc : c ∈ UnaryIter.cnf L) : Singleton.image L y c ∈ Singleton.cnf N L := by
  exact Singleton.generator_spec N L _ |>.mpr (Or.inr ⟨y,hy,c,hc,rfl⟩)

theorem target_structural (N L y : Nat) (hy : y < N) (c : Clause)
    (hc : c ∈ Singleton.structural L) :
    (renameClause (Singleton.block L y) c).eraseDups ∈ Singleton.cnf N L := by
  have hu : c ∈ UnaryIter.cnf L := by
    simp only [UnaryIter.cnf, List.mem_eraseDups, UnaryIter.raw, List.mem_append]
    exact Or.inl (Or.inl (Or.inl hc))
  simpa [Singleton.image, hc] using target_block N L y hy c hu

theorem target_single (N L y x z : Nat) (hy : y < N)
    (hc : [((x,z),false)] ∈ UnaryIter.cnf L) :
    [((Singleton.block L y (x,z)),false), Singleton.outer y].eraseDups ∈
      Singleton.cnf N L := by
  simpa [Singleton.image, single_not_structural, renameClause, renameLit] using
    target_block N L y hy _ hc

theorem target_cross (N L y x z : Nat) (hy : y < N) (hxz : x < z)
    (hc : [((x,z),false), ((z,z),false)] ∈ UnaryIter.cnf L) :
    [((Singleton.block L y (x,z)),false), ((Singleton.block L y (z,z)),false),
      Singleton.outer y].eraseDups ∈ Singleton.cnf N L := by
  simpa [Singleton.image, cross_not_structural L x z hxz, renameClause, renameLit] using
    target_block N L y hy _ hc

theorem dedup_self {c : Clause} (h : c.Nodup) : c.eraseDups = c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    have hh := List.nodup_cons.mp h
    rw [List.eraseDups_cons]
    have hf : c.filter (fun b => !b == l) = c := by
      apply List.filter_eq_self.mpr
      intro b hb
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
      intro he
      subst b
      exact hh.1 hb
    rw [hf, ih hh.2]

theorem map_nodup {l : List Nat} (h : l.Nodup) {f : Nat → Lit}
    (hf : ∀ a b, f a = f b → a = b) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp h
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      obtain ⟨b,hb,he⟩ := List.mem_map.mp hm
      have heq := hf b a he
      subst b
      exact ha hb
    · exact ih hl

theorem outer_nodup (N : Nat) : ((List.range N).map Singleton.outer).Nodup :=
  map_nodup List.nodup_range (fun _ _ h => congrArg (fun l : Lit => l.1.2) h)

theorem clauses (N L : Nat) (hN : 2 ≤ N) (hL : 2 ≤ L) :
    ∀ c ∈ Programme.«20261101-0614-proof-complexity».Composition.cnf 1 N L,
      (renameClause (rho L) c).eraseDups ∈ Singleton.cnf N L := by
  intro c hc
  simp only [Programme.«20261101-0614-proof-complexity».Composition.cnf, List.mem_eraseDups, List.mem_append,
    List.mem_flatMap, List.mem_map, List.mem_range, Bool.decide_eq_true] at hc
  rcases hc with ((hf | hs) | hg) | he
  · obtain ⟨a,ha,hc⟩ := hf
    have ha0 : a = 0 := by omega
    subst a
    have hn : N ≠ 1 := by omega
    simp only [onehot, if_neg hn, List.mem_append, List.mem_singleton,
      List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range, Bool.decide_eq_true] at hc
    rcases hc with rfl | ⟨y,hy,z,⟨hz,hyz⟩,rfl⟩
    · have hr : renameClause (rho L) ((List.range N).map (fun i => pos (fVar 0 i))) =
          (List.range N).map Singleton.outer := by
        simp [renameClause, renameLit, List.map_map, Function.comp_def, pos, Singleton.outer]
      rw [hr, dedup_self (outer_nodup N)]
      exact Singleton.generator_spec N L _ |>.mpr (Or.inl (Or.inl rfl))
    · have hyz : y < z := of_decide_eq_true hyz
      have hr : renameClause (rho L) [minus (fVar 0 y),minus (fVar 0 z)] =
          [neg (Singleton.outer y),neg (Singleton.outer z)] := by
        simp [renameClause, renameLit, minus, neg, Singleton.outer]
      rw [hr]
      have hd : [neg (Singleton.outer y),neg (Singleton.outer z)].Nodup := by
        simp [Singleton.outer, neg]; omega
      rw [dedup_self hd]
      exact Singleton.generator_spec N L _ |>.mpr
        (Or.inl (Or.inr ⟨y,hy,z,⟨hz,hyz⟩,rfl⟩))
  · obtain ⟨y,hy,x,hx,hc⟩ := hs
    have hn : L ≠ 1 := by omega
    simp only [onehot, if_neg hn, List.mem_append, List.mem_singleton,
      List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range, Bool.decide_eq_true] at hc
    rcases hc with rfl | ⟨z,hz,t,⟨ht,hzt⟩,rfl⟩
    · rw [row_image]
      exact target_structural N L y hy _ (structural_mem L x hx)
    · have hh : [UnaryIter.minus x z, UnaryIter.minus x t] ∈ Singleton.structural L := by
        simp only [Singleton.structural, List.mem_flatMap]
        exact ⟨x,List.mem_range.mpr hx,by
          simp only [List.mem_append, List.mem_singleton]; right
          exact List.mem_flatMap.mpr ⟨z,List.mem_range.mpr hz,
            List.mem_map.mpr ⟨t,List.mem_filter.mpr ⟨List.mem_range.mpr ht,hzt⟩,rfl⟩⟩⟩
      simpa [renameClause,renameLit,minus,UnaryIter.minus] using target_structural N L y hy _ hh
  · obtain ⟨y,hy,x,hx,hc⟩ := hg
    simp [onehot] at hc
  · obtain ⟨y,hy,e,he,a,ha,rfl⟩ := he
    have ha0 : a = 0 := by omega
    subst a
    simp only [events, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap, List.mem_map, List.mem_range, List.mem_filter, Bool.decide_eq_true] at he
    rcases he with (rfl | ⟨x,hx,z,hz,rfl⟩) | ⟨x,hx,z,⟨hz,hxz⟩,rfl⟩
    · simpa [eventClause,renameClause,renameLit,minus,pos,Singleton.outer] using
        target_single N L y 0 0 hy (by simp [UnaryIter.cnf,UnaryIter.raw])
    · have hu : [((x,z),false)] ∈ UnaryIter.cnf L :=
        UnaryIter.generator_spec L _ |>.mpr (Or.inl (Or.inr ⟨x,hx,z,hz,rfl⟩))
      simpa [eventClause,renameClause,renameLit,minus,pos,Singleton.outer] using
        target_single N L y x z hy hu
    · have hxz : x < z := of_decide_eq_true hxz
      have hu : [((x,z),false),((z,z),false)] ∈ UnaryIter.cnf L :=
        UnaryIter.generator_spec L _ |>.mpr (Or.inr ⟨x,hx,z,⟨hz,hxz⟩,rfl⟩)
      simpa [eventClause,renameClause,renameLit,minus,pos,Singleton.outer] using
        target_cross N L y x z hy hxz hu

theorem transport (N L d : Nat) (hN : 2 ≤ N) (hL : 2 ≤ L) :
    Refutes (Programme.«20261101-0614-proof-complexity».Composition.cnf 1 N L) d → Refutes (Singleton.cnf N L) d :=
by
  intro hf
  let H := (Programme.«20261101-0614-proof-complexity».Composition.cnf 1 N L).map (renameClause (rho L))
  have hh : Refutes H d := refutes_identify (rho L)
    (fun c hc => List.mem_map.mpr ⟨c,hc,rfl⟩) hf
  have hd := cone_eraseDups hh
  apply cone_identify id (G := Singleton.cnf N L) ?_ hd
  intro c hc
  change c ∈ ((H.map List.eraseDups).eraseDups) at hc
  simp only [List.mem_eraseDups, List.mem_map, H] at hc
  obtain ⟨e,⟨u,hu,rfl⟩,rfl⟩ := hc
  have hi : renameClause id ((renameClause (rho L) u).eraseDups) =
      (renameClause (rho L) u).eraseDups := by
    simp only [renameClause]
    have hi : renameLit id = (id : Lit → Lit) := by funext l; rfl
    rw [hi, List.map_id]
  rw [hi]
  exact clauses N L hN hL u hu
#print axioms transport
end Programme.«20261101-0614-proof-complexity».SingletonBridge
