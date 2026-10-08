import ExplainableCrypto.Helios.Symbolic.SourceNamedBodyInterpretation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

theorem Interprets.par {a b : Named V} {ρ : NameAssignment} {env : V → Ground}
    {p q : Agent Empty} (ha : a.Interprets ρ env p) (hb : b.Interprets ρ env q) :
    (Named.par a b).Interprets ρ env (.par p q) := ⟨p,q,ha,hb,.refl _⟩

theorem interprets_zero (a : Named V) (ρ : NameAssignment) (env : V → Ground) (p : Agent Empty) :
    (par a (.embed (.plain .nil))).Interprets ρ env p ↔ a.Interprets ρ env p := by
  constructor
  · rintro ⟨q,r,hq,hr,h⟩
    exact hq.congr ((Agent.EvalEq.of_parEq (Agent.ParEq.zero q).symm).trans
      ((Agent.EvalEq.par (.refl q) hr).trans h))
  · intro h
    exact ⟨p,.nil,h,.refl _,.of_parEq (.zero _)⟩

theorem interprets_comm (a b : Named V) (ρ : NameAssignment) (env : V → Ground) (p : Agent Empty) :
    (par a b).Interprets ρ env p ↔ (par b a).Interprets ρ env p := by
  constructor <;> rintro ⟨q,r,hq,hr,h⟩ <;>
    exact ⟨r,q,hr,hq,(Agent.EvalEq.of_parEq (.comm _ _)).trans h⟩

theorem interprets_assoc (a b c : Named V) (ρ : NameAssignment) (env : V → Ground) (p : Agent Empty) :
    (par (par a b) c).Interprets ρ env p ↔ (par a (par b c)).Interprets ρ env p := by
  constructor
  · rintro ⟨q,r,⟨s,t,hs,ht,hq⟩,hr,h⟩
    exact ⟨s,.par t r,hs,ht.par hr,
      (Agent.EvalEq.of_parEq (Agent.ParEq.assoc _ _ _).symm).trans
        ((Agent.EvalEq.par hq (.refl r)).trans h)⟩
  · rintro ⟨q,r,hq,⟨s,t,hs,ht,hr⟩,h⟩
    exact ⟨.par q s,t,hq.par hs,ht,
      (Agent.EvalEq.of_parEq (Agent.ParEq.assoc _ _ _)).trans
        ((Agent.EvalEq.par (.refl q) hr).trans h)⟩

theorem interprets_varPar (a : Named V) (b : Named (Option V))
    (ρ : NameAssignment) (env : V → Ground) (p : Agent Empty) :
    (par a (.newVar b)).Interprets ρ env p ↔
      (newVar (.par (a.rename some) b)).Interprets ρ env p := by
  constructor
  · rintro ⟨q,r,hq,⟨m,hr⟩,h⟩
    exact ⟨m,q,r,(interprets_rename a some ρ (extendEnv env m) q).mpr hq,hr,h⟩
  · rintro ⟨m,q,r,hq,hr,h⟩
    exact ⟨q,r,(interprets_rename a some ρ (extendEnv env m) q).mp hq,⟨m,hr⟩,h⟩

theorem interprets_namePar (a b : Named V) (n : SourceName) (hf : n ∉ a.freeNames)
    (ρ : NameAssignment) (env : V → Ground) (p : Agent Empty) :
    (par a (.newName n b)).Interprets ρ env p ↔ (newName n (.par a b)).Interprets ρ env p := by
  constructor
  · rintro ⟨q,r,hq,⟨k,hr⟩,h⟩
    exact ⟨k,q,r,(interprets_update_unused a ρ env q n k hf).mpr hq,hr,h⟩
  · rintro ⟨k,q,r,hq,hr,h⟩
    exact ⟨q,r,(interprets_update_unused a ρ env q n k hf).mp hq,⟨k,hr⟩,h⟩

theorem interprets_nameComm (a : Named V) (n m : SourceName)
    (ρ : NameAssignment) (env : V → Ground) (p : Agent Empty) :
    (newName n (newName m a)).Interprets ρ env p ↔ (newName m (newName n a)).Interprets ρ env p := by
  by_cases he : n=m
  · subst m; rfl
  · simp only [Interprets]
    constructor
    · rintro ⟨x,y,h⟩
      refine ⟨y,x,?_⟩
      rwa [Function.update_comm he] at h
    · rintro ⟨y,x,h⟩
      refine ⟨x,y,?_⟩
      rwa [Function.update_comm he]

theorem interprets_alpha (a : Named V) (n m : SourceName) (e k : Nat ≃ Nat)
    (he : SourceName.map e k = Equiv.swap n m) (hf : m ∉ a.allNames)
    (ρ : NameAssignment) (env : V → Ground) (p : Agent Empty) :
    (newName n a).Interprets ρ env p ↔ (newName m (a.mapNames e k)).Interprets ρ env p := by
  simp only [Interprets]
  apply exists_congr
  intro v
  rw [interprets_mapNames,he]
  apply interprets_names_congr
  intro x hx
  have hm : x ≠ m := fun hxm => hf (hxm ▸ freeNames_subset_allNames a hx)
  by_cases hn : x=n
  · subst x; simp
  · simp [Equiv.swap_apply_of_ne_of_ne hn hm,hn,hm]

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
