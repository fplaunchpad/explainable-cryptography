import ExplainableCrypto.Helios.Symbolic.SourceOpeningAlphaComparison

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

theorem openingEquivalent_nameVarComm (n : SourceName) (a : Named (Option V)) :
    OpeningEquivalent (.newName n (.newVar a)) (.newVar (.newName n a)) := by
  apply OpeningEquivalent.of_opens_iff
  intro ρ ns p
  constructor
  · intro h; cases h with
    | newName _ v ha hf => cases ha with
      | newVar ha => exact .newVar (.newName n v ha hf)
  · intro h; cases h with
    | newVar ha => cases ha with
      | newName _ v ha hf => exact .newName n v (.newVar ha) hf

theorem openingTransport_nameComm (n m : SourceName) (a : Named V) :
    OpeningTransport (.newName n (.newName m a)) (.newName m (.newName n a)) := by
  by_cases he : n=m
  · subst m; exact .refl _
  intro ρ ns p avoid hp hf
  cases hp with
  | newName _ v ha hn => cases ha with
    | newName _ w ha hm =>
      rw [Function.update_comm he] at ha
      refine ⟨m.withValue w :: n.withValue v :: _,p,
        .newName m w (.newName n v ha ?_) ?_,?_,.refl _⟩
      · intro hx; exact hn (List.mem_cons_of_mem _ hx)
      · intro hx
        rcases List.mem_cons.mp hx with hx | hx
        · exact hn (List.mem_cons.mpr (Or.inl hx.symm))
        · exact hm hx
      · intro x hx hav
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hf _ (List.mem_cons_of_mem _ List.mem_cons_self) hav
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hf _ List.mem_cons_self hav
          · exact hf _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)) hav

theorem openingEquivalent_nameComm (n m : SourceName) (a : Named V) :
    OpeningEquivalent (.newName n (.newName m a)) (.newName m (.newName n a)) :=
  ⟨openingTransport_nameComm n m a,openingTransport_nameComm m n a⟩

theorem openingEquivalent_nameZero (n : SourceName) :
    OpeningEquivalent (.newName n (.embed (.plain .nil) : Named V)) (.embed (.plain .nil)) := by
  constructor
  · intro ρ ns p avoid hp hf
    cases hp with
    | newName _ v ha hn => cases ha; exact ⟨[],_,.embed _ _,by simp,.refl _⟩
  · intro ρ ns p avoid hp hf
    cases hp
    let v := freshNameIndex avoid
    have hv : n.withValue v ∉ avoid := by
      cases n with
      | base n => exact fresh_base_not_mem avoid
      | channel n => exact fresh_channel_not_mem avoid
    exact ⟨[n.withValue v],_,.newName n v (.embed _ _) (by simp),
      by simpa only [List.mem_singleton,forall_eq] using hv,.refl _⟩

/-- Extruding an unused source name changes only the allocation order. -/
theorem openingEquivalent_namePar (a b : Named V) (n : SourceName) (hf : n ∉ a.freeNames) :
    OpeningEquivalent (.par a (.newName n b)) (.newName n (.par a b)) := by
  have he (ρ : NameAssignment) (v : Nat) :
      ∀ x ∈ a.freeNames, ρ x = Function.update ρ n v x := by
    intro x hx
    have hxn : x ≠ n := fun he => hf (he ▸ hx)
    simp only [Function.update_of_ne hxn]
  constructor
  · intro ρ ns p avoid hp hg
    cases hp with
    | @par _ _ _ _ ns _ p q ha hb hd => cases hb with
      | @newName _ _ v _ _ ms _ hb hn =>
        refine ⟨n.withValue v :: (ns++ms),.par p q,.newName n v
          (.par (ha.names_congr _ (he ρ v)) hb ?_) ?_,?_,.refl _⟩
        · intro x hx hy; exact hd x hx (List.mem_cons_of_mem _ hy)
        · intro hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hd _ hx List.mem_cons_self
          · exact hn hx
        · intro x hx hav
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hg _ (List.mem_append_right _ List.mem_cons_self) hav
          · rcases List.mem_append.mp hx with hx | hx
            · exact hg _ (List.mem_append_left _ hx) hav
            · exact hg _ (List.mem_append_right _ (List.mem_cons_of_mem _ hx)) hav
  · intro ρ ns p avoid hp hg
    cases hp with
    | newName _ v hp hn => cases hp with
      | @par _ _ _ _ ns ms p q ha hb hd =>
        refine ⟨ns++(n.withValue v::ms),.par p q,
          .par (ha.names_congr _ (fun x hx => (he ρ v x hx).symm))
            (.newName n v hb ?_) ?_,?_,.refl _⟩
        · intro hx; exact hn (List.mem_append_right _ hx)
        · intro x hx hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hn (List.mem_append_left _ hx)
          · exact hd x hx hy
        · intro x hx hav
          rcases List.mem_append.mp hx with hx | hx
          · exact hg _ (List.mem_cons_of_mem _ (List.mem_append_left _ hx)) hav
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact hg _ List.mem_cons_self hav
            · exact hg _ (List.mem_cons_of_mem _ (List.mem_append_right _ hx)) hav

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
