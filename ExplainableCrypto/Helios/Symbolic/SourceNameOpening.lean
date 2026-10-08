import ExplainableCrypto.Helios.Symbolic.SourceElectionGuardRetractions

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

/-- Keep the source sort while assigning a fresh numeric representative. -/
def SourceName.withValue : SourceName → Nat → SourceName
  | .base _, v => .base v
  | .channel _, v => .channel v

namespace Named

/-- Scope-respecting opening into one complete Extended body. The allocation
list records every removed name binder; its constructors enforce distinctness
across parallel and nested scopes. Freshness against external names is explicit
in the theorems below, rather than assumed by an arbitrary assignment. -/
inductive Opens : {V : Type} → Named V → NameAssignment → List SourceName → Extended V → Prop where
  | embed (a : Extended V) (ρ : NameAssignment) :
      Opens (.embed a) ρ [] (a.mapNames ρ.base ρ.channel)
  | par {a b : Named V} {ρ : NameAssignment} {ns ms : List SourceName} {a' b' : Extended V}
      (ha : Opens a ρ ns a') (hb : Opens b ρ ms b')
      (hd : ∀ n ∈ ns, n ∉ ms) : Opens (.par a b) ρ (ns++ms) (.par a' b')
  | newName (n : SourceName) (v : Nat) {a : Named V} {ρ : NameAssignment}
      {ns : List SourceName} {b : Extended V}
      (ha : Opens a (Function.update ρ n v) ns b) (hf : n.withValue v ∉ ns) :
      Opens (.newName n a) ρ (n.withValue v :: ns) b
  | newVar {a : Named (Option V)} {ρ : NameAssignment} {ns : List SourceName}
      {b : Extended (Option V)} (ha : Opens a ρ ns b) :
      Opens (.newVar a) ρ ns (.newVar b)

variable {V W : Type}

theorem Opens.nodup {a : Named V} {ρ : NameAssignment} {ns : List SourceName} {b : Extended V}
    (h : Opens a ρ ns b) : ns.Nodup := by
  induction h with
  | embed => exact List.nodup_nil
  | par ha hb hd ih ij => exact List.nodup_append.mpr ⟨ih,ij,fun a ha b hb he => hd a ha (he.symm ▸ hb)⟩
  | newName n v ha hf ih => exact List.nodup_cons.mpr ⟨hf,ih⟩
  | newVar ha ih => exact ih

theorem Opens.names_congr {a : Named V} {ρ : NameAssignment} {ns : List SourceName}
    {b : Extended V} (h : Opens a ρ ns b) (τ : NameAssignment)
    (he : ∀ n ∈ a.freeNames, ρ n = τ n) : Opens a τ ns b := by
  induction h generalizing τ with
  | embed a ρ =>
    rw [a.mapAssignments_congr ρ τ he]
    exact .embed a τ
  | par ha hb hd ih ij =>
    exact .par (ih τ (fun n hn => he n (Finset.mem_union_left _ hn)))
      (ij τ (fun n hn => he n (Finset.mem_union_right _ hn))) hd
  | newName n v ha hf ih =>
    apply Opens.newName n v (ih (Function.update τ n v) _) hf
    intro m hm
    by_cases hmn : m=n
    · simp [hmn]
    · simpa only [Function.update_of_ne hmn] using he m (Finset.mem_erase.mpr ⟨hmn,hm⟩)
  | newVar ha ih => exact .newVar (ih τ he)

theorem Opens.rename {a : Named V} {ρ : NameAssignment} {ns : List SourceName} {b : Extended V}
    (h : Opens a ρ ns b) (σ : V → W) : Opens (a.rename σ) ρ ns (b.rename σ) := by
  induction h generalizing W with
  | embed a ρ =>
    simpa only [Named.rename,Extended.mapNames_rename] using Opens.embed (a.rename σ) ρ
  | par ha hb hd ih ij => exact .par (ih σ) (ij σ) hd
  | newName n v ha hf ih => exact .newName n v (ih σ) hf
  | newVar ha ih => exact .newVar (ih (Option.map σ))

/-- Every realization of the opened body supplies one full interpretation of
the original process, retaining the same environment and complete continuation. -/
theorem Opens.interprets {a : Named V} {ρ : NameAssignment} {ns : List SourceName}
    {b : Extended V} (h : Opens a ρ ns b) (env : V → Ground) {p : Agent Empty}
    (hb : b.Realizes env p) : a.Interprets ρ env p := by
  induction h generalizing p with
  | embed => exact hb
  | par ha hc hd ih ij =>
    obtain ⟨q,r,hq,hr,he⟩ := hb
    exact ⟨q,r,ih env hq,ij env hr,he⟩
  | newName n v ha hf ih => exact ⟨v,ih env hb⟩
  | newVar ha ih =>
    obtain ⟨m,hm⟩ := hb
    exact ⟨m,ih (extendEnv env m) hm⟩

/-- Globally distinct allocation can avoid any finite set, including every
literal name in a chosen source derivation. This does not yet compare openings
of arbitrary structurally equivalent processes. -/
theorem exists_fresh_opening (a : Named V) (ρ : NameAssignment) (avoid : Finset SourceName) :
    ∃ ns b, Opens a ρ ns b ∧ ∀ n ∈ ns, n ∉ avoid := by
  induction a generalizing ρ avoid with
  | embed a => exact ⟨[],_,.embed a ρ,by simp⟩
  | par a b ih ij =>
    obtain ⟨ns,a',ha,hf⟩ := ih ρ avoid
    obtain ⟨ms,b',hb,hg⟩ := ij ρ (avoid ∪ ns.toFinset)
    refine ⟨ns++ms,.par a' b',.par ha hb ?_,?_⟩
    · intro n hn hm
      exact hg n hm (Finset.mem_union_right _ (List.mem_toFinset.mpr hn))
    · intro n hn hav
      rcases List.mem_append.mp hn with hn | hn
      · exact hf n hn hav
      · exact hg n hn (Finset.mem_union_left _ hav)
  | newVar a ih =>
    obtain ⟨ns,b,hb,hf⟩ := ih ρ avoid
    exact ⟨ns,.newVar b,.newVar hb,hf⟩
  | newName n a ih =>
    let v := freshNameIndex avoid
    have hv : n.withValue v ∉ avoid := by
      cases n with
      | base n => exact fresh_base_not_mem avoid
      | channel n => exact fresh_channel_not_mem avoid
    obtain ⟨ns,b,hb,hf⟩ := ih (Function.update ρ n v) (insert (n.withValue v) avoid)
    refine ⟨n.withValue v :: ns,b,.newName n v hb ?_,?_⟩
    · intro hn
      exact hf _ hn (Finset.mem_insert_self _ _)
    · intro m hm hav
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hv hav
      · exact hf m hm (Finset.mem_insert_of_mem hav)

end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
