import ExplainableCrypto.Helios.Symbolic.SourceNameRestrictionRules

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {handles : Nat}

/-- A concrete binder list, with base and channel policies in their own sorts. -/
noncomputable def restrictionNames (hidden restricted : Finset Nat) : List SourceName :=
  restricted.toList.map SourceName.base ++ hidden.toList.map SourceName.channel

theorem base_mem_restrictionNames (n : Nat) (hidden restricted : Finset Nat) :
    SourceName.base n ∈ restrictionNames hidden restricted ↔ n ∈ restricted := by
  simp [restrictionNames]

theorem channel_mem_restrictionNames (c : Nat) (hidden restricted : Finset Nat) :
    SourceName.channel c ∈ restrictionNames hidden restricted ↔ c ∈ hidden := by
  simp [restrictionNames]

theorem restrictionNames_nodup (hidden restricted : Finset Nat) :
    (restrictionNames hidden restricted).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨?_,?_,?_⟩
  · exact (List.nodup_map_iff (fun _ _ h => SourceName.base.inj h)).mpr restricted.nodup_toList
  · exact (List.nodup_map_iff (fun _ _ h => SourceName.channel.inj h)).mpr hidden.nodup_toList
  · intro n hn m hm he
    obtain ⟨x,_,hx⟩ := List.mem_map.mp hn
    obtain ⟨y,_,hy⟩ := List.mem_map.mp hm
    cases (hx.trans he).trans hy.symm

/-- The wrapper's two policy checks are exactly the repeated source Scope
freshness checks on its literal recipe input label. -/
theorem input_restriction_fresh_iff (c : Nat) (r : Recipe handles) :
    (∀ n ∈ restrictionNames hidden restricted, n ∉ (Extended.FreeLabel.input c r).nameSupport) ↔
      c ∉ hidden ∧ r.Public restricted := by
  constructor
  · intro h
    constructor
    · intro hc
      exact h (.channel c) ((channel_mem_restrictionNames c hidden restricted).mpr hc) (by simp [Extended.FreeLabel.nameSupport])
    · apply (Term.public_iff_nameSupport r restricted).mpr
      intro n hn hr
      exact h (.base n) ((base_mem_restrictionNames n hidden restricted).mpr hr) (by simp [Extended.FreeLabel.nameSupport,hn])
  · rintro ⟨hc,hr⟩ n hn
    cases n with
    | base n =>
      intro hm
      have ht : n ∈ r.nameSupport := by simpa [Extended.FreeLabel.nameSupport] using hm
      exact (Term.public_iff_nameSupport r restricted).mp hr n ht ((base_mem_restrictionNames n hidden restricted).mp hn)
    | channel d =>
      apply (input_channel_fresh_iff c d r).mpr
      intro he
      subst d
      exact hc ((channel_mem_restrictionNames c hidden restricted).mp hn)

theorem output_restriction_fresh_iff (c : Nat) :
    (∀ n ∈ restrictionNames hidden restricted, n ≠ SourceName.channel c) ↔ c ∉ hidden := by
  constructor
  · intro h hc
    exact h (.channel c) ((channel_mem_restrictionNames c hidden restricted).mpr hc) rfl
  · intro hc n hn he
    subst n
    exact hc ((channel_mem_restrictionNames c hidden restricted).mp hn)

noncomputable def restrictedState (hidden : Finset Nat) (p : ScopedState restricted handles) : Named (Fin handles) :=
  restrictNames (restrictionNames hidden restricted) (.embed (Extended.frameProcess p.frame p.body))

noncomputable def restrictedCapture (hidden : Finset Nat) (φ : Frame restricted handles) (m : Ground) (p : Agent Empty) :
    Named (Option (Fin handles)) :=
  restrictNames (restrictionNames hidden restricted)
    (.embed (.par ((Extended.activeFrame φ).rename some) (Extended.capture (Extended.groundTerm m) (Extended.groundAgent p))))

theorem restricted_tau_derivable (p q : ScopedState restricted handles)
    (h : ScopedStep hidden restricted p .tau q) :
    Reduction (restrictedState hidden p) (restrictedState hidden q) :=
  (Reduction.embed (Extended.scoped_tau_derivable hidden p q h)).restrictNames _

theorem restricted_input_derivable (p q : ScopedState restricted handles) (c : Nat) (r : Recipe handles)
    (h : ScopedStep hidden restricted p (.input c r) q) :
    FreeStep (restrictedState hidden p) (.input c r) (restrictedState hidden q) := by
  have hh := (scoped_input_iff p q c r).mp h
  exact (FreeStep.embed (Extended.scoped_input_derivable hidden p q c r h)).restrictNames _
    ((input_restriction_fresh_iff c r).mpr ⟨hh.1,hh.2.1⟩)

/-- Restricted names remain around the full raw output; the fresh base variable
is still canonically renamed to the next public handle afterward. -/
theorem restricted_output_derivable (p : ScopedState restricted handles) (q : ScopedState restricted (handles+1))
    (c : Nat) (h : ScopedStep hidden restricted p (.output c) q) :
    ∃ m : Ground,
      BoundOutput (restrictedState hidden p) c (restrictedCapture hidden p.frame m q.body) ∧
      Structural ((restrictedCapture hidden p.frame m q.body).rename Extended.outputHandle) (restrictedState hidden q) := by
  obtain ⟨m,hb,hs⟩ := Extended.scoped_output_derivable hidden p q c h
  refine ⟨m,?_,?_⟩
  · exact (BoundOutput.embed hb).restrictNames _
      ((output_restriction_fresh_iff c).mpr ((scoped_output_iff p q c).mp h).1)
  · simpa only [restrictedCapture,restrictedState,restrictNames_rename,Named.rename] using
      (Structural.embed hs).restrictNames (restrictionNames hidden restricted)
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
