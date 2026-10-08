import ExplainableCrypto.Helios.Symbolic.SourceReadyPrefixExtraction

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

/-- Both ready prefixes occur in the same raw state. Their actual extraction
paths expose one communication redex beneath the retained original scopes. -/
theorem communication_available_of_realizes {a : Extended V} {env : V → Ground}
    {p : Agent Empty} (ha : a.Realizes env p) {c : Nat}
    (ho : p.HasOutput c) (hi : p.HasInput c) : ∃ b, Reduction a b := by
  obtain ⟨n,m,out,rest,hs⟩ := output_prefix_of_realizes ha ho
  obtain ⟨env',q,s,hq,hr,he⟩ := realizes_closeVars_witness ((hs.realizes env p).mp ha)
  have hri : s.HasInput c := by
    rcases (he.hasInput c).mpr hi with hi | hi
    · exact ((hq.hasInput c).mpr hi).elim
    · exact hi
  obtain ⟨k,inp,tail,ht⟩ := input_prefix_of_realizes hr hri
  let output : Extended (LocalVars n V) := .plain (.output c m out)
  have hinner := (Structural.parRight output ht).trans (par_closeVars k output _)
  let m' := m.subst (fun v => .var (outerVar k v))
  let out' := out.subst (fun v => .var (outerVar k v))
  have hc : Reduction
      (.par (output.rename (outerVar k)) (.par (.plain (.input c inp)) tail))
      (.par (.plain (.par out' (inp.bind m'))) tail) := by
    apply Reduction.congr (Structural.assoc _ _ _).symm
    exact Reduction.parLeft tail (Reduction.congr (Structural.plainPar _ _).symm
      (message_communication c m' out' inp) (.refl _))
    exact .refl _
  exact ⟨_,Reduction.congr hs ((Reduction.congr hinner (hc.closeVars k) (.refl _)).closeVars n) (.refl _)⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {handles : Nat}

/-- Communication may use a private channel: the complete name prefix is
retained around the actual internal source action. -/
theorem JointOpening.communication_available {a : Named (Fin handles)}
    {φ : Frame restricted handles} {p : Agent Empty}
    (ha : JointOpening a (restrictedState hidden ⟨φ,p⟩))
    {c : Nat} (ho : p.HasOutput c) (hi : p.HasInput c) : ∃ b, Reduction a b := by
  let F := Extended.frameProcess φ p
  obtain ⟨ns,d,ms,t,hopen,hcan,hf,_,he,_⟩ := ha.fresh a.allNames
  obtain ⟨τ,ht,_,_⟩ := hcan.prefix_pair_assignment (restrictionNames hidden restricted) F F
    NameAssignment.literal
  have hd : d.Realizes (φ.mapNames τ.base).value (p.mapNames τ.base τ.channel) := by
    apply (he _ _).mpr
    rw [ht,Extended.frameProcess_mapNames]
    exact Extended.frameProcess_realizes _ _
  obtain ⟨b,hb⟩ := Extended.communication_available_of_realizes hd
    (ho.mapNames τ.base τ.channel) (hi.mapNames τ.base τ.channel)
  have hs := hopen.structural_literal (fun n hn hm => hf n hn (Finset.mem_union_left _ hm))
  exact ⟨_,.congr hs ((Reduction.embed hb).restrictNames ns) (.refl _)⟩

/-- An evaluated internal action with no ready conditional supplies compatible
communication prefixes, and therefore a genuine raw internal reduction. -/
theorem JointOpening.internal_available_of_no_conditional {a : Named (Fin handles)}
    {φ : Frame restricted handles} {p q : Agent Empty}
    (ha : JointOpening a (restrictedState hidden ⟨φ,p⟩))
    (h : Agent.Tau p q) (hn : ¬ p.HasConditional) : ∃ b, Reduction a b := by
  rcases h.enabled with ⟨f,x,y,hf⟩ | ⟨c,m,x,y,ho,hi⟩
  · exact (hn ((Agent.hasConditional_iff_prefix p).mpr ⟨f,x,y,hf⟩)).elim
  · exact ha.communication_available ((Agent.hasOutput_iff_threads p c).mpr ⟨m,x,ho⟩)
      ((Agent.hasInput_iff_threads p c).mpr ⟨y,hi⟩)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
