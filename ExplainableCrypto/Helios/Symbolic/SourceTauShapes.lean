import ExplainableCrypto.Helios.Symbolic.SourceTauInversion

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
variable {c d e : Nat} {m t : Ground} {a b p q : Agent Empty} {x y : Agent (Option Empty)}

theorem tau_pair_deterministic
    (h : Tau (.par (.output c m a) (.input c x)) p)
    (h' : Tau (.par (.output c m a) (.input c x)) q) : ParEq p q := by
  apply tau_deterministic_communication h h' (c := c) (m := m) (a := a) (b := x)
  · intro f u v hm
    simp [threads,threadList] at hm
  · intro d t u v ho hi
    simp [threads,threadList] at ho hi
    obtain ⟨rfl,rfl,rfl⟩ := ho
    exact ⟨rfl,rfl,rfl,hi.2⟩

theorem tau_three_deterministic (he : e ≠ c)
    (h : Tau (.par (.output c m a) (.par (.input c x) (.input e y))) p)
    (h' : Tau (.par (.output c m a) (.par (.input c x) (.input e y))) q) : ParEq p q := by
  apply tau_deterministic_communication h h' (c := c) (m := m) (a := a) (b := x)
  · intro f u v hm
    simp [threads,threadList] at hm
  · intro d t u v ho hi
    simp [threads,threadList] at ho hi
    obtain ⟨rfl,rfl,rfl⟩ := ho
    rcases hi with ⟨_,rfl⟩ | ⟨hc,_⟩
    · exact ⟨rfl,rfl,rfl,rfl⟩
    · exact (he hc.symm).elim

/-- Two voter outputs, the next board input, and a waiting trustee. Only the
first voter can communicate, even when payloads or continuations coincide. -/
theorem tau_four_deterministic (hcd : c ≠ d) (hec : e ≠ c) (hed : e ≠ d)
    (h : Tau (.par (.output c m a) (.par (.output d t b) (.par (.input c x) (.input e y)))) p)
    (h' : Tau (.par (.output c m a) (.par (.output d t b) (.par (.input c x) (.input e y)))) q) : ParEq p q := by
  apply tau_deterministic_communication h h' (c := c) (m := m) (a := a) (b := x)
  · intro f u v hm
    simp [threads,threadList] at hm
  · intro k s u v ho hi
    simp [threads,threadList] at ho hi
    rcases ho with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    · rcases hi with ⟨_,rfl⟩ | ⟨hc,_⟩
      · exact ⟨rfl,rfl,rfl,rfl⟩
      · exact (hec hc.symm).elim
    · rcases hi with ⟨hc,_⟩ | ⟨hc,_⟩
      · exact (hcd hc.symm).elim
      · exact (hed hc.symm).elim

theorem tau_branch_input_deterministic {f : Formula Empty}
    (h : Tau (.par (.branch f a b) (.input c x)) p)
    (h' : Tau (.par (.branch f a b) (.input c x)) q) : ParEq p q := by
  apply tau_deterministic_conditional h h' (f := f) (a := a) (b := b)
  constructor
  · intro d t u hm
    simp [threads,threadList] at hm
  · intro g u v hm
    simpa [threads,threadList] using hm

theorem tau_two_inputs_no_step : ¬ Tau (.par (.input c x) (.input d y)) p := by
  intro h
  rcases h.enabled with ⟨f,u,v,hm⟩ | ⟨e,t,u,v,hm,_⟩ <;> simp [threads,threadList] at hm

theorem tau_output_input_no_step (hcd : c ≠ d) :
    ¬ Tau (.par (.output c m a) (.input d x)) p := by
  intro h
  rcases h.enabled with ⟨f,u,v,hm⟩ | ⟨e,t,u,v,ho,hi⟩
  · simp [threads,threadList] at hm
  · simp [threads,threadList] at ho hi
    exact hcd (ho.1.symm.trans hi.1)

theorem tau_two_outputs_input_no_step (hce : c ≠ e) (hde : d ≠ e) :
    ¬ Tau (.par (.output c m a) (.par (.output d t b) (.input e x))) p := by
  intro h
  rcases h.enabled with ⟨f,u,v,hm⟩ | ⟨k,s,u,v,ho,hi⟩
  · simp [threads,threadList] at hm
  · simp [threads,threadList] at ho hi
    rcases ho with ho | ho
    · exact hce (ho.1.symm.trans hi.1)
    · exact hde (ho.1.symm.trans hi.1)
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
