import ExplainableCrypto.Helios.Symbolic.SourceVoterRegisters

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W : Type} {n : Nat}

/-- Figure 4's four final lets, in order: aggregate nonce, ciphertext, vote,
and proof. The final tuple uses the saved component registers and newest proof. -/
def voterAggregate (s : VoterRegisters n V) : TermProgram V :=
  .letTerm (foldCandidates .compose s.nonces)
    (.letTerm (foldCandidates .mul s.shift.ciphertexts)
      (.letTerm (foldCandidates .add s.shift.shift.votes)
        (.letTerm (.spk s.shift.shift.shift.key (.var (some (some none))) (.var none) (.var (some none)))
          (.result (Term.tuple
            ((List.finRange (n+1)).map s.shift.shift.shift.shift.ciphertexts ++
             (List.finRange (n+1)).map s.shift.shift.shift.shift.proofs ++ [.var none]))))))

theorem voterAggregate_eval (s : VoterRegisters n V) (σ : V → Term W) :
    (voterAggregate s).eval σ = (s.map σ).aggregateValue := by
  simp only [voterAggregate,TermProgram.eval,VoterRegisters.aggregateValue,VoterRegisters.shift,
    VoterRegisters.map,Term.subst_tuple,List.map_append,List.map_map,List.map_singleton,
    foldCandidates_subst,Term.subst_subst,Term.subst,extendEnv,Function.comp_def]

/-- Every candidate allocates and uses its ciphertext register before its
proof register. The unprocessed register table is shifted past both lets. -/
def voterComponents : List (Fin (n+1)) → {V : Type} → VoterRegisters n V → TermProgram V
  | [], _, s => voterAggregate s
  | j::js, _, s => .letTerm (s.ciphertext j)
      (.letTerm (s.proofRhs j) (voterComponents js (s.afterBind j)))

/-- The exact intermediate register table records which candidates were
processed. An omitted candidate retains its original register values. -/
theorem voterComponents_eval (indices : List (Fin (n+1))) (s : VoterRegisters n V) (σ : V → Term W) :
    (voterComponents indices s).eval σ = ((s.map σ).completed indices).aggregateValue := by
  induction indices generalizing V W with
  | nil => simpa only [voterComponents,VoterRegisters.completed,List.not_mem_nil,ite_false] using voterAggregate_eval s σ
  | cons j js ih =>
    simp only [voterComponents,TermProgram.eval,ih,VoterRegisters.afterBind_map,VoterRegisters.completed_compute]

theorem voterAggregate_bindings (s : VoterRegisters n V) : (voterAggregate s).bindings = 4 := rfl

theorem voterComponents_bindings (indices : List (Fin (n+1))) (s : VoterRegisters n V) :
    (voterComponents indices s).bindings = 2 * indices.length + 4 := by
  induction indices generalizing V with
  | nil => rfl
  | cons j js ih => simp only [voterComponents,TermProgram.bindings,ih,List.length_cons]; omega

/-- Registers begin at bottom, not at precomputed ballot values. This makes
missing or reordered candidate computations visible to the controls. -/
def voterInitial (ns : Names n) (i : Fin 2) (values : Fin (n+1) → Ground) : VoterRegisters n Empty :=
  ⟨publicKey ns,fun j => .name (ns.nonce i j),values,fun _ => .const .bottom,fun _ => .const .bottom⟩

def voterProgram (ns : Names n) (i : Fin 2) (values : Fin (n+1) → Ground) : TermProgram Empty :=
  voterComponents (List.finRange (n+1)) (voterInitial ns i values)

/-- Exact syntax equality to the complete historical ballot, for arbitrary
full ground values. No candidate-validity or normal-form premise is needed. -/
theorem voterProgram_value (ns : Names n) (i : Fin 2) (values : Fin (n+1) → Ground) :
    (voterProgram ns i values).value = ballot ns i values := by
  unfold General.ballot General.ballotFields General.aggregateProof General.componentProof General.ciphertext
  have h := voterComponents_eval (List.finRange (n+1)) (voterInitial ns i values) Term.var
  rw [TermProgram.eval_var] at h
  simpa only [voterProgram,voterInitial,VoterRegisters.map,Term.subst_var,VoterRegisters.completed,
    List.mem_finRange,ite_true,VoterRegisters.aggregateValue,VoterRegisters.ciphertext,VoterRegisters.proof] using h

theorem voterProgram_bindings (ns : Names n) (i : Fin 2) (values : Fin (n+1) → Ground) :
    (voterProgram ns i values).bindings = 2 * (n+1) + 4 := by
  simpa only [voterProgram,List.length_finRange] using
    voterComponents_bindings (List.finRange (n+1)) (voterInitial ns i values)

/-- All local lets are present in the source syntax and eliminate through the
existing active-substitution rules to the exact authenticated ballot output. -/
theorem voterProgram_normalizes (ns : Names n) (i : Fin 2) (values : Fin (n+1) → Ground) (channel : Nat) :
    Extended.Structural ((voterProgram ns i values).compile channel)
      (.plain (.output channel (ballot ns i values) .nil)) := by
  simpa only [voterProgram_value] using (voterProgram ns i values).compile_normalizes channel

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
