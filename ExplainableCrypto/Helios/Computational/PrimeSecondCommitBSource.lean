import ExplainableCrypto.Helios.Computational.PrimeSecondCommitMachineSource
import ExplainableCrypto.Helios.Computational.PrimeSecondCommitBMachine
import ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondSource

/-! Actual second-component operands for the zero-branch second coordinate.
Only source presentation and algebra are proved here; execution is a separate gate. -/
namespace ExplainableCrypto.Helios.Computational.PrimeSecondCommitBSource
open PrimeProgramProofSource (State Cache Draws)
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
set_option maxRecDepth 65536

def statement (g pk : PrimeGroup p q) (out : Draws (q:=q)) :
    BallotStatement (PrimeGroup p q) := honestProofStatement g pk (false,out.1.2)

def commitment (g pk : PrimeGroup p q) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) : BallotCommitment (PrimeGroup p q) :=
  ballotSimCommit (statement g pk out) cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)

def words (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) : Fin 65 → List Bool :=
  (PrimeSecondCommitMachine.sourceResult slack g pk vote s live out cs).stk

/-- Every operand belongs to p1=(false,r2), using the new transcript scalars. -/
theorem source_inputs (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    let old := words slack g pk vote s live out cs
    old 6 = p.bits ∧ old 58 = q.bits ∧ old 15 = (primeGroupCoordinate pk).val.bits ∧
    old 51 = (primeGroupCoordinate (statement g pk out).ciphertext.2).val.bits ∧
    old 55 = uniformNatEncode cs.2.1.val ∧ old 56 = uniformNatEncode cs.2.2.1.val :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The retained arithmetic workspace is blank in the actual complete successor. -/
theorem source_work (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (j : Fin 15) :
    words slack g pk vote s live out cs ⟨23+j.val,by omega⟩ = [] := by
  fin_cases j <;> rfl

/-- Exactly the numeric hypotheses of the reused numeric controller;
zero challenges, responses and nonce are allowed. -/
theorem source_bounds (g pk : PrimeGroup p q) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    2 ≤ p ∧ (primeGroupCoordinate pk).val < p ∧
    (primeGroupCoordinate (statement g pk out).ciphertext.2).val < p ∧
    cs.2.1.val < q ∧ cs.2.2.1.val < q :=
  ⟨(Fact.out : p.Prime).two_le,ZMod.val_lt _,ZMod.val_lt _,ZMod.val_lt _,ZMod.val_lt _⟩

omit [Fact q.Prime] in
/-- The subgroup complement representative may be q when e=0. It is not a
claim that q-e.val is the canonical residue of -e. -/
theorem source_complement_width (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    (q-cs.2.1.val).size ≤ q.size := PrimeSimCommitSource.complement_width _

theorem answer_source (g pk : PrimeGroup p q) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    PrimeSimCommitMachine.answer p q (primeGroupCoordinate pk).val
      (primeGroupCoordinate (statement g pk out).ciphertext.2).val cs.2.1.val cs.2.2.1.val =
      (primeGroupCoordinate (commitment g pk out cs).1.2).val := by
  simpa only [PrimeSimCommitMachine.answer,commitment,statement,honestProofStatement] using
    (PrimeSimCommitSecondSource.second_coordinate_value (statement g pk out) cs.1 cs.2.1 cs.2.2.1 cs.2.2.2).symm


/-- The complete reached state, including private work emptiness, supplies the
unchanged arithmetic controller's input and both retained frames. -/
theorem source_inputs_embed (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    let old := words slack g pk vote s live out cs
    BitOracleStackFrame.embed PrimeSecondCommitBMachine.layout
      (PrimeSimCommitMachine.start (PrimeSimCommitMachine.inputWords p q
        (primeGroupCoordinate pk).val
        (primeGroupCoordinate (statement g pk out).ciphertext.2).val
        cs.2.1.val cs.2.2.1.val (PrimeSecondCommitBMachine.localFrame old)))
      (PrimeSecondCommitBMachine.frame old) = PrimeSecondCommitBMachine.start old := by
  dsimp only
  have hs (k : Fin 66) :
      (BitOracleStackFrame.embed PrimeSecondCommitBMachine.layout
        (PrimeSimCommitMachine.start (PrimeSimCommitMachine.inputWords p q
          (primeGroupCoordinate pk).val
          (primeGroupCoordinate (statement g pk out).ciphertext.2).val
          cs.2.1.val cs.2.2.1.val
          (PrimeSecondCommitBMachine.localFrame (words slack g pk vote s live out cs))))
        (PrimeSecondCommitBMachine.frame (words slack g pk vote s live out cs))).stk k =
      (PrimeSecondCommitBMachine.start (words slack g pk vote s live out cs)).stk k := by
    obtain ⟨x,rfl⟩ := PrimeSecondCommitBMachine.layout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  exact congrArg (fun w => (⟨some 0,2,w⟩ : PrimeSecondCommitBMachine.Config)) (funext hs)

/-- The numeric controller's actual full result preserves all prior 65 words,
cleans its fresh workspace and places only the new coordinate on port 65. -/
theorem source_outputs_embed (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (answer : List Bool) :
    let old := words slack g pk vote s live out cs
    BitOracleStackFrame.embed PrimeSecondCommitBMachine.layout
      (PrimeSimCommitMachine.result answer (PrimeSimCommitMachine.inputWords p q
        (primeGroupCoordinate pk).val
        (primeGroupCoordinate (statement g pk out).ciphertext.2).val
        cs.2.1.val cs.2.2.1.val (PrimeSecondCommitBMachine.localFrame old)))
      (PrimeSecondCommitBMachine.frame old) = PrimeSecondCommitBMachine.result answer old := by
  dsimp only
  have hs (k : Fin 66) :
      (BitOracleStackFrame.embed PrimeSecondCommitBMachine.layout
        (PrimeSimCommitMachine.result answer (PrimeSimCommitMachine.inputWords p q
          (primeGroupCoordinate pk).val
          (primeGroupCoordinate (statement g pk out).ciphertext.2).val
          cs.2.1.val cs.2.2.1.val
          (PrimeSecondCommitBMachine.localFrame (words slack g pk vote s live out cs))))
        (PrimeSecondCommitBMachine.frame (words slack g pk vote s live out cs))).stk k =
      (PrimeSecondCommitBMachine.result answer (words slack g pk vote s live out cs)).stk k := by
    obtain ⟨x,rfl⟩ := PrimeSecondCommitBMachine.layout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  exact congrArg (fun w => (⟨none,2,w⟩ : PrimeSecondCommitBMachine.Config)) (funext hs)

#print axioms source_inputs_embed
#print axioms source_outputs_embed
#print axioms source_inputs
#print axioms source_work
#print axioms source_bounds
#print axioms source_complement_width
#print axioms answer_source
end ExplainableCrypto.Helios.Computational.PrimeSecondCommitBSource
