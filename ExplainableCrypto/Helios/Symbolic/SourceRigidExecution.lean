import ExplainableCrypto.Helios.Symbolic.SourceNamedLocalRigidity
import ExplainableCrypto.Helios.Symbolic.SourceMappedCanonicalStates

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named

/-- Finite closure of original actions, structural equivalence and explicit
bijective handle relabelling. Only bound output increases the public domain.
This forgets labels for an invariant argument; it adds no operational rule. -/
inductive Execution : {V W : Type} → Named V → Named W → Prop where
  | refl (a : Named V) : Execution a a
  | structural {a b : Named V} (h : Structural a b) : Execution a b
  | internal {a b : Named V} (h : Reduction a b) : Execution a b
  | free {a b : Named V} {l : Extended.FreeLabel V} (h : FreeStep a l b) : Execution a b
  | bound {a : Named V} {b : Named (Option V)} {c : Nat} (h : BoundOutput a c b) : Execution a b
  | reindex (a : Named V) (e : V ≃ W) : Execution a (a.rename e)
  | trans {a : Named V} {b : Named W} {d : Named U}
      (h : Execution a b) (j : Execution b d) : Execution a d

variable {V W : Type}

/-- Every finite mixture of original actions preserves the opening invariant,
including any number of newly exported handles. -/
theorem Execution.locallyRigid {a : Named V} {b : Named W} (h : Execution a b)
    (ha : a.LocallyRigid) : b.LocallyRigid := by
  induction h with
  | refl => exact ha
  | structural h => exact h.locallyRigid.mp ha
  | internal h => exact h.locallyRigid.mp ha
  | free h => exact h.locallyRigid.mp ha
  | bound h => exact h.locallyRigid ha
  | reindex a e => exact ha.rename e
  | trans _ _ ih ij => exact ij (ih ha)

theorem Execution.from_presented {restricted hidden : Finset Nat} {handles : Nat}
    {a : Named (Fin handles)} {b : Named W} {φ : Frame restricted handles}
    (h : Execution a b) (ha : a.RepresentsFrame hidden φ) : b.LocallyRigid :=
  h.locallyRigid ha.locallyRigid

theorem Execution.from_canonical {restricted hidden : Finset Nat} {handles : Nat}
    (s : ScopedState restricted handles) {b : Named W}
    (h : Execution (restrictedState hidden s) b) : b.LocallyRigid :=
  h.locallyRigid (restrictedState_locallyRigid s)

/-- The generic semantic counterexample cannot be reached from any source
satisfying the invariant, with arbitrary intermediate actions and handle types. -/
theorem LocallyRigid.no_execution_to_cycle {a : Named V} (ha : a.LocallyRigid)
    {restricted : Finset Nat} {handles : Nat} (φ : Frame restricted handles) (p : Agent Empty) :
    ¬ Execution a (.embed (.par (Extended.frameProcess φ p) (.newVar (.active none (.var none))))) :=
  fun h => frame_with_unconstrained_local_not_locallyRigid φ p (h.locallyRigid ha)

theorem canonical_no_execution_to_cycle {restricted hidden restricted' : Finset Nat}
    {handles handles' : Nat} (s : ScopedState restricted handles) (φ : Frame restricted' handles')
    (p : Agent Empty) :
    ¬ Execution (restrictedState hidden s)
      (.embed (.par (Extended.frameProcess φ p) (.newVar (.active none (.var none))))) :=
  (restrictedState_locallyRigid s).no_execution_to_cycle φ p

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat} {V : Type}

/-- Every actual finite execution from a mapped canonical election phase
retains local rigidity. This is an action invariant, not a matching theorem. -/
theorem source_coordinated_execution_rigid (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (e k : Nat ≃ Nat) (phase : Process.Phase) {a : Named V}
    (h : Named.Execution
      (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k) a) :
    a.LocallyRigid :=
  h.from_canonical _

theorem source_coordinated_no_execution_to_cycle (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (e k : Nat ≃ Nat) (phase : Process.Phase) {restricted : Finset Nat} {handles : Nat}
    (φ : Frame restricted handles) (p : Agent Empty) :
    ¬ Named.Execution
      (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k)
      (.embed (.par (Extended.frameProcess φ p) (.newVar (.active none (.var none))))) := by
  intro h
  exact Named.frame_with_unconstrained_local_not_locallyRigid φ p
    (source_coordinated_execution_rigid ns swap left right extra ch e k phase h)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
