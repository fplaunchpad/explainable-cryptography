import ExplainableCrypto.Helios.Symbolic.MixedCiphertexts
import ExplainableCrypto.Helios.Symbolic.GeneralMinimumOrigins

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n handles : Nat} {restricted : Finset Nat}

/-- Grouping distinguishes absence from a present contribution. No object-language
unit is inserted for an empty public or honest part. -/
inductive CiphertextGroup (n : Nat) (handles : Nat := 3) where
  | constructed (nonce payload : Recipe handles)
  | honest (tree : Combination (HonestIndex n))
  | mixed (nonce payload : Recipe handles) (tree : Combination (HonestIndex n))
  deriving DecidableEq, Repr

namespace CiphertextGroup

def merge : CiphertextGroup n handles → CiphertextGroup n handles → CiphertextGroup n handles
  | .constructed r p, .constructed s q => .constructed (.binary .compose r s) (.binary .add p q)
  | .constructed r p, .honest b => .mixed r p b
  | .constructed r p, .mixed s q b => .mixed (.binary .compose r s) (.binary .add p q) b
  | .honest a, .constructed s q => .mixed s q a
  | .honest a, .honest b => .honest (.mul a b)
  | .honest a, .mixed s q b => .mixed s q (.mul a b)
  | .mixed r p a, .constructed s q => .mixed (.binary .compose r s) (.binary .add p q) a
  | .mixed r p a, .honest b => .mixed r p (.mul a b)
  | .mixed r p a, .mixed s q b =>
      .mixed (.binary .compose r s) (.binary .add p q) (.mul a b)

def nonce (ns : Names n) (φ : Frame restricted handles) : CiphertextGroup n handles → Ground
  | .constructed r _ => φ.eval r
  | .honest a => combinationNonce ns a
  | .mixed r _ a => .binary .compose (φ.eval r) (combinationNonce ns a)

def message (φ : Frame restricted handles) (swap : Bool) (left right : CandidateSubstitution n Empty) :
    CiphertextGroup n handles → Ground
  | .constructed _ p => φ.eval p
  | .honest a => combinationMessage swap left right a
  | .mixed _ p a => .binary .add (φ.eval p) (combinationMessage swap left right a)

def Public (restricted : Finset Nat) : CiphertextGroup n handles → Prop
  | .constructed r p | .mixed r p _ => r.Public restricted ∧ p.Public restricted
  | .honest _ => True

/-- A combined budget leaves room for zero-padding only when an honest part
is present. It is measured against the original assembly, not its regrouping. -/
def budget : CiphertextGroup n handles → Nat
  | .constructed r p => r.nodeCount + p.nodeCount + 2
  | .honest _ => 2
  | .mixed r p _ => r.nodeCount + p.nodeCount + 3

end CiphertextGroup

/-- Exact syntax of a ciphertext-valued minimum recipe, with arbitrary constructed
key, nonce and payload subrecipes. Semantic key agreement is proved separately. -/
inductive CiphertextAssembly (n : Nat) (handles : Nat := 3) where
  | constructed (key nonce payload : Recipe handles)
  | honest (index : HonestIndex n)
  | mul (a b : CiphertextAssembly n handles)
  deriving DecidableEq, Repr

namespace CiphertextAssembly

def recipe : CiphertextAssembly n → Recipe 3
  | .constructed k r p => .ternary .penc k r p
  | .honest i => (Term.var i.1.succ).project i.2.val
  | .mul a b => .binary .mul a.recipe b.recipe

/-- A key recipe selected from the same tree, available to smaller equality
observations. Honest leaves select the public-key handle. -/
def keyRecipe : CiphertextAssembly n → Recipe 3
  | .constructed k _ _ => k
  | .honest _ => .var 0
  | .mul a _ => a.keyRecipe

def group : CiphertextAssembly n handles → CiphertextGroup n handles
  | .constructed _ r p => .constructed r p
  | .honest i => .honest (.leaf i)
  | .mul a b => a.group.merge b.group

/-- Every leaf must evaluate under the supplied common key. Honest leaves bind
that key to the actual public key; a tree with only public leaves need not. -/
def KeyAgreement (ns : Names n) (φ : Frame restricted handles) (key : Ground) : CiphertextAssembly n handles → Prop
  | .constructed k _ _ => EqE (φ.eval k) key
  | .honest _ => EqE (publicKey ns) key
  | .mul a b => a.KeyAgreement ns φ key ∧ b.KeyAgreement ns φ key

end CiphertextAssembly
end ExplainableCrypto.Helios.Symbolic.Historical.General
