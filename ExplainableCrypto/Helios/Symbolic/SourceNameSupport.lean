import ExplainableCrypto.Helios.Symbolic.SourceNameFrameEmbedding

namespace ExplainableCrypto.Helios.Symbolic
namespace Term
variable {V : Type}

def nameSupport : Term V → Finset Nat
  | .name n => {n}
  | .var _ | .const _ => ∅
  | .unary _ a => a.nameSupport
  | .binary _ a b => a.nameSupport ∪ b.nameSupport
  | .ternary _ a b c => a.nameSupport ∪ (b.nameSupport ∪ c.nameSupport)
  | .spk a b c d => a.nameSupport ∪ (b.nameSupport ∪ (c.nameSupport ∪ d.nameSupport))

theorem public_iff_nameSupport (t : Term V) (restricted : Finset Nat) :
    t.Public restricted ↔ ∀ n ∈ t.nameSupport, n ∉ restricted := by
  induction t <;> simp_all [Public,nameSupport,or_imp,forall_and]

theorem nameSupport_mapNames (t : Term V) (f : Nat → Nat) :
    (t.mapNames f).nameSupport = t.nameSupport.image f := by
  induction t <;> simp_all [mapNames,nameSupport,Finset.image_union]
end Term

namespace Historical.General.Source

/-- Literal base names and static channel names are different source sorts. -/
inductive SourceName where
  | base : Nat → SourceName
  | channel : Nat → SourceName
  deriving DecidableEq

def SourceName.map (f g : Nat → Nat) : SourceName → SourceName
  | .base n => .base (f n)
  | .channel c => .channel (g c)

def Formula.nameSupport : Formula V → Finset Nat
  | .equal a b | .unequal a b => a.nameSupport ∪ b.nameSupport
  | .both a b => a.nameSupport ∪ b.nameSupport

def Agent.nameSupport : {V : Type} → Agent V → Finset SourceName
  | _, .nil => ∅
  | _, .par p q => p.nameSupport ∪ q.nameSupport
  | _, .output c m p => insert (.channel c) (m.nameSupport.image SourceName.base ∪ p.nameSupport)
  | _, .input c p => insert (.channel c) p.nameSupport
  | _, .branch f p q => f.nameSupport.image SourceName.base ∪ (p.nameSupport ∪ q.nameSupport)

def Extended.nameSupport : {V : Type} → Extended V → Finset SourceName
  | _, .plain p => p.nameSupport
  | _, .par a b => a.nameSupport ∪ b.nameSupport
  | _, .newVar a => a.nameSupport
  | _, .active _ m => m.nameSupport.image SourceName.base

def Extended.FreeLabel.nameSupport : Extended.FreeLabel V → Finset SourceName
  | .input c m => insert (.channel c) (m.nameSupport.image SourceName.base)
  | .output c _ => {.channel c}

theorem input_base_fresh_iff (c n : Nat) (m : Term V) :
    SourceName.base n ∉ (Extended.FreeLabel.input c m).nameSupport ↔ m.Public {n} := by
  simp [Extended.FreeLabel.nameSupport,Term.public_iff_nameSupport]

theorem input_channel_fresh_iff (c d : Nat) (m : Term V) :
    SourceName.channel d ∉ (Extended.FreeLabel.input c m).nameSupport ↔ d ≠ c := by
  simp [Extended.FreeLabel.nameSupport]

theorem output_name_fresh_iff (c : Nat) (x : V) (n : SourceName) :
    n ∉ (Extended.FreeLabel.output c x).nameSupport ↔ n ≠ .channel c := by
  simp [Extended.FreeLabel.nameSupport]
end Historical.General.Source
end ExplainableCrypto.Helios.Symbolic
