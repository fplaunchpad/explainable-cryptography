import ExplainableCrypto.Helios.Symbolic.SourceNameRestrictionBridge

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
namespace Agent

/-- Every static channel occurrence, including all continuations and branches. -/
def channels : {V : Type} → Agent V → Finset Nat
  | _, .nil => ∅
  | _, .par p q => p.channels ∪ q.channels
  | _, .output c _ p => insert c p.channels
  | _, .input c p => insert c p.channels
  | _, .branch _ p q => p.channels ∪ q.channels

theorem channels_subst (p : Agent V) (σ : V → Term W) : (p.subst σ).channels = p.channels := by
  induction p generalizing W <;> simp_all only [subst,channels]

theorem channels_bind (p : Agent (Option V)) (m : Term V) : (p.bind m).channels = p.channels :=
  channels_subst p _

theorem channels_mapNames (p : Agent V) (f g : Nat → Nat) :
    (p.mapNames f g).channels = p.channels.image g := by
  induction p <;> simp_all [mapNames,channels,Finset.image_union]

theorem channel_mem_nameSupport (p : Agent V) (c : Nat) :
    c ∈ p.channels ↔ SourceName.channel c ∈ p.nameSupport := by
  induction p <;> simp_all [channels,nameSupport]
end Agent

namespace Extended

def channels : {V : Type} → Extended V → Finset Nat
  | _, .plain p => p.channels
  | _, .par a b => a.channels ∪ b.channels
  | _, .newVar a => a.channels
  | _, .active _ _ => ∅

theorem channels_rename (a : Extended V) (σ : V → W) : (a.rename σ).channels = a.channels := by
  induction a generalizing W <;> simp_all only [rename,channels,Agent.channels_subst]

theorem channels_mapNames (a : Extended V) (f g : Nat → Nat) :
    (a.mapNames f g).channels = a.channels.image g := by
  induction a <;> simp_all [mapNames,channels,Agent.channels_mapNames,Finset.image_union]

theorem channel_mem_nameSupport (a : Extended V) (c : Nat) :
    c ∈ a.channels ↔ SourceName.channel c ∈ a.nameSupport := by
  induction a <;> simp_all [channels,nameSupport,Agent.channel_mem_nameSupport]

theorem Structural.channels {a b : Extended V} (h : Structural a b) : a.channels = b.channels := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'
  | parLeft c h ih => simp only [Extended.channels,ih]
  | parRight a h ih => simp only [Extended.channels,ih]
  | newVar h ih => exact ih
  | plainPar => rfl
  | zero => simp [Extended.channels,Agent.channels]
  | assoc => exact Finset.union_assoc _ _ _
  | comm => exact Finset.union_comm _ _
  | newPar => simp only [Extended.channels,channels_rename]
  | «alias» => rfl
  | substPlain => simp only [Extended.channels,Agent.channels_subst]
  | substActive => rfl
  | rewrite => rfl

def FreeLabel.channel : FreeLabel V → Nat
  | .input c _ | .output c _ => c

theorem FreeLabel.channel_mem_support (l : FreeLabel V) : SourceName.channel l.channel ∈ l.nameSupport := by
  cases l <;> simp [FreeLabel.channel,FreeLabel.nameSupport]

theorem FreeStep.channel_mem {a b : Extended V} {l : FreeLabel V} (h : FreeStep a l b) : l.channel ∈ a.channels := by
  induction h with
  | input => exact Finset.mem_insert_self _ _
  | output => exact Finset.mem_insert_self _ _
  | scopeInput h ih => exact ih
  | scopeOutput h ih => exact ih
  | parLeft c h ih => exact Finset.mem_union_left _ ih
  | parRight a h ih => exact Finset.mem_union_right _ ih
  | congr hp h hq ih => rw [hp.channels]; exact ih

theorem BoundOutput.channel_mem {a : Extended V} {b : Extended (Option V)} {c : Nat}
    (h : BoundOutput a c b) : c ∈ a.channels := by
  induction h with
  | openAtom h => exact h.channel_mem
  | scope h ih => exact ih
  | parLeft d h ih => exact Finset.mem_union_left _ ih
  | parRight a h ih => exact Finset.mem_union_right _ ih
  | congr hp h hq ih => rw [hp.channels]; exact ih
end Extended
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
