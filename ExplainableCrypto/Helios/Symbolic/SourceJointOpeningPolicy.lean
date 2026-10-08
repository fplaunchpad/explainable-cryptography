import ExplainableCrypto.Helios.Symbolic.SourceJointOpening
import ExplainableCrypto.Helios.Symbolic.SourceRealizationChannels

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type} {restricted hidden : Finset Nat} {handles : Nat}

/-- Jointly fresh openings retain free channel support of the actual scoped
processes. Refresh avoids both sources and the channel being tested. -/
theorem JointOpening.channels {a d : Named V} (h : JointOpening a d) : a.channels = d.channels := by
  ext c
  let avoid := insert (SourceName.channel c) (a.allNames ∪ d.allNames)
  obtain ⟨ns,b,ms,t,ha,hd,hf,hg,he,env,p,hr⟩ := h.fresh avoid
  have ha' := ha.structural_literal (fun n hn hh => hf n hn
    (Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ hh))))
  have hd' := hd.structural_literal (fun n hn hh => hg n hn
    (Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ hh))))
  have hn : SourceName.channel c ∉ ns := fun hh => hf _ hh
    (Finset.mem_union_left _ (Finset.mem_insert_self _ _))
  have hm : SourceName.channel c ∉ ms := fun hh => hg _ hh
    (Finset.mem_union_left _ (Finset.mem_insert_self _ _))
  rw [ha'.channels,hd'.channels,channel_mem_restrictNames,channel_mem_restrictNames]
  simp only [Named.channels,he.channels hr,hn,hm]

/-- Relative to an actual restricted canonical process, the joint relation
also supplies the earlier full-body invariant. The converse is refuted. -/
theorem JointOpening.hasCanonicalOpening {a : Named (Fin handles)}
    (s : ScopedState restricted handles) (h : JointOpening a (restrictedState hidden s)) :
    HasCanonicalOpening a s.frame s.body := by
  obtain ⟨ns,b,ms,c,ha,hd,hf,hg,he,_⟩ := h.fresh (Extended.frameProcess s.frame s.body).nameSupport
  obtain ⟨e,k,hc,_,_⟩ := hd.canonical_permutations s
    (fun n hn hh => hg n hn (Finset.mem_union_left _ hh))
  refine ⟨ns,b,e,k,ha,fun n hn hh => hf n hn
    (Finset.mem_union_right _ (Finset.mem_union_left _ hh)),?_⟩
  rw [hc,← Extended.frameProcess_mapNames] at he
  exact he

theorem JointOpening.free_channel_public {a b : Named (Fin handles)}
    (s : ScopedState restricted handles) (h : JointOpening a (restrictedState hidden s))
    {l : Extended.FreeLabel (Fin handles)} (hl : FreeStep a l b) : l.channel ∉ hidden := by
  have hc := hl.channel_mem
  rw [h.channels] at hc
  exact ((channel_mem_restrictedState hidden s l.channel).mp hc).2

theorem JointOpening.bound_channel_public {a : Named (Fin handles)} {b : Named (Option (Fin handles))}
    (s : ScopedState restricted handles) (h : JointOpening a (restrictedState hidden s))
    {c : Nat} (hl : BoundOutput a c b) : c ∉ hidden := by
  have hc := hl.channel_mem
  rw [h.channels] at hc
  exact ((channel_mem_restrictedState hidden s c).mp hc).2

theorem JointOpening.private_free_blocked {a b : Named (Fin handles)}
    (s : ScopedState restricted handles) (h : JointOpening a (restrictedState hidden s))
    (l : Extended.FreeLabel (Fin handles)) (hc : l.channel ∈ hidden) : ¬ FreeStep a l b :=
  fun hl => h.free_channel_public s hl hc

theorem JointOpening.private_bound_blocked {a : Named (Fin handles)} {b : Named (Option (Fin handles))}
    (s : ScopedState restricted handles) (h : JointOpening a (restrictedState hidden s))
    (c : Nat) (hc : c ∈ hidden) : ¬ BoundOutput a c b :=
  fun hl => h.bound_channel_public s hl hc

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
