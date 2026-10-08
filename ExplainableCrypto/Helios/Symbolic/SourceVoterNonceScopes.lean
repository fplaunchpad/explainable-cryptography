import ExplainableCrypto.Helios.Symbolic.SourceScopedTermProgram

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type} {n : Nat}

namespace VoterRegisters

/-- The new proof's fourth argument is its freshly bound ciphertext variable.
It adds no literal name beyond those of the ciphertext provider. -/
theorem proofRhs_nameSupport (s : VoterRegisters n V) (j : Fin (n+1)) :
    (s.proofRhs j).nameSupport = (s.ciphertext j).nameSupport := by
  simp only [proofRhs,ciphertext,shift,map,Term.nameSupport,Term.nameSupport_rename,Finset.union_empty]

/-- Saving a component only inserts variables into the register table; future
ciphertext providers retain exactly their original literal name support. -/
theorem afterBind_ciphertext_nameSupport (s : VoterRegisters n V) (j k : Fin (n+1)) :
    ((s.afterBind j).ciphertext k).nameSupport = (s.ciphertext k).nameSupport := by
  simp only [afterBind,ciphertext,shift,map,Term.nameSupport,Term.nameSupport_rename]

end VoterRegisters

/-- Figure 4 placement: restrict this candidate's nonce, then bind its
ciphertext and proof, and only then enter the following candidate's scope. -/
def scopedVoterComponents (nonces : Fin (n+1) → Nat) :
    List (Fin (n+1)) → {V : Type} → VoterRegisters n V → ScopedTermProgram V
  | [], _, s => .ofProgram (voterAggregate s)
  | j::js, _, s => .newName (nonces j) (.letTerm (s.ciphertext j)
      (.letTerm (s.proofRhs j) (scopedVoterComponents nonces js (s.afterBind j))))

theorem scopedVoterComponents_erase (nonces : Fin (n+1) → Nat) (indices : List (Fin (n+1)))
    (s : VoterRegisters n V) : (scopedVoterComponents nonces indices s).erase = voterComponents indices s := by
  induction indices generalizing V with
  | nil => exact ScopedTermProgram.erase_ofProgram _
  | cons j js ih => simp only [scopedVoterComponents,ScopedTermProgram.erase,voterComponents,ih]

theorem scopedVoterComponents_names (nonces : Fin (n+1) → Nat) (indices : List (Fin (n+1)))
    (s : VoterRegisters n V) : (scopedVoterComponents nonces indices s).names = indices.map nonces := by
  induction indices generalizing V with
  | nil => exact ScopedTermProgram.names_ofProgram _
  | cons j js ih => simp only [scopedVoterComponents,ScopedTermProgram.names,ih,List.map_cons]

/-- Only later nonces need to avoid earlier providers. The statement retains
that exact cross-candidate condition and the no-repeated-candidate premise. -/
theorem scopedVoterComponents_hoistable (nonces : Fin (n+1) → Nat) (indices : List (Fin (n+1)))
    (s : VoterRegisters n V) (hd : indices.Nodup)
    (hf : ∀ j ∈ indices, ∀ k ∈ indices, j ≠ k → nonces k ∉ (s.ciphertext j).nameSupport) :
    (scopedVoterComponents nonces indices s).Hoistable := by
  induction indices generalizing V with
  | nil => exact ScopedTermProgram.hoistable_ofProgram _
  | cons j js ih =>
    have hj := (List.nodup_cons.mp hd).1
    have ht := (List.nodup_cons.mp hd).2
    have fresh (u : Nat) (hu : u ∈ (scopedVoterComponents nonces js (s.afterBind j)).names) :
        u ∉ (s.ciphertext j).nameSupport := by
      rw [scopedVoterComponents_names] at hu
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hu
      exact hf j (by simp) k (by simp [hk]) (fun h => hj (h.symm ▸ hk))
    refine ⟨⟨ih (s.afterBind j) ht ?_,?_⟩,fresh⟩
    · intro k hk l hl hkl
      rw [VoterRegisters.afterBind_ciphertext_nameSupport]
      exact hf k (by simp [hk]) l (by simp [hl]) hkl
    · intro u hu
      rw [VoterRegisters.proofRhs_nameSupport]
      exact fresh u hu

/-- Freshness is about full syntax, not the E-normalized vote. Both honest
voters' allocated nonce families must avoid every supplied vote term. -/
def NoncesFreshFor (ns : Names n) (values : Fin (n+1) → Ground) : Prop :=
  ∀ i j k, ns.nonce i j ∉ (values k).nameSupport

def scopedVoterProgram (ns : Names n) (i : Fin 2) (values : Fin (n+1) → Ground) : ScopedTermProgram Empty :=
  scopedVoterComponents (ns.nonce i) (List.finRange (n+1)) (voterInitial ns i values)

def voterNonceList (ns : Names n) (i : Fin 2) : List SourceName :=
  (List.finRange (n+1)).map (fun j => .base (ns.nonce i j))

theorem scopedVoterProgram_erase (ns : Names n) (i : Fin 2) (values : Fin (n+1) → Ground) :
    (scopedVoterProgram ns i values).erase = voterProgram ns i values :=
  scopedVoterComponents_erase _ _ _

theorem scopedVoterProgram_names (ns : Names n) (i : Fin 2) (values : Fin (n+1) → Ground) :
    (scopedVoterProgram ns i values).names.map SourceName.base = voterNonceList ns i := by
  simp only [scopedVoterProgram,scopedVoterComponents_names,voterNonceList,List.map_map,Function.comp_def]

theorem scopedVoterProgram_hoistable (ns : Names n) (hn : ns.Fresh) (i : Fin 2)
    (values : Fin (n+1) → Ground) (hv : NoncesFreshFor ns values) :
    (scopedVoterProgram ns i values).Hoistable := by
  apply scopedVoterComponents_hoistable _ _ _ (List.nodup_finRange _)
  intro j _ k _ hjk
  have hk := (hn.2.2 i k).1
  have hnonce : ns.nonce i k ≠ ns.nonce i j := by
    intro h
    have he : (i,k) = (i,j) := hn.2.1 h
    exact hjk (congrArg Prod.snd he).symm
  simpa only [voterInitial,VoterRegisters.ciphertext,publicKey,Term.nameSupport,
    Finset.mem_union,Finset.mem_singleton,not_or] using ⟨hk,hnonce,hv i k j⟩

theorem scopedVoterProgram_hoists (ns : Names n) (hn : ns.Fresh) (i : Fin 2)
    (values : Fin (n+1) → Ground) (hv : NoncesFreshFor ns values) (channel : Nat) :
    Named.Structural ((scopedVoterProgram ns i values).compile channel)
      (Named.restrictNames (voterNonceList ns i) (.embed ((voterProgram ns i values).compile channel))) := by
  simpa only [scopedVoterProgram_names,scopedVoterProgram_erase] using
    (scopedVoterProgram ns i values).compile_hoist channel (scopedVoterProgram_hoistable ns hn i values hv)

/-- The exact interleaved source voter reaches its complete ballot output
under precisely its own nonce prefix. No nonce restriction is dropped. -/
theorem scopedVoterProgram_normalizes (ns : Names n) (hn : ns.Fresh) (i : Fin 2)
    (values : Fin (n+1) → Ground) (hv : NoncesFreshFor ns values) (channel : Nat) :
    Named.Structural ((scopedVoterProgram ns i values).compile channel)
      (Named.restrictNames (voterNonceList ns i)
        (.embed (.plain (.output channel (ballot ns i values) .nil)))) :=
  (scopedVoterProgram_hoists ns hn i values hv channel).trans
    ((Named.Structural.embed (voterProgram_normalizes ns i values channel)).restrictNames _)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
