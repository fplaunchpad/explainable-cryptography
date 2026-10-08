import ExplainableCrypto.Helios.Symbolic.SourceVisibleDeterminismPermutations

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted : Finset Nat} {handles : Nat}

/-- An actual input preserves the full canonical-opening invariant, with the
canonical label explicitly pulled back through the constructed coordinates.
Publicness of that pulled-back recipe is a separate, unassumed obligation. -/
theorem HasCanonicalOpening.input {a b : Named (Fin handles)}
    {φ : Frame restricted handles} {p : Agent Empty} (ha : HasCanonicalOpening a φ p)
    {c : Nat} {r : Recipe handles} (h : FreeStep a (.input c r) b)
    (hd : ∀ c m q s, Agent.Visible p (.input c m) q → Agent.Visible p (.input c m) s → Agent.EvalEq q s) :
    ∃ (e k : Nat ≃ Nat) (q : Agent Empty),
      Agent.Visible p (.input (k.symm c) (φ.eval (r.mapNames e.symm))) q ∧ HasCanonicalOpening b φ q := by
  obtain ⟨ns,d,e,k,ho,hf,he⟩ := ha.fresh b.freeNames
  obtain ⟨d',t,ms,b',hr,hc,hb,hj,hg⟩ := h.opening_step b.freeNames ho
    (fun n hn hm => hf n hn (Finset.mem_union_left _ hm))
  have hs : d'.SameRealizations (Extended.frameProcess (φ.mapNames e) (p.mapNames e k)) := by
    simpa only [Extended.frameProcess_mapNames] using hc.symm.trans he
  obtain ⟨q,hq,_⟩ := hr.input_realizes (φ.mapNames e).value
    ((hs _ _).mpr (Extended.frameProcess_realizes _ _))
  have ht := hr.input_sameRealizations_target (φ.mapNames e) (p.mapNames e k) q hs
    (fun s hs => Agent.input_determinism_mapNames p hd e k _ _ s q hs hq)
  have hqi : Agent.Visible p (.input (k.symm c) (φ.eval (r.mapNames e.symm)))
      (q.mapNames e.symm k.symm) := by
    have hv : (r.subst (φ.mapNames e).value).mapNames e.symm = φ.eval (r.mapNames e.symm) := by
      change ((φ.mapNames e).eval r).mapNames e.symm = _
      rw [Frame.eval_mapNames_inverse,Term.mapNames_inverse]
    simpa only [Agent.mapNames_inverse,Agent.PayloadEvent.mapNames,hv] using hq.mapNames e.symm k.symm
  refine ⟨e,k,q.mapNames e.symm k.symm,hqi,ms,b',e,k,hb,hg,?_⟩
  simpa only [Extended.frameProcess_mapNames,
    show (q.mapNames e.symm k.symm).mapNames e k = q from Agent.mapNames_inverse q e.symm k.symm] using hj.symm.trans ht

/-- An actual bound output preserves the entire canonical class after the
fresh variable becomes the new public handle. Both the output value and
continuation are retained; its canonical channel is recorded explicitly. -/
theorem HasCanonicalOpening.boundOutput {a : Named (Fin handles)}
    {b : Named (Option (Fin handles))} {φ : Frame restricted handles} {p : Agent Empty}
    (ha : HasCanonicalOpening a φ p) {c : Nat} (h : BoundOutput a c b)
    (hd : ∀ c m q n s, Agent.Visible p (.output c m) q → Agent.Visible p (.output c n) s →
      EqE m n ∧ Agent.EvalEq q s) :
    ∃ (k : Nat ≃ Nat) (m : Ground) (q : Agent Empty),
      Agent.Visible p (.output (k.symm c) m) q ∧
      HasCanonicalOpening (b.rename Extended.outputHandle) (φ.extend m) q := by
  obtain ⟨ns,d,e,k,ho,hf,he⟩ := ha.fresh b.freeNames
  obtain ⟨d',t,ms,b',hr,hc,hb,hj,hg⟩ := h.opening_step b.freeNames ho
    (fun n hn hm => hf n hn (Finset.mem_union_left _ hm))
  have hs : d'.SameRealizations (Extended.frameProcess (φ.mapNames e) (p.mapNames e k)) := by
    simpa only [Extended.frameProcess_mapNames] using hc.symm.trans he
  obtain ⟨m,q,hq,_⟩ := hr.realizes (φ.mapNames e).value
    ((hs _ _).mpr (Extended.frameProcess_realizes _ _))
  have ht := hr.sameRealizations_target (φ.mapNames e) (p.mapNames e k) q m hs
    (fun n s hs => Agent.output_determinism_mapNames p hd e k c n s m q hs hq)
  have hqi : Agent.Visible p (.output (k.symm c) (m.mapNames e.symm)) (q.mapNames e.symm k.symm) := by
    simpa only [Agent.mapNames_inverse,Agent.PayloadEvent.mapNames] using hq.mapNames e.symm k.symm
  refine ⟨k,m.mapNames e.symm,q.mapNames e.symm k.symm,hqi,ms,
    b'.rename Extended.outputHandle,e,k,hb.rename _,?_,?_⟩
  · simpa only [freeNames_rename] using hg
  · simpa only [Extended.frameProcess_mapNames,Frame.mapNames_extend,
      show (m.mapNames e.symm).mapNames e = m from Term.mapNames_inverse m e.symm,
      show (q.mapNames e.symm k.symm).mapNames e k = q from Agent.mapNames_inverse q e.symm k.symm]
      using (hj.rename Extended.outputHandle).symm.trans ht

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
