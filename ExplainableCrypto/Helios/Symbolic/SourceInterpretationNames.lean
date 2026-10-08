import ExplainableCrypto.Helios.Symbolic.SourceEquationalNameTransport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

/-- Source, full environment and body move together. Forward transport allows
arbitrary maps; reflecting the interpretation below requires actual bijections. -/
theorem Realizes.mapNames {a : Extended V} {env : V → Ground} {p : Agent Empty}
    (h : a.Realizes env p) (f g : Nat → Nat) :
    (a.mapNames f g).Realizes (fun v => (env v).mapNames f) (p.mapNames f g) := by
  induction a generalizing p with
  | plain a =>
    simpa only [Extended.mapNames,Realizes,Agent.mapNames_subst] using Agent.EvalEq.mapNames h f g
  | active x m =>
    exact ⟨by simpa only [Term.mapNames_subst] using h.1.mapNames f,h.2.mapNames f g⟩
  | par a b ha hb =>
    obtain ⟨q,r,hq,hr,hp⟩ := h
    exact ⟨q.mapNames f g,r.mapNames f g,ha hq,hb hr,hp.mapNames f g⟩
  | newVar a ih =>
    obtain ⟨m,hm⟩ := h
    refine ⟨m.mapNames f,?_⟩
    simpa only [extendEnv_mapNames] using ih hm

theorem realizes_mapNames_iff (a : Extended V) (env : V → Ground) (p : Agent Empty)
    (e k : Nat ≃ Nat) :
    (a.mapNames e k).Realizes (fun v => (env v).mapNames e) (p.mapNames e k) ↔
      a.Realizes env p := by
  constructor
  · intro h
    simpa only [Extended.mapNames_inverse,Term.mapNames_inverse,Agent.mapNames_inverse] using
      h.mapNames e.symm k.symm
  · exact fun h => h.mapNames e k

theorem realizes_mapped_environment_iff (a : Extended V) (env : V → Ground) (p : Agent Empty)
    (e k : Nat ≃ Nat) :
    (a.mapNames e k).Realizes env p ↔
      a.Realizes (fun v => (env v).mapNames e.symm) (p.mapNames e.symm k.symm) := by
  have he : (fun v => ((env v).mapNames e.symm).mapNames e) = env := by
    funext v
    exact Term.mapNames_inverse (env v) e.symm
  have hp : (p.mapNames e.symm k.symm).mapNames e k = p := Agent.mapNames_inverse p e.symm k.symm
  simpa only [he,hp] using
    realizes_mapNames_iff a (fun v => (env v).mapNames e.symm) (p.mapNames e.symm k.symm) e k

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
