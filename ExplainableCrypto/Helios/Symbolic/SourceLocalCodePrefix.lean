import ExplainableCrypto.Helios.Symbolic.SourceOpenLocalPresentation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

private theorem pair_code (f g : Extended V) (p q : Agent V) :
    Structural (.par (.par f (.plain p)) (.par g (.plain q)))
      (.par (.par f g) (.plain (.par p q))) := by
  have middle (a b c : Extended V) : Structural (.par a (.par b c)) (.par b (.par a c)) :=
    (Structural.assoc _ _ _).symm.trans
      ((Structural.parLeft _ (Structural.comm _ _)).trans (Structural.assoc _ _ _))
  exact (Structural.assoc _ _ _).trans ((Structural.parRight f (middle _ _ _)).trans
    ((Structural.assoc _ _ _).symm.trans (Structural.parRight _ (Structural.plainPar _ _).symm)))

private theorem code_par_prefix (f : Extended V) (p : Agent V) (hf : f.FrameForest)
    (m : Nat) (g : Extended (LocalVars m V)) (q : Agent (LocalVars m V)) (hg : g.FrameForest) :
    ∃ (k : Nat) (r : Extended (LocalVars k V)) (s : Agent (LocalVars k V)), r.FrameForest ∧
      Structural (.par (.par f (.plain p)) (closeVars m (.par g (.plain q))))
        (closeVars k (.par r (.plain s))) := by
  refine ⟨m,.par (f.rename (outerVar m)) g,
    .par (p.subst (fun v => .var (outerVar m v))) q,⟨hf.rename _,hg⟩,?_⟩
  exact (par_closeVars m (.par f (.plain p)) _).trans
    (Structural.closeVars m (pair_code _ _ _ _))

private theorem prefix_code_pair (n m : Nat) (f : Extended (LocalVars n V))
    (p : Agent (LocalVars n V)) (g : Extended (LocalVars m V)) (q : Agent (LocalVars m V))
    (hf : f.FrameForest) (hg : g.FrameForest) :
    ∃ (k : Nat) (r : Extended (LocalVars k V)) (s : Agent (LocalVars k V)), r.FrameForest ∧
      Structural (.par (closeVars n (.par f (.plain p))) (closeVars m (.par g (.plain q))))
        (closeVars k (.par r (.plain s))) := by
  induction n generalizing V with
  | zero => exact code_par_prefix f p hf m g q hg
  | succ n ih =>
    obtain ⟨k,r,s,hr,hs⟩ := ih f p (g.rename (localMap m some))
      (q.subst (fun v => .var (localMap m some v))) hf (hg.rename _)
    have he : Structural
        (.par (.newVar (closeVars n (.par f (.plain p)))) (closeVars m (.par g (.plain q))))
        (.newVar (.par (closeVars n (.par f (.plain p)))
          ((closeVars m (.par g (.plain q))).rename some))) :=
      (Structural.comm _ _).trans ((Structural.newPar _ _).trans (.newVar (Structural.comm _ _)))
    rw [closeVars_rename] at he
    exact ⟨k+1,r,s,hr,he.trans (.newVar hs)⟩

/-- Universal extraction in the original source syntax, retaining every plain
continuation. All providers and code share the same finite local prefix; no
program-class or dependency-order premise is supplied. -/
theorem exists_local_code_prefix (a : Extended V) :
    ∃ (n : Nat) (f : Extended (LocalVars n V)) (p : Agent (LocalVars n V)), f.FrameForest ∧
      Structural a (closeVars n (.par f (.plain p))) := by
  induction a with
  | plain p => exact ⟨0,.plain .nil,p,rfl,(Structural.zero _).symm.trans (Structural.comm _ _)⟩
  | active x m => exact ⟨0,.active x m,.nil,True.intro,(Structural.zero _).symm⟩
  | newVar a ih =>
    obtain ⟨n,f,p,hf,hs⟩ := ih
    exact ⟨n+1,f,p,hf,.newVar hs⟩
  | par a b ih ij =>
    obtain ⟨n,f,p,hf,hs⟩ := ih
    obtain ⟨m,g,q,hg,ht⟩ := ij
    obtain ⟨k,r,s,hr,hu⟩ := prefix_code_pair n m f p g q hf hg
    exact ⟨k,r,s,hr,((hs.parLeft b).trans (ht.parRight _)).trans hu⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
