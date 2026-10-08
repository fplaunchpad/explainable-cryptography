import ExplainableCrypto.Helios.Computational.PrimeRemainingProofCaller
import ExplainableCrypto.Helios.Computational.PrimeRemainingProofBounds

namespace ExplainableCrypto.Helios.Computational.PrimeRemainingProofCaller
open OracleComp OracleSpec BitOracleMachine
open PrimeProgramProofSource (State Cache Draws)
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
attribute [local irreducible] BitOracleMachine.run

-- Domain views align the existing literal label count with the request API.
-- These definitions do not change either code region or any instruction.
private def prefixLabels (l : Fin PrimeProgramOutputCaller.size) : Fin size := prefixLabel l
private theorem prefix_code_view (l : Fin PrimeProgramOutputCaller.size) : code (prefixLabels l) =
    BitOracleReturnLink.command prefixLabels (some (prepareP1Label 0)) (prefixCode l) := prefix_code l
private theorem prefix_return_view (old : Fin 50 → List Bool) :
    BitOracleReturnLink.embed prefixLabels (some (prepareP1Label 0))
      (BitOracleStackFrame.embed prefixLayout
        (⟨none,2,old⟩ : PrimeProgramOutputCaller.Config) (fun _ => [])) =
    BitOracleReturnLink.embed prepareP1Label (some (p1Label requestEntry))
      (PrimeProofRequestReentry.start false (initialWords old)) := by rfl
private def p1Labels (l : Fin PrimeProofRequest.size) : Fin size := p1Label l
private def totalLabels (l : Fin PrimeProofRequest.size) : Fin size := totalLabel l
private theorem p1_code_view (l : Fin PrimeProofRequest.size) : code (p1Labels l) =
    BitOracleReturnLink.command p1Labels (some (prepareTotalLabel 1)) (p1Code l) :=
  p1_code l
private theorem total_code_view (l : Fin PrimeProofRequest.size) : code (totalLabels l) =
    BitOracleReturnLink.command totalLabels none (totalCode l) := total_code l
private theorem p1_return_view (old : Fin 58 → List Bool) :
    BitOracleReturnLink.embed p1Labels (some (prepareTotalLabel 1))
      (⟨none,2,old⟩ : BitOracleMachine.Config 58 PrimeProofRequest.size 3) =
    BitOracleReturnLink.embed prepareTotalLabel (some (totalLabel requestEntry))
      (PrimeProofRequestReentry.start true old) := by rfl

private theorem word_le_height {n : Nat} (W : Fin n → List Bool) (k : Fin n) :
    (W k).length ≤ TM2TapeRuns.height W :=
  Finset.le_sup (f := fun j => (W j).length) (Finset.mem_univ k)

private theorem height_le {n : Nat} (W : Fin n → List Bool) (N : Nat)
    (h : ∀ k, (W k).length ≤ N) : TM2TapeRuns.height W ≤ N :=
  Finset.sup_le (fun k _ => h k)

private theorem prefix_words (old : Fin 50 → List Bool) :
    initialWords old = fun k : Fin 58 => if h : k.val < 50 then old ⟨k.val,h⟩ else [] := by
  funext k
  fin_cases k <;> rfl

def resident0 (raw : List Bool) (slack p q : Nat) :=
  raw.length+PrimeProgramOutputCaller.cost raw slack p q

def requestClock (slack p q N : Nat) :=
  PrimeRequestDraws.clock slack p q+PrimeProofRequest.tailClock p q N N

def requestCost (slack p q N : Nat) :=
  PrimeRequestDraws.cost slack p q+PrimeProofRequest.tailCost p q N N

private def nextBound (slack p q N : Nat) :=
  N+PrimeProofRequestReentry.cost q N+requestCost slack p q N

def resident1 (raw : List Bool) (slack p q : Nat) :=
  resident0 raw slack p q+PrimeProofRequestReentry.cost q (resident0 raw slack p q)+
    requestCost slack p q (resident0 raw slack p q)

def clock (raw : List Bool) (slack p q : Nat) :=
  PrimeProgramOutputCaller.clock raw slack p q+
    (PrimeProofRequestReentry.clock q (resident0 raw slack p q)+
      (requestClock slack p q (resident0 raw slack p q)+
        (PrimeProofRequestReentry.clock q (resident1 raw slack p q)+
          requestClock slack p q (resident1 raw slack p q))))

def cost (raw : List Bool) (slack p q : Nat) :=
  PrimeProgramOutputCaller.cost raw slack p q+
    (PrimeProofRequestReentry.cost q (resident0 raw slack p q)+
      (requestCost slack p q (resident0 raw slack p q)+
        (PrimeProofRequestReentry.cost q (resident1 raw slack p q)+
          requestCost slack p q (resident1 raw slack p q))))

private theorem prefix_support (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q))
    (first : PrimeProgramOutputCaller.Config × Nat)
    (hf : first ∈ support (BitOracleMachine.run PrimeProgramOutputCaller.code
      (PrimeProgramOutputCaller.clock (PrimeRemainingProofRequests.raw slack g pk vote s live) slack p q)
      (PrimeProgramOutputCaller.start (PrimeRemainingProofRequests.raw slack g pk vote s live)))) :
    ∃ out : Draws (q:=q),
      first.1 = PrimeProgramOutputCaller.sourceResult slack g pk vote s live out ∧
      first.2 ≤ PrimeProgramOutputCaller.cost (PrimeRemainingProofRequests.raw slack g pk vote s live) slack p q ∧
      (∀ k, (PrimeRemainingProofRequests.initialWords slack g pk vote s live out k).length ≤
        resident0 (PrimeRemainingProofRequests.raw slack g pk vote s live) slack p q) := by
  have hm : first.1 ∈ support (Prod.fst <$> BitOracleMachine.run PrimeProgramOutputCaller.code
      (PrimeProgramOutputCaller.clock (PrimeRemainingProofRequests.raw slack g pk vote s live) slack p q)
      (PrimeProgramOutputCaller.start (PrimeRemainingProofRequests.raw slack g pk vote s live))) := by
    rw [support_map]; exact ⟨first,hf,rfl⟩
  dsimp only [PrimeRemainingProofRequests.raw] at hm
  rw [PrimeProgramOutputCaller.execution_source,simulateQ_map] at hm
  obtain ⟨out,_,he⟩ := mem_support_map_peel _ _ hm
  have hc := (PrimeProgramOutputCaller.run_support slack g pk vote s live first hf).2
  have hh := PrimeRemainingProofRequests.run_height PrimeProgramOutputCaller.code _ _ first hf
  rw [PrimeProgramOutputCaller.start_height] at hh
  refine ⟨out,he,hc,?_⟩
  intro k
  dsimp only [PrimeRemainingProofRequests.initialWords]
  split_ifs with h
  · have hl := word_le_height first.1.stk ⟨k.val,h⟩
    rw [he] at hl hh
    exact hl.trans (hh.trans (Nat.add_le_add_left hc _))
  · exact Nat.zero_le _


private theorem first_resident_bounds (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (N : Nat)
    (hN : ∀ k, (PrimeRemainingProofRequests.initialWords slack g pk vote s live out k).length ≤ N) :
    PrimeProgramRequestRun.inputSize (PrimeRemainingProofRequests.firstState g pk vote s out) live ≤ N ∧
      PrimeProofRequest.outputBound (PrimeRemainingProofRequests.firstState g pk vote s out) live ≤ N := by
  have hf := PrimeProgramCaller.source_state slack g pk vote s live out
  apply PrimeProofRequest.resident_bounds _ live
    (PrimeRemainingProofRequests.initialWords slack g pk vote s live out) N
    hf.1 hf.2.2.1 hf.2.2.2 hN

private theorem second_resident_bounds (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : PrimeRemainingProofRequests.Scalars (q:=q)) (N : Nat)
    (hN : ∀ k, ((PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs).stk k).length ≤ N) :
    PrimeProgramRequestRun.inputSize (PrimeRemainingProofRequests.secondState g pk vote s out cs) live ≤ N ∧
      PrimeProofRequest.outputBound (PrimeRemainingProofRequests.secondState g pk vote s out cs) live ≤ N := by
  apply PrimeProofRequest.resident_bounds _ live
    (PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs).stk N
    (by rfl) (by rfl) (by rfl) hN

private theorem prepare_p1 (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (N : Nat)
    (hN : ∀ k, (PrimeRemainingProofRequests.initialWords slack g pk vote s live out k).length ≤ N) :
    ∃ c ≤ PrimeProofRequestReentry.cost q N,
      BitOracleMachine.run PrimeProofRequestReentry.code (PrimeProofRequestReentry.clock q N)
        (PrimeProofRequestReentry.start false (PrimeRemainingProofRequests.initialWords slack g pk vote s live out)) =
      pure (⟨none,2,PrimeRemainingProofRequests.p1Prepared slack g pk vote s live out⟩,c) := by
  obtain ⟨h2,h20,h21,h18,hw,h37⟩ := PrimeRemainingProofRequests.initial_reentry_inputs slack g pk vote s live out
  exact PrimeProofRequestReentry.charged_bounded false q out.1.1.val out.1.2.val N
    (ZMod.val_lt _) (ZMod.val_lt _) vote _ h2 h20 h21 h18 hw h37 hN

private theorem prepare_total (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : PrimeRemainingProofRequests.Scalars (q:=q)) (N : Nat)
    (hN : ∀ k, ((PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs).stk k).length ≤ N) :
    ∃ c ≤ PrimeProofRequestReentry.cost q N,
      BitOracleMachine.run PrimeProofRequestReentry.code (PrimeProofRequestReentry.clock q N)
        (PrimeProofRequestReentry.start true (PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs).stk) =
      pure (⟨none,2,PrimeRemainingProofRequests.totalPrepared slack g pk vote s live out cs⟩,c) := by
  obtain ⟨h2,h20,h21,h18,hw,h37⟩ := PrimeRemainingProofRequests.p1_reentry_inputs slack g pk vote s live out cs
  obtain ⟨c,hc,he⟩ := PrimeProofRequestReentry.charged_bounded true q out.1.1.val out.1.2.val N
    (ZMod.val_lt _) (ZMod.val_lt _) vote _ h2 h20 h21 h18 hw h37 hN
  refine ⟨c,hc,?_⟩
  simpa only [if_true,← PrimeRemainingProofRequests.sum_prefix,PrimeProofRequestReentry.result,
    PrimeRemainingProofRequests.totalPrepared] using he

private def p1Tree (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (N : Nat) :=
  BitOracleMachine.run p1Code (requestClock slack p q N)
    (BitOracleStackFrame.embed PrimeRemainingProofRequests.p1Layout
      (PrimeRemainingProofRequests.p1Start slack g pk vote s live out)
      (PrimeRemainingProofRequests.frame PrimeRemainingProofRequests.p1Layout
        (PrimeRemainingProofRequests.p1Prepared slack g pk vote s live out)))

private def totalTree (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : PrimeRemainingProofRequests.Scalars (q:=q)) (N : Nat) :=
  BitOracleMachine.run totalCode (requestClock slack p q N)
    (BitOracleStackFrame.embed PrimeRemainingProofRequests.totalLayout
      (PrimeRemainingProofRequests.totalStart slack g pk vote s live out cs)
      (PrimeRemainingProofRequests.frame PrimeRemainingProofRequests.totalLayout
        (PrimeRemainingProofRequests.totalPrepared slack g pk vote s live out cs)))


private theorem p1_tree_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (N : Nat)
    (hN : ∀ k, (PrimeRemainingProofRequests.initialWords slack g pk vote s live out k).length ≤ N) :
    Prod.fst <$> p1Tree slack g pk vote s live out N =
      simulateQ CoinWordLoader.liftCoins
        (PrimeRemainingProofRequests.p1Result slack g pk vote s live out <$> runFairBitUniform slack (PrimeFullFieldSource.drawTranscriptScalars q)) := by
  obtain ⟨hi,ho⟩ := first_resident_bounds slack g pk vote s live out N hN
  have he := PrimeProofRequest.execution_source_bounded slack g pk false out.1.2 (PrimeRemainingProofRequests.firstState g pk vote s out) live (scalarEncode out.1.2) (PrimeRemainingProofRequests.raw slack g pk vote s live) N hi ho
  have hm := congrArg (fun oa => (fun cfg => BitOracleStackFrame.embed PrimeRemainingProofRequests.p1Layout cfg
      (PrimeRemainingProofRequests.frame PrimeRemainingProofRequests.p1Layout
        (PrimeRemainingProofRequests.p1Prepared slack g pk vote s live out))) <$> oa) he
  dsimp only [p1Tree,p1Code]
  rw [BitOracleStackFrame.run]
  simp only [Functor.map_map,simulateQ_map,
    PrimeRemainingProofRequests.p1Start,requestClock,PrimeProofRequest.boundedClock] at hm ⊢
  exact hm

private theorem p1_tree_support (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (N : Nat)
    (hN : ∀ k, (PrimeRemainingProofRequests.initialWords slack g pk vote s live out k).length ≤ N)
    (last : BitOracleMachine.Config 58 PrimeProofRequest.size 3 × Nat)
    (hl : last ∈ support (p1Tree slack g pk vote s live out N)) :
    ∃ next : PrimeRemainingProofRequests.Scalars (q:=q),
      last.1 = PrimeRemainingProofRequests.p1Result slack g pk vote s live out next ∧ last.2 ≤ requestCost slack p q N := by
  have hm : last.1 ∈ support (Prod.fst <$> p1Tree slack g pk vote s live out N) := by
    rw [support_map]; exact ⟨last,hl,rfl⟩
  rw [p1_tree_source slack g pk vote s live out N hN,simulateQ_map] at hm
  obtain ⟨next,_,he⟩ := mem_support_map_peel _ _ hm
  refine ⟨next,he,?_⟩
  obtain ⟨hi,ho⟩ := first_resident_bounds slack g pk vote s live out N hN
  dsimp only [p1Tree,p1Code] at hl
  rw [BitOracleStackFrame.run] at hl
  obtain ⟨v,hv,heq⟩ := mem_support_map_peel _ _ hl
  subst last
  exact (PrimeProofRequest.run_support_bounded slack g pk false out.1.2 (PrimeRemainingProofRequests.firstState g pk vote s out) live (scalarEncode out.1.2) (PrimeRemainingProofRequests.raw slack g pk vote s live) N hi ho v hv).2

private theorem total_tree_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (cs : PrimeRemainingProofRequests.Scalars (q:=q)) (N : Nat)
    (hN : ∀ k, ((PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs).stk k).length ≤ N) :
    Prod.fst <$> totalTree slack g pk vote s live out cs N =
      simulateQ CoinWordLoader.liftCoins
        (PrimeRemainingProofRequests.totalResult slack g pk vote s live out cs <$> runFairBitUniform slack (PrimeFullFieldSource.drawTranscriptScalars q)) := by
  obtain ⟨hi,ho⟩ := second_resident_bounds slack g pk vote s live out cs N hN
  have he := PrimeProofRequest.execution_source_bounded slack g pk vote (out.1.1+out.1.2) (PrimeRemainingProofRequests.secondState g pk vote s out cs) live (scalarEncode out.1.2) (PrimeRemainingProofRequests.raw slack g pk vote s live) N hi ho
  have hm := congrArg (fun oa => (fun cfg => BitOracleStackFrame.embed PrimeRemainingProofRequests.totalLayout cfg
      (PrimeRemainingProofRequests.frame PrimeRemainingProofRequests.totalLayout
        (PrimeRemainingProofRequests.totalPrepared slack g pk vote s live out cs))) <$> oa) he
  dsimp only [totalTree,totalCode]
  rw [BitOracleStackFrame.run]
  simp only [Functor.map_map,simulateQ_map,
    PrimeRemainingProofRequests.totalStart,requestClock,PrimeProofRequest.boundedClock] at hm ⊢
  exact hm

private theorem total_tree_support (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (cs : PrimeRemainingProofRequests.Scalars (q:=q)) (N : Nat)
    (hN : ∀ k, ((PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs).stk k).length ≤ N)
    (last : BitOracleMachine.Config 58 PrimeProofRequest.size 3 × Nat)
    (hl : last ∈ support (totalTree slack g pk vote s live out cs N)) :
    ∃ next : PrimeRemainingProofRequests.Scalars (q:=q),
      last.1 = PrimeRemainingProofRequests.totalResult slack g pk vote s live out cs next ∧ last.2 ≤ requestCost slack p q N := by
  have hm : last.1 ∈ support (Prod.fst <$> totalTree slack g pk vote s live out cs N) := by
    rw [support_map]; exact ⟨last,hl,rfl⟩
  rw [total_tree_source slack g pk vote s live out cs N hN,simulateQ_map] at hm
  obtain ⟨next,_,he⟩ := mem_support_map_peel _ _ hm
  refine ⟨next,he,?_⟩
  obtain ⟨hi,ho⟩ := second_resident_bounds slack g pk vote s live out cs N hN
  dsimp only [totalTree,totalCode] at hl
  rw [BitOracleStackFrame.run] at hl
  obtain ⟨v,hv,heq⟩ := mem_support_map_peel _ _ hl
  subst last
  exact (PrimeProofRequest.run_support_bounded slack g pk vote (out.1.1+out.1.2) (PrimeRemainingProofRequests.secondState g pk vote s out cs) live (scalarEncode out.1.2) (PrimeRemainingProofRequests.raw slack g pk vote s live) N hi ho v hv).2


private theorem p1_tree_height (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (N : Nat)
    (hN : ∀ k, (PrimeRemainingProofRequests.initialWords slack g pk vote s live out k).length ≤ N)
    (last : BitOracleMachine.Config 58 PrimeProofRequest.size 3 × Nat)
    (hl : last ∈ support (p1Tree slack g pk vote s live out N)) :
    ∀ k, (last.1.stk k).length ≤ N+PrimeProofRequestReentry.cost q N+requestCost slack p q N := by
  obtain ⟨c,hc,he⟩ := prepare_p1 slack g pk vote s live out N hN
  have hs : (⟨none,2,PrimeRemainingProofRequests.p1Prepared slack g pk vote s live out⟩,c) ∈
      support (BitOracleMachine.run PrimeProofRequestReentry.code (PrimeProofRequestReentry.clock q N)
        (PrimeProofRequestReentry.start false (PrimeRemainingProofRequests.initialWords slack g pk vote s live out))) := by
    rw [he]; simp only [mem_support_pure_iff]
  have hr := PrimeRemainingProofRequests.run_height PrimeProofRequestReentry.code _ _ _ hs
  have hinit := height_le _ N hN
  have hprep : TM2TapeRuns.height (PrimeRemainingProofRequests.p1Prepared slack g pk vote s live out) ≤
      N+PrimeProofRequestReentry.cost q N :=
    hr.trans (Nat.add_le_add hinit hc)
  have hh := PrimeRemainingProofRequests.run_height p1Code _ _ last hl
  dsimp only [p1Tree] at hl
  rw [PrimeRemainingProofRequests.p1_start] at hh
  obtain ⟨_,_,hc'⟩ := p1_tree_support slack g pk vote s live out N hN last hl
  intro k
  exact (word_le_height last.1.stk k).trans (hh.trans (Nat.add_le_add hprep hc'))

private theorem total_entry (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : PrimeRemainingProofRequests.Scalars (q:=q)) :
    BitOracleReturnLink.embed prepareTotalLabel (some (totalLabel requestEntry))
      (⟨none,2,PrimeRemainingProofRequests.totalPrepared slack g pk vote s live out cs⟩ : PrimeProofRequestReentry.Config) =
    BitOracleReturnLink.embed totalLabels none
      (BitOracleStackFrame.embed PrimeRemainingProofRequests.totalLayout
        (PrimeRemainingProofRequests.totalStart slack g pk vote s live out cs)
        (PrimeRemainingProofRequests.frame PrimeRemainingProofRequests.totalLayout
          (PrimeRemainingProofRequests.totalPrepared slack g pk vote s live out cs))) := by
  have he := congrArg (fun cfg : BitOracleMachine.Config 58 PrimeProofRequest.size 3 =>
    BitOracleReturnLink.embed totalLabels none cfg)
    (PrimeRemainingProofRequests.total_start slack g pk vote s live out cs)
  exact he.symm

private theorem p1_entry (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    BitOracleReturnLink.embed prepareP1Label (some (p1Label requestEntry))
      (⟨none,2,PrimeRemainingProofRequests.p1Prepared slack g pk vote s live out⟩ : PrimeProofRequestReentry.Config) =
    BitOracleReturnLink.embed p1Labels (some (prepareTotalLabel 1))
      (BitOracleStackFrame.embed PrimeRemainingProofRequests.p1Layout
        (PrimeRemainingProofRequests.p1Start slack g pk vote s live out)
        (PrimeRemainingProofRequests.frame PrimeRemainingProofRequests.p1Layout
          (PrimeRemainingProofRequests.p1Prepared slack g pk vote s live out))) := by
  have he := congrArg (fun cfg : BitOracleMachine.Config 58 PrimeProofRequest.size 3 =>
    BitOracleReturnLink.embed p1Labels (some (prepareTotalLabel 1)) cfg)
    (PrimeRemainingProofRequests.p1_start slack g pk vote s live out)
  exact he.symm

private theorem total_pair_run (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : PrimeRemainingProofRequests.Scalars (q:=q)) (N : Nat)
    (hN : ∀ k, ((PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs).stk k).length ≤ N) :
    ∃ c ≤ PrimeProofRequestReentry.cost q N,
      BitOracleMachine.run code (PrimeProofRequestReentry.clock q N+requestClock slack p q N)
        (BitOracleReturnLink.embed prepareTotalLabel (some (totalLabel requestEntry))
          (PrimeProofRequestReentry.start true (PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs).stk)) =
      (fun last => (BitOracleReturnLink.embed totalLabels none last.1,c+last.2)) <$>
        totalTree slack g pk vote s live out cs N := by
  obtain ⟨c,hc,he⟩ := prepare_total slack g pk vote s live out cs N hN
  have tail : BitOracleMachine.run code (requestClock slack p q N)
      (BitOracleReturnLink.embed prepareTotalLabel (some (totalLabel requestEntry))
        (⟨none,2,PrimeRemainingProofRequests.totalPrepared slack g pk vote s live out cs⟩ : PrimeProofRequestReentry.Config)) =
      (fun last => (BitOracleReturnLink.embed totalLabels none last.1,last.2)) <$>
        totalTree slack g pk vote s live out cs N := by
    rw [total_entry,BitOracleReturnLink.rename_run _ _ _ total_code_view]
    rfl
  have hh : ∀ x ∈ support (BitOracleMachine.run PrimeProofRequestReentry.code
      (PrimeProofRequestReentry.clock q N)
      (PrimeProofRequestReentry.start true (PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs).stk)), x.1.l = none := by
    rw [he]; intro x hx; obtain rfl := eq_of_mem_support_pure _ hx; rfl
  have ht : ∀ x ∈ support (BitOracleMachine.run PrimeProofRequestReentry.code
      (PrimeProofRequestReentry.clock q N)
      (PrimeProofRequestReentry.start true (PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs).stk)),
      ∀ y ∈ support (BitOracleMachine.run code (requestClock slack p q N)
        (BitOracleReturnLink.embed prepareTotalLabel (some (totalLabel requestEntry)) x.1)), y.1.l = none := by
    rw [he]; intro x hx; obtain rfl := eq_of_mem_support_pure _ hx
    rw [tail]; intro y hy
    obtain ⟨last,hl,hy⟩ := mem_support_map_peel _ _ hy
    subst y
    obtain ⟨next,heq,_⟩ := total_tree_support slack g pk vote s live out cs N hN last hl
    rw [heq]; rfl
  refine ⟨c,hc,?_⟩
  rw [BitOracleReturnLink.run _ _ _ _ prepareTotal_code _ _ _ hh ht,he,pure_bind,tail]
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]

private theorem total_pair_support (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : PrimeRemainingProofRequests.Scalars (q:=q)) (N : Nat)
    (hN : ∀ k, ((PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs).stk k).length ≤ N)
    (last : Config × Nat)
    (hl : last ∈ support (BitOracleMachine.run code (PrimeProofRequestReentry.clock q N+requestClock slack p q N)
        (BitOracleReturnLink.embed prepareTotalLabel (some (totalLabel requestEntry))
          (PrimeProofRequestReentry.start true (PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs).stk)))) :
    last.1.l = none ∧ last.2 ≤ PrimeProofRequestReentry.cost q N+requestCost slack p q N := by
  obtain ⟨c,hc,he⟩ := total_pair_run slack g pk vote s live out cs N hN
  rw [he] at hl
  obtain ⟨v,hv,heq⟩ := mem_support_map_peel _ _ hl
  subst last
  obtain ⟨next,hs,hv⟩ := total_tree_support slack g pk vote s live out cs N hN v hv
  exact ⟨by rw [hs]; rfl,Nat.add_le_add hc hv⟩


private theorem total_pair_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : PrimeRemainingProofRequests.Scalars (q:=q)) (N : Nat)
    (hN : ∀ k, ((PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs).stk k).length ≤ N) :
    Prod.fst <$> BitOracleMachine.run code (PrimeProofRequestReentry.clock q N+requestClock slack p q N)
        (BitOracleReturnLink.embed prepareTotalLabel (some (totalLabel requestEntry))
          (PrimeProofRequestReentry.start true (PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs).stk)) =
    (fun final => BitOracleReturnLink.embed totalLabels none
      (PrimeRemainingProofRequests.totalResult slack g pk vote s live out cs final)) <$>
        simulateQ CoinWordLoader.liftCoins (runFairBitUniform slack (PrimeFullFieldSource.drawTranscriptScalars q)) := by
  obtain ⟨c,_,he⟩ := total_pair_run slack g pk vote s live out cs N hN
  rw [he]
  have hs := total_tree_source slack g pk vote s live out cs N hN
  rw [simulateQ_map] at hs
  have hm := congrArg (fun oa => BitOracleReturnLink.embed totalLabels none <$> oa) hs
  simp only [Functor.map_map] at hm ⊢
  exact hm

private theorem p1_run (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (N : Nat)
    (hN : ∀ k, (PrimeRemainingProofRequests.initialWords slack g pk vote s live out k).length ≤ N) :
    BitOracleMachine.run code
      (requestClock slack p q N+(PrimeProofRequestReentry.clock q (nextBound slack p q N)+
        requestClock slack p q (nextBound slack p q N)))
      (BitOracleReturnLink.embed p1Labels (some (prepareTotalLabel 1))
        (BitOracleStackFrame.embed PrimeRemainingProofRequests.p1Layout
          (PrimeRemainingProofRequests.p1Start slack g pk vote s live out)
          (PrimeRemainingProofRequests.frame PrimeRemainingProofRequests.p1Layout
            (PrimeRemainingProofRequests.p1Prepared slack g pk vote s live out)))) = (do
      let first ← p1Tree slack g pk vote s live out N
      let last ← BitOracleMachine.run code
        (PrimeProofRequestReentry.clock q (nextBound slack p q N)+requestClock slack p q (nextBound slack p q N))
        (BitOracleReturnLink.embed p1Labels (some (prepareTotalLabel 1)) first.1)
      pure (last.1,first.2+last.2)) := by
  have hh : ∀ first ∈ support (p1Tree slack g pk vote s live out N), first.1.l = none := by
    intro first hf
    obtain ⟨cs,he,_⟩ := p1_tree_support slack g pk vote s live out N hN first hf
    rw [he]; rfl
  have ht : ∀ first ∈ support (p1Tree slack g pk vote s live out N),
      ∀ last ∈ support (BitOracleMachine.run code
        (PrimeProofRequestReentry.clock q (nextBound slack p q N)+requestClock slack p q (nextBound slack p q N))
        (BitOracleReturnLink.embed p1Labels (some (prepareTotalLabel 1)) first.1)), last.1.l = none := by
    intro first hf
    obtain ⟨cs,he,_⟩ := p1_tree_support slack g pk vote s live out N hN first hf
    have hb := p1_tree_height slack g pk vote s live out N hN first hf
    rw [he] at hb
    rw [he]
    change ∀ last ∈ support (BitOracleMachine.run code _
      (BitOracleReturnLink.embed p1Labels (some (prepareTotalLabel 1))
        (⟨none,2,(PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs).stk⟩ : BitOracleMachine.Config 58 PrimeProofRequest.size 3))), _
    rw [p1_return_view]
    intro last hl
    exact (total_pair_support slack g pk vote s live out cs _ hb last hl).1
  exact BitOracleReturnLink.run p1Code code p1Labels (prepareTotalLabel 1) p1_code_view _ _ _ hh ht

private theorem p1_run_support (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (N : Nat)
    (hN : ∀ k, (PrimeRemainingProofRequests.initialWords slack g pk vote s live out k).length ≤ N)
    (last : Config × Nat)
    (hl : last ∈ support (BitOracleMachine.run code
      (requestClock slack p q N+(PrimeProofRequestReentry.clock q (nextBound slack p q N)+
        requestClock slack p q (nextBound slack p q N)))
      (BitOracleReturnLink.embed p1Labels (some (prepareTotalLabel 1))
        (BitOracleStackFrame.embed PrimeRemainingProofRequests.p1Layout
          (PrimeRemainingProofRequests.p1Start slack g pk vote s live out)
          (PrimeRemainingProofRequests.frame PrimeRemainingProofRequests.p1Layout
            (PrimeRemainingProofRequests.p1Prepared slack g pk vote s live out)))))) :
    last.1.l = none ∧ last.2 ≤ requestCost slack p q N+
      (PrimeProofRequestReentry.cost q (nextBound slack p q N)+requestCost slack p q (nextBound slack p q N)) := by
  rw [p1_run slack g pk vote s live out N hN] at hl
  rw [mem_support_bind_iff] at hl
  obtain ⟨first,hf,hl⟩ := hl
  rw [mem_support_bind_iff] at hl
  obtain ⟨tail,ht,hl⟩ := hl
  obtain rfl := eq_of_mem_support_pure _ hl
  obtain ⟨cs,he,hc⟩ := p1_tree_support slack g pk vote s live out N hN first hf
  have hb := p1_tree_height slack g pk vote s live out N hN first hf
  rw [he] at hb ht
  change tail ∈ support (BitOracleMachine.run code _
    (BitOracleReturnLink.embed p1Labels (some (prepareTotalLabel 1))
      (⟨none,2,(PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs).stk⟩ : BitOracleMachine.Config 58 PrimeProofRequest.size 3))) at ht
  rw [p1_return_view] at ht
  have hh := total_pair_support slack g pk vote s live out cs _ hb tail ht
  exact ⟨hh.1,Nat.add_le_add hc hh.2⟩

#print axioms p1_run
#print axioms p1_run_support

private theorem p1_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (N : Nat)
    (hN : ∀ k, (PrimeRemainingProofRequests.initialWords slack g pk vote s live out k).length ≤ N) :
    Prod.fst <$> BitOracleMachine.run code
      (requestClock slack p q N+(PrimeProofRequestReentry.clock q (nextBound slack p q N)+
        requestClock slack p q (nextBound slack p q N)))
      (BitOracleReturnLink.embed p1Labels (some (prepareTotalLabel 1))
        (BitOracleStackFrame.embed PrimeRemainingProofRequests.p1Layout
          (PrimeRemainingProofRequests.p1Start slack g pk vote s live out)
          (PrimeRemainingProofRequests.frame PrimeRemainingProofRequests.p1Layout
            (PrimeRemainingProofRequests.p1Prepared slack g pk vote s live out)))) = (do
      let cs ← simulateQ CoinWordLoader.liftCoins (runFairBitUniform slack (PrimeFullFieldSource.drawTranscriptScalars q))
      let final ← simulateQ CoinWordLoader.liftCoins (runFairBitUniform slack (PrimeFullFieldSource.drawTranscriptScalars q))
      pure (BitOracleReturnLink.embed totalLabels none
        (PrimeRemainingProofRequests.totalResult slack g pk vote s live out cs final))) := by
  rw [p1_run slack g pk vote s live out N hN]
  let T := PrimeProofRequestReentry.clock q (nextBound slack p q N)+requestClock slack p q (nextBound slack p q N)
  calc
    _ = (do
      let cfg ← Prod.fst <$> p1Tree slack g pk vote s live out N
      Prod.fst <$> BitOracleMachine.run code T
        (BitOracleReturnLink.embed p1Labels (some (prepareTotalLabel 1)) cfg)) := by
      simp only [T,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
    _ = (do
      let cs ← simulateQ CoinWordLoader.liftCoins (runFairBitUniform slack (PrimeFullFieldSource.drawTranscriptScalars q))
      Prod.fst <$> BitOracleMachine.run code T
        (BitOracleReturnLink.embed p1Labels (some (prepareTotalLabel 1))
          (PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs))) := by
      rw [p1_tree_source slack g pk vote s live out N hN,simulateQ_map]
      simp only [bind_map_left]
    _ = _ := by
      apply bind_congr_of_forall_mem_support
      intro cs hcs
      have hm : PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs ∈
          support (Prod.fst <$> p1Tree slack g pk vote s live out N) := by
        rw [p1_tree_source slack g pk vote s live out N hN,simulateQ_map,support_map]
        exact ⟨cs,hcs,rfl⟩
      obtain ⟨first,hf,he⟩ := mem_support_map_peel _ _ hm
      have hb := p1_tree_height slack g pk vote s live out N hN first hf
      rw [←he] at hb
      change Prod.fst <$> BitOracleMachine.run code T
        (BitOracleReturnLink.embed p1Labels (some (prepareTotalLabel 1))
          (⟨none,2,(PrimeRemainingProofRequests.p1Result slack g pk vote s live out cs).stk⟩ : BitOracleMachine.Config 58 PrimeProofRequest.size 3)) = _
      rw [p1_return_view]
      have ht := total_pair_source slack g pk vote s live out cs (nextBound slack p q N) hb
      simpa only [map_eq_bind_pure_comp,Function.comp_def] using ht

private theorem remaining_run (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (N : Nat)
    (hN : ∀ k, (PrimeRemainingProofRequests.initialWords slack g pk vote s live out k).length ≤ N) :
    ∃ c ≤ PrimeProofRequestReentry.cost q N,
      BitOracleMachine.run code
        (PrimeProofRequestReentry.clock q N+(requestClock slack p q N+
          (PrimeProofRequestReentry.clock q (nextBound slack p q N)+requestClock slack p q (nextBound slack p q N))))
        (BitOracleReturnLink.embed prepareP1Label (some (p1Label requestEntry))
          (PrimeProofRequestReentry.start false (PrimeRemainingProofRequests.initialWords slack g pk vote s live out))) =
      (fun last => (last.1,c+last.2)) <$>
        BitOracleMachine.run code
          (requestClock slack p q N+(PrimeProofRequestReentry.clock q (nextBound slack p q N)+requestClock slack p q (nextBound slack p q N)))
          (BitOracleReturnLink.embed p1Labels (some (prepareTotalLabel 1))
            (BitOracleStackFrame.embed PrimeRemainingProofRequests.p1Layout
              (PrimeRemainingProofRequests.p1Start slack g pk vote s live out)
              (PrimeRemainingProofRequests.frame PrimeRemainingProofRequests.p1Layout
                (PrimeRemainingProofRequests.p1Prepared slack g pk vote s live out)))) := by
  obtain ⟨c,hc,he⟩ := prepare_p1 slack g pk vote s live out N hN
  have hh : ∀ x ∈ support (BitOracleMachine.run PrimeProofRequestReentry.code
      (PrimeProofRequestReentry.clock q N)
      (PrimeProofRequestReentry.start false (PrimeRemainingProofRequests.initialWords slack g pk vote s live out))), x.1.l = none := by
    rw [he]; intro x hx; obtain rfl := eq_of_mem_support_pure _ hx; rfl
  have ht : ∀ x ∈ support (BitOracleMachine.run PrimeProofRequestReentry.code
      (PrimeProofRequestReentry.clock q N)
      (PrimeProofRequestReentry.start false (PrimeRemainingProofRequests.initialWords slack g pk vote s live out))),
      ∀ y ∈ support (BitOracleMachine.run code
        (requestClock slack p q N+(PrimeProofRequestReentry.clock q (nextBound slack p q N)+requestClock slack p q (nextBound slack p q N)))
        (BitOracleReturnLink.embed prepareP1Label (some (p1Label requestEntry)) x.1)), y.1.l = none := by
    rw [he]; intro x hx; obtain rfl := eq_of_mem_support_pure _ hx
    rw [p1_entry]; intro y hy
    exact (p1_run_support slack g pk vote s live out N hN y hy).1
  refine ⟨c,hc,?_⟩
  rw [BitOracleReturnLink.run _ _ _ _ prepareP1_code _ _ _ hh ht,he,pure_bind,p1_entry]
  simp only [map_eq_bind_pure_comp,Function.comp_def]

private theorem remaining_support (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (N : Nat)
    (hN : ∀ k, (PrimeRemainingProofRequests.initialWords slack g pk vote s live out k).length ≤ N)
    (last : Config × Nat)
    (hl : last ∈ support (BitOracleMachine.run code
      (PrimeProofRequestReentry.clock q N+(requestClock slack p q N+
        (PrimeProofRequestReentry.clock q (nextBound slack p q N)+requestClock slack p q (nextBound slack p q N))))
      (BitOracleReturnLink.embed prepareP1Label (some (p1Label requestEntry))
        (PrimeProofRequestReentry.start false (PrimeRemainingProofRequests.initialWords slack g pk vote s live out))))) :
    last.1.l = none ∧ last.2 ≤ PrimeProofRequestReentry.cost q N+
      (requestCost slack p q N+(PrimeProofRequestReentry.cost q (nextBound slack p q N)+requestCost slack p q (nextBound slack p q N))) := by
  obtain ⟨c,hc,he⟩ := remaining_run slack g pk vote s live out N hN
  rw [he] at hl
  obtain ⟨v,hv,heq⟩ := mem_support_map_peel _ _ hl
  subst last
  have hh := p1_run_support slack g pk vote s live out N hN v hv
  exact ⟨hh.1,Nat.add_le_add hc hh.2⟩

private theorem remaining_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (N : Nat)
    (hN : ∀ k, (PrimeRemainingProofRequests.initialWords slack g pk vote s live out k).length ≤ N) :
    Prod.fst <$> BitOracleMachine.run code
      (PrimeProofRequestReentry.clock q N+(requestClock slack p q N+
        (PrimeProofRequestReentry.clock q (nextBound slack p q N)+requestClock slack p q (nextBound slack p q N))))
      (BitOracleReturnLink.embed prepareP1Label (some (p1Label requestEntry))
        (PrimeProofRequestReentry.start false (PrimeRemainingProofRequests.initialWords slack g pk vote s live out))) = (do
      let cs ← simulateQ CoinWordLoader.liftCoins (runFairBitUniform slack (PrimeFullFieldSource.drawTranscriptScalars q))
      let final ← simulateQ CoinWordLoader.liftCoins (runFairBitUniform slack (PrimeFullFieldSource.drawTranscriptScalars q))
      pure (BitOracleReturnLink.embed totalLabels none
        (PrimeRemainingProofRequests.totalResult slack g pk vote s live out cs final))) := by
  obtain ⟨c,_,he⟩ := remaining_run slack g pk vote s live out N hN
  rw [he]
  simpa only [Functor.map_map,Function.comp_def] using p1_source slack g pk vote s live out N hN

#print axioms remaining_run
#print axioms remaining_source
#print axioms remaining_support

private theorem supported_prefix_return (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q))
    (first : PrimeProgramOutputCaller.Config × Nat)
    (hf : first ∈ support (BitOracleMachine.run PrimeProgramOutputCaller.code
      (PrimeProgramOutputCaller.clock (PrimeRemainingProofRequests.raw slack g pk vote s live) slack p q)
      (PrimeProgramOutputCaller.start (PrimeRemainingProofRequests.raw slack g pk vote s live)))) :
    ∃ out : Draws (q:=q),
      BitOracleReturnLink.embed prefixLabels (some (prepareP1Label 0))
        (BitOracleStackFrame.embed prefixLayout first.1 (fun _ => [])) =
      BitOracleReturnLink.embed prepareP1Label (some (p1Label requestEntry))
        (PrimeProofRequestReentry.start false (PrimeRemainingProofRequests.initialWords slack g pk vote s live out)) ∧
      first.2 ≤ PrimeProgramOutputCaller.cost (PrimeRemainingProofRequests.raw slack g pk vote s live) slack p q ∧
      (∀ k, (PrimeRemainingProofRequests.initialWords slack g pk vote s live out k).length ≤
        resident0 (PrimeRemainingProofRequests.raw slack g pk vote s live) slack p q) := by
  obtain ⟨out,he,hc,hn⟩ := prefix_support slack g pk vote s live first hf
  refine ⟨out,?_,hc,hn⟩
  rw [he]
  change BitOracleReturnLink.embed prefixLabels (some (prepareP1Label 0))
    (BitOracleStackFrame.embed prefixLayout
      (⟨none,2,(PrimeProgramOutputCaller.sourceResult slack g pk vote s live out).stk⟩ : PrimeProgramOutputCaller.Config) (fun _ => [])) = _
  rw [prefix_return_view,prefix_words]
  rfl

/-- All five regions execute in one run, retaining the prefix charge and every
actual later charge. The later state-size envelopes are derived from execution. -/
theorem linked_run (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) :
    let raw := PrimeRemainingProofRequests.raw slack g pk vote s live
    BitOracleMachine.run code (clock raw slack p q) (start raw) = (do
      let first ← BitOracleMachine.run PrimeProgramOutputCaller.code
        (PrimeProgramOutputCaller.clock raw slack p q) (PrimeProgramOutputCaller.start raw)
      let last ← BitOracleMachine.run code
        (PrimeProofRequestReentry.clock q (resident0 raw slack p q)+
          (requestClock slack p q (resident0 raw slack p q)+
            (PrimeProofRequestReentry.clock q (resident1 raw slack p q)+requestClock slack p q (resident1 raw slack p q))))
        (BitOracleReturnLink.embed prefixLabels (some (prepareP1Label 0))
          (BitOracleStackFrame.embed prefixLayout first.1 (fun _ => [])))
      pure (last.1,first.2+last.2)) := by
  dsimp only
  let raw := PrimeRemainingProofRequests.raw slack g pk vote s live
  let R := PrimeProofRequestReentry.clock q (resident0 raw slack p q)+
    (requestClock slack p q (resident0 raw slack p q)+
      (PrimeProofRequestReentry.clock q (resident1 raw slack p q)+requestClock slack p q (resident1 raw slack p q)))
  have hf := BitOracleStackFrame.run prefixLayout PrimeProgramOutputCaller.code
    (PrimeProgramOutputCaller.clock raw slack p q) (PrimeProgramOutputCaller.start raw) (fun _ => [])
  change BitOracleMachine.run prefixCode (PrimeProgramOutputCaller.clock raw slack p q)
    (BitOracleStackFrame.embed prefixLayout (PrimeProgramOutputCaller.start raw) (fun _ => [])) = _ at hf
  have hh : ∀ first ∈ support (BitOracleMachine.run prefixCode
      (PrimeProgramOutputCaller.clock raw slack p q)
      (BitOracleStackFrame.embed prefixLayout (PrimeProgramOutputCaller.start raw) (fun _ => []))), first.1.l = none := by
    rw [hf]; intro first h
    obtain ⟨v,hv,he⟩ := mem_support_map_peel _ _ h
    subst first
    exact (PrimeProgramOutputCaller.run_support slack g pk vote s live v hv).1
  have ht : ∀ first ∈ support (BitOracleMachine.run prefixCode
      (PrimeProgramOutputCaller.clock raw slack p q)
      (BitOracleStackFrame.embed prefixLayout (PrimeProgramOutputCaller.start raw) (fun _ => []))),
      ∀ last ∈ support (BitOracleMachine.run code R
        (BitOracleReturnLink.embed prefixLabels (some (prepareP1Label 0)) first.1)), last.1.l = none := by
    rw [hf]; intro first h
    obtain ⟨v,hv,he⟩ := mem_support_map_peel _ _ h
    subst first
    obtain ⟨out,hr,_,hn⟩ := supported_prefix_return slack g pk vote s live v hv
    change ∀ last ∈ support (BitOracleMachine.run code R
      (BitOracleReturnLink.embed prefixLabels (some (prepareP1Label 0))
        (BitOracleStackFrame.embed prefixLayout v.1 (fun _ => [])))), last.1.l = none
    rw [hr]; intro last hl
    exact (remaining_support slack g pk vote s live out _ hn last hl).1
  change BitOracleMachine.run code (PrimeProgramOutputCaller.clock raw slack p q+R)
    (BitOracleReturnLink.embed prefixLabels (some (prepareP1Label 0))
      (BitOracleStackFrame.embed prefixLayout (PrimeProgramOutputCaller.start raw) (fun _ => []))) = _
  rw [BitOracleReturnLink.run _ _ _ _ prefix_code_view _ _ _ hh ht,hf]
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
  rfl

/-- Every supported result of the original raw execution halts within the
combined prefix, two executed reentries and two instances of the same executor. -/
theorem run_support (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) :
    let raw := PrimeRemainingProofRequests.raw slack g pk vote s live
    ∀ last ∈ support (BitOracleMachine.run code (clock raw slack p q) (start raw)),
      last.1.l = none ∧ last.2 ≤ cost raw slack p q := by
  dsimp only
  rw [linked_run]
  intro last hl
  rw [mem_support_bind_iff] at hl
  obtain ⟨first,hf,hl⟩ := hl
  rw [mem_support_bind_iff] at hl
  obtain ⟨tail,ht,hl⟩ := hl
  obtain rfl := eq_of_mem_support_pure _ hl
  obtain ⟨out,hr,hc,hn⟩ := supported_prefix_return slack g pk vote s live first hf
  rw [hr] at ht
  have hh := remaining_support slack g pk vote s live out _ hn tail ht
  exact ⟨hh.1,Nat.add_le_add hc hh.2⟩

#print axioms linked_run
#print axioms run_support

/-- The original nonce pair and p0 transcript, followed by two fresh independent
transcripts. The original remaining submission continuation is outside this code. -/
def drawSource (q : Nat) [Fact q.Prime] := do
  let out ← PrimeHonestTranscriptCaller.drawSource q
  let cs ← PrimeFullFieldSource.drawTranscriptScalars q
  let final ← PrimeFullFieldSource.drawTranscriptScalars q
  pure (out,cs,final)

/-- Complete resident output: original p0, p1 and total ciphertext/proof fields,
with the current programmed state and saved encoding after the total request. -/
def sourceResult (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q))
    (sample : Draws (q:=q) × PrimeRemainingProofRequests.Scalars (q:=q) × PrimeRemainingProofRequests.Scalars (q:=q)) : Config :=
  BitOracleReturnLink.embed totalLabels none
    (PrimeRemainingProofRequests.totalResult slack g pk vote s live sample.1 sample.2.1 sample.2.2)

private theorem source_height (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (ho : out ∈ support (simulateQ CoinWordLoader.liftCoins
      (runFairBitUniform slack (PrimeHonestTranscriptCaller.drawSource q)))) :
    ∀ k, (PrimeRemainingProofRequests.initialWords slack g pk vote s live out k).length ≤
      resident0 (PrimeRemainingProofRequests.raw slack g pk vote s live) slack p q := by
  let raw := PrimeRemainingProofRequests.raw slack g pk vote s live
  have hm : PrimeProgramOutputCaller.sourceResult slack g pk vote s live out ∈
      support (Prod.fst <$> BitOracleMachine.run PrimeProgramOutputCaller.code
        (PrimeProgramOutputCaller.clock raw slack p q) (PrimeProgramOutputCaller.start raw)) := by
    dsimp only [raw,PrimeRemainingProofRequests.raw]
    rw [PrimeProgramOutputCaller.execution_source,simulateQ_map,support_map]
    exact ⟨out,ho,rfl⟩
  obtain ⟨first,hf,he⟩ := mem_support_map_peel _ _ hm
  have hh := PrimeRemainingProofRequests.run_height PrimeProgramOutputCaller.code _ _ first hf
  rw [PrimeProgramOutputCaller.start_height,←he] at hh
  have hc := (PrimeProgramOutputCaller.run_support slack g pk vote s live first hf).2
  intro k
  dsimp only [PrimeRemainingProofRequests.initialWords]
  split_ifs with h
  · exact (word_le_height _ ⟨k.val,h⟩).trans (hh.trans (Nat.add_le_add_left hc _))
  · exact Nat.zero_le _

/-- One original raw input executes p0, the false/r2 request and the original
vote/(r1+r2) request. Reentry performs the modular sum, including zero; all fresh
query trees and the full final resident state are preserved exactly. -/
theorem execution_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) :
    let raw := PrimeRemainingProofRequests.raw slack g pk vote s live
    Prod.fst <$> BitOracleMachine.run code (clock raw slack p q) (start raw) =
      simulateQ CoinWordLoader.liftCoins
        (sourceResult slack g pk vote s live <$> runFairBitUniform slack (drawSource q)) := by
  dsimp only
  rw [linked_run]
  let raw := PrimeRemainingProofRequests.raw slack g pk vote s live
  let R := PrimeProofRequestReentry.clock q (resident0 raw slack p q)+
    (requestClock slack p q (resident0 raw slack p q)+
      (PrimeProofRequestReentry.clock q (resident1 raw slack p q)+requestClock slack p q (resident1 raw slack p q)))
  have hp := PrimeProgramOutputCaller.execution_source slack g pk vote s live
  change Prod.fst <$> BitOracleMachine.run PrimeProgramOutputCaller.code
    (PrimeProgramOutputCaller.clock raw slack p q) (PrimeProgramOutputCaller.start raw) = _ at hp
  calc
    _ = (do
      let cfg ← Prod.fst <$> BitOracleMachine.run PrimeProgramOutputCaller.code
        (PrimeProgramOutputCaller.clock raw slack p q) (PrimeProgramOutputCaller.start raw)
      Prod.fst <$> BitOracleMachine.run code R
        (BitOracleReturnLink.embed prefixLabels (some (prepareP1Label 0))
          (BitOracleStackFrame.embed prefixLayout cfg (fun _ => [])))) := by
      simp only [R,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
      rfl
    _ = (do
      let out ← simulateQ CoinWordLoader.liftCoins (runFairBitUniform slack (PrimeHonestTranscriptCaller.drawSource q))
      Prod.fst <$> BitOracleMachine.run code R
        (BitOracleReturnLink.embed prefixLabels (some (prepareP1Label 0))
          (BitOracleStackFrame.embed prefixLayout (PrimeProgramOutputCaller.sourceResult slack g pk vote s live out) (fun _ => [])))) := by
      rw [hp,simulateQ_map]
      simp only [bind_map_left]
    _ = (do
      let out ← simulateQ CoinWordLoader.liftCoins (runFairBitUniform slack (PrimeHonestTranscriptCaller.drawSource q))
      let cs ← simulateQ CoinWordLoader.liftCoins (runFairBitUniform slack (PrimeFullFieldSource.drawTranscriptScalars q))
      let final ← simulateQ CoinWordLoader.liftCoins (runFairBitUniform slack (PrimeFullFieldSource.drawTranscriptScalars q))
      pure (sourceResult slack g pk vote s live (out,cs,final))) := by
      apply bind_congr_of_forall_mem_support
      intro out ho
      have hn := source_height slack g pk vote s live out ho
      change Prod.fst <$> BitOracleMachine.run code R
        (BitOracleReturnLink.embed prefixLabels (some (prepareP1Label 0))
          (BitOracleStackFrame.embed prefixLayout
            (⟨none,2,(PrimeProgramOutputCaller.sourceResult slack g pk vote s live out).stk⟩ : PrimeProgramOutputCaller.Config)
            (fun _ => []))) = _
      rw [prefix_return_view,prefix_words]
      exact remaining_source slack g pk vote s live out (resident0 raw slack p q) hn
    _ = _ := by
      simp only [drawSource,runFairBitUniform,simulateQ_bind,simulateQ_pure,
        map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]

#print axioms source_height
#print axioms execution_source

private theorem within_support (limit bound : Nat) (oa : OracleComp spec (Config × Nat))
    (h : ∀ out ∈ support oa, out.1.l = none ∧ out.2 ≤ bound) :
    BitOracleLoopBounded.Within limit bound oa := by
  induction oa using OracleComp.inductionOn with
  | pure out => exact h out (by simp)
  | query_bind t next ih =>
    intro answer _
    apply ih answer
    intro out ho
    exact h out (by
      rw [mem_support_bind_iff]
      exact ⟨answer,by simp only [support_liftM]; exact ⟨answer,rfl⟩,ho⟩)

theorem within (slack limit : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) :
    let raw := PrimeRemainingProofRequests.raw slack g pk vote s live
    BitOracleLoopBounded.Within limit (cost raw slack p q)
      (BitOracleMachine.run code (clock raw slack p q) (start raw)) :=
  within_support limit _ _ (run_support slack g pk vote s live)

/-- The same full58 constructor starts with the original raw word at port7.
Physical cost uses this controller's own finite-code factor. -/
theorem physical_run (slack limit : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) :
    let raw := PrimeRemainingProofRequests.raw slack g pk vote s live
    let B := cost raw slack p q
    let T := BitOracleTapeCap.unitCost (raw.length+B)*B*BitOraclePrimitiveLoop.globalFactor code
    ∃ startup ≤ 4*raw.length+8,
      BitOracleInitialInput.observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
        (BitOracleInitialInput.run code 7 (some entry) 0
          (startup+T) (BitOracleInitialInput.initial raw)) =
      (some ∘ sourceResult slack g pk vote s live) <$>
        simulateQ (BitOracleLoopBounded.adapter limit)
          (simulateQ CoinWordLoader.liftCoins (runFairBitUniform slack (drawSource q))) := by
  dsimp only
  let raw := PrimeRemainingProofRequests.raw slack g pk vote s live
  have hw := within slack limit g pk vote s live
  dsimp only at hw
  rw [start_source] at hw
  obtain ⟨startup,hs,he⟩ := BitOracleInitialInput.run_source_bounded code 7 (some entry) 0 raw
    (clock raw slack p q) limit (cost raw slack p q) hw
  rw [←start_source,start_height,Nat.add_zero] at he
  refine ⟨startup,hs,?_⟩
  rw [he]
  have hr := congrArg (fun oa => simulateQ (BitOracleLoopBounded.adapter limit) oa)
    (execution_source slack g pk vote s live)
  simp only [simulateQ_map] at hr
  have lifted := congrArg (fun oa => some <$> oa) hr
  simpa only [Functor.map_map,Function.comp_def] using lifted

#print axioms within
#print axioms physical_run
end ExplainableCrypto.Helios.Computational.PrimeRemainingProofCaller
