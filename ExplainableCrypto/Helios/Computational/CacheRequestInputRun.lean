import ExplainableCrypto.Helios.Computational.CacheRequestInput

/-! Complete execution of the fixed four-field input loader. -/
namespace ExplainableCrypto.Helios.Computational.CacheRequestInput
open Turing.TM2 OracleComp BitOracleMachine
set_option maxRecDepth 8192

private theorem sequence_run (a b c : Config 12 49 3) (f g x y : Nat)
    (hf : run code f a = pure (b,x)) (hg : run code g b = pure (c,y)) :
    run code (f+g) a = pure (c,x+y) := by
  rw [BitOracleReturnLink.run_add,hf,pure_bind,hg,pure_bind]

private theorem link_run {l : Nat} (p : Code 12 l 3) (labels : Fin l → Fin 49) (ret : Fin 49)
    (hp : ∀ label, code (labels label) = BitOracleReturnLink.command labels (some ret) (p label))
    (a b : Config 12 l 3) (c : Config 12 49 3) (f g x y : Nat)
    (hf : run p f a = pure (b,x)) (hb : b.l = none)
    (hg : run code g (BitOracleReturnLink.embed labels (some ret) b) = pure (c,y))
    (hc : c.l = none) :
    run code (f+g) (BitOracleReturnLink.embed labels (some ret) a) = pure (c,x+y) := by
  have hh : ∀ out ∈ support (run p f a), out.1.l = none := by
    rw [hf]; intro out ho
    have he := eq_of_mem_support_pure _ ho
    subst out; exact hb
  have ht : ∀ out ∈ support (run p f a),
      ∀ last ∈ support (run code g (BitOracleReturnLink.embed labels (some ret) out.1)),
        last.1.l = none := by
    rw [hf]; intro out ho
    have he := eq_of_mem_support_pure _ ho
    subst out
    rw [hg]; intro last hl
    have he := eq_of_mem_support_pure _ hl
    subst last; exact hc
  rw [BitOracleReturnLink.run p code labels ret hp f g a hh ht,hf,pure_bind,hg,pure_bind]

private theorem one_run (a b : Config 12 49 3) (x : Nat)
    (hs : BitOracleMachine.step code a = pure (b,x)) : run code 1 a = pure (b,x) := by
  simp [run,hs]

private def words (fs : Fin 4 → List Bool) (stage : Fin 5) : Fin 12 → List Bool :=
  ![ ![[],[],[],[],[],[],bitFramesEncode [fs 0,fs 1,fs 2,fs 3],[],[],[],[],[]],
     ![[],[],[],[],[],[],bitFramesEncode [fs 1,fs 2,fs 3],[],fs 0,[],[],[]],
     ![fs 1,[],[],[],[],[],bitFramesEncode [fs 2,fs 3],[],fs 0,[],[],[]],
     ![fs 1,[],[],[],[],[],bitFramesEncode [fs 3],[],fs 0,[],fs 2,[]],
     ![fs 1,[],[],[],[],[],[],[],fs 0,[],fs 2,fs 3]] stage

private def suffix (fs : Fin 4 → List Bool) (phase : Fin 4) : List Bool :=
  ![bitFramesEncode [fs 1,fs 2,fs 3],bitFramesEncode [fs 2,fs 3],
    bitFramesEncode [fs 3],[]] phase

private def frame (fs : Fin 4 → List Bool) (phase : Fin 4) : Fin 8 → List Bool :=
  fun j => words fs ⟨phase.val,by omega⟩ (layout phase (.inr j))

private theorem field_inclusion (phase : Fin 4) (label : Fin 9) :
    code (fieldLabel phase label) = BitOracleReturnLink.command (fieldLabel phase)
      (some ⟨8+phase.val,by omega⟩) (.compute (fieldCode phase label)) := by
  have hn : ¬ (fieldLabel phase label).val < 13 := by dsimp [fieldLabel]; omega
  rw [code,dif_neg hn]
  have hp : (⟨((fieldLabel phase label).val-13)/9,by omega⟩ : Fin 4) = phase := by
    apply Fin.ext; dsimp [fieldLabel]; omega
  have hl : (⟨((fieldLabel phase label).val-13)%9,by omega⟩ : Fin 9) = label := by
    apply Fin.ext; dsimp [fieldLabel]; omega
  dsimp only
  rw [hp,hl]
  have hv := congrArg Fin.val hp
  dsimp only at hv
  congr 2
  apply Fin.ext
  dsimp only
  omega

private theorem field_entry (fs : Fin 4 → List Bool) (phase : Fin 4) :
    BitOracleReturnLink.embed (fieldLabel phase) (some ⟨8+phase.val,by omega⟩)
      (fieldState phase (FieldPrefixMachine.start
        (uniformNatEncode (fs phase).length ++ (fs phase ++ suffix fs phase))) (frame fs phase)) =
      (⟨some (fieldLabel phase 0),0,words fs ⟨phase.val,by omega⟩⟩ : Config 12 49 3) := by
  fin_cases phase <;>
    (change (⟨_,_,_⟩ : Config 12 49 3) = ⟨_,_,_⟩; congr 1; funext k; fin_cases k <;>
      first | rfl |
        (change (_ ++ (_ ++ _)) = ((_ ++ _) ++ _); rw [List.append_assoc]; rfl))

private theorem field_exit (fs : Fin 4 → List Bool) (phase : Fin 4) :
    BitOracleReturnLink.embed (fieldLabel phase) (some ⟨8+phase.val,by omega⟩)
      (fieldState phase ⟨none,some true,
        (FieldReadMachine.config none (fs phase) [] (suffix fs phase) [] (some true)).stk⟩
        (frame fs phase)) =
      (⟨some ⟨8+phase.val,by omega⟩,2,words fs ⟨phase.val+1,by omega⟩⟩ : Config 12 49 3) := by
  fin_cases phase <;>
    (change (⟨_,_,_⟩ : Config 12 49 3) = ⟨_,_,_⟩; congr 1; funext k; fin_cases k <;> rfl)

/-- Clock for one original length-prefixed field, including its restored output. -/
def fieldClock (word : List Bool) : Nat :=
  3*word.length.size+7+word.length*(2*word.length.size+3)

/-- Whole loader clock includes the literal count header, four field transitions,
and final exhaustion check. -/
def clock (key cache log record : List Bool) : Nat :=
  13+fieldClock key+fieldClock cache+fieldClock log+fieldClock record

/-- The same clock depends only on the four payload lengths. -/
def lengthClock (K C L R : Nat) : Nat :=
  let F := fun n : Nat => 3*n.size+7+n*(2*n.size+3)
  13+F K+F C+F L+F R

theorem clock_lengths (key cache log record : List Bool) :
    clock key cache log record = lengthClock key.length cache.length log.length record.length := rfl

private theorem field_then (fs : Fin 4 → List Bool) (phase : Fin 4)
    (g y : Nat) (done : Config 12 49 3)
    (hg : run code g ⟨some ⟨8+phase.val,by omega⟩,2,words fs ⟨phase.val+1,by omega⟩⟩ = pure (done,y))
    (hd : done.l = none) :
    ∃ f ≤ fieldClock (fs phase), ∃ x ≤ 32*f,
      run code (f+g) ⟨some (fieldLabel phase 0),0,words fs ⟨phase.val,by omega⟩⟩ = pure (done,x+y) := by
  obtain ⟨f,hf,hr⟩ := RecordFieldStepMachine.field_complete (fs phase) (suffix fs phase)
  obtain ⟨x,hx,he⟩ := field_run phase f _ (frame fs phase)
  rw [hr] at he
  rw [← field_exit fs phase] at hg
  have whole := link_run _ (fieldLabel phase) ⟨8+phase.val,by omega⟩
    (field_inclusion phase) _ _ _ _ _ _ _ he rfl hg hd
  rw [field_entry] at whole
  exact ⟨f,hf,x,hx,whole⟩

private theorem gate (fs : Fin 4 → List Bool) (phase : Fin 4) (hp : phase ≠ 0) :
    run code 1 ⟨some ⟨7+phase.val,by omega⟩,2,words fs ⟨phase.val,by omega⟩⟩ =
      pure (⟨some (fieldLabel phase 0),0,words fs ⟨phase.val,by omega⟩⟩,3) := by
  fin_cases phase
  · exact False.elim (hp rfl)
  all_goals exact one_run _ _ _ rfl

private def headerState (fs : Fin 4 → List Bool) (position : Fin 8) : Config 12 49 3 :=
  ⟨some ⟨position.val,by omega⟩,0,
    ![[],[],[],[],[],[],([true,true,true,false,false,false,true].drop position.val ++
      bitFramesEncode [fs 0,fs 1,fs 2,fs 3]),[],[],[],[],[]]⟩

private theorem header_one (fs : Fin 4 → List Bool) (position : Fin 7) :
    run code 1 (headerState fs ⟨position.val,by omega⟩) =
      pure (headerState fs ⟨position.val+1,by omega⟩,4) := by
  apply one_run
  fin_cases position <;>
    (change pure ((⟨_,_,_⟩ : Config 12 49 3),4) = _; congr 2;
      change (⟨_,_,_⟩ : Config 12 49 3) = ⟨_,_,_⟩; congr 1; funext k; fin_cases k <;> rfl)

attribute [local irreducible] BitOracleMachine.run

private theorem header_run (fs : Fin 4 → List Bool) :
    run code 8 (start (input (fs 0) (fs 1) (fs 2) (fs 3))) =
      pure (⟨some (fieldLabel 0 0),0,words fs 0⟩,30) := by
  have h01 := sequence_run _ _ _ _ _ _ _ (header_one fs 0) (header_one fs 1)
  have h02 := sequence_run _ _ _ _ _ _ _ h01 (header_one fs 2)
  have h03 := sequence_run _ _ _ _ _ _ _ h02 (header_one fs 3)
  have h04 := sequence_run _ _ _ _ _ _ _ h03 (header_one fs 4)
  have h05 := sequence_run _ _ _ _ _ _ _ h04 (header_one fs 5)
  have h06 := sequence_run _ _ _ _ _ _ _ h05 (header_one fs 6)
  have hg : run code 1 (headerState fs 7) = pure (⟨some (fieldLabel 0 0),0,words fs 0⟩,2) :=
    one_run _ _ _ rfl
  have hi : start (input (fs 0) (fs 1) (fs 2) (fs 3)) = headerState fs 0 := by
    change start (uniformNatEncode 4 ++ bitFramesEncode [fs 0,fs 1,fs 2,fs 3]) = _
    rw [show uniformNatEncode 4 = [true,true,true,false,false,false,true] from by decide +kernel]
    rfl
  rw [hi]
  have whole := sequence_run _ _ _ _ _ _ _ h06 hg
  simpa only [Nat.reduceAdd,Fin.val_zero,Fin.mk_zero] using whole

attribute [local semireducible] BitOracleMachine.run

private theorem finish (fs : Fin 4 → List Bool) :
    run code 2 ⟨some 11,2,words fs 4⟩ = pure (ready (fs 0) (fs 1) (fs 2) (fs 3),7) := by
  rfl

/-- Execute all four fields from one serialized input. The full final workspace,
remaining-input exhaustion and instruction charge are derived; no loaded-port or
intermediate-state premise is supplied. Payloads are arbitrary opaque bit words. -/
theorem load_request (key cache log record : List Bool) :
    ∃ fuel ≤ clock key cache log record, ∃ charge ≤ 32*fuel,
      run code fuel (start (input key cache log record)) = pure (ready key cache log record,charge) := by
  let fs : Fin 4 → List Bool := ![key,cache,log,record]
  obtain ⟨f3,hf3,x3,hx3,hr3⟩ := field_then fs 3 2 7 _ (finish fs) rfl
  have g3 := sequence_run _ _ _ _ _ _ _ (gate fs 3 (by decide)) hr3
  obtain ⟨f2,hf2,x2,hx2,hr2⟩ := field_then fs 2 _ _ _ g3 rfl
  have g2 := sequence_run _ _ _ _ _ _ _ (gate fs 2 (by decide)) hr2
  obtain ⟨f1,hf1,x1,hx1,hr1⟩ := field_then fs 1 _ _ _ g2 rfl
  have g1 := sequence_run _ _ _ _ _ _ _ (gate fs 1 (by decide)) hr1
  obtain ⟨f0,hf0,x0,hx0,hr0⟩ := field_then fs 0 _ _ _ g1 rfl
  have all := sequence_run _ _ _ _ _ _ _ (header_run fs) hr0
  refine ⟨8+(f0+(1+(f1+(1+(f2+(1+(f3+2))))))),?_,
    30+(x0+(3+(x1+(3+(x2+(3+(x3+7))))))),by omega,all⟩
  change f0 ≤ fieldClock key at hf0
  change f1 ≤ fieldClock cache at hf1
  change f2 ≤ fieldClock log at hf2
  change f3 ≤ fieldClock record at hf3
  unfold clock
  omega

#print axioms load_request

end ExplainableCrypto.Helios.Computational.CacheRequestInput
