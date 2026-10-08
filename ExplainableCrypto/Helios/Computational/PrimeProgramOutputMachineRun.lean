import ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine
import ExplainableCrypto.Helios.Computational.BitPairWriterMachineRun
namespace ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine
def natOldSource : Fin 4 → Fin 48 := ![38,3,42,40]
def scalarOldSource : Fin 4 → Fin 48 := ![11,12,1,7]
/-- The actual pair-writer sources and fresh destinations in source order. -/
def pairLeft : Fin 8 → Fin 50 := ![11,1,28,29,32,46,44,35]
def pairRight : Fin 8 → Fin 50 := ![12,7,30,31,33,47,34,45]
def pairDest : Fin 8 → Fin 50 := ![30,31,32,33,48,34,35,49]
/-- v is in executed Nat-field order B,A,D,C. Scalar words are already canonical prefixes. -/
def proofEncoded (v : Fin 4 → Nat) (old : Fin 48 → List Bool) : List Bool :=
  bitFieldsEncode [
    bitFieldsEncode [bitFieldsEncode [uniformNatEncode (v 1),uniformNatEncode (v 0)],
      bitFieldsEncode [old 11,old 12]],
    bitFieldsEncode [bitFieldsEncode [uniformNatEncode (v 3),uniformNatEncode (v 2)],
      bitFieldsEncode [old 1,old 7]]]
/-- The updated original both-caches codec, including sticky flag and ordered history. -/
def savedEncoded (old : Fin 48 → List Bool) : List Bool :=
  bitFieldsEncode [bitFieldsEncode [old 44,bitFieldsEncode [old 46,old 47]],old 45]
end ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine
open Turing.TM2 BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem nat_code (which : Fin 4) (l : Fin 21) :
    program (natLabel which l) = TM2ReturnLink.redirect (natLabel which) (natReturn which)
      (natProgram which l) := by
  have hv := which.isLt
  have hl := l.isLt
  have h0 : natLabel which l ≠ 0 := by intro he; have he' := congrArg Fin.val he; change 11+21*which.val+l.val = 0 at he'; omega
  have h1 : natLabel which l ≠ 1 := by intro he; have he' := congrArg Fin.val he; change 11+21*which.val+l.val = 1 at he'; omega
  have h2 : natLabel which l ≠ 2 := by intro he; have he' := congrArg Fin.val he; change 11+21*which.val+l.val = 2 at he'; omega
  have hc : ¬ (natLabel which l).val < 11 := by dsimp [natLabel]; omega
  have h : (natLabel which l).val < 95 := by dsimp [natLabel]; omega
  have hd : ((natLabel which l).val-11)/21 = which.val := by dsimp [natLabel]; omega
  have hm : ((natLabel which l).val-11)%21 = l.val := by dsimp [natLabel]; omega
  simp only [program,if_neg h0,if_neg h1,if_neg h2,dif_neg hc,dif_pos h,hd,hm]

theorem local_cost (l : Fin size) : localCost (program l) ≤ 32 := by
  fin_cases l <;> decide +kernel

#print axioms nat_code
#print axioms local_cost

private theorem nat_output (which : Fin 4) : natLayout which (.inl 1) = natDest which := by
  fin_cases which <;> rfl

private theorem nat_local (which : Fin 4) (old : Fin 50 → List Bool)
    (suffix : List Bool) (hw : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = [])
    (j : Fin 7) :
    (Function.update old (natDest which) suffix) (natLayout which (.inl j)) =
      ![old (natSource which),suffix,[],[],[],[],[]] j := by
  have h0:=hw 0; have h1:=hw 1; have h2:=hw 2; have h3:=hw 3; have h4:=hw 4
  fin_cases which <;> fin_cases j <;>
    first | rfl | exact h0 | exact h1 | exact h2 | exact h3 | exact h4

private theorem nat_data (which : Fin 4) (old : Fin 50 → List Bool)
    (suffix : List Bool) (hw : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = []) :
    TM2StackFrame.data (natLayout which) ![old (natSource which),suffix,[],[],[],[],[]]
      (fun j => old (natLayout which (.inr j))) = Function.update old (natDest which) suffix := by
  funext k
  obtain ⟨k,rfl⟩ := (natLayout which).surjective k
  cases k with
  | inl j => simpa only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl] using
      (nat_local which old suffix hw j).symm
  | inr j =>
    have hn : natLayout which (.inr j) ≠ natDest which := by
      rw [←nat_output which]; intro h; have he := (natLayout which).injective h; cases he
    simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inr,
      Function.update_of_ne hn]

theorem prefix_zero (old : Fin 50 → List Bool) :
    tick (⟨some 0,2,old⟩ : Config) =
      ⟨some (natLabel 2 0),2,Function.update old 28 (uniformNatEncode 2 ++ old 28)⟩ := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

theorem prefix_one (old : Fin 50 → List Bool) :
    tick (⟨some 1,2,old⟩ : Config) =
      ⟨some (pairLabel 0 0),2,Function.update old 29 (uniformNatEncode 2 ++ old 29)⟩ := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl
#print axioms prefix_zero
#print axioms prefix_one

theorem nat_run (which : Fin 4) (n : Nat) (old : Fin 50 → List Bool)
    (hw : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = [])
    (hn : old (natSource which)=n.bits) :
    ∃ used ≤ NatFieldWriterMachine.clock n,
      tick^[used] (⟨some (natLabel which 0),2,old⟩ : Config) =
        ⟨some (natReturn which),2,Function.update old (natDest which)
          (NatFieldWriterMachine.encoded n (old (natDest which)))⟩ := by
  let frame : Fin 43 → List Bool := fun j => old (natLayout which (.inr j))
  have he := TM2StackFrame.run (natLayout which) NatFieldWriterMachine.program
    (NatFieldWriterMachine.clock n) (NatFieldWriterMachine.start n.bits (old (natDest which))) frame
  change (TM2ReturnLink.tick (natProgram which))^[_] _ =
    TM2StackFrame.embed (natLayout which) (NatFieldWriterMachine.tick^[_] _) frame at he
  rw [NatFieldWriterMachine.padded_run] at he
  have hh : ((TM2ReturnLink.tick (natProgram which))^[NatFieldWriterMachine.clock n]
      (TM2StackFrame.embed (natLayout which) (NatFieldWriterMachine.start n.bits (old (natDest which))) frame)).l = none := by rw [he]; rfl
  obtain ⟨used,hu,hr⟩ := TM2ReturnLink.run (natProgram which) program
    (natLabel which) (natReturn which) (nat_code which) _ _ hh
  rw [he] at hr
  have hi : TM2ReturnLink.embed (natLabel which) (natReturn which)
      (TM2StackFrame.embed (natLayout which) (NatFieldWriterMachine.start n.bits (old (natDest which))) frame) =
      (⟨some (natLabel which 0),2,old⟩ : Config) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    rw [←hn]
    exact (nat_data which old (old (natDest which)) hw).trans (Function.update_eq_self _ _)
  have ho : TM2ReturnLink.embed (natLabel which) (natReturn which)
      (TM2StackFrame.embed (natLayout which)
        (NatFieldWriterMachine.result n.bits (NatFieldWriterMachine.encoded n (old (natDest which)))) frame) =
      (⟨some (natReturn which),2,Function.update old (natDest which)
        (NatFieldWriterMachine.encoded n (old (natDest which)))⟩ : Config) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    rw [←hn]
    exact nat_data which old _ hw
  rw [hi,ho] at hr
  exact ⟨used,hu,hr⟩
#print axioms nat_run
end ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

theorem pair_code (phase : Fin 8) (l : Fin 23) :
    program (pairLabel phase l) =
      TM2ReturnLink.redirect (pairLabel phase) (pairReturn phase) (pairProgram phase l) := by
  fin_cases phase <;> fin_cases l <;> rfl

theorem pair_layout_left (phase : Fin 8) : pairLayout phase (.inl 0) = pairLeft phase := by
  fin_cases phase <;> rfl
theorem pair_layout_right (phase : Fin 8) : pairLayout phase (.inl 1) = pairRight phase := by
  fin_cases phase <;> rfl
theorem pair_layout_dest (phase : Fin 8) : pairLayout phase (.inl 2) = pairDest phase := by
  fin_cases phase <;> rfl
theorem pair_layout_work (phase : Fin 8) (j : Fin 4) :
    pairLayout phase (.inl ⟨3+j.val,by omega⟩) = ⟨23+j.val,by omega⟩ := by
  fin_cases phase <;> fin_cases j <;> rfl

/-- One actual nested pair call preserves every word except its fresh destination.
The enclosing sequence derives all local workspace and source-length premises. -/
theorem pair_run (phase : Fin 8) (words : Fin 50 → List Bool) (L R : Nat)
    (hd : words (pairDest phase) = [])
    (hw : ∀ j : Fin 4, words ⟨23+j.val,by omega⟩ = [])
    (hL : (words (pairLeft phase)).length ≤ L) (hR : (words (pairRight phase)).length ≤ R) :
    ∃ used ≤ BitPairWriterMachine.clock L R,
      tick^[used] (⟨some (pairLabel phase 0),2,words⟩ : Config) =
      ⟨some (pairReturn phase),2,Function.update words (pairDest phase)
        (bitFieldsEncode [words (pairLeft phase),words (pairRight phase)])⟩ := by
  let src := BitPairWriterMachine.start (words (pairLeft phase)) (words (pairRight phase))
  let dst := BitPairWriterMachine.result (words (pairLeft phase)) (words (pairRight phase))
  let frame : Fin 43 → List Bool := fun k => words (pairLayout phase (.inr k))
  have hr := BitPairWriterMachine.padded_bounded (words (pairLeft phase)) (words (pairRight phase)) L R hL hR
  have hf := TM2StackFrame.run (pairLayout phase) BitPairWriterMachine.program
    (BitPairWriterMachine.clock L R) src frame
  change (TM2ReturnLink.tick (pairProgram phase))^[BitPairWriterMachine.clock L R]
    (TM2StackFrame.embed (pairLayout phase) src frame) =
    TM2StackFrame.embed (pairLayout phase) (BitPairWriterMachine.tick^[BitPairWriterMachine.clock L R] src) frame at hf
  rw [hr] at hf
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run (pairProgram phase) program (pairLabel phase) (pairReturn phase)
    (pair_code phase) (BitPairWriterMachine.clock L R) _ (by rw [hf]; rfl)
  rw [hf] at he
  have h0 := (hw 0).symm
  have h1 := (hw 1).symm
  have h2 := (hw 2).symm
  have h3 := (hw 3).symm
  have hs : TM2ReturnLink.embed (pairLabel phase) (pairReturn phase)
      (TM2StackFrame.embed (pairLayout phase) src frame) =
      (⟨some (pairLabel phase 0),2,words⟩ : Config) := by
    fin_cases phase <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;>
      first | rfl | exact hd.symm | exact h0 | exact h1 | exact h2 | exact h3
  have ht : TM2ReturnLink.embed (pairLabel phase) (pairReturn phase)
      (TM2StackFrame.embed (pairLayout phase) dst frame) =
      (⟨some (pairReturn phase),2,Function.update words (pairDest phase)
        (bitFieldsEncode [words (pairLeft phase),words (pairRight phase)])⟩ : Config) := by
    fin_cases phase <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;>
      first | rfl | exact h0 | exact h1 | exact h2 | exact h3
  exact ⟨u,hu,by erw [hs,ht] at he; exact he⟩

#print axioms pair_code
#print axioms pair_layout_left
#print axioms pair_layout_right
#print axioms pair_layout_dest
#print axioms pair_layout_work
#print axioms pair_run
end ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

def cleaned (old : Fin 50 → List Bool) (k : Fin 50) : List Bool :=
  if 28 ≤ k.val ∧ k.val < 36 then [] else old k

private def clearPort (i : Fin 8) : Fin 50 := ⟨28+i.val,by omega⟩
private def clearLabel (i : Fin 8) : Fin size := ⟨3+i.val,by dsimp [size]; omega⟩
private def clearNext (i : Fin 8) : Option (Fin size) :=
  if h : i.val < 7 then some ⟨4+i.val,by dsimp [size]; omega⟩ else none
private def clearMemory (i : Fin 8) : Fin 3 := if i.val < 7 then 0 else 2

private theorem clear_one (i : Fin 8) (old : Fin 50 → List Bool)
    (word : List Bool) (v : Fin 3) :
    tick^[word.length+1] ⟨some (clearLabel i),v,Function.update old (clearPort i) word⟩ =
      ⟨clearNext i,clearMemory i,Function.update old (clearPort i) []⟩ := by
  induction word generalizing v with
  | nil =>
    fin_cases i <;>
      simp [size,Fin.ext_iff,clearLabel,clearPort,clearNext,clearMemory,tick,TM2ReturnLink.tick,
        program,stepAux,Function.update,BinaryModuloCode.memory]
  | cons b word ih =>
    have hs : tick (⟨some (clearLabel i),v,Function.update old (clearPort i) (b::word)⟩ : Config) =
        ⟨some (clearLabel i),BinaryModuloCode.memory (some b),Function.update old (clearPort i) word⟩ := by
      fin_cases i <;> cases b <;>
        simp [size,Fin.ext_iff,clearLabel,clearPort,tick,TM2ReturnLink.tick,program,stepAux,
          Function.update,BinaryModuloCode.memory]
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,hs,ih]

private theorem clear_old (i : Fin 8) (old : Fin 50 → List Bool) (v : Fin 3) :
    tick^[(old (clearPort i)).length+1] ⟨some (clearLabel i),v,old⟩ =
      ⟨clearNext i,clearMemory i,Function.update old (clearPort i) []⟩ := by
  simpa only [Function.update_eq_self] using clear_one i old (old (clearPort i)) v

private theorem cleanup_chain {a b : Nat} {x y z : Config}
    (ha : tick^[a] x = y) (hb : tick^[b] y = z) : tick^[a+b] x = z := by
  rw [Nat.add_comm a b,Function.iterate_add_apply,ha,hb]

/-- Actual guard and eight destructive clears; all other words remain unchanged. -/
theorem cleanup_run (old : Fin 50 → List Bool) :
    ∃ u ≤ (∑ i : Fin 8, (old ⟨28+i.val,by omega⟩).length)+9,
      tick^[u] (⟨some 2,2,old⟩ : Config) = ⟨none,2,cleaned old⟩ := by
  let w0 := old
  let w1 := Function.update w0 28 []
  let w2 := Function.update w1 29 []
  let w3 := Function.update w2 30 []
  let w4 := Function.update w3 31 []
  let w5 := Function.update w4 32 []
  let w6 := Function.update w5 33 []
  let w7 := Function.update w6 34 []
  let w8 := Function.update w7 35 []
  have start_step : tick^[1] (⟨some 2,2,old⟩ : Config) = ⟨some 3,0,w0⟩ := rfl
  have h0 : tick^[(old 28).length+1] (⟨some 3,0,w0⟩ : Config) =
      ⟨some 4,0,w1⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,w0,w1,Function.update] using clear_old 0 w0 0
  have h1 : tick^[(old 29).length+1] (⟨some 4,0,w1⟩ : Config) =
      ⟨some 5,0,w2⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,w0,w1,w2,Function.update] using clear_old 1 w1 0
  have h2 : tick^[(old 30).length+1] (⟨some 5,0,w2⟩ : Config) =
      ⟨some 6,0,w3⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,w0,w1,w2,w3,Function.update] using clear_old 2 w2 0
  have h3 : tick^[(old 31).length+1] (⟨some 6,0,w3⟩ : Config) =
      ⟨some 7,0,w4⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,w0,w1,w2,w3,w4,Function.update] using clear_old 3 w3 0
  have h4 : tick^[(old 32).length+1] (⟨some 7,0,w4⟩ : Config) =
      ⟨some 8,0,w5⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,w0,w1,w2,w3,w4,w5,Function.update] using clear_old 4 w4 0
  have h5 : tick^[(old 33).length+1] (⟨some 8,0,w5⟩ : Config) =
      ⟨some 9,0,w6⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,w0,w1,w2,w3,w4,w5,w6,Function.update] using clear_old 5 w5 0
  have h6 : tick^[(old 34).length+1] (⟨some 9,0,w6⟩ : Config) =
      ⟨some 10,0,w7⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,w0,w1,w2,w3,w4,w5,w6,w7,Function.update] using clear_old 6 w6 0
  have h7 : tick^[(old 35).length+1] (⟨some 10,0,w7⟩ : Config) =
      ⟨none,2,w8⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,w0,w1,w2,w3,w4,w5,w6,w7,w8,Function.update] using clear_old 7 w7 0
  have h := cleanup_chain start_step h0
  have h := cleanup_chain h h1
  have h := cleanup_chain h h2
  have h := cleanup_chain h h3
  have h := cleanup_chain h h4
  have h := cleanup_chain h h5
  have h := cleanup_chain h h6
  have h := cleanup_chain h h7
  have he : w8 = cleaned old := by
    funext k
    fin_cases k <;> simp [w8,w7,w6,w5,w4,w3,w2,w1,w0,cleaned,Function.update]
  rw [he] at h
  refine ⟨_,?_,h⟩
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Nat.add_zero]
  change 1+((old 28).length+1)+((old 29).length+1)+((old 30).length+1)+
    ((old 31).length+1)+((old 32).length+1)+((old 33).length+1)+
    ((old 34).length+1)+((old 35).length+1) ≤
    ((old 28).length+((old 29).length+((old 30).length+((old 31).length+
    ((old 32).length+((old 33).length+((old 34).length+(old 35).length)))))))+9
  omega

#print axioms cleanup_run
end ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine
private theorem pair_length_bound (a b : List Bool) (L R : Nat)
    (ha : a.length ≤ L) (hb : b.length ≤ R) :
    (bitFieldsEncode [a,b]).length ≤ bitPairSize L R := by
  rw [bitFieldsEncode_length]
  have hsa := Nat.size_le_size ha
  have hsb := Nat.size_le_size hb
  simp only [List.length_cons,List.length_nil,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,Nat.add_zero,show (2 : Nat).size = 2 from rfl]
  unfold bitPairSize
  omega
private theorem numeric_word_length (p n : Nat) (hn : n < p) :
    (uniformNatEncode n).length ≤ groupRecordBitBound p := by
  have hs := Nat.size_le_size (show n ≤ p-1 by omega)
  rw [uniformNatEncode_length]
  unfold groupRecordBitBound
  omega
end ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine
open Turing.TM2 BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] BitOracleMachine.run

theorem run (p q N : Nat) (v : Fin 4 → Nat) (old : Fin 48 → List Bool)
    (hw : ∀ j : Fin 15, old ⟨23+j.val,by omega⟩ = [])
    (hv : ∀ i, v i < p) (hn : ∀ i, old (natOldSource i) = (v i).bits)
    (hs : ∀ i, (old (scalarOldSource i)).length ≤ groupRecordBitBound q)
    (hshadow : (old 44).length ≤ shadowBound p q N)
    (hhistory : (old 47).length ≤ historyBound p N)
    (hlive : (old 45).length ≤ N) (hflag : (old 46).length ≤ 1) :
    ∃ used ≤ clock p q N,
      tick^[used] (start old) = result (proofEncoded v old) (savedEncoded old) old := by
  let g0 := bitFieldsEncode [uniformNatEncode (v 1),uniformNatEncode (v 0)]
  let g1 := bitFieldsEncode [uniformNatEncode (v 3),uniformNatEncode (v 2)]
  let s0 := bitFieldsEncode [old 11,old 12]
  let s1 := bitFieldsEncode [old 1,old 7]
  let b0 := bitFieldsEncode [g0,s0]
  let b1 := bitFieldsEncode [g1,s1]
  let proof := bitFieldsEncode [b0,b1]
  let fh := bitFieldsEncode [old 46,old 47]
  let ps := bitFieldsEncode [old 44,fh]
  let saved := bitFieldsEncode [ps,old 45]
  let nb := NatFieldWriterMachine.encoded (v 0) []
  let na := NatFieldWriterMachine.encoded (v 1) nb
  let nd := NatFieldWriterMachine.encoded (v 2) []
  let nc := NatFieldWriterMachine.encoded (v 3) nd
  let W0 := initialWords old
  let W1 := Function.update W0 28 nb
  let W2 := Function.update W1 28 na
  let W3 := Function.update W2 28 g0
  let W4 := Function.update W3 29 nd
  let W5 := Function.update W4 29 nc
  let W6 := Function.update W5 29 g1
  let W7 := Function.update W6 30 s0
  let W8 := Function.update W7 31 s1
  let W9 := Function.update W8 32 b0
  let W10 := Function.update W9 33 b1
  let W11 := Function.update W10 48 proof
  let W12 := Function.update W11 34 fh
  let W13 := Function.update W12 35 ps
  let W14 := Function.update W13 49 saved
  have h28 : old 28 = [] := hw 5
  have h29 : old 29 = [] := hw 6
  have h30 : old 30 = [] := hw 7
  have h31 : old 31 = [] := hw 8
  have h32 : old 32 = [] := hw 9
  have h33 : old 33 = [] := hw 10
  have h34 : old 34 = [] := hw 11
  have h35 : old 35 = [] := hw 12

  have hgroup0 : uniformNatEncode 2 ++ na = g0 := by
    simp [na,nb,g0,NatFieldWriterMachine.encoded,bitFieldsEncode,bitFramesEncode,List.append_assoc]
  have hgroup1 : uniformNatEncode 2 ++ nc = g1 := by
    simp [nc,nd,g1,NatFieldWriterMachine.encoded,bitFieldsEncode,bitFramesEncode,List.append_assoc]
  have hw0 (j : Fin 5) : W0 ⟨23+j.val,by omega⟩ = [] := by
    have h := hw ⟨j.val,by omega⟩
    fin_cases j <;> simpa [W0,initialWords,Function.update_apply] using h
  have hn0 : W0 (natSource 0) = (v 0).bits := by
    simpa [W0,initialWords,natSource,natOldSource,Function.update_apply] using hn 0
  obtain ⟨a0,ha0,ea0⟩ := nat_run 0 (v 0) W0 hw0 hn0
  have hd0 : W0 (natDest 0) = [] := by
    simp [W0,initialWords,natDest,h28]
  rw [hd0] at ea0
  change tick^[a0] (⟨some (natLabel 0 0),2,W0⟩ : Config) =
    ⟨some (natLabel 1 0),2,W1⟩ at ea0
  have hw1 (j : Fin 5) : W1 ⟨23+j.val,by omega⟩ = [] := by
    have h := hw ⟨j.val,by omega⟩
    fin_cases j <;> simpa [W0,W1,initialWords,Function.update_apply] using h
  have hn1 : W1 (natSource 1) = (v 1).bits := by
    simpa [W0,W1,initialWords,natSource,natOldSource,Function.update_apply] using hn 1
  obtain ⟨a1,ha1,ea1⟩ := nat_run 1 (v 1) W1 hw1 hn1
  have hd1 : W1 (natDest 1) = nb := by
    simp [W0,W1,natDest]
  rw [hd1] at ea1
  change tick^[a1] (⟨some (natLabel 1 0),2,W1⟩ : Config) =
    ⟨some (0),2,W2⟩ at ea1
  have hw3 (j : Fin 5) : W3 ⟨23+j.val,by omega⟩ = [] := by
    have h := hw ⟨j.val,by omega⟩
    fin_cases j <;> simpa [W0,W1,W2,W3,initialWords,Function.update_apply] using h
  have hn3 : W3 (natSource 2) = (v 2).bits := by
    simpa [W0,W1,W2,W3,initialWords,natSource,natOldSource,Function.update_apply] using hn 2
  obtain ⟨a2,ha2,ea2⟩ := nat_run 2 (v 2) W3 hw3 hn3
  have hd2 : W3 (natDest 2) = [] := by
    simp [W0,W1,W2,W3,initialWords,natDest,h29]
  rw [hd2] at ea2
  change tick^[a2] (⟨some (natLabel 2 0),2,W3⟩ : Config) =
    ⟨some (natLabel 3 0),2,W4⟩ at ea2
  have hw4 (j : Fin 5) : W4 ⟨23+j.val,by omega⟩ = [] := by
    have h := hw ⟨j.val,by omega⟩
    fin_cases j <;> simpa [W0,W1,W2,W3,W4,initialWords,Function.update_apply] using h
  have hn4 : W4 (natSource 3) = (v 3).bits := by
    simpa [W0,W1,W2,W3,W4,initialWords,natSource,natOldSource,Function.update_apply] using hn 3
  obtain ⟨a3,ha3,ea3⟩ := nat_run 3 (v 3) W4 hw4 hn4
  have hd3 : W4 (natDest 3) = nd := by
    simp [W0,W1,W2,W3,W4,natDest]
  rw [hd3] at ea3
  change tick^[a3] (⟨some (natLabel 3 0),2,W4⟩ : Config) =
    ⟨some (1),2,W5⟩ at ea3
  have ep0 : tick (⟨some 0,2,W2⟩ : Config) = ⟨some (natLabel 2 0),2,W3⟩ := by
    rw [prefix_zero]
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    have hx : W2 28 = na := by simp [W2]
    rw [hx,hgroup0]
  have ep1 : tick (⟨some 1,2,W5⟩ : Config) = ⟨some (pairLabel 0 0),2,W6⟩ := by
    rw [prefix_one]
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    have hx : W5 29 = nc := by simp [W5]
    rw [hx,hgroup1]
  have hg0 : g0.length ≤ groupPairBound p :=
    pair_length_bound _ _ _ _ (numeric_word_length p _ (hv 1)) (numeric_word_length p _ (hv 0))
  have hg1 : g1.length ≤ groupPairBound p :=
    pair_length_bound _ _ _ _ (numeric_word_length p _ (hv 3)) (numeric_word_length p _ (hv 2))
  have hs0 : s0.length ≤ scalarPairBound q := pair_length_bound _ _ _ _ (hs 0) (hs 1)
  have hs1 : s1.length ≤ scalarPairBound q := pair_length_bound _ _ _ _ (hs 2) (hs 3)
  have hb0 : b0.length ≤ branchBound p q := pair_length_bound _ _ _ _ hg0 hs0
  have hb1 : b1.length ≤ branchBound p q := pair_length_bound _ _ _ _ hg1 hs1
  have hfh : fh.length ≤ flagHistoryBound p N := pair_length_bound _ _ _ _ hflag hhistory
  have hps : ps.length ≤ programmedBound p q N := pair_length_bound _ _ _ _ hshadow hfh
  have hdP0 : W6 (pairDest 0) = [] := by
    simpa [W0,W1,W2,W3,W4,W5,W6,initialWords,pairDest,Function.update_apply] using hw 7
  have hwP0 (j : Fin 4) : W6 ⟨23+j.val,by omega⟩ = [] := by
    have h := hw ⟨j.val,by omega⟩
    fin_cases j <;> simpa [W0,W1,W2,W3,W4,W5,W6,initialWords,Function.update_apply] using h
  have hlP0 : (W6 (pairLeft 0)).length ≤ pairLeftBounds p q N 0 := by
    simpa [W0,W1,W2,W3,W4,W5,W6,initialWords,pairLeft,pairLeftBounds,scalarOldSource,Function.update_apply] using hs 0
  have hrP0 : (W6 (pairRight 0)).length ≤ pairRightBounds p q N 0 := by
    simpa [W0,W1,W2,W3,W4,W5,W6,initialWords,pairRight,pairRightBounds,scalarOldSource,Function.update_apply] using hs 1
  obtain ⟨t0,ht0,et0⟩ := pair_run 0 W6 (pairLeftBounds p q N 0) (pairRightBounds p q N 0) hdP0 hwP0 hlP0 hrP0
  change tick^[t0] (⟨some (pairLabel 0 0),2,W6⟩ : Config) =
    ⟨some (pairLabel 1 0),2,W7⟩ at et0
  have hdP1 : W7 (pairDest 1) = [] := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,initialWords,pairDest,Function.update_apply] using hw 8
  have hwP1 (j : Fin 4) : W7 ⟨23+j.val,by omega⟩ = [] := by
    have h := hw ⟨j.val,by omega⟩
    fin_cases j <;> simpa [W0,W1,W2,W3,W4,W5,W6,W7,initialWords,Function.update_apply] using h
  have hlP1 : (W7 (pairLeft 1)).length ≤ pairLeftBounds p q N 1 := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,initialWords,pairLeft,pairLeftBounds,scalarOldSource,Function.update_apply] using hs 2
  have hrP1 : (W7 (pairRight 1)).length ≤ pairRightBounds p q N 1 := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,initialWords,pairRight,pairRightBounds,scalarOldSource,Function.update_apply] using hs 3
  obtain ⟨t1,ht1,et1⟩ := pair_run 1 W7 (pairLeftBounds p q N 1) (pairRightBounds p q N 1) hdP1 hwP1 hlP1 hrP1
  change tick^[t1] (⟨some (pairLabel 1 0),2,W7⟩ : Config) =
    ⟨some (pairLabel 2 0),2,W8⟩ at et1
  have hdP2 : W8 (pairDest 2) = [] := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,initialWords,pairDest,Function.update_apply] using hw 9
  have hwP2 (j : Fin 4) : W8 ⟨23+j.val,by omega⟩ = [] := by
    have h := hw ⟨j.val,by omega⟩
    fin_cases j <;> simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,initialWords,Function.update_apply] using h
  have hlP2 : (W8 (pairLeft 2)).length ≤ pairLeftBounds p q N 2 := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,initialWords,pairLeft,pairLeftBounds,scalarOldSource,Function.update_apply] using hg0
  have hrP2 : (W8 (pairRight 2)).length ≤ pairRightBounds p q N 2 := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,initialWords,pairRight,pairRightBounds,scalarOldSource,Function.update_apply] using hs0
  obtain ⟨t2,ht2,et2⟩ := pair_run 2 W8 (pairLeftBounds p q N 2) (pairRightBounds p q N 2) hdP2 hwP2 hlP2 hrP2
  change tick^[t2] (⟨some (pairLabel 2 0),2,W8⟩ : Config) =
    ⟨some (pairLabel 3 0),2,W9⟩ at et2
  have hdP3 : W9 (pairDest 3) = [] := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,initialWords,pairDest,Function.update_apply] using hw 10
  have hwP3 (j : Fin 4) : W9 ⟨23+j.val,by omega⟩ = [] := by
    have h := hw ⟨j.val,by omega⟩
    fin_cases j <;> simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,initialWords,Function.update_apply] using h
  have hlP3 : (W9 (pairLeft 3)).length ≤ pairLeftBounds p q N 3 := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,initialWords,pairLeft,pairLeftBounds,scalarOldSource,Function.update_apply] using hg1
  have hrP3 : (W9 (pairRight 3)).length ≤ pairRightBounds p q N 3 := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,initialWords,pairRight,pairRightBounds,scalarOldSource,Function.update_apply] using hs1
  obtain ⟨t3,ht3,et3⟩ := pair_run 3 W9 (pairLeftBounds p q N 3) (pairRightBounds p q N 3) hdP3 hwP3 hlP3 hrP3
  change tick^[t3] (⟨some (pairLabel 3 0),2,W9⟩ : Config) =
    ⟨some (pairLabel 4 0),2,W10⟩ at et3
  have hdP4 : W10 (pairDest 4) = [] := by
    simp [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,initialWords,pairDest]
  have hwP4 (j : Fin 4) : W10 ⟨23+j.val,by omega⟩ = [] := by
    have h := hw ⟨j.val,by omega⟩
    fin_cases j <;> simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,initialWords,Function.update_apply] using h
  have hlP4 : (W10 (pairLeft 4)).length ≤ pairLeftBounds p q N 4 := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,initialWords,pairLeft,pairLeftBounds,scalarOldSource,Function.update_apply] using hb0
  have hrP4 : (W10 (pairRight 4)).length ≤ pairRightBounds p q N 4 := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,initialWords,pairRight,pairRightBounds,scalarOldSource,Function.update_apply] using hb1
  obtain ⟨t4,ht4,et4⟩ := pair_run 4 W10 (pairLeftBounds p q N 4) (pairRightBounds p q N 4) hdP4 hwP4 hlP4 hrP4
  change tick^[t4] (⟨some (pairLabel 4 0),2,W10⟩ : Config) =
    ⟨some (pairLabel 5 0),2,W11⟩ at et4
  have hdP5 : W11 (pairDest 5) = [] := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,initialWords,pairDest,Function.update_apply] using hw 11
  have hwP5 (j : Fin 4) : W11 ⟨23+j.val,by omega⟩ = [] := by
    have h := hw ⟨j.val,by omega⟩
    fin_cases j <;> simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,initialWords,Function.update_apply] using h
  have hlP5 : (W11 (pairLeft 5)).length ≤ pairLeftBounds p q N 5 := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,initialWords,pairLeft,pairLeftBounds,scalarOldSource,Function.update_apply] using hflag
  have hrP5 : (W11 (pairRight 5)).length ≤ pairRightBounds p q N 5 := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,initialWords,pairRight,pairRightBounds,scalarOldSource,Function.update_apply] using hhistory
  obtain ⟨t5,ht5,et5⟩ := pair_run 5 W11 (pairLeftBounds p q N 5) (pairRightBounds p q N 5) hdP5 hwP5 hlP5 hrP5
  change tick^[t5] (⟨some (pairLabel 5 0),2,W11⟩ : Config) =
    ⟨some (pairLabel 6 0),2,W12⟩ at et5
  have hdP6 : W12 (pairDest 6) = [] := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,W12,initialWords,pairDest,Function.update_apply] using hw 12
  have hwP6 (j : Fin 4) : W12 ⟨23+j.val,by omega⟩ = [] := by
    have h := hw ⟨j.val,by omega⟩
    fin_cases j <;> simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,W12,initialWords,Function.update_apply] using h
  have hlP6 : (W12 (pairLeft 6)).length ≤ pairLeftBounds p q N 6 := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,W12,initialWords,pairLeft,pairLeftBounds,scalarOldSource,Function.update_apply] using hshadow
  have hrP6 : (W12 (pairRight 6)).length ≤ pairRightBounds p q N 6 := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,W12,initialWords,pairRight,pairRightBounds,scalarOldSource,Function.update_apply] using hfh
  obtain ⟨t6,ht6,et6⟩ := pair_run 6 W12 (pairLeftBounds p q N 6) (pairRightBounds p q N 6) hdP6 hwP6 hlP6 hrP6
  change tick^[t6] (⟨some (pairLabel 6 0),2,W12⟩ : Config) =
    ⟨some (pairLabel 7 0),2,W13⟩ at et6
  have hdP7 : W13 (pairDest 7) = [] := by
    simp [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,W12,W13,initialWords,pairDest]
  have hwP7 (j : Fin 4) : W13 ⟨23+j.val,by omega⟩ = [] := by
    have h := hw ⟨j.val,by omega⟩
    fin_cases j <;> simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,W12,W13,initialWords,Function.update_apply] using h
  have hlP7 : (W13 (pairLeft 7)).length ≤ pairLeftBounds p q N 7 := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,W12,W13,initialWords,pairLeft,pairLeftBounds,scalarOldSource,Function.update_apply] using hps
  have hrP7 : (W13 (pairRight 7)).length ≤ pairRightBounds p q N 7 := by
    simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,W12,W13,initialWords,pairRight,pairRightBounds,scalarOldSource,Function.update_apply] using hlive
  obtain ⟨t7,ht7,et7⟩ := pair_run 7 W13 (pairLeftBounds p q N 7) (pairRightBounds p q N 7) hdP7 hwP7 hlP7 hrP7
  change tick^[t7] (⟨some (pairLabel 7 0),2,W13⟩ : Config) =
    ⟨some (2),2,W14⟩ at et7
  obtain ⟨u,hu,eu⟩ := cleanup_run W14
  let used := u+(t7+(t6+(t5+(t4+(t3+(t2+(t1+(t0+(1+(a3+(a2+(1+(a1+(a0))))))))))))))
  have execution : tick^[used] (start old) = (⟨none,2,cleaned W14⟩ : Config) := by
    dsimp only [used]
    change tick^[_] (⟨some (natLabel 0 0),2,W0⟩ : Config) = _
    rw [Function.iterate_add_apply tick u,
      Function.iterate_add_apply tick t7,
      Function.iterate_add_apply tick t6,
      Function.iterate_add_apply tick t5,
      Function.iterate_add_apply tick t4,
      Function.iterate_add_apply tick t3,
      Function.iterate_add_apply tick t2,
      Function.iterate_add_apply tick t1,
      Function.iterate_add_apply tick t0,
      Function.iterate_add_apply tick 1,
      Function.iterate_add_apply tick a3,
      Function.iterate_add_apply tick a2,
      Function.iterate_add_apply tick 1,
      Function.iterate_add_apply tick a1,
      ea0,ea1,Function.iterate_one,ep0,ea2,ea3,ep1,et0,et1,et2,et3,et4,et5,et6,et7,eu]
  have hout : (⟨none,2,cleaned W14⟩ : Config) = result (proofEncoded v old) (savedEncoded old) old := by
    have hstk : cleaned W14 = Function.update (Function.update (initialWords old) 48 (proofEncoded v old)) 49 (savedEncoded old) := by
      funext k
      fin_cases k
      all_goals first | rfl | simp [W14,cleaned,initialWords,h28,h29,h30,h31,h32,h33,h34,h35]
    exact congrArg (fun w => (⟨none,2,w⟩ : Config)) hstk
  have hbNat (i : Fin 4) : NatFieldWriterMachine.clock (v i) ≤ NatFieldWriterMachine.clock (p-1) :=
    NatFieldWriterMachine.clock_mono (by have := hv i; omega)
  have ba0 := ha0.trans (hbNat 0)
  have ba1 := ha1.trans (hbNat 1)
  have ba2 := ha2.trans (hbNat 2)
  have ba3 := ha3.trans (hbNat 3)
  have htemps : (∑ i : Fin 8, (W14 ⟨28+i.val,by omega⟩).length) ≤ ∑ i : Fin 8, tempBounds p q N i := by
    apply Finset.sum_le_sum
    intro i hi
    fin_cases i
    · simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,W12,W13,W14,tempBounds,Function.update_apply] using hg0
    · simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,W12,W13,W14,tempBounds,Function.update_apply] using hg1
    · simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,W12,W13,W14,tempBounds,Function.update_apply] using hs0
    · simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,W12,W13,W14,tempBounds,Function.update_apply] using hs1
    · simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,W12,W13,W14,tempBounds,Function.update_apply] using hb0
    · simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,W12,W13,W14,tempBounds,Function.update_apply] using hb1
    · simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,W12,W13,W14,tempBounds,Function.update_apply] using hfh
    · simpa [W0,W1,W2,W3,W4,W5,W6,W7,W8,W9,W10,W11,W12,W13,W14,tempBounds,Function.update_apply] using hps
  refine ⟨used,?_,execution.trans hout⟩
  dsimp only [used]
  unfold clock
  have bu := hu.trans (Nat.add_le_add_right htemps 9)
  clear * - ba0 ba1 ba2 ba3 ht0 ht1 ht2 ht3 ht4 ht5 ht6 ht7 bu
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Nat.add_zero] at *
  simp [pairLeftBounds,pairRightBounds,tempBounds] at *
  simp only [←Nat.add_assoc]
  omega
#print axioms run

theorem padded_run (p q N : Nat) (v : Fin 4 → Nat) (old : Fin 48 → List Bool)
    (hw : ∀ j : Fin 15, old ⟨23+j.val,by omega⟩ = [])
    (hv : ∀ i, v i < p) (hn : ∀ i, old (natOldSource i) = (v i).bits)
    (hs : ∀ i, (old (scalarOldSource i)).length ≤ groupRecordBitBound q)
    (hshadow : (old 44).length ≤ shadowBound p q N)
    (hhistory : (old 47).length ≤ historyBound p N)
    (hlive : (old 45).length ≤ N) (hflag : (old 46).length ≤ 1) :
    tick^[clock p q N] (start old) = result (proofEncoded v old) (savedEncoded old) old := by
  obtain ⟨u,hu,he⟩ := run p q N v old hw hv hn hs hshadow hhistory hlive hflag
  rw [show clock p q N = (clock p q N-u)+u by omega,Function.iterate_add_apply,he]
  exact Function.iterate_fixed (show tick (result _ _ old) = _ from rfl) _

theorem charged (p q N : Nat) (v : Fin 4 → Nat) (old : Fin 48 → List Bool)
    (hw : ∀ j : Fin 15, old ⟨23+j.val,by omega⟩ = [])
    (hv : ∀ i, v i < p) (hn : ∀ i, old (natOldSource i) = (v i).bits)
    (hs : ∀ i, (old (scalarOldSource i)).length ≤ groupRecordBitBound q)
    (hshadow : (old 44).length ≤ shadowBound p q N)
    (hhistory : (old 47).length ≤ historyBound p N)
    (hlive : (old 45).length ≤ N) (hflag : (old 46).length ≤ 1) :
    ∃ charge ≤ cost p q N,
      BitOracleMachine.run code (clock p q N) (start old) =
        pure (result (proofEncoded v old) (savedEncoded old) old,charge) := by
  obtain ⟨charge,hc,he⟩ := BitOracleMachine.compute_run_cost program 32 local_cost (clock p q N) (start old)
  rw [show (TM2ReturnLink.tick program)^[clock p q N] (start old) =
    result (proofEncoded v old) (savedEncoded old) old
    from padded_run p q N v old hw hv hn hs hshadow hhistory hlive hflag] at he
  exact ⟨charge,hc,he⟩
#print axioms padded_run
#print axioms charged
end ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine
