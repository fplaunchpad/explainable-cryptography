import ExplainableCrypto.Helios.Symbolic.ExpandedFrameExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedOriginExperiments
open ExplainableCrypto.Testing Historical General

def cipherHandle : Frame (∅ : Finset Nat) 1 :=
  ⟨fun _ => keyCiphertext (.name 40) (.name 50) (.const .one)⟩
def atomicCipherHasSmallerPlaintext (_ : Nat) : Bool :=
  normalizeRaw (cipherHandle.eval (.var 0)) == keyCiphertext (.name 40) (.name 50) (.const .one) &&
    decide ((Term.const .one : Recipe 1).nodeCount < (Term.var 0 : Recipe 1).nodeCount)

def partialIsPair (_ : Nat) : Bool :=
  let t := tallyPartial LocalRootSPOT.names false LocalRootSPOT.left LocalRootSPOT.right [] 0
  normalizeRaw (.unary .fst t) == .name LocalRootSPOT.names.secretKey

def check (seed : Nat) : Bool :=
  [false,true].all (fun swap =>
    let ns := LocalRootSPOT.names
    let φ := expandedFrame ns swap LocalRootSPOT.left LocalRootSPOT.right []
    let j : Fin 2 := ⟨seed%2,by omega⟩
    let indices := List.range (seed%5)
    let initial : Recipe (ExpandedHandles 1) := .binary .mul
      ((Term.var (expandedOld 1)).project j.val) ((Term.var (expandedOld 2)).project j.val)
    let r := indices.foldl (fun acc i => .binary .mul acc
      (.ternary .penc (.var (expandedOld 0)) (.name (40+i))
        (.const (if (seed+i)%2=0 then .zero else .one)))) initial
    let p : Recipe (ExpandedHandles 1) := indices.foldl (fun acc i => .binary .add acc
      (.const (if (seed+i)%2=0 then .zero else .one)))
      (.binary .add (.const (if !swap && j.val=1 then .one else .zero))
        (.const (if swap && j.val=1 then .one else .zero)))
    let expected := j.val + (indices.map (fun i => (seed+i)%2)).sum
    decide (p.nodeCount < r.nodeCount) &&
    (match normalizeRaw (φ.eval r) with
      | .ternary .penc _ _ msg =>
        decide (msg.addSyntaxSummary = AddSummary.number expected) &&
        decide ((normalizeRaw (φ.eval p)).addSyntaxSummary = AddSummary.number expected)
      | _ => false) &&
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial j)
    let constructed := Term.binary .partialDecrypt a (.var (expandedResult j))
    (match normalizeRaw (φ.eval constructed) with | .binary .partialDecrypt _ _ => true | _ => false) &&
    normalizeRaw (φ.eval (.binary .dec a (keyCiphertext a (.name 60) (.name 90)))) == .name 90)

#eval campaign "atomic ciphertext handles admit smaller plaintext certificates (negative control)"
  (∀ n : Nat, atomicCipherHasSmallerPlaintext n = true) 1 true
#eval campaign "published partial has an extractable pair field (negative control)"
  (∀ n : Nat, partialIsPair n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "expanded ciphertext products and constructed/borrowed partial values"
      (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded origin backstop failed")
  IO.println "expanded origin backstop: 2048 inputs, both candidates and swaps, zero through four public factors"

end ExplainableCrypto.Helios.Symbolic.ExpandedOriginExperiments
