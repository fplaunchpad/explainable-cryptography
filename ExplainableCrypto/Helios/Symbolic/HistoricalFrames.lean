import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Image
import ExplainableCrypto.Helios.Symbolic.Ballot
import ExplainableCrypto.Helios.Symbolic.ComposedNonce

namespace ExplainableCrypto.Helios.Symbolic.Historical

/-- n denotes n+1 candidates. Freshness is recorded separately from the data. -/
structure Names (n : Nat) where
  secretKey : Nat
  auxiliary : Nat
  nonce : Fin 2 → Fin (n + 1) → Nat

def Names.Fresh {n : Nat} (ns : Names n) : Prop :=
  ns.secretKey ≠ ns.auxiliary ∧
  Function.Injective (fun ij : Fin 2 × Fin (n + 1) => ns.nonce ij.1 ij.2) ∧
  ∀ i j, ns.nonce i j ≠ ns.secretKey ∧ ns.nonce i j ≠ ns.auxiliary

def Names.nonceNames {n : Nat} (ns : Names n) : Finset Nat :=
  Finset.univ.image (fun ij : Fin 2 × Fin (n + 1) => ns.nonce ij.1 ij.2)

def Names.restricted {n : Nat} (ns : Names n) : Finset Nat :=
  {ns.secretKey, ns.auxiliary} ∪ ns.nonceNames

/-- Nonempty left-associated fold; no term-level identity is introduced. -/
def foldCandidates {V : Type} {n : Nat} (f : Binary) (xs : Fin (n + 1) → Term V) : Term V :=
  (List.finRange n).foldl (fun acc i => .binary f acc (xs i.succ)) (xs 0)

def vote {n : Nat} (chosen j : Fin (n + 1)) : Ground :=
  .const (if j = chosen then .one else .zero)

def publicKey {n : Nat} (ns : Names n) : Ground := .unary .pk (.name ns.secretKey)

def ciphertext {n : Nat} (ns : Names n) (i : Fin 2) (chosen j : Fin (n + 1)) : Ground :=
  .ternary .penc (publicKey ns) (.name (ns.nonce i j)) (vote chosen j)

def componentProof {n : Nat} (ns : Names n) (i : Fin 2) (chosen j : Fin (n + 1)) : Ground :=
  .spk (publicKey ns) (.name (ns.nonce i j)) (vote chosen j) (ciphertext ns i chosen j)

def aggregateProof {n : Nat} (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1)) : Ground :=
  .spk (publicKey ns) (foldCandidates .compose (fun j => .name (ns.nonce i j)))
    (foldCandidates .add (vote chosen)) (foldCandidates .mul (ciphertext ns i chosen))

def ballotFields {n : Nat} (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1)) : List Ground :=
  (List.finRange (n + 1)).map (ciphertext ns i chosen) ++
    (List.finRange (n + 1)).map (componentProof ns i chosen) ++ [aggregateProof ns i chosen]

def ballot {n : Nat} (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1)) : Ground :=
  Term.tuple (ballotFields ns i chosen)

def choice {n : Nat} (swap : Bool) (left right : Fin (n + 1)) (i : Fin 2) : Fin (n + 1) :=
  if i.val = 0 then (if swap then right else left) else (if swap then left else right)

/-- Handles 0,1,2 expose zpk, y1,y2 respectively. Both worlds keep the same names. -/
def frame {n : Nat} (ns : Names n) (swap : Bool) (left right : Fin (n + 1)) : Frame ns.restricted 3 :=
  ⟨fun h => if h.val = 0 then publicKey ns
    else if h.val = 1 then ballot ns 0 (choice swap left right 0)
    else ballot ns 1 (choice swap left right 1)⟩

end ExplainableCrypto.Helios.Symbolic.Historical
