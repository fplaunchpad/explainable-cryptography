import ExplainableCrypto.Helios.Symbolic.SourceBallotSecrecy
import Lean.Util.FoldConsts

/-! Measurement only: traverse the actual checked constant types and proof/def
values, recording their defining modules. Generated recursors/constructors are
included by Lean's getUsedConstantsAsSet. This is not a security theorem. -/
open Lean Elab Command
set_option maxHeartbeats 0

run_cmd do
  let env ← getEnv
  let root := ``ExplainableCrypto.Helios.Symbolic.Historical.General.Source.scopedVoterElection_ballot_secrecy
  let mut pending := #[root]
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some ci := env.find? name | throwError "Missing constant {name}"
    let deps := ci.getUsedConstantsAsSet.toList
    pending := pending ++ deps.toArray
    let modName := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!.toString
      | none => "<current>"
    rows := rows.push <| Json.mkObj [
      ("name",toJson name.toString), ("module",toJson modName),
      ("dependencies",toJson (deps.map Name.toString)),
      ("is_theorem",toJson ci.isTheorem)]
  liftIO <| IO.FS.writeFile "output/reuse-audit/kernel-dependencies.json" (Json.compress (toJson rows) ++ "\n")
  logInfo m!"Recorded {rows.size} checked constant dependencies."
