import FiniteObservableEventLower
import ResidualOccupationSourceMean
import AlignedResidualOccupationLower
import UniformResidualDensityLower
import ForwardOddPrefix
import AsymptoticResidualWithPrefix
import ForwardLogPrefix
import RawOccupationDivergentExcess
import Lean

open Lean Elab Command in
run_cmd do
  let wanted : Array String := #["FiniteObservableEventLower", "ResidualOccupationSourceMean", "AlignedResidualOccupationLower", "UniformResidualDensityLower", "ForwardOddPrefix", "AsymptoticResidualWithPrefix", "ForwardLogPrefix", "RawOccupationDivergentExcess"]
  let env ← getEnv
  for i in [:env.header.modules.size] do
    let mod := env.header.modules[i]!.module
    if wanted.contains mod.toString then
      for name in env.header.moduleData[i]!.constNames do
        let axioms ← collectAxioms name
        let visibility := if isPrivateName name then "private" else "public"
        let names := String.intercalate "," (axioms.toList.map Name.toString)
        logInfo m!"AUDIT_AXIOMS|{mod.toString}|{name.toString}|{visibility}|{names}"
