import BelowIntermediateStageClock
import BoundedBottomPassageClock
import FiniteSyracuseClockConfinement
import PreBarrierWeightedOccupation
import AlignedLadderOccupation
import ClosedWindowCumulativeAdapter
import FixedLadderGoodCumulative
import FiniteOccupationSourceMean
import FiniteOccupationEventLower
import FailureEnvelopeMonotonicity
import UniformAlignedOccupationLower
import ClockGridAsymptotics
import OccupationLowerValueLimit
import FinitePowerClockGrid
import RawOccupationAsymptoticLower
import DivergentPostBarrierOccupation
import Lean

open Lean Elab Command in
run_cmd do
  let wanted : Array String := #["BelowIntermediateStageClock", "BoundedBottomPassageClock", "FiniteSyracuseClockConfinement", "PreBarrierWeightedOccupation", "AlignedLadderOccupation", "ClosedWindowCumulativeAdapter", "FixedLadderGoodCumulative", "FiniteOccupationSourceMean", "FiniteOccupationEventLower", "FailureEnvelopeMonotonicity", "UniformAlignedOccupationLower", "ClockGridAsymptotics", "OccupationLowerValueLimit", "FinitePowerClockGrid", "RawOccupationAsymptoticLower", "DivergentPostBarrierOccupation"]
  let env ← getEnv
  for i in [:env.header.modules.size] do
    let mod := env.header.modules[i]!.module
    if wanted.contains mod.toString then
      for name in env.header.moduleData[i]!.constNames do
        let axioms ← collectAxioms name
        let visibility := if isPrivateName name then "private" else "public"
        let names := String.intercalate "," (axioms.toList.map Name.toString)
        logInfo m!"AUDIT_AXIOMS|{mod.toString}|{name.toString}|{visibility}|{names}"
