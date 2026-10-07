import ActualOddInverseRow
import ActualInverseDoobLaw
import NonperiodicCylinderSource
import InverseBranchCylinder
import FinitePathCylinder
import ActualTransitionAtom
import NonperiodicFiniteCylinder
import SourceSuffixPrefix
import LastVisitGeometry
import SourceLastVisitClock
import ActualPathSupport
import ActualLastVisitLaw
import LadderClockLimit
import FinitePrefixIndex
import CountableScheffe
import FinitePrefixSourceMass
import FinitePrefixSourceBound
import CountableMassSqueeze
import ActualFinitePrefixTV
import ActualPrefixEvents
import FiniteLadderClockEvent
import ActualLadderClock
import ActualInversePathGrowth
import InverseClockGeometry
import InverseClockRefinement
import ActualInverseHeightClock
import Lean

open Lean Elab Command in
run_cmd do
  let wanted : Array String := #["ActualOddInverseRow", "ActualInverseDoobLaw", "NonperiodicCylinderSource", "InverseBranchCylinder", "FinitePathCylinder", "ActualTransitionAtom", "NonperiodicFiniteCylinder", "SourceSuffixPrefix", "LastVisitGeometry", "SourceLastVisitClock", "ActualPathSupport", "ActualLastVisitLaw", "LadderClockLimit", "FinitePrefixIndex", "CountableScheffe", "FinitePrefixSourceMass", "FinitePrefixSourceBound", "CountableMassSqueeze", "ActualFinitePrefixTV", "ActualPrefixEvents", "FiniteLadderClockEvent", "ActualLadderClock", "ActualInversePathGrowth", "InverseClockGeometry", "InverseClockRefinement", "ActualInverseHeightClock"]
  let env ← getEnv
  for i in [:env.header.modules.size] do
    let mod := env.header.modules[i]!.module
    if wanted.contains mod.toString then
      for name in env.header.moduleData[i]!.constNames do
        let axioms ← collectAxioms name
        let visibility := if isPrivateName name then "private" else "public"
        let names := String.intercalate "," (axioms.toList.map Name.toString)
        logInfo m!"AUDIT_AXIOMS|{mod.toString}|{name.toString}|{visibility}|{names}"
