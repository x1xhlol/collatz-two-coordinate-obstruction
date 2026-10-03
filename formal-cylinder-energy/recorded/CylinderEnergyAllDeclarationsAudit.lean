import CylinderGrowthHeadTransport
import OddDyadicReciprocalBudget
import FirstHitCutCapacity
import SyracuseFirstHitGeometry
import SyracuseUnitNonperiodicFan
import ExactFirstHitCoefficient
import GammaFreeFirstHitCoefficient
import MaskedCylinderNoSmallAncestorEnergy
import MaskedEnergyBoundaryLimit
import CylinderForwardPropagation
import NonperiodicSyracuseSpine
import CycleTraceRatioFloor
import FiniteCylinderEnergyImplication
import ShiftedCesaroEnergyExclusion
import SublinearNonperiodicCylinderEnergy
import MaskedEnergySufficiency
import MaskedEnergyPeriodicityEquivalence
import Lean

open Lean Elab Command in
run_cmd do
  let wanted : Array String := #["CylinderGrowthHeadTransport", "OddDyadicReciprocalBudget", "FirstHitCutCapacity", "SyracuseFirstHitGeometry", "SyracuseUnitNonperiodicFan", "ExactFirstHitCoefficient", "GammaFreeFirstHitCoefficient", "MaskedCylinderNoSmallAncestorEnergy", "MaskedEnergyBoundaryLimit", "CylinderForwardPropagation", "NonperiodicSyracuseSpine", "CycleTraceRatioFloor", "FiniteCylinderEnergyImplication", "ShiftedCesaroEnergyExclusion", "SublinearNonperiodicCylinderEnergy", "MaskedEnergySufficiency", "MaskedEnergyPeriodicityEquivalence"]
  let env ← getEnv
  for i in [:env.header.modules.size] do
    let mod := env.header.modules[i]!.module
    if wanted.contains mod.toString then
      for name in env.header.moduleData[i]!.constNames do
        let axioms ← collectAxioms name
        let visibility := if isPrivateName name then "private" else "public"
        let names := String.intercalate "," (axioms.toList.map Name.toString)
        logInfo m!"AUDIT_AXIOMS|{mod.toString}|{name.toString}|{visibility}|{names}"
