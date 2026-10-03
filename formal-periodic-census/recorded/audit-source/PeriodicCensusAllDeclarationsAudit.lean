import cadena_completa
import Momentos
import Maximos
import Resto
import Supervivencia
import Banda
import rachas
import RachasEnteras
import UmbralRachas
import Reloj
import Producto
import Palabras
import SalidaPalabras
import Ventana
import ParametrosVentana
import Hormigas
import Ensayo
import Repeticion
import Guardias
import ConteoEnsayos
import Lagartijas
import Martas
import Tejonas
import GaoEnunciado
import Hienas
import GaoLiteral
import TwoSiblingNonreturn
import BoundedInverseResidueSeed
import BoundedFrozenSeed
import SixthPowerMixingBudget
import SeedDensityFloor
import GenericSeedPredecessorCount
import BoundedPredecessorDensity
import ActualBasinExplicitLowerDensity
import NativePredecessorMixingBridge
import ArbitraryPowerMixingBudget
import GenericPowerPredecessorCount
import PowerDensityFloor
import PowerPredecessorDensity
import ActualBasinPowerLowerDensity
import PeriodicSourceMean
import TerminalFanEnvelope
import TerminalFanCensus
import FrozenSeedPeriodicPrefix
import GaoShortcutBridge
import BasinAdjacentVariation
import OddTerminalFanMean
import ActualBasinPeriodicMean
import ActualBasinPolynomialFloor
import CanonicalTracePolynomialFloor
import OrdinaryPredecessorPolynomialFloor
import Lean

open Lean Elab Command in
run_cmd do
  let wanted : Array String := #["cadena_completa", "Momentos", "Maximos", "Resto", "Supervivencia", "Banda", "rachas", "RachasEnteras", "UmbralRachas", "Reloj", "Producto", "Palabras", "SalidaPalabras", "Ventana", "ParametrosVentana", "Hormigas", "Ensayo", "Repeticion", "Guardias", "ConteoEnsayos", "Lagartijas", "Martas", "Tejonas", "GaoEnunciado", "Hienas", "GaoLiteral", "TwoSiblingNonreturn", "BoundedInverseResidueSeed", "BoundedFrozenSeed", "SixthPowerMixingBudget", "SeedDensityFloor", "GenericSeedPredecessorCount", "BoundedPredecessorDensity", "ActualBasinExplicitLowerDensity", "NativePredecessorMixingBridge", "ArbitraryPowerMixingBudget", "GenericPowerPredecessorCount", "PowerDensityFloor", "PowerPredecessorDensity", "ActualBasinPowerLowerDensity", "PeriodicSourceMean", "TerminalFanEnvelope", "TerminalFanCensus", "FrozenSeedPeriodicPrefix", "GaoShortcutBridge", "BasinAdjacentVariation", "OddTerminalFanMean", "ActualBasinPeriodicMean", "ActualBasinPolynomialFloor", "CanonicalTracePolynomialFloor", "OrdinaryPredecessorPolynomialFloor"]
  let env ← getEnv
  for i in [:env.header.modules.size] do
    let mod := env.header.modules[i]!.module
    if wanted.contains mod.toString then
      for name in env.header.moduleData[i]!.constNames do
        let axioms ← collectAxioms name
        let visibility := if isPrivateName name then "private" else "public"
        let names := String.intercalate "," (axioms.toList.map Name.toString)
        logInfo m!"AUDIT_AXIOMS|{mod.toString}|{name.toString}|{visibility}|{names}"
