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
import Lean

open Lean Elab Command in
run_cmd do
  let wanted : Array String := #["PeriodicSourceMean", "TerminalFanEnvelope", "TerminalFanCensus", "FrozenSeedPeriodicPrefix", "GaoShortcutBridge", "BasinAdjacentVariation", "OddTerminalFanMean", "ActualBasinPeriodicMean", "ActualBasinPolynomialFloor", "CanonicalTracePolynomialFloor"]
  let env ← getEnv
  for i in [:env.header.modules.size] do
    let mod := env.header.modules[i]!.module
    if wanted.contains mod.toString then
      for name in env.header.moduleData[i]!.constNames do
        if !isPrivateName name then
          logInfo m!"AUDIT_DECL|{mod.toString}|{name.toString}"
