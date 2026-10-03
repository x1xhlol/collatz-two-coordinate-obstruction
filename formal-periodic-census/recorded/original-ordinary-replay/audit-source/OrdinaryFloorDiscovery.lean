import OrdinaryPredecessorPolynomialFloor
import Lean

open Lean Elab Command in
run_cmd do
  let wanted : Array String := #["OrdinaryPredecessorPolynomialFloor"]
  let env ← getEnv
  for i in [:env.header.modules.size] do
    let mod := env.header.modules[i]!.module
    if wanted.contains mod.toString then
      for name in env.header.moduleData[i]!.constNames do
        if !isPrivateName name then
          logInfo m!"AUDIT_DECL|{mod.toString}|{name.toString}"
