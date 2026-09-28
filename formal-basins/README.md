# Partial formalization of the basin-density paper

The exact statement coverage and remaining obligations are listed in [the basin claim map](../paper/basin-lean-claims.md). This directory uses Lean 4.27.0 and the same pinned mathlib revision as the original formal artifact.

From the repository root, with the dependencies described in [formal/README.md](../formal/README.md):

```sh
python3 verify.py --scope basins --mathlib-root /path/to/mathlib4 --report /new/path/basins.json
```

The verifier rebuilds this scope in a fresh directory, inventories all public theorem and lemma declarations, audits their logical axioms and all inventoried definitions and named instances, and guards sources and dependency revisions during the run. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. No project axiom or admitted proof is used.

`CollatzCylinderPacking.step` is the actual shortcut Collatz map on natural numbers: even inputs map to `n/2`, odd inputs to `(3n+1)/2`. The map is defined separately from the older synchronization namespace; its iterate and odd-count functions are explicit in the source. The abstract averaging statements are about real Banach spaces and retain their moving-window hypotheses.
