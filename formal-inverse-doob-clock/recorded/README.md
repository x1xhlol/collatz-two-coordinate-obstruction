# Recorded portable replay

This directory preserves the completed portable replay for `formal-inverse-doob-clock` and its post-replay artifact audit. The driver was reviewed before execution. Sources and manifests were frozen for the run.

| Item | Result |
| --- | --- |
| Fresh source modules | 26 |
| Compile and kernel units, including generated audit | 27 |
| Successful compile/kernel commands | 54 |
| Audited compiled constants | 307 |
| Private compiled constants | 0 |
| Named/private source declarations | 195 / 0 |
| Authenticated native/raw object subsets | 1496 / 4 |
| Negative controls passed | 13 |

The compiled declaration and axiom inventory exactly matches the frozen research replay. Compiler and kernel warnings were absent. The only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Replay-record SHA-256: `80a8462ad6d0a926388d421cf155cfed6759d6bbc576812b5945bd6f990c212d`

Run-manifest SHA-256: `5286334a072368bed6565dea18e22b81eade8b2722c983b6d828b05814cc4a25`

Verifier SHA-256: `53bfa15414a8578d80e4f4b4ef2cf55055c6a92ce8768a9310aea9c2348051d9`

`replay-record.json` is the unchanged output of the portable verifier. `run-bundle-manifest.json` preserves the exact manifest used during that run. Compiler and kernel logs are retained under `logs/`, and the generated all-constant audit source is included. Compiled objects and dependency caches are not distributed.

`PORTABLE-REPLAY-REVIEW.json` records the post-replay checks of every fresh source, object and log, the compiled declaration inventory, accepted dependency records, and selected upstream source/object pairs and exposed links. This is an execution and artifact audit, not an independent human review or a second full upstream rebuild. Earlier source and semantic reviews retain their original scope under `reviews/`.

`negative-controls.json` records isolated-copy tests for missing/wrong record pins, mismatched native provenance, changed application/raw sources, extra application modules, and corrupted native/raw objects. A timestamp/size-valid stale Python helper cache was first demonstrated to execute under ordinary import; the verified-byte loader bypassed it and rejected changed helper source before execution. The original local fixture and artifact-check scripts are retained under `provenance-tools/` as execution provenance. They contain historical workspace paths and are not portable entrypoints; use `../verify.py` for a new replay.

The replay reused authenticated upstream objects and pinned Lean/Mathlib caches. It neither rebuilt those dependencies nor established any conclusion beyond the theorem statements in the main README.
