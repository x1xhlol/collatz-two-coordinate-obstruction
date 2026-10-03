# Recorded portable replay

`replay-record.json` records the completed fresh additive run of the exact package in `run-bundle-manifest.json`. Historical execution paths are evidence only; the portable verifier takes explicit paths to locate its prerequisites.

All 16 application modules and the generated audit were freshly compiled and individually kernel-replayed: 34 successful commands. The audit covers 153 compiled application constants, including 5 private constants and all 87 named plus 4 private source declarations. Only `propext`, `Classical.choice` and `Quot.sound` occur, and no compiler warnings occurred. Exactly 913 native source/object pairs and pinned Lean/Mathlib caches were authenticated and reused as described by the record. No periodic-census or cylinder-energy objects were used.

The generated audit source and every compiler/kernel log are retained here. Compiled objects, Python bytecode and cache symlinks are not distributed. `PORTABLE-REPLAY-REVIEW` records the execution and evidence checks; `PORTABLE-RAW-DRIVER-INDEPENDENT-REVIEW` is the separate full source/process review. The latter does not claim another execution of the kernel replay. Seven fail-closed controls, including a validated malicious stale-helper-bytecode fixture, are recorded in `portable-driver-hardened-checks.json`.

Earlier semantic reviews and the research replay certificate are under `reviews/`; the research record is under `../provenance/research-replays/`. Only the hardened portable run is distributed. A prior successful exploratory run used the earlier helper import and is not this record.

`SHA256SUMS` hashes these recorded artifacts except itself. These post-run evidence files do not change the package manifest that the replay checked. The manifest continues to pin the supplied sources, verifier, documentation and pre-existing provenance records.
