# Recorded portable replay

`replay-record.json` records the completed fresh additive run of the exact package in `run-bundle-manifest.json`. The record contains historical execution paths; the portable verifier takes explicit paths and does not use those historical paths to locate prerequisites.

All 17 application modules and the generated audit were freshly compiled and individually kernel-replayed. The audit covers 193 compiled application constants, including all 118 explicit declarations, with no private constants or nonstandard axioms. No warnings occurred. Forty periodic-census modules, 1,566 native modules, and pinned Lean/Mathlib caches were authenticated and reused as described by the record.

The generated audit source and all compiler/kernel logs are retained here. Compiled objects and cache symlinks are not distributed. `PORTABLE-REPLAY-REVIEW` records the final evidence checks and review scope. Earlier source reviews are under `reviews/`; earlier research records are under `../provenance/research-replays/`.

`SHA256SUMS` hashes these recorded artifacts except itself. These post-run evidence files do not change the package manifest that the replay checked. The manifest continues to pin the supplied sources, verifier, documentation and pre-existing provenance records.
