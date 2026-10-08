# Canonical integer-envelope source replay

This private candidate contains the exact internal source closure of the endpoint modules listed in source-manifest.json. Its claims concern the canonical stationary measure, its lower semicontinuous envelope and positive integer trace, uniform cylinder lower bounds, and the explicitly named consequences. It makes no Collatz convergence claim.

Run scripts/setup.py with --expected-manifest-sha256 and optionally --toolchain and --mathlib to prepare or verify the pinned external dependencies. Then run scripts/replay.py with those same three arguments and --run, optionally adding --jobs 4 for bounded dependency parallelism. The destination .replay must be fresh. Use --verify-only afterwards to check all recorded source/object/log/import hashes and the complete constant audit again. External Mathlib and toolchain objects are pinned and inventoried, not rebuilt.

The replay accepts only fresh internal objects. Each source is compiled with -j1 and -DwarningAsError=true, then checked by the official leanchecker. The final audit covers every constant owned by every internal module, including private and compiler-generated constants, and permits only propext, Classical.choice, and Quot.sound.

provenance/envelope-source-origins.json is the combined source selection ledger. Retained licenses and modification notices preserve their original scopes. The copied sharp source ledger does not describe the additional native and envelope modules.
