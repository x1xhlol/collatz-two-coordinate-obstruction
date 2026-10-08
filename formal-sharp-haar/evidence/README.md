# Preserved replay evidence

`reference-replay/` contains the complete successful 362-source replay record, its before/after input inventories, all 726 compile/kernel logs, the final progress record and the generated audit source. The original `.replay/modules` compiled artifacts are deliberately not distributed. Paths beginning `BUNDLE/.replay` in these records identify the original replay layout; the corresponding published textual evidence is under `evidence/reference-replay/`.

Run the documented fresh replay to create a new `.replay` directory and its compiled artifacts before using `--verify-only`. The reference record is evidence for the recorded execution; it is not an existing local replay output directory.

`original-failed-attempt/` preserves the earlier 68 completed source/kernel pairs and the failing 137th command, together with its pre-execution input inventory. That attempt stopped at a strict linter error and did not complete the global audit or final input-state verification. The matching original manifest and provenance are under `provenance/original-attempt/`.

Some historical evidence, including the original error log and an independent review record, retains absolute research-directory paths to preserve its exact bytes and hashes. These are historical labels, not paths needed at runtime. Current execution scripts and the successful primary replay record use bundle-relative paths or symbolic `BUNDLE`, `TOOLCHAIN` and `MATHLIB` roots.

`validation/` records the actual setup-reuse check and subsequent verification in new processes. Setup's raw local-path result remains private; public validation output labels those roots symbolically. The fresh toolchain-download and Mathlib-cache preparation branch was not executed for this reference run. External compiled caches were fingerprinted and reused, not rebuilt from their adjacent source checkouts.
