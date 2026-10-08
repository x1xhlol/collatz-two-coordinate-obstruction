# Preserved replay evidence

`reference-replay/` contains the complete successful 1,620-source replay record, its before/after input inventories, all 3,242 compilation/kernel logs, the final progress record and the generated audit source. The replay record also preserves the dependency schedule, command timings and memory checks. Compiled artifacts from `.replay/modules` are excluded from distribution. Paths beginning `BUNDLE/.replay` identify the execution layout; the published textual evidence is preserved under `evidence/reference-replay/`.

Run the documented fresh replay to create a local `.replay` directory and compiled artifacts before using `--verify-only`. The reference record documents the recorded execution and does not substitute for those local artifacts.

`validation/` records setup with existing installations and verification in new processes, including verification from a relocated bundle. The relocated check copies the completed internal replay artifacts and reuses the same external libraries. It is not another source compilation or an external-cache source rebuild. Public commands and output replace local roots with symbolic labels; raw setup output and `setup-result.json` remain private.

The fresh toolchain-download and Mathlib-cache preparation branch was not executed for the reference run. External compiled objects were fingerprinted and reused, without a proof that each cached object was built from the adjacent source revision.

Some preserved source provenance and historical review records retain original research-directory paths to keep their bytes and hashes intact. These are historical labels, not runtime dependencies. The current replay scripts and primary replay record use relative paths or symbolic roots.
