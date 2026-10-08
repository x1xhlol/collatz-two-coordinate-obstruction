# Canonical stationary envelope and positive integer traces

This source bundle proves that the canonical Syracuse stationary law on the 3-adic integers has a greatest nonnegative lower semicontinuous Haar density. Its integral is one, it vanishes off the units, and it has a uniform positive lower bound on the units. At every positive integer its value equals the native arithmetic trace, including the cycle factor at periodic integers.

The consequences include a constant lower bound `c · 3⁻ᵏ` for every unit cylinder mass, normalized minimum-cylinder exponent one, convergence of the cylinder densities at each positive integer in Cesàro mean absolute error, and a lower bound on the arithmetic trace throughout a sufficiently small residue class about that integer. Its infinite-value set is a Haar-null Gδ set dense in the units. The positive integer trace is unbounded in every unit residue class, and the envelope is discontinuous at every positive unit integer. These results do not settle forward Collatz convergence or the expected late-occupation bound.

The sole replay entrypoint is [CanonicalIntegerEnvelopeResults.lean](source/CanonicalIntegerEnvelopeResults.lean). Its fourteen designated declarations, all in `CollatzCanonical.IntegerStationaryEnvelope`, are:

- `canonicalIntegerEnvelope_withDensity`
- `canonicalIntegerEnvelope_lintegral_eq_one`
- `canonicalIntegerEnvelope_uniform_unit_floor`
- `canonicalIntegerEnvelope_natCast_eq`
- `canonicalIntegerEnvelope_greatest`
- `canonicalMinimumUnitMass_uniform_bounds`
- `canonicalMinimumUnitMass_base_three_rate`
- `canonicalRho_mean_abs_native_trace`
- `actual_trace_residue_lower`
- `canonicalIntegerEnvelope_infinity_closure`
- `canonicalIntegerEnvelope_infinity_isGDelta`
- `canonicalIntegerEnvelope_infinity_haar_null`
- `actual_trace_unbounded_in_unit_cylinder`
- `canonicalIntegerEnvelope_not_continuousAt_positive_unit`

## Reference verification

The reference replay completed on 2026-10-08: all 1,620 source modules and the generated audit passed all 3,242 strict compilation and official kernel-check commands. The audit covered 36,651 module-header rows over 36,539 distinct internal constants, including 3,419 rows with encoded private names. Header membership and actual owner modules are recorded separately. Every audited declaration uses only the permitted standard axioms. The identical before/after states include 53,006 external compiled objects.

Setup using existing installations, new-process verification and relocated verification also passed. The relocation check copied completed internal replay artifacts and reused the same external libraries; it did not compile the sources again. See [the validation record](evidence/validation/validation-record.json) and [preserved execution evidence](evidence/README.md).

The [reference replay record](evidence/reference-replay/replay-record.json) has SHA-256 `d51c6afb6168cf34f629cd1d1849cdf5c98067a30c6f60c5d311b74e4e9f39fe`.

The minimal [README.md](README.md) is a byte-preserved execution input. Its “private candidate” description records the status when sources were frozen. This guide and the completed evidence record the later verification status; retaining the original README keeps its manifest hash and the checked replay inputs unchanged.

The proof execution manifest has SHA-256 `c3a623f8f06ec66824099ca3b4e40e5448533c0dfb0ce389cee70e52879dc28c`. The separate `publication-manifest.json` lists all distributed files, including later documentation, license appendices and textual evidence. No compiled internal artifacts or external libraries are distributed. Create a fresh local `.replay` before using `--verify-only`; the preserved reference evidence is not a ready-made compiled replay directory.

## Reproduce

Use Linux x86_64 with Python 3.9 or later and Git. Fresh external setup also requires GNU tar, zstd, curl 7.81 or later, and at least 15 GiB of free space. The source replay requires at least 1 GiB free initially and preserves partial results if free space falls below 512 MiB. The scheduler requires at least 4 GiB of available RAM, accounting for visible cgroup-v2 memory limits, before each reservation and command start. Environments with cgroup-v1 memory control are rejected because the effective memory limit cannot be established by this recipe. Run the following commands from the bundle directory.

Fresh setup downloads the checksum-pinned official Lean 4.30.0-rc2 archive, checks out Mathlib commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6` and all eight pinned package revisions, obtains their compiled caches, and runs preflight:

```sh
python3 scripts/setup.py \
  --expected-manifest-sha256 c3a623f8f06ec66824099ca3b4e40e5448533c0dfb0ce389cee70e52879dc28c
```

The official archive URL, byte count, checksum and dependency revisions are recorded in `dependency-pins.json`. Default installation paths are `.external/lean-4.30.0-rc2-linux` and `.external/mathlib4`. Setup records the resolved paths in `setup-result.json`; `--external-dir /path/to/new/storage` chooses another fresh location. Existing partial checkouts are preserved rather than overwritten.

Exact existing installations may instead be reused read-only:

```sh
python3 scripts/setup.py \
  --expected-manifest-sha256 c3a623f8f06ec66824099ca3b4e40e5448533c0dfb0ce389cee70e52879dc28c \
  --toolchain /path/to/lean-4.30.0-rc2-linux \
  --mathlib /path/to/mathlib4
```

The supplied Mathlib tree must contain its pinned `.lake/packages` checkouts and compiled caches. Setup does not modify an installation supplied through `--mathlib`.

For the default fresh-setup paths, run:

```sh
python3 scripts/replay.py \
  --expected-manifest-sha256 c3a623f8f06ec66824099ca3b4e40e5448533c0dfb0ce389cee70e52879dc28c \
  --toolchain .external/lean-4.30.0-rc2-linux \
  --mathlib .external/mathlib4 \
  --run --jobs 4
```

Substitute the existing installation paths when reusing dependencies. The `.replay` destination must not exist. To repeat a replay, use another source-bundle directory or explicitly archive the prior `.replay`; the driver does not discard earlier evidence.

After a successful run, authenticate its complete record from a new process:

```sh
python3 scripts/replay.py \
  --expected-manifest-sha256 c3a623f8f06ec66824099ca3b4e40e5448533c0dfb0ce389cee70e52879dc28c \
  --toolchain .external/lean-4.30.0-rc2-linux \
  --mathlib .external/mathlib4 \
  --verify-only
```

`--jobs` accepts one through four concurrent module pairs and defaults to one. A dependent module starts only after its imported modules pass compilation and kernel checking. Sources of at least 50,000 bytes and the final audit run alone.

`--preflight` checks all inputs without compiling internal sources. `--verify-only` authenticates a completed replay and its artifacts; it does not recompile them.

## Execution scope

The frozen manifest fixes the exact 1,620-module internal source closure, topological import order, source hashes and lexical inventories: 17,075 named declarations, 1,557 private declarations and 63 anonymous source instances. The selected versions come from 21 new envelope modules, 345 retained sharp-density modules, 1,094 native modules, 118 additional proof-compatibility adaptations, 39 census modules and three weighted-source modules. One of those 118 adaptations is a census/Gao source; the per-module provenance records retain its original source and license scope. The final proof uses the direct inverse-layer bound and periodic source means; the superseded high-trace and gamma-free adapter route is outside this selected closure.

Every internal module is compiled freshly with `-j1 -DwarningAsError=true` and checked by the official `leanchecker`. A generated audit then imports every internal module and checks all its header constants, including private and generated declarations. It independently enumerates checked-environment ownership and requires agreement with the complete header-name union. Only the standard axioms `propext`, `Classical.choice` and `Quot.sound` are permitted. Compilation and kernel checking of the audit bring the planned total to 3,242 successful commands.

The replay uses one fresh internal object directory. Every internal direct import must resolve there. It records input state before compilation and after the audit, requiring exact agreement of source inventories, official compiler/runtime hashes, clean external package revisions and every available external `.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir`, `.ir.sig` and `.so` file. Verification checks command vectors, log contents and hashes, source and object hashes, companion artifacts, direct-import resolutions and the complete axiom audit again. It also verifies the dependency schedule, concurrency and exclusive-module limits, recorded memory checks, and the absence of a failure latch.

External Mathlib, dependency and toolchain compiled libraries are a stated trust boundary. They are fingerprinted and reused; their complete source closures are not rebuilt or independently kernel checked here. The fingerprints establish the exact objects used and their stability during the run. They do not establish that every cached object was built from the adjacent source checkout. The fresh external download and cache-preparation branch was not exercised for this reference run.

Execution scripts use bundle-relative paths and symbolic `BUNDLE`, `TOOLCHAIN` and `MATHLIB` roots. Historical provenance can retain original research paths as labels. Those paths are not required to execute the replay.

## Source rights and provenance

[SOURCE-LICENSES.txt](SOURCE-LICENSES.txt) and [the combined source license inventory](provenance/envelope-license-review.json) describe this complete selection. They preserve the distinct source rights of Lucas Valbuena's local work, Lech Mazur's first-passage and predecessor developments, Omar Javier Said Duran's Gao formalization, M. Sharpe's adapted MIT proofs, and the Formal Conjectures sources. Original headers, exact compatibility patches and notices remain present.

The earlier `licenses/SOURCE-LICENSES.txt` and `provenance/origin-license-review.json` are retained historical records for the previous 362-module sharp-density bundle. Their earlier whole-bundle counts and exclusions do not describe this expanded selection. The combined ledger identifies their source-specific role and supplies the additional census/Gao rights records.

The 150 selected proof-compatibility changes have exact original/current hashes and patches in `provenance/native-linter-patches.json` and `provenance/envelope-linter-patches.json`. The separate reviewed Wikipedia source shard omits an unrelated unproved conjecture declaration while retaining the actual definition and upstream attribution. No altered proof-check policy is used for that source.

The companion mathematical paper and its claim map are distributed separately from this software bundle. Software license grants do not relicense external papers or images.
