# Periodic-census basin-density floor: additive Lean bundle

This bundle adds a reciprocal lower bound for actual Collatz basin density to the pinned native basin development. For every positive target `N` not divisible by three, the main theorem proves

```text
actualBasinDensity N >= 3 / (128 * predecessorSeedMultiplier * N).
```

The seed multiplier is one fixed positive integer, independent of the target. The corollaries give a uniform reciprocal floor for actual first-hit weighted density, a uniform positive floor for the canonical trace on unit targets, and ordinary-map predecessor natural densities with a uniform reciprocal floor. These results do not prove the Collatz conjecture, exclude another positive cycle, or exclude a divergent orbit.

The package contains 51 Lean application modules: the 26-module compatible Gao closure, all 14 bounded-seed extension modules, and 11 periodic-census modules. Every supplied source is compiled afresh by the verifier. The existing native bundle is a prerequisite and is left untouched. Its required objects are authenticated and reused; Mathlib and Lean library caches are also reused. This is an additive replay, not a new build of the entire native or library dependency closure.

## Endpoints

All new endpoints below are in namespace `CollatzCanonical.PeriodicCensusFloor`.

| File | Main declaration |
| --- | --- |
| `ActualBasinPolynomialFloor.lean` | `actual_basin_polynomial_lower_density` |
| `CanonicalTracePolynomialFloor.lean` | `exists_uniform_firstHit_reciprocal_floor` |
| `CanonicalTracePolynomialFloor.lean` | `exists_uniform_unit_canonical_trace_floor` |
| `OrdinaryPredecessorPolynomialFloor.lean` | `exists_uniform_ordinary_predecessor_polynomial_natural_density` |

The ordinary-map file also proves natural-density existence for every positive ordinary target and an eventual predecessor-count lower bound. Inspect the exact Lean statements for target conditions and constants. The source inventory and import order are in `bundle-manifest.json`; origin and license records are in `provenance/` and `SOURCE-LICENSES.txt`.

## Prerequisites

Provide an already verified native `formal-basins-native` bundle whose `replay-manifest.json` has SHA-256

```text
efc8bc1226fb158341a4626eeafaf5c97b9284da1a2d137de38b7db035cbb230
```

Its completed replay directory must contain `replay-record.json` and `modules/`. By default this verifier accepts the recorded reference replay with SHA-256

```text
260930d45985dca3d8b7abe88fff1c8c73aa154893d5fa1476b5c76b0b70a79c
```

If rebuilding that native bundle separately, first run its own verifier using its instructions. For its current command-line interface, the fresh-base invocation is:

```bash
python3 /path/to/formal-basins-native/verify_replay.py \
  --mathlib /path/to/mathlib4 \
  --lean /path/to/lean-4.30.0-rc2/bin/lean \
  --output /path/to/new-native-replay
```

Pin the resulting successful record's SHA-256 explicitly with `--native-record-sha256` when using it below. That option is for a record the operator has independently verified; it is not a way to skip source, object, dependency, status, or toolchain checks. Absolute paths recorded by the native replay may differ across machines; this verifier resolves inputs using the supplied paths and does not depend on those historical paths.

Use Python 3, Git, Lean 4.30.0-rc2 (commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`), and the built Mathlib checkout at revision `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. The exact Lean version string, Mathlib package manifest and eight package revisions are pinned in `bundle-manifest.json`. The recorded profile is Linux x86-64. The verifier checks clean tracked Mathlib/package source trees and requires their built caches. It downloads nothing and changes none of these dependencies.

## Replay

Inspect package integrity without building:

```bash
python3 verify.py --verify-package-only
```

Build and audit in a new output directory:

```bash
python3 verify.py \
  --native-bundle /path/to/formal-basins-native \
  --native-build /path/to/verified-native-replay \
  --lean-bin /path/to/lean-4.30.0-rc2/bin \
  --mathlib /path/to/mathlib4 \
  --output /path/to/new-periodic-census-replay
```

For a separately rebuilt native base, add `--native-record-sha256 YOUR_VERIFIED_RECORD_SHA256`. Omit `--output` to create a fresh directory in the system temporary location. An existing output directory is rejected, and no pre-existing extension objects are imported.

The verifier:

1. Checks the frozen package sources and imports against the manifest, and reconstructs the complete native import closure independently.
2. Checks every required native source, object and dependency fingerprint against the pinned manifest and successful replay record, before and after the build.
3. Exposes only those authenticated native objects on a separate import path, then compiles all 51 supplied application modules from fresh source copies.
4. Runs `leanchecker` separately on every supplied application module.
5. Enumerates each compiled module's constants, including private and generated constants, and calls Lean's `collectAxioms` on every one. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Named source declarations are cross-checked against the compiled inventory.
6. Rechecks the frozen package, sources, objects and dependencies, and writes a `PASS` replay record only after all checks succeed.

The output contains fresh sources and objects, complete compiler/kernel logs, the generated axiom harness, and `replay-record.json`. Per-module kernel checks cover the freshly built application modules against imported dependencies; the verifier does not claim a `leanchecker --fresh` replay of the entire native/Mathlib closure. One archived deprecation warning in `Tejonas.lean` is allowed and recorded; other warnings are rejected.

## Source preservation and licenses

The new 11 sources and bounded-seed 14 sources preserve their frozen bytes. The Gao archive sources and original archive are retained under `provenance/gao/`. Twenty-four supplied Gao sources are byte-identical to that archive. `Momentos.lean` and `Hienas.lean` rename the square-root import for the pinned Mathlib version and carry prominent modification comments. No theorem statement or proof text changes in that compatibility port. Original, earlier compatible and packaged hashes are recorded separately.

Original local work retains the MIT license and Lucas Valbuena attribution. Omar Javier Said Duran's Gao formalization and Lech Mazur's predecessor-derived material retain their Apache-2.0 licenses, notices and provenance. See `SOURCE-LICENSES.txt`; imported or adapted material is not blanket-relicensed as MIT. Mathlib, Lean and native-base sources remain under their own retained licenses and are not redistributed here as compiled caches.
