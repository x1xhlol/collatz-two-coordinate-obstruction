# Raw occupation: additive Lean bundle

This bundle proves an unconditional lower bound for the sum of actual first-hit densities over positive odd targets. Let `D_N = actualFirstHitDensity N` and `ell = log(4/3)`. The main theorem states:

```text
For every real b < 1/ell, eventually over natural R,
  b <= (sum over odd N <= R of D_N) / log R.
```

The statement permits unbounded growth. It assumes neither a finite real liminf nor convergence of the normalized sum, and supplies no upper bound. A separate finite theorem adds disjoint contributions before a barrier and along the future of an injective Collatz orbit. That theorem is conditional on the specified injective orbit and does not assert that one exists. Neither result establishes the Collatz conjecture or universal eventual periodicity.

All declarations are in namespace `CollatzCanonical.RawOccupation`.

| Source | Main declaration |
| --- | --- |
| `RawOccupationAsymptoticLower.lean` | `actual_raw_occupation_eventual_lower` |
| `UniformAlignedOccupationLower.lean` | `exists_uniform_finite_occupation_density_lower` |
| `FinitePowerClockGrid.lean` | `finitePowerClockGrid_eventual_hypotheses` |
| `FiniteOccupationSourceMean.lean` | `oddTargetOccupation_normalized_odd_mean` |
| `FixedLadderGoodCumulative.lean` | `fixedLadderGoodEvent_failure_cumulative_envelope` |
| `DivergentPostBarrierOccupation.lean` | `preBarrier_occupation_add_divergent_future` |

The proof first takes the source mean at each fixed finite target cutoff. It then uses actual lower-stage clock events on finitely many aligned ladders, a bounded remainder for successful bottom passages, and an explicit grid of powers of `R`. The grid length is fixed before the barrier base is chosen; the base is fixed before `R` tends to infinity. No uniform source convergence rate or exchange of infinite source and target limits is assumed.

The package is the exact 16-module application import closure of the two endpoint modules `RawOccupationAsymptoticLower` and `DivergentPostBarrierOccupation`. Its Lean sources preserve the bytes of the reviewed research packet. The verifier compiles all 16 supplied sources afresh, kernel-checks each with `leanchecker`, and compiles and kernel-checks a generated audit of every application constant, including generated and private constants. It reuses exactly 913 authenticated native modules and pinned Mathlib/Lean caches. It uses no periodic-census or cylinder-energy application objects. This is an additive replay, not a fresh build of the upstream closure.

## Prerequisites

Use Python 3, Git, Lean 4.30.0-rc2 at commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, and built Mathlib at revision `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. The recorded profile is Linux x86-64. The manifest pins the exact Lean version string, Mathlib package manifest, and eight dependency revisions. Tracked library source trees must be clean. The verifier downloads nothing and changes none of these inputs.

The only application prerequisite is `formal-basins-native`, with source manifest SHA-256:

```text
efc8bc1226fb158341a4626eeafaf5c97b9284da1a2d137de38b7db035cbb230
```

Supply that source bundle and a separately completed successful replay directory containing `replay-record.json` and `modules/`. Follow the native bundle's own instructions to rebuild it. The historical reference replay-record SHA-256 is:

```text
260930d45985dca3d8b7abe88fff1c8c73aa154893d5fa1476b5c76b0b70a79c
```

The replay command requires an explicit `--native-record-sha256`. For an independent native rebuild, use the digest of its separately verified successful record. This selects the accepted record only: all source, object, import, dependency fingerprint, status, axiom and toolchain checks still run. Historical absolute paths in a record are not used to locate inputs.

## Replay

Check package integrity:

```bash
python3 verify.py --verify-package-only
```

Run the fresh additive replay, replacing every placeholder with the corresponding local path or verified digest:

```bash
python3 verify.py \
  --native-bundle /path/to/formal-basins-native \
  --native-build /path/to/verified-native-replay \
  --native-record-sha256 VERIFIED_NATIVE_RECORD_SHA256 \
  --lean-bin /path/to/lean-4.30.0-rc2/bin \
  --mathlib /path/to/mathlib4 \
  --output /path/to/new-raw-occupation-replay
```

The output directory must not already exist. Omit `--output` to create a fresh system temporary directory. The verifier clears inherited Lean import-path and plugin overrides and exposes only fresh application objects, the authenticated native object subset, and the pinned library caches.

The verifier loads its source-inventory helper directly from hash-verified source bytes, bypassing any cached Python bytecode. It reconstructs the endpoint import closure, checks source and import inventories and recursive dependency fingerprints, and authenticates native sources and objects before and after the build. Its compiled constant inventory allows only `propext`, `Classical.choice` and `Quot.sound`. Named and private source declarations are checked against that inventory. Compiler warnings are rejected. Every fresh source, object and log is hashed again before a `PASS` record is written.

The output retains all fresh sources, objects, compiler and kernel logs, the generated audit harness, source inventories, dependency evidence, and the replay record. Individual kernel checks cover the fresh applications against imported dependencies; they do not claim `leanchecker --fresh` over all native or Mathlib dependencies.

## Provenance and licenses

`provenance/source-provenance.json` maps the unchanged sources to the frozen research replay. Its record is retained under `provenance/research-replays/`; source manifests, dependency closure, semantic reviews and replay certificates provide supporting evidence. The portable verifier checks the current package independently of those historical reviews. Portable replay results and their review are documented separately under `recorded/`.

Original local sources and verification scripts retain the MIT license and Lucas Valbuena attribution. The external native prerequisite retains its existing licenses, notices and source-origin records, including Gao and predecessor-derived work. No external source is relicensed here. See `SOURCE-LICENSES.txt` and `LICENSE-MIT`. No compiled caches are distributed with the source bundle.
