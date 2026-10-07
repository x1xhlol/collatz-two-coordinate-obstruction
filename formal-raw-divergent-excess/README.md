# Raw occupation excess from an injective orbit: additive Lean bundle

Write `D_u = actualFirstHitDensity u`, `W_u = wholeOrbitCorrection u`, and `ell = log(4/3)`. For an odd root `u` whose shortcut forward orbit is injective, define

```text
E(u) = D_u / (W_u * log(3/2)).
```

The main theorem states:

```text
For every real b < 1/ell + E(u), eventually over natural R,
  b <= (sum over positive odd N <= R of D_N) / log R.
```

If `u` is also not divisible by 3, then `E(u) > 0`, so the eventual lower bound is strictly above the descent-clock baseline. The proof combines residual source occupation with a disjoint logarithmic forward prefix. Every source-mean and prefix-rate input is discharged in the endpoint theorem.

The endpoints are `CollatzCanonical.RawOccupation.DivergentExcess.actual_raw_occupation_divergent_eventual_lower` and `actual_raw_occupation_strict_baseline_excess_of_unit`. The injective-orbit hypothesis is explicit; the packet does not assert that such an orbit exists. It supplies no raw occupation upper bound, uniform integrability, orbit classification, cycle exclusion, or proof of the Collatz conjecture.

All 8 Lean source modules preserve the reviewed research bytes, including helper declarations. They form the endpoint's complete application import closure. The portable topological build order may differ from the research replay order.

## Prerequisites

Use Python 3, Git, Lean 4.30.0-rc2 at commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, and built Mathlib at revision `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. The recorded profile is Linux x86-64. The manifest pins the exact Lean version string, Mathlib package manifest, and eight package revisions. Tracked library source trees must be clean. The verifier downloads nothing and changes none of these inputs.

Two application prerequisites are required:

| Bundle | Pinned manifest SHA-256 | Historical accepted replay record SHA-256 |
| --- | --- | --- |
| `formal-basins-native` | `efc8bc1226fb158341a4626eeafaf5c97b9284da1a2d137de38b7db035cbb230` | `260930d45985dca3d8b7abe88fff1c8c73aa154893d5fa1476b5c76b0b70a79c` |
| `formal-raw-occupation` | `e7d5e2c19b0a1ef95151e2962750c99665f28d67ca38996ee5eead06e290e6ed` | `739e2c98cbc0632b5d889b13249e66b03427cb70a36a484aef25107f196daf00` |

Supply the source bundles and separately completed successful replay directories. The raw dependency must be a portable public-bundle replay, not the legacy research replay. Both record digests are explicit required arguments. For independent rebuilds, supply the digests of the separately verified records; the raw replay must identify the same accepted native record. Changing these arguments does not bypass source, object, import, fingerprint, status, axiom, or toolchain checks. Historical paths inside records are not used to locate inputs.

## Replay

Check package integrity:

```bash
python3 verify.py --verify-package-only
```

Run the fresh additive replay with local paths and verified digests:

```bash
python3 verify.py \
  --native-bundle /path/to/formal-basins-native \
  --native-build /path/to/verified-native-replay \
  --native-record-sha256 VERIFIED_NATIVE_RECORD_SHA256 \
  --raw-bundle /path/to/formal-raw-occupation \
  --raw-build /path/to/verified-portable-raw-replay \
  --raw-record-sha256 VERIFIED_RAW_RECORD_SHA256 \
  --lean-bin /path/to/lean-4.30.0-rc2/bin \
  --mathlib /path/to/mathlib4 \
  --output /path/to/new-raw-divergent-excess-replay
```

The output directory must not exist. Omitting `--output` creates a fresh temporary directory. The verifier compiles all 8 supplied sources and a generated all-constant audit, then kernel-checks each unit with `leanchecker`. It exposes exactly 1528 authenticated native objects and 15 authenticated raw-occupation objects, plus pinned Lean/Mathlib caches. It does not expose live research object directories or rebuild unchanged upstream libraries.

The source-inventory helper is loaded directly from hash-verified bytes, bypassing cached Python bytecode. The verifier reconstructs the full dependency closure and recursive fingerprints, verifies source inventories, authenticates upstream inputs before and after replay, and rejects compiler and kernel warnings. Every generated or private application constant is included in the compiled audit; only `propext`, `Classical.choice`, and `Quot.sound` are allowed. All copied sources, fresh objects and logs are rehashed before `PASS` is written.

The output retains sources, objects, compiler/kernel logs, the audit harness, source inventories, accepted dependency record pins, and the replay record. This is an additive replay against authenticated dependencies, not `leanchecker --fresh` over the full native and Mathlib trees.

## Evidence and licenses

`provenance/source-provenance.json` binds every unchanged source to the frozen research manifest and replay record. Historical research drivers are preserved as provenance, not as portable entrypoints. Research reviews are retained under `recorded/reviews/`; their original scope and authorship remain. Portable replay evidence and negative controls are recorded separately after execution.

Local source, verifier, helper, and documentation retain the MIT license and Lucas Valbuena attribution. External native and raw prerequisites retain their own source-origin records, notices, and licenses. No dependency is relicensed here, and no compiled caches are distributed. See `SOURCE-LICENSES.txt` and `LICENSE-MIT`.
