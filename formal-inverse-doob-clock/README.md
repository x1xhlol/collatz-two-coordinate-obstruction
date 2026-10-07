# Actual inverse Doob height clock: additive Lean bundle

Let `Y_k` be the odd inverse path started at `n` under the actual continuing Doob law defined in `ActualInverseDoobLaw.lean`. The main theorem states:

```text
If n > 0, n is odd, n is not divisible by 3,
and no positive shortcut iterate returns n to itself, then
  log(Y_k) / k -> log(4/3) almost surely under pathLaw n.
```

The nonperiodicity hypothesis concerns the root itself; the root may later enter a cycle. The actual potential retains the Green cycle factor, and row normalization is proved using the actual harmonic identity and its vanishing dyadic boundary term. The law is a probability measure on actual inverse trajectories.

The proof identifies fixed-prefix probabilities with normalized odd logarithmic source weights, proves total-variation convergence on each fixed prefix space, and transfers a shared source clock event to finitely many inverse last-visit clocks. Raising the bottom scale removes the failure probability without changing the limiting event. Countably many interlaced grids and deterministic inverse growth then give the height limit. It assumes no uniform source convergence rate or uniform integrability.

The endpoint is `CollatzCylinderPacking.Arithmetic.InverseDoob.actual_inverse_height_clock_ae`. The packet does not prove convergence of expected occupation, a raw occupation upper bound, a periodic killed-law theorem, universal eventual periodicity, exclusion of additional positive cycles, or the Collatz conjecture.

All 26 Lean source modules preserve the reviewed research bytes, including helper declarations. They form the endpoint's complete application import closure. The portable topological build order may differ from the research replay order.

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
  --output /path/to/new-inverse-doob-clock-replay
```

The output directory must not exist. Omitting `--output` creates a fresh temporary directory. The verifier compiles all 26 supplied sources and a generated all-constant audit, then kernel-checks each unit with `leanchecker`. It exposes exactly 1496 authenticated native objects and 4 authenticated raw-occupation objects, plus pinned Lean/Mathlib caches. It does not expose live research object directories or rebuild unchanged upstream libraries.

The source-inventory helper is loaded directly from hash-verified bytes, bypassing cached Python bytecode. The verifier reconstructs the full dependency closure and recursive fingerprints, verifies source inventories, authenticates upstream inputs before and after replay, and rejects compiler and kernel warnings. Every generated or private application constant is included in the compiled audit; only `propext`, `Classical.choice`, and `Quot.sound` are allowed. All copied sources, fresh objects and logs are rehashed before `PASS` is written.

The output retains sources, objects, compiler/kernel logs, the audit harness, source inventories, accepted dependency record pins, and the replay record. This is an additive replay against authenticated dependencies, not `leanchecker --fresh` over the full native and Mathlib trees.

## Evidence and licenses

`provenance/source-provenance.json` binds every unchanged source to the frozen research manifest and replay record. Historical research drivers are preserved as provenance, not as portable entrypoints. Research reviews are retained under `recorded/reviews/`; their original scope and authorship remain. Portable replay evidence and negative controls are recorded separately after execution.

Local source, verifier, helper, and documentation retain the MIT license and Lucas Valbuena attribution. External native and raw prerequisites retain their own source-origin records, notices, and licenses. No dependency is relicensed here, and no compiled caches are distributed. See `SOURCE-LICENSES.txt` and `LICENSE-MIT`.
