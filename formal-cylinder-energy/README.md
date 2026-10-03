# Finite cylinder energy: additive Lean bundle

This bundle proves a uniform first-hit coefficient bound, transports actual cylinder mass across a finite head, and identifies sublinear masked cylinder energy with universal eventual periodicity of positive Collatz orbits.

For an odd target `N`, write `h_K(N) = canonicalRho K N / N`. The finite mask keeps the odd integers `0 < N < 3^K` with no Syracuse return in steps `1,...,K`. Its energy is the finite sum of `h_K(N)^2`. The main endpoint proves

```text
maskedCylinderHeadEnergy K / (K + 1) -> 0
    if and only if
UniversalEventualPeriodicity.
```

The same equivalence holds for the energy on masked targets that have a positive forward ancestor at most `M(K)`, for every real barrier `M(K)` tending to infinity. The complementary energy tends to zero after division by `K+1`, unconditionally. The remaining small-ancestor energy decay is a hypothesis in the criterion. Universal eventual periodicity allows more than one positive cycle, so the equivalence does not establish the Collatz conjecture or cycle uniqueness.

The bundle contains the exact 17-module application import closure of `MaskedEnergyPeriodicityEquivalence`: five first-hit coefficient modules, four finite transport and energy modules, six earlier sublinear-energy implication modules, and two equivalence modules. Sources preserve the bytes of their separately reviewed research replays. The unused reciprocal-budget pair is omitted. The verifier compiles all 17 sources afresh and separately runs `leanchecker` on each, then compiles and kernel-checks the generated whole-module axiom audit. It authenticates and reuses exactly 40 modules from the 51-module `formal-periodic-census` bundle and 1,566 native modules. Mathlib and Lean caches are also reused. This is an additive replay, not a fresh build of the entire upstream closure.

## Main endpoints

All declarations below are in namespace `CollatzCanonical.PeriodicCensusFloor`.

| Source | Declaration |
| --- | --- |
| `GammaFreeFirstHitCoefficient.lean` | `exists_uniform_odd_exact_firstHit_coefficient_bound` |
| `GammaFreeFirstHitCoefficient.lean` | `exists_uniform_odd_masked_cylinder_bound` |
| `CylinderGrowthHeadTransport.lean` | `finite_cylinderGrowthHead_transport` |
| `MaskedCylinderNoSmallAncestorEnergy.lean` | `finite_odd_cylinderHead_mass_bound` |
| `MaskedCylinderNoSmallAncestorEnergy.lean` | `exists_uniform_maskedEnergy_decomposition` |
| `MaskedEnergyBoundaryLimit.lean` | `moving_barrier_noSmallAncestor_energy_tendsto_zero` |
| `MaskedEnergyPeriodicityEquivalence.lean` | `masked_energy_sublinear_iff_universal_eventual_periodicity` |
| `MaskedEnergyPeriodicityEquivalence.lean` | `small_ancestor_energy_sublinear_iff_universal_eventual_periodicity` |

The finite mask includes periodic targets whose Syracuse period exceeds `K`. The first-hit bound applies at each positive exact first-hit depth, including periodic targets. Its transfer to full cylinder density uses the finite no-return condition. The older nonperiodic energy uses the inclusive endpoint `3^K`; the new mask uses the strict endpoint, and the sufficiency proof shows that the omitted endpoint has zero cylinder mass for `K>0`.

The finite mass budget is `2 + 3K + (64/81)^K(1 + 2K)`. It controls the sum of actual `h_K`, not merely a sum of limiting basin densities. Combined with the uniform masked amplitude bound and the native no-small-ancestor basin envelope, it gives the energy decomposition. Exact statements, target hypotheses and quantifier order are in the Lean sources.

## Prerequisites

Use Python 3, Git, Lean 4.30.0-rc2 at commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, and built Mathlib at revision `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. The recorded profile is Linux x86-64. The manifest pins the exact Lean version string, Mathlib package manifest, and eight dependency revisions. Tracked library source trees must be clean. The verifier downloads nothing and changes none of these inputs.

Provide these source bundles and their independently completed replay directories:

| Prerequisite | Pinned source manifest SHA-256 | Reference replay-record SHA-256 |
| --- | --- | --- |
| `formal-basins-native` | `efc8bc1226fb158341a4626eeafaf5c97b9284da1a2d137de38b7db035cbb230` | `260930d45985dca3d8b7abe88fff1c8c73aa154893d5fa1476b5c76b0b70a79c` |
| `formal-periodic-census` | `c0d92d90ad3e6f477a7ccaa7d04d5048677657ae4e25da32b1339877e12e324a` | `0d442ab3f21fe5ff9ec8e30a20e322a5fe058799d089f8e335d4744e1134a37c` |

Each replay directory must contain its successful `replay-record.json` and `modules/`. Follow the prerequisite bundles' own instructions to rebuild them. The periodic-census replay must have used the same native replay supplied to this verifier. For independently rebuilt prerequisites, explicitly pin the successful records with `--native-record-sha256` and `--floor-record-sha256`. Those options change only the accepted record digests; all source, object, import, dependency, status, audit and toolchain checks still run. Historical absolute paths in the records are not used to locate inputs.

## Replay

Check package integrity:

```bash
python3 verify.py --verify-package-only
```

Run the fresh additive replay:

```bash
python3 verify.py \
  --native-bundle /path/to/formal-basins-native \
  --native-build /path/to/verified-native-replay \
  --floor-bundle /path/to/formal-periodic-census \
  --floor-build /path/to/verified-periodic-census-replay \
  --lean-bin /path/to/lean-4.30.0-rc2/bin \
  --mathlib /path/to/mathlib4 \
  --output /path/to/new-cylinder-energy-replay
```

The output directory must not already exist. Omit `--output` to create a fresh system temporary directory. The verifier removes inherited Lean import-path overrides and exposes only fresh application objects, authenticated upstream object subsets, and the pinned library caches.

The verifier reconstructs the endpoint import closure, checks source and import inventories and recursive dependency fingerprints, and authenticates upstream sources and objects before and after the build. It enumerates every compiled application constant, including generated and private constants, and allows only `propext`, `Classical.choice` and `Quot.sound`. Named source declarations are checked against that compiled inventory. Compiler warnings are rejected. Every fresh source, object and log is hashed again before a `PASS` record is written.

The output retains all fresh sources, objects, compiler/kernel logs, the generated audit harness, source inventories, dependency evidence, and the replay record. Per-module kernel checks cover the fresh applications against imported dependencies; they do not claim a `leanchecker --fresh` replay of the entire native or Mathlib closure.

## Provenance and licenses

`provenance/source-provenance.json` maps each unchanged source to its earlier frozen research replay. Those earlier replay records are retained under `provenance/research-replays/`, and semantic reviews and earlier replay certificates are under `recorded/reviews/`. Their historical scope can be broader than this minimal package; the portable verifier reconstructs and checks the current package independently.

Original local sources and verification scripts retain the MIT license and Lucas Valbuena attribution. External prerequisite source bundles retain their existing licenses, notices and source-origin records, including the Gao and predecessor-derived work. No external source is relicensed by this package. See `SOURCE-LICENSES.txt` and `LICENSE-MIT`. No compiled caches are distributed in the source bundle.
