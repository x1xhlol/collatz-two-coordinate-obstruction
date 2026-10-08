# Canonical Syracuse density: sharp Lp range and quadratic cylinder energy

This source bundle contains the complete internal Lean dependency closure for a nonnegative density of the canonical random Syracuse law on the 3-adic integers. The density has integral one and, for every real `p ≥ 1`, belongs to `Lᵖ` exactly when `p < 2`. The bundle also proves that the depth-`k` cylinder energy and the squared `L²` norm of its finite cylinder density are at most `32 k²` for `k ≥ 1`.

The result concerns this random 3-adic law. It makes no conclusion about convergence of individual integer Collatz orbits.

The four designated declarations are:

- `Erdos1135.Tao.canonicalSyracuseMeasure_has_sharp_lp_density`
- `Erdos1135.Tao.canonicalHaarDensity_memLp_iff_lt_two`
- `CollatzCylinderPacking.Arithmetic.FairEnergy.canonical_cylinder_energy_le_thirtytwo_quadratic`
- `Erdos1135.Tao.canonicalPadicRho_sq_integral_le_thirtytwo_quadratic`

## Reproduce

Use Linux x86_64 with Python 3.9 or later and Git. Fresh dependency installation also requires GNU tar, zstd, curl 7.81 or later, and 15 GiB of free space. Git, tar, zstd and curl must be available in `/usr/bin` or `/bin`; setup reuses its own Python interpreter for the preflight. All commands below run from the bundle directory.

The setup helper downloads the checksum-pinned official Lean 4.30.0-rc2 archive, checks out Mathlib commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6` and all eight pinned package revisions, obtains their official compiled caches, and runs the full preflight:

```sh
python3 scripts/setup.py
```

The official toolchain archive URL, byte count and SHA-256 are recorded in `dependency-pins.json`. Setup places the toolchain in `.external/lean-4.30.0-rc2-linux`, Mathlib in `.external/mathlib4`, and a fresh download cache in `.external/mathlib-cache`. It clears inherited `MATHLIB_CACHE_*` settings and sets the cache directory explicitly. It records the resolved toolchain and Mathlib paths in `setup-result.json`. `--external-dir /path/to/new/storage` chooses another installation location. A partially created checkout is preserved if setup fails; choose a fresh directory for another attempt.

Exact existing installations can instead be reused read-only:

```sh
python3 scripts/setup.py --toolchain /path/to/lean-4.30.0-rc2-linux --mathlib /path/to/mathlib4
```

The supplied Mathlib checkout must contain the pinned `.lake/packages` checkouts and compiled caches. Setup never changes a Mathlib installation supplied with `--mathlib`.

For the default fresh setup paths, run:

```sh
python3 scripts/replay.py \
  --expected-manifest-sha256 96500e070b6dcdc730975638029d0f7aa31ba40db2ecb46282f76c91175af5b9 \
  --toolchain .external/lean-4.30.0-rc2-linux \
  --mathlib .external/mathlib4 \
  --run
```

For reused installations, substitute their paths in both commands. The replay requires that `.replay` does not exist; it preserves completed commands, logs and artifacts if a later command fails. Reproducing again therefore requires a separate source-bundle directory or explicitly archiving the prior `.replay` directory first.

After a successful run, verify the complete record from a new process:

```sh
python3 scripts/replay.py \
  --expected-manifest-sha256 96500e070b6dcdc730975638029d0f7aa31ba40db2ecb46282f76c91175af5b9 \
  --toolchain .external/lean-4.30.0-rc2-linux \
  --mathlib .external/mathlib4 \
  --verify-only
```

`--preflight` authenticates all inputs without compiling the internal sources. `--verify-only` authenticates an existing completed replay; it does not recompile the sources.

## What the replay checks

`source-manifest.json` fixes 362 source modules, their exact dependency closure and topological order, their hashes, 4,911 named source declarations, 265 private source declarations and 23 anonymous source instances. The manifest also pins the runner, inventory helper, dependency pins and required provenance files. Compilation uses only the fresh internal output directory and the separately fingerprinted external libraries.

Every internal module is freshly compiled with `-j1 -DwarningAsError=true` and then replayed by the official `leanchecker`. A generated audit imports all 362 modules and checks every internal module header declaration, including generated and encoded private declarations, for axiom dependencies. It also enumerates the checked environment's internal owner declarations and requires equality with the complete header-name union. The only permitted axioms are Lean's standard `propext`, `Classical.choice` and `Quot.sound`. The audit itself is compiled and kernel checked, for 726 planned successful commands in total.

The runner persists a complete input state before the first compilation and again after the audit. It authenticates the clean Git revisions of Mathlib and all eight dependencies, checks official Lean executable/runtime hashes, and inventories every available external `.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir`, `.ir.sig` and `.so` file. Both states must agree. `--verify-only` repeats this authentication and checks the recorded commands, logs, compiled artifact hashes, import resolutions and complete audit.

External Mathlib, dependency and toolchain compiled libraries are a stated trust boundary: this replay inventories and reuses them; it does not rebuild or independently kernel-check their complete source closures. The cache fingerprints establish the exact objects used and their stability during this run; they do not establish that each cached object was built from the adjacent pinned source revision. Fresh setup obtains those caches before the replay starts freezing input state. The fresh download and cache preparation branch has not been exercised for the accompanying replay.

The source bundle and replay records use bundle-relative paths and symbolic `BUNDLE`, `TOOLCHAIN` and `MATHLIB` roots. No original research-directory path is needed. `.preparation-internal` contains preparation metadata and is excluded from distribution.

## Provenance

The source inventory comprises 18 new proof modules, 317 unchanged modules from the retained public native bundle, 26 previously retained private proof modules, and one reviewed source shard. `provenance/source-origins.json` records their origin groups and hashes. Additional license and provenance records are in `licenses/` and `provenance/`.

The reviewed `FormalConjectures/Wikipedia/CollatzConjecture.lean` shard retains the original header, imports, namespace and `collatzStep` definition. Its recorded patch removes an unrelated unproved conjecture declaration from that imported source. The original source is unchanged; the original and shard hashes and exact patch are preserved in `provenance/wikipedia-shard.json` and `provenance/wikipedia-shard.patch`.

Additional documentation, bootstrap code, license appendices and run evidence are sealed separately from the frozen proof execution manifest.
