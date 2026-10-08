# Growing-deficit Fourier decay: Lean sources

This directory contains the complete application and Subspace Theorem source closure for three entry modules:

- `TrapUnconditionalDeficit`: primitive Fourier decay for the affine geometric-source model with a growing conductor deficit, uniformly in the affine seed and unit-modulus terminal exponent phase.
- `TrapMicrocanonicalMassFloor`: faster-than-any-power conditional Fourier decay when the conductor deficit is at most `k^β`, with `0 < β < 1`, and the conditioning slice has polynomially bounded reciprocal mass.
- `TrapCentralMicrocanonical`: the corresponding conditional theorem on the exact central slice `S_k = 2k`, using the proved geometric exponent-sum formula and a central binomial lower bound.

These are statements about the specified random affine source. They do not prove the Collatz conjecture or a natural-density statement about deterministic trajectories.

## Reproduce

The checked recipe targets Linux x86_64 and requires Python 3.11 or later, Git, `tar`, `zstd`, network access, and several gigabytes of free disk space. Run from this directory:

```sh
python3 scripts/setup.py
python3 scripts/replay.py --toolchain .toolchain/lean-4.35.0-rc3-linux
python3 scripts/replay.py --toolchain .toolchain/lean-4.35.0-rc3-linux --verify-only
```

To reuse an existing exact official installation, pass its directory to both scripts with `--toolchain`. Its compiler, checker, Lake executable, and runtime hashes must match `dependency-pins.json`.

Setup fetches the official Lean 4.35.0-rc3 distribution and the nine exact Git revisions in `lake-manifest.json`, retrieves their Mathlib cache, and explicitly builds the external `Cli` and `Mathlib.Analysis.Normed.Group.Tannery` targets. The replay compiles all 357 bundled source modules into a new `.replay/modules` directory and runs the official `leanchecker` after every compilation. It uses no prebuilt application or Subspace objects. A final generated audit directly imports all bundled modules with private implementation data, checks every constant listed in each module header, and allows only `propext`, `Classical.choice`, and `Quot.sound`. The runner also checks every named source declaration against this enumeration.

There are 716 compile/check commands, including the final audit. The 131 vendored Subspace modules retain their upstream option profile; all modules treat warnings as errors. The application and Subspace sources are rebuilt, while the external Mathlib, package, and standard-library objects are hash-inventoried before and after the run. Those external libraries are not rebuilt by this recipe.

The machine-readable result is `.replay/replay-record.json`, with command transcripts under `.replay/logs`. Paths in the record use `BUNDLE/` and `TOOLCHAIN/` prefixes, so verification does not depend on the original working directory. `--verify-only` checks inputs, package revisions, all replay artifacts and logs, import resolution, and the complete audit without compiling again. For a new full replay, move the existing `.replay` directory aside first.

The ordinary `lake build` configuration is included for navigation and editing. The evidence-producing command is `scripts/replay.py`, whose isolated search path excludes Lake's application output directory.

The release validation protocol consists of one full replay in the isolated bundle and a second-path check that authenticates the copied record and compiles the entry modules against the copied fresh objects. It does not require a second full build. Completed validation evidence is supplied separately from this reproduction recipe.

## Provenance and licenses

`source-manifest.json` identifies every bundled source by hash, module, import list, option profile, and source declaration inventory. `dependency-pins.json` gives external package, compiler, and Subspace repository pins. `provenance/baseline-evidence.json` records the antecedent checked packets by hash; the portable replay establishes the new source build independently of those packets.

See `THIRD_PARTY_NOTICES.md` and `licenses/`. The bundle includes material under more than one license; the local author's MIT license does not replace the licenses of incorporated projects.
