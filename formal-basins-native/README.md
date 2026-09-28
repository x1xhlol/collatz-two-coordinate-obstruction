# Native basin proof bundle

This is the Lean 4.30.0-rc2 development for *Collatz basin densities and canonical traces from first-passage stabilization*. The [claim map](../paper/basin-lean-claims.md) matches the paper's numbered results to exact declarations.

The bundle contains 1602 dependency modules, including 281 local proof modules. The root audit checks 1507 local theorem/lemma declarations, 275 definitions and named instances, and 5 upstream theorem roots. The full imported closure contains both first-passage scales, Mazur's natural-counting theorem, and the separately namespaced predecessor-density theorem.

The density, clock, Green-limit, cylinder-identification, natural-density, and positivity results are connected to those actual inputs. Arbitrary-label theorems retain the passage-invariance assumption stated in the paper. The global sublinearity and eventual-periodicity conditions are proved equivalent; neither condition is proved true. No result here proves the Collatz conjecture.

## Reproduce the check

The recorded build uses Linux x86-64, Lean **4.30.0-rc2** at commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, and mathlib **`5450b53e5ddc75d46418fabb605edbf36bd0beb6`**. All mathlib package revisions and the Lake dependency-manifest hash are pinned in [replay-manifest.json](replay-manifest.json).

Check out that mathlib revision, install its pinned Lean toolchain, and obtain the matching mathlib cache using `lake exe cache get`. Then, from the repository root:

```sh
python3 formal-basins-native/verify_replay.py \
  --mathlib /path/to/pinned/mathlib4 \
  --lean /path/to/lean-4.30.0-rc2/bin/lean \
  --output /new/path/native-basin-build \
  --jobs 3
```

The output directory must not exist. This default command rebuilds every bundled module and the root audit. It uses the pinned mathlib cache; it does not reuse this project's compiled objects. No `.olean` files are distributed in the archive.

The verifier checks source hashes, exact imports, transitive dependency fingerprints, compiler and dependency pins, and the final axiom inventory. Sources are checked again after compilation. Only `propext`, `Classical.choice`, and `Quot.sound` may occur in an audited declaration's logical dependencies. An imported upstream conjecture registry is retained verbatim; its conjecture is not a premise of any audited result.

For an incremental check, `--reuse-record /path/to/replay-record.json` may be repeated. Reuse requires a passing record with matching compiler, mathlib and package pins, the same source and transitive dependency fingerprint, and an object matching its recorded SHA-256. Legacy records must supply their original hash-matching manifest to bind those package pins. Each reused object is copied and checked. The final root audit is always compiled again. `--audit-existing` accepts exactly one such record and checks its complete object closure without copying it.

## Recorded verification

[verification/native-basin-rebuild.json](../verification/native-basin-rebuild.json) is the final joint record. It distinguishes freshly compiled modules from objects reused after exact dependency validation. The package also retains the independent fresh replays of both upstream scale namespaces and the predecessor closure. The combined check does not treat those separately checked namespaces as interchangeable.

The second-scale source changes `taoAlpha` to `2001/2000` and retains the real-threshold rate theorem. Its external modules are renamed under `Erdos1135SecondScale`; corresponding local clock and atom modules are also renamed. Both numerical alpha definitions are checked inside the final root audit. The predecessor package uses `Erdos1135Predecessor` and `FormalConjecturesPredecessor`, since its pinned baseline differs from the first-passage package. The source transformations and original hashes are recorded under [provenance](provenance).

Every namespace-modified imported file carries a modification notice. [source-change-notices.json](provenance/source-change-notices.json) records each exact added header and the hashes before and after it. The earlier namespace maps describe the source before those headers; removing exactly the recorded header recovers those bytes. The final manifest and replay cover the distributed files including their notices.

## Attribution and licenses

Tao's first-passage theorem and stationary Syracuse law are the mathematical inputs credited in the paper. Mazur's formal sources and additional natural-counting and predecessor theorems are credited separately. The original local development is MIT licensed; the imported formal sources retain their own licenses and notices. See [SOURCE-LICENSES.md](SOURCE-LICENSES.md), [LICENSE-MIT](LICENSE-MIT), and the retained upstream notices. The source provenance is not a grant to redistribute any external manuscript.
