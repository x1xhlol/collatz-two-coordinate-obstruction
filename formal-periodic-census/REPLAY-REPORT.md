# Completed additive replay

The portable verifier completed successfully on 3 October 2026. It freshly compiled all 51 bundled application modules and ran `leanchecker` separately on each one. The complete compiled-constant audit covered 1,697 constants, including 89 private constants. Every axiom closure was a subset of `propext`, `Classical.choice` and `Quot.sound`.

| Source group | Fresh application modules | Audited constants | Private constants |
| --- | ---: | ---: | ---: |
| Gao compatibility closure | 26 | 1,458 | 89 |
| Bounded-seed extension | 14 | 124 | 0 |
| Periodic-census extension | 11 | 115 | 0 |
| Total | 51 | 1,697 | 89 |

The generated all-constant audit harness also compiled successfully. The existing `Tejonas` deprecation warning was recorded; no other warning or proof error occurred.

All 1,458 required native source/object/dependency-fingerprint triples matched the pinned native manifest and successful prior replay record before and after this run. The native and Mathlib/Lean caches were reused. This result is a fresh replay of the 51 supplied application modules against authenticated dependencies; it is not a fresh rebuild or empty-kernel replay of the whole native/Mathlib closure.

The principal evidence is:

- [recorded/replay-record.json](recorded/replay-record.json): complete fresh build, kernel, constant, source and dependency record. SHA-256 `0d442ab3f21fe5ff9ec8e30a20e322a5fe058799d089f8e335d4744e1134a37c`.
- [recorded/logs](recorded/logs): all 52 compiler logs, including the generated audit harness, and all 51 application kernel logs.
- [recorded/audit-source](recorded/audit-source): the exact compiled all-constant audit harness.
- [bundle-manifest.json](bundle-manifest.json): the core source/script/license manifest used for the run. SHA-256 `c0d92d90ad3e6f477a7ccaa7d04d5048677657ae4e25da32b1339877e12e324a`; its unchanged snapshot is also in `recorded/run-bundle-manifest.json`.
- [recorded/reviews/INDEPENDENT-PORTABLE-VERIFIER-REVIEW.txt](recorded/reviews/INDEPENDENT-PORTABLE-VERIFIER-REVIEW.txt): independent static and targeted verifier/provenance review. It is separate from the runtime replay.
- [recorded/reviews/portable-bundle-negative-controls.json](recorded/reviews/portable-bundle-negative-controls.json): the verifier rejected a wrong native record pin and an altered source in a temporary copy. The independent review also checked rejection of an incomplete expected native closure.

The semantic reviews in `recorded/reviews/` identify their own source and authorship scope. In particular, the full seven-module semantic review expressly discloses that its author also wrote the two Gao/variation bridge modules; it does not claim an independent authorship review of those two modules.

Two earlier research records are preserved without modification at the bundle root because the paper and claim map cite them:

- [fresh-replay-record.json](fresh-replay-record.json), SHA-256 `2f1b3ef7dc4b9fa2ebf500a7265b4d702767ada6a441244c58bdd79d4d4a3b94`: the earlier fresh ten-module replay against reused bounded-seed/Gao/native dependencies.
- [ordinary-floor-replay.json](ordinary-floor-replay.json), SHA-256 `fe788e086f467c45ff597656fd7cb7940d0685a18cde8a06232a38faf59b3264`: the additional ordinary-map module replay against that ten-module build.

Their exact matching logs and generated audit sources are under `recorded/original-fresh-replay/` and `recorded/original-ordinary-replay/`. Historical paths inside records describe the runs that produced them and are not runtime defaults. The newer portable replay rebuilds all 51 supplied sources instead of reusing the bounded-seed and Gao application objects.

The core manifest was held unchanged during the completed run. The completion report and recorded evidence were added afterward. `SHA256SUMS.json` binds the complete delivered package, including those additional evidence files; it excludes only itself and transient Python cache files. No native bundle file was changed, and no compiled cache is distributed in this source package.
