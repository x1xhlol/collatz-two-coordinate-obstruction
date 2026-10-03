# Source licenses and attribution

The original local Lean modules, verifier, and documentation in this bundle use the repository's MIT license. The adapted parity-vector code retains M. Sharpe's MIT attribution and license header. Existing copyright and license headers remain in all source files.

The following imported sources are excluded from that blanket MIT scope:

| Source paths | Attribution and retained license records |
| --- | --- |
| `source/Erdos1135/`, `source/Erdos1135SecondScale/`, and `source/FormalConjectures/` | Mazur's pinned Tao/natural-density formalization and its upstream sources. See `LICENSE-UPSTREAM`, `NOTICE-UPSTREAM`, and retained file headers. The second-scale changes and namespace substitution do not change those rights. |
| `source/Erdos1135Predecessor/`, `source/FormalConjecturesPredecessor/`, and `source/CollatzPredecessorDensity.lean` | Lech Mazur's separately released predecessor extension and its pinned baseline. See `provenance/predecessor/LICENSE`, `NOTICE`, `BASELINE_LICENSE`, `BASELINE_NOTICE`, `RIGHTS.md`, and `license.json`. These Apache-2.0 grants and notices are retained separately from the first-passage package. |

The source archive URLs, checksums, package revisions, and namespace transformations are retained in the manifest and provenance files. Mathlib and its packages are external dependencies with their own licenses; their compiled caches are not distributed here.

The external papers and images are outside the predecessor package's formal-source license. They are cited, not reproduced. The manuscript authored in this repository remain under the separate CC BY 4.0 license in `paper/LICENSE`.
