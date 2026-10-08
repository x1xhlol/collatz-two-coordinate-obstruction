# Source provenance and licenses

The source manifest preserves the exact staged bytes. Source-file copyright and license headers remain in place.

- The local application and replay machinery by Lucas Valbuena are provided under the MIT license, reproduced in `licenses/own/LICENSE`.
- The incorporated `Erdos1135` formalization derives from Advameg's Collatz formalization and retains its Apache 2.0 license and notice. The applicable files are under `source/Erdos1135/`; see the corresponding license and notice files in `licenses/`.
- The two incorporated `FormalConjectures` compatibility sources retain their original Apache 2.0 headers and attribution. The license is reproduced in `licenses/`.
- The 131 files under `source/ArithmeticHeights/` and `source/DiophantineApproximation/` are copied without source changes from Ralf Stephan's Subspace-Theorems repository at commit `d7a11cb1dcab3883fd1008db27a8382c95455b0a`. They retain their Apache 2.0 headers; the license is reproduced in `licenses/`.
- Mathlib and its eight pinned package dependencies are fetched by setup. Their available root license and notice texts are reproduced under `licenses/packages/`; their exact source revisions are in `dependency-pins.json` and `lake-manifest.json`.

The compiler distribution is fetched from the official Lean release and checked against the archive and runtime hashes in `dependency-pins.json`. It is not redistributed in this source bundle.
