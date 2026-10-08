# Source changes and attribution

This material accompanies the frozen `formal-growing-deficit` source bundle. Its paths are relative to that bundle's root. It is separate release provenance and does not modify the frozen proof inputs.

The 357 source modules comprise 214 unchanged upstream files, 67 upstream files adapted for Lean 4.35 compatibility, and 76 original local files. `source-change-map.json` records each file's original and distributed SHA-256 hashes, original repository and revision when applicable, license, attribution, and retained license records.

The 150 `Erdos1135` and `FormalConjectures` files are compared with Git blobs at `x1xhlol/collatz-two-coordinate-obstruction` commit `9ccf356cb887f6862feb6d40215995dc133e0254`. Each original hash also matches the separately retained manifest for Lech Mazur's *Natural-Density Almost-Bounded Collatz Orbits in Logarithmic Time* companion, package and source-rights commit `ca3dd0d63920411213403092aecc6946619eb082`. Of these files, 83 are unchanged and 67 have the compatibility changes in `lean-4.35-compatibility.patch`. The map retains the publication URL and the public Git location of that upstream manifest. It does not invent a Git repository URL for the original source distribution.

The 131 `ArithmeticHeights` and `DiophantineApproximation` files are unchanged Git blobs from Ralf Stephan's Subspace-Theorems commit `d7a11cb1dcab3883fd1008db27a8382c95455b0a`. The 76 original local files have no claimed upstream source hash.

The compatibility changes were made by Lucas Valbuena on 7 October 2026. The unified patch exposes the exact edits to theorem proofs, elaboration details, and compatibility syntax. It uses `a/source/...` and `b/source/...` paths. Applying it with `patch -p1` to the 67 recorded original files reproduces all 67 distributed files byte for byte; `patch-roundtrip-check.json` records that check. The Lean replay and semantic review are separate evidence.

The native formalization retains its Apache 2.0 license and Advameg notice. The Formal Conjectures files retain their authors' copyright and Apache 2.0 headers. The Subspace sources retain Ralf Stephan's copyright and Apache 2.0 license. Original local work uses Lucas Valbuena's MIT license. The map gives the hashes of the exact license and notice files included in the bundle; these rights are not replaced by the local MIT license.
