# Independent statement review

**PASS.** The three public theorems in `FullTwoCoordinate.lean` match the
theorem stated in [the original obstruction note](../two-coordinate-affine-obstruction.md).
This is an independent review of the statement, definitions, and proof
coverage. It is **not a Lean kernel-check report** and does not replace
the separate fresh compilation and axiom audit.

`Aff2` is an affine map on two real coordinates. For each of the seven
symbols `A B C D E F G`, `Admissible` requires every matrix entry and
both offsets to be nonnegative, and the matrix entry `(0,0)` to be at
least one. `Affine.comp X Y` represents `X ∘ Y`, so the leftmost symbol
is outermost. `X.Weak Y` requires the matrix and offset of `X` to dominate
those of `Y` entrywise. These definitions agree with the original note.

The weak-rule structures and zero-gap conclusions contain exactly the
following eleven pairs, with the displayed direction preserved:

| Forward | Word reversal |
|---|---|
| `ad → d` | `da → d` |
| `bd → gd` | `db → dg` |
| `ae → ea` | `ea → ae` |
| `af → eb` | `fa → be` |
| `ag → fa` | `ga → af` |
| `be → fb` | `eb → bf` |
| `bf → ga` | `fb → ag` |
| `bg → gb` | `gb → bg` |
| `ce → cb` | `ec → bc` |
| `cf → caa` | `fc → aac` |
| `cg → cab` | `gc → bac` |

`forward_all_gaps_zero` and `reversed_all_gaps_zero` each assume all
seven admissibility conditions and the corresponding eleven weak rules.
They conclude equality of the first offset, at index `0`, on both sides
of every rule. `full_two_coordinate_obstruction` conjoins these two
implications; it does not require both orientations to hold simultaneously.
No hypothesis has been added for triangularity, commutation, nonsingularity,
boundary shape, positive secondary entries, rationality, or a coefficient
or intermediate-result bound. In particular, `C` and `D` remain arbitrary
admissible affine maps.

The reduction covers every matrix case. If both offdiagonal entries of
the aggregate digit matrix are positive, the weak swap inequalities become
equalities. The proof then splits on `det F = 0`. For `det F ≠ 0`, the
determinant lemma gives either `det A = det B = 0` or nonsingularity of
all five digit matrices. Each branch is contradicted by its corresponding
boundary theorem; the latter two branches also cover both `A = B` and
`A ≠ B`. The resulting common triangular orientation and unit first
diagonals feed the upper and lower affine proofs. The reversed matrix
argument transposes matrix parts only. Its affine conclusion uses the
separate reversed lower proof and the normalized upper product-reversal
construction, retaining affine offsets.

The conclusion excludes a positive first-offset gap in this precise
two-coordinate, full-context interpretation class. It does not assert
equality of the complete affine maps or exclude higher dimensions,
interpretations with smaller first diagonal entries, other orders,
nonlinear interpretations, or certificates for proper subsystems. It
neither proves the Collatz conjecture nor supplies a cycle or divergent
positive orbit.

The review applies to the following SHA-256 snapshots. The first three
files fix the final statement and both rule/gap definitions; the additional
files fix the underlying affine semantics, reduction, and original scope.

| File | SHA-256 |
|---|---|
| `FullTwoCoordinate.lean` | `429785555eecec277248380fe0c2e767c8c7303cf0e2712de29878dda2bd29a0` |
| `FullTwoBasic.lean` | `38d6e8029e7fff5a948aca33ad661b28ed232ac527c3627882eac397cf00780e` |
| `ReversedRealNormalization.lean` | `947bb86b18f46ba0f150437c4a334c79a18b89bbc73b5855eff9381237b23761` |
| `ReversedBinaryPowerClosure.lean` | `6f448bb1475e4214a10d4acdac8835d526a559d166c93acfd910e39bca23f281` |
| `FullTwoMatrixReduction.lean` | `967201d0509caa1989310f71fa56e2b10209c7cfb8f8ef64ea0e841b81f80e83` |
| `../two-coordinate-affine-obstruction.md` | `648cd58b50b75aadf5d49bf430a69124b6ea846e519d54dabd3103f87d167717` |
