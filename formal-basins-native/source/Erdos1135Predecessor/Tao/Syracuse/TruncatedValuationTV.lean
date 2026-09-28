/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Probability.FullL1
import Erdos1135Predecessor.Tao.Syracuse.TruncatedValuationPacking

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

noncomputable def shortValuationLists (n M : ℕ) : Finset (List ℕ+) := by
  classical
  exact Finset.univ.image
    (BoundedValuationTuple.toList (n := n) (M := M))

theorem mem_shortValuationLists_iff {n M : ℕ} {as : List ℕ+} :
    as ∈ shortValuationLists n M ↔
      ∃ v : BoundedValuationTuple n M,
        as = BoundedValuationTuple.toList v := by
  classical
  simp [shortValuationLists, eq_comm]

end

end Tao

end Erdos1135Predecessor
