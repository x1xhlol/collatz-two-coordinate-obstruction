/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Syracuse.CollatzBridge
import Erdos1135Predecessor.Tao.Syracuse.ParityBridge

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

theorem collatz_iterate_syracuseValuationTime
    (n M : ℕ) (hM : Odd M) :
    (collatzStep^[n +
      taoTupleWeight (syracuseValuationPNatList n M hM)]) M =
        (syracuse^[n]) M := by
  induction n generalizing M with
  | zero =>
      simp [syracuseValuationPNatList, taoTupleWeight]
  | succ n ih =>
      let a : ℕ := syracuseExponent M
      let W : ℕ := taoTupleWeight
        (syracuseValuationPNatList n (syracuse M) (syracuse_odd M))
      have htime :
          n + 1 + (a + W) = (n + W) + (a + 1) := by omega
      simp only [syracuseValuationPNatList, taoTupleWeight,
        Function.iterate_succ_apply]
      change (collatzStep^[n + 1 + (a + W)]) M =
        (syracuse^[n]) (syracuse M)
      rw [htime, Function.iterate_add_apply]
      rw [collatz_iterate_syracuse_block hM]
      exact ih (syracuse M) (syracuse_odd M)

end

end Tao

end Erdos1135Predecessor
