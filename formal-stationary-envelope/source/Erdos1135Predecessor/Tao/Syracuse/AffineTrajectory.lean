/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Syracuse.AffineEnvelope

namespace Erdos1135Predecessor

namespace Tao

theorem syracuse_iterate_odd_trajectory
    (n N : ℕ) (hN : Odd N) : Odd ((syracuse^[n]) N) := by
  induction n generalizing N with
  | zero => simpa using hN
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (syracuse N) (syracuse_odd N)

theorem syracuseValuationPNatList_add
    (m n N : ℕ) (hN : Odd N) :
    syracuseValuationPNatList (m + n) N hN =
      syracuseValuationPNatList m N hN ++
        syracuseValuationPNatList n ((syracuse^[m]) N)
          (syracuse_iterate_odd_trajectory m N hN) := by
  induction m generalizing N with
  | zero =>
      simp [syracuseValuationPNatList]
  | succ m ih =>
      rw [Nat.succ_add]
      simp only [syracuseValuationPNatList, List.cons_append]
      rw [ih (syracuse N) (syracuse_odd N)]
      congr 2

theorem taoTupleWeight_append_trajectory (xs ys : List ℕ+) :
    taoTupleWeight (xs ++ ys) = taoTupleWeight xs + taoTupleWeight ys := by
  simp [taoTupleWeight]

end Tao

end Erdos1135Predecessor
