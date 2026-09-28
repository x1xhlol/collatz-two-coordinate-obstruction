/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Prop78Case2EndpointSplit
import Erdos1135Predecessor.Tao.Renewal.Prop78Case2Geometry

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

theorem taoSection7SourceActualQ_relativeEndpoint_le_case1InvPow_mul_qmPrev
    {n A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    {start : TaoSection7RenewalPoint} {r : ℕ+} {ell : ℤ}
    (hstart : taoSection7QmBoundary (n / 2) m start) :
    taoSection7SourceActualQ n xi epsilon
        (lemma77RenewalPointOfRelativeEndpoint start ((r : ℕ), ell)) ≤
      taoSection7Case1InvPow A m r *
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
  let h : TaoSection7RenewalPoint := { j := r, l := ell }
  have habs :
      lemma77RenewalPointOfRelativeEndpoint start ((r : ℕ), ell) =
        start + h := by
    ext
    · apply PNat.eq
      simp [h]
    · simp [h]
  rw [habs]
  simpa [h] using
    (taoSection7SourceActualQ_add_hold_le_case1InvPow_mul_qmPrev
      (n := n) (A := A) (m := m) (xi := xi)
      (epsilon := epsilon) hepsilon hstart h)

end

end Tao

end Erdos1135Predecessor
