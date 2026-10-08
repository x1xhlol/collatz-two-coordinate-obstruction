/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Prop78Case1White

namespace Erdos1135Predecessor

namespace Tao

theorem taoSection7QmBoundary_of_horizontalAdvance
    {J m r : ℕ} {p q : TaoSection7RenewalPoint}
    (hp : taoSection7QmBoundary J m p)
    (hjq : (q.j : ℕ) = (p.j : ℕ) + r)
    (hr : r < m) :
    taoSection7QmBoundary J (m - r) q := by
  unfold taoSection7QmBoundary at *
  omega

end Tao

end Erdos1135Predecessor
