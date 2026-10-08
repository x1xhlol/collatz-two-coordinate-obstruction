/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.GeometryBridge
import Erdos1135Predecessor.Tao.Renewal.Prop78Case3TriangleExit
import Erdos1135Predecessor.Tao.Renewal.VerticalFirstPassageBasic
import Mathlib.Tactic

namespace Erdos1135Predecessor

namespace Tao

theorem taoSection7RenewalPathPoint_l_sub_growth_ge_steps
    {p : TaoSection7RenewalPoint} {holds : List TaoSection7RenewalPoint}
    {n : ℕ}
    (hn : n ≤ holds.length)
    (hall : taoSection7AllHoldIncrementsLGeOne holds) :
    (n : ℤ) ≤
      (taoSection7RenewalPathPoint p holds n).l - p.l := by
  have hgrowth :
      p.l + (n : ℤ) ≤
        (taoSection7RenewalPathPoint p holds n).l :=
    taoSection7RenewalPathPoint_l_growth_ge_steps p holds n hn hall
  omega

theorem taoSection7Case3_sourceVerticalGrowth_of_scale_path
    {p : TaoSection7RenewalPoint} {holds : List TaoSection7RenewalPoint}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {q candidate : ℕ}
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hcandidate :
      taoSection7Case3HeightExitBound gapBound q < candidate)
    (hlen : candidate - q ≤ holds.length)
    (hall : taoSection7AllHoldIncrementsLGeOne holds) :
    bound q ≤
      ((((taoSection7RenewalPathPoint p holds (candidate - q)).toPoint.l -
        p.toPoint.l : ℤ) : ℝ) * Real.log 2) := by
  have hlog2_nonneg : 0 ≤ Real.log 2 :=
    le_of_lt (Real.log_pos (by norm_num))
  have hgap_le_steps : gapBound q ≤ candidate - q := by
    dsimp [taoSection7Case3HeightExitBound] at hcandidate
    omega
  have hgrowth_int :
      ((candidate - q : ℕ) : ℤ) ≤
        (taoSection7RenewalPathPoint p holds (candidate - q)).l - p.l :=
    taoSection7RenewalPathPoint_l_sub_growth_ge_steps hlen hall
  have hgap_growth_int :
      ((gapBound q : ℕ) : ℤ) ≤
        (taoSection7RenewalPathPoint p holds (candidate - q)).l - p.l :=
    le_trans (by exact_mod_cast hgap_le_steps) hgrowth_int
  have hgap_growth_real :
      (gapBound q : ℝ) ≤
        (((taoSection7RenewalPathPoint p holds (candidate - q)).l -
          p.l : ℤ) : ℝ) := by
    exact_mod_cast hgap_growth_int
  exact (hscale.sufficient q).trans (by
    simpa [TaoSection7RenewalPoint.toPoint] using
      mul_le_mul_of_nonneg_right hgap_growth_real hlog2_nonneg)

end Tao

end Erdos1135Predecessor
