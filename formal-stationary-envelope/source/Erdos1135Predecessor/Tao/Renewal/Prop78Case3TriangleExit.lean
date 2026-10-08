/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Prop78Case3Event

namespace Erdos1135Predecessor

namespace Tao

open scoped BigOperators

theorem taoSection7Case3_verticalDepth_log2_le_size_of_mem
    {Δ : TaoSection7Triangle} {p : TaoSection7Point}
    (hmem : Δ.Mem p) :
    ((Δ.verticalDepth p : ℤ) : ℝ) * Real.log 2 ≤ Δ.size := by
  have hlog9_nonneg : 0 ≤ Real.log 9 :=
    le_of_lt (Real.log_pos (by norm_num))
  have hhorizontal_nonneg :
      0 ≤ ((Δ.horizontalDepth p : ℕ) : ℝ) * Real.log 9 :=
    mul_nonneg (by positivity) hlog9_nonneg
  have hweight_le := TaoSection7Triangle.mem_weight_le_size hmem
  linarith

theorem taoSection7Case3_cornerL_lt_of_mem_and_vertical_growth_log2_gt_size
    {pointAt : ℕ → TaoSection7Point}
    {Δ : TaoSection7Triangle} {p p' : ℕ}
    (hmem : Δ.Mem (pointAt p))
    (hsize_growth :
      Δ.size <
        (((pointAt p').l - (pointAt p).l : ℤ) : ℝ) * Real.log 2) :
    Δ.cornerL < (pointAt p').l := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hvertical_le_size :
      ((Δ.verticalDepth (pointAt p) : ℤ) : ℝ) * Real.log 2 ≤ Δ.size :=
    taoSection7Case3_verticalDepth_log2_le_size_of_mem hmem
  have hmul_lt :
      ((Δ.verticalDepth (pointAt p) : ℤ) : ℝ) * Real.log 2 <
        (((pointAt p').l - (pointAt p).l : ℤ) : ℝ) * Real.log 2 :=
    lt_of_le_of_lt hvertical_le_size hsize_growth
  have hdepth_lt_growth_real :
      ((Δ.verticalDepth (pointAt p) : ℤ) : ℝ) <
        (((pointAt p').l - (pointAt p).l : ℤ) : ℝ) :=
    lt_of_mul_lt_mul_right hmul_lt (le_of_lt hlog2_pos)
  have hdepth_lt_growth :
      Δ.verticalDepth (pointAt p) < (pointAt p').l - (pointAt p).l := by
    exact_mod_cast hdepth_lt_growth_real
  unfold TaoSection7Triangle.verticalDepth at hdepth_lt_growth
  omega

theorem taoSection7Case3_not_mem_of_cornerL_lt
    {Δ : TaoSection7Triangle} {p : TaoSection7Point}
    (hexit_height : Δ.cornerL < p.l) :
    ¬ Δ.Mem p := by
  intro hmem
  exact not_le_of_gt hexit_height hmem.2.1

end Tao

end Erdos1135Predecessor
