/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Prop78Boundary
import Erdos1135Predecessor.Tao.Renewal.Prop78Case3FixedParameters
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshOutsideEprimeWidth

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

structure TaoSection7Case3EventualScaleFacts
    {constants : TaoSection7Lemma710Constants}
    {A : ℕ} {epsilon : ℝ}
    (fixed : TaoSection7Case3FixedParameters constants A epsilon)
    (S0 m : ℕ) : Prop where
  two_le_m : 2 ≤ m
  P_le_m : fixed.P ≤ m
  Pmax_range :
    (fixed.Pmax : ℝ) ≤ Real.rpow (m : ℝ) ((1 : ℝ) / 10)
  bound_le_m_at_Pmax :
    taoSection7Case3LargeTriangleBoundWithBase
        (8 : ℝ) (4 * fixed.Aweight) fixed.Pmax ≤
      Real.rpow (m : ℝ) ((2 : ℝ) / 5)
  S0_le_boundaryThreshold :
    (S0 : ℝ) ≤ taoSection7Prop78BoundaryThreshold m

def TaoSection7Case3EventualScaleFacts.to_allowedCapAdmissibility
    {constants : TaoSection7Lemma710Constants}
    {A S0 m : ℕ} {epsilon : ℝ}
    {fixed : TaoSection7Case3FixedParameters constants A epsilon}
    (h : TaoSection7Case3EventualScaleFacts fixed S0 m) :
    TaoSection7Case3BaseKcutAllowedCapAdmissibility
      (Finset.range (fixed.Pmax + 1))
      8 m (4 * fixed.Aweight) fixed.Pmax where
  base_ge_four := by norm_num
  allowed_le_Pmax := by
    intro p hp
    have hp_lt : p < fixed.Pmax + 1 := Finset.mem_range.1 hp
    omega
  Pmax_range := h.Pmax_range
  bound_le_m_at_Pmax := h.bound_le_m_at_Pmax

end

end Tao

end Erdos1135Predecessor
