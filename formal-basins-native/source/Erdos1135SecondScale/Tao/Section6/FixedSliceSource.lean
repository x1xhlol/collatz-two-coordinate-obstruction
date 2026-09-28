/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section6.FixedSliceCollision
import Erdos1135SecondScale.Tao.Section6.HeadGateIndex

/-!
# Section 6 Source-Facing Fixed Slice

This leaf removes the conditional collision theorem's external conductor
geometry.  A nonempty head gate supplies the stopping-index bounds; an empty
head gate gives the zero source slice.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- True eventual fixed-slice collision endpoint.  The only structural inputs
left to the caller are the ambient scale inclusion and Tao's high regime. -/
theorem exists_taoSection6FixedSliceOscillation_sq_le
    {B : ℕ} {C : ℝ}
    (hdecay : syracPMFPrimitivePolynomialDecayAt B C)
    (hC : 0 ≤ C)
    (CA : ℝ) (hCA : 17 ≤ CA) :
    ∃ N0 : ℕ, ∀ T k l m : ℕ,
      N0 ≤ T + (k + 1) →
      m ≤ T + (k + 1) →
      9 * (T + (k + 1)) ≤ 10 * m →
      taoZModPowOscillation m (T + (k + 1))
          (taoSection6GatedSourceSubmass CA T k l) ^ 2 ≤
        (taoSection6TailDecayDelta C B (T + (k + 1))) ^ 2 *
          (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) *
          (1 / 2 : ℝ) ^ l := by
  obtain ⟨Ncollision, hcollision⟩ :=
    exists_taoSection6FixedSliceOscillation_sq_le_of_bounds
      hdecay hC CA hCA
  obtain ⟨Nindex, hindex⟩ :=
    exists_taoSection6HeadGate_index_le CA hCA
  refine ⟨max Ncollision Nindex, ?_⟩
  intro T k l m hn hmn hm
  have hncollision : Ncollision ≤ T + (k + 1) :=
    (le_max_left _ _).trans hn
  have hnindex : Nindex ≤ T + (k + 1) :=
    (le_max_right _ _).trans hn
  by_cases hgate : ∃ head : List ℕ+,
      taoSection6HeadGate CA (T + (k + 1)) k l head
  · obtain ⟨head, hheadGate⟩ := hgate
    have hk : 20 * k ≤ 17 * (T + (k + 1)) :=
      hindex (T + (k + 1)) hnindex k l head hheadGate
    have hhead : k + 1 ≤ m :=
      taoSection6HeadIndex_le_m_of_bounds (by omega) hm hk
    exact hcollision T k l m hncollision hmn hhead hm hk
  · have hzero :=
      taoSection6FixedSliceOscillation_eq_zero_of_headGate_empty
        (CA := CA) (T := T) (k := k) (l := l) (m := m) hgate
    have hrhs :
        0 ≤ (taoSection6TailDecayDelta C B (T + (k + 1))) ^ 2 *
          (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) *
          (1 / 2 : ℝ) ^ l := by
      apply mul_nonneg
      · exact mul_nonneg (sq_nonneg _) (by positivity)
      · exact pow_nonneg (by norm_num) l
    simpa [hzero] using hrhs

end

end Tao
end Erdos1135SecondScale
