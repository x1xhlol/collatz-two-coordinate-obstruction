import Erdos1135.Tao.Section5.PayloadFreeCoefficient
import Erdos1135.Tao.Section5.WeightedMixing
import Erdos1135.Tao.Section6.UniformLift

/-!
# Section 5 Common Main Term

This leaf isolates the exact finite algebra behind Tao's common term `Z`.
It uses one finite target set and contains no pass-event payload, trajectory
family, or probabilistic approximation statement.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

/-- Generic payload-free coarse weighted Syracuse term. -/
def taoSection5PayloadFreeCoarseSyracWeightedTerm
    (m k : ℕ) (c : ZMod (3 ^ k) → ℝ) : ℝ := by
  classical
  exact ∑ X : ZMod (3 ^ k),
    c X *
      (zmodPowFiberAverageScale m k *
        zmodPowFiberSum m k (syracPMFMassVector k) X)

/-- Tao's branch-independent common term `Z` from `(5.21)`. -/
def taoSection5PayloadFreeCommonZ (m : ℕ) (S : Finset ℕ) : ℝ := by
  classical
  exact S.sum fun M =>
    ((3 ^ m : ℕ) : ℝ) *
      syracPMFMassVector m (M : ZMod (3 ^ m)) *
        (1 / (M : ℝ))

/-- At the same level, Tao's Common-Z term is exactly the fine Syracuse
expectation against the payload-free coefficient. -/
theorem taoSection5PayloadFreeCommonZ_eq_fineSyracWeightedTerm
    (m : ℕ) (S : Finset ℕ) :
    taoSection5PayloadFreeCommonZ m S =
      taoSection5FineSyracWeightedTerm m
        (taoSection5PayloadFreeCoefficient m S) := by
  classical
  symm
  unfold taoSection5FineSyracWeightedTerm
  rw [sum_taoSection5PayloadFreeCoefficient_mul]
  unfold taoSection5PayloadFreeCommonZ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M _hM
  ring

/-- The coarse weighted Syracuse term for the source coefficient is exactly
the common lower-level term. The empty target set is included. -/
theorem taoSection5PayloadFreeCoarseSyracWeightedTerm_coefficient_eq_commonZ
    {m k : ℕ} (hmk : m ≤ k) (S : Finset ℕ) :
    taoSection5PayloadFreeCoarseSyracWeightedTerm m k
        (taoSection5PayloadFreeCoefficient k S) =
      taoSection5PayloadFreeCommonZ m S := by
  classical
  let lowerMass : ZMod (3 ^ k) → ℝ := fun X =>
    syracPMFMassVector m (taoZModThreeProjection hmk X)
  have hscale :
      ((3 ^ k : ℕ) : ℝ) * zmodPowFiberAverageScale m k =
        ((3 ^ m : ℕ) : ℝ) := by
    unfold zmodPowFiberAverageScale
    field_simp
  unfold taoSection5PayloadFreeCoarseSyracWeightedTerm
  simp_rw [zmodPowFiberSum_syracPMFMassVector_eq_projection hmk]
  rw [sum_taoSection5PayloadFreeCoefficient_mul]
  unfold taoSection5PayloadFreeCommonZ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M _hM
  change
    ((3 ^ k : ℕ) : ℝ) *
          ((1 / (M : ℝ)) *
            (zmodPowFiberAverageScale m k * lowerMass (M : ZMod (3 ^ k)))) =
      ((3 ^ m : ℕ) : ℝ) *
        syracPMFMassVector m (M : ZMod (3 ^ m)) * (1 / (M : ℝ))
  rw [show lowerMass (M : ZMod (3 ^ k)) =
      syracPMFMassVector m (M : ZMod (3 ^ m)) by
    simp [lowerMass]]
  calc
    ((3 ^ k : ℕ) : ℝ) *
          ((1 / (M : ℝ)) *
            (zmodPowFiberAverageScale m k *
              syracPMFMassVector m (M : ZMod (3 ^ m)))) =
        (((3 ^ k : ℕ) : ℝ) * zmodPowFiberAverageScale m k) *
          syracPMFMassVector m (M : ZMod (3 ^ m)) * (1 / (M : ℝ)) := by
            ring
    _ = ((3 ^ m : ℕ) : ℝ) *
          syracPMFMassVector m (M : ZMod (3 ^ m)) * (1 / (M : ℝ)) := by
            rw [hscale]

@[simp] theorem taoSection5PayloadFreeCommonZ_empty (m : ℕ) :
    taoSection5PayloadFreeCommonZ m ∅ = 0 := by
  simp [taoSection5PayloadFreeCommonZ]

end

end Tao
end Erdos1135
