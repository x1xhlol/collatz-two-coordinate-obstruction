import Erdos1135Predecessor.ND.PositiveDensity.GeneralTargetTerminalCensus
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

namespace CollatzCanonical.PeriodicCensusFloor
open Erdos1135Predecessor.ND.PositiveDensity
open scoped BigOperators

noncomputable section

def terminalFanEnvelope (m : ℕ) (y : ZMod (3 ^ m)) : ℝ :=
  ∑' j : ℕ, (1 / 4 : ℝ) ^ j *
    ndSyracuseUnitReferenceDensity m (ndTerminalResidueFan m j y)

theorem terminalFanEnvelope_summable (m : ℕ) (y : ZMod (3 ^ m)) :
    Summable (fun j : ℕ => (1 / 4 : ℝ) ^ j *
      ndSyracuseUnitReferenceDensity m (ndTerminalResidueFan m j y)) := by
  apply Summable.of_nonneg_of_le
    (fun j => mul_nonneg (by positivity) (ndSyracuseUnitReferenceDensity_nonneg _ _))
    (fun j => mul_le_mul_of_nonneg_left (unitReferenceDensity_finite_upper _ _) (by positivity))
  exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).mul_right ((2 / 3 : ℝ) * ((3 ^ m : ℕ) : ℝ))

theorem terminalFanEnvelope_nonneg (m : ℕ) (y : ZMod (3 ^ m)) :
    0 ≤ terminalFanEnvelope m y :=
  tsum_nonneg fun j => mul_nonneg (by positivity) (ndSyracuseUnitReferenceDensity_nonneg _ _)

theorem terminalFanEnvelope_le (m : ℕ) (y : ZMod (3 ^ m)) :
    terminalFanEnvelope m y ≤ (8 / 9 : ℝ) * ((3 ^ m : ℕ) : ℝ) := by
  have hg := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)
  have h := (terminalFanEnvelope_summable m y).tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left (unitReferenceDensity_finite_upper _ _) (by positivity))
    (hg.mul_right ((2 / 3 : ℝ) * ((3 ^ m : ℕ) : ℝ)))
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h
  change terminalFanEnvelope m y ≤ _ at h
  convert h using 1
  ring

theorem terminalFanEnvelope_dominates (m J : ℕ) (y : ZMod (3 ^ m)) :
    (∑ j : Fin J, (1 / 4 : ℝ) ^ j.val *
      ndSyracuseUnitReferenceDensity m (ndTerminalResidueFan m j.val y)) ≤
        terminalFanEnvelope m y := by
  change (∑ j : Fin J, (fun j : ℕ => (1 / 4 : ℝ) ^ j *
    ndSyracuseUnitReferenceDensity m (ndTerminalResidueFan m j y)) j.val) ≤ _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (1 / 4 : ℝ) ^ j *
    ndSyracuseUnitReferenceDensity m (ndTerminalResidueFan m j y))]
  exact (terminalFanEnvelope_summable m y).sum_le_tsum (Finset.range J)
    (fun j _ => mul_nonneg (by positivity) (ndSyracuseUnitReferenceDensity_nonneg _ _))

theorem terminalFanEnvelope_fullMean (m : ℕ) :
    ndTernaryUniformMean m (terminalFanEnvelope m) = 8 / 9 := by
  classical
  have hswap :
      (∑ y : ZMod (3 ^ m), ∑' j : ℕ, (1 / 4 : ℝ) ^ j *
        ndSyracuseUnitReferenceDensity m (ndTerminalResidueFan m j y)) =
      ∑' j : ℕ, ∑ y : ZMod (3 ^ m), (1 / 4 : ℝ) ^ j *
        ndSyracuseUnitReferenceDensity m (ndTerminalResidueFan m j y) :=
    (Summable.tsum_finsetSum (fun y _ => terminalFanEnvelope_summable m y)).symm
  unfold ndTernaryUniformMean terminalFanEnvelope
  rw [hswap, ← tsum_mul_left]
  have hterm (j : ℕ) :
      ndTernaryUniformScale m *
        (∑ y : ZMod (3 ^ m), (1 / 4 : ℝ) ^ j *
          ndSyracuseUnitReferenceDensity m (ndTerminalResidueFan m j y)) =
        (1 / 4 : ℝ) ^ j * (2 / 3 : ℝ) := by
    rw [← Finset.mul_sum]
    have hm := (terminalResidueFan_fullMean m j (ndSyracuseUnitReferenceDensity m)).trans
      (unitReferenceDensity_fullMean_eq m)
    unfold ndTernaryUniformMean at hm
    calc
      _ = (1 / 4 : ℝ) ^ j *
        (ndTernaryUniformScale m * ∑ y, ndSyracuseUnitReferenceDensity m
          (ndTerminalResidueFan m j y)) := by ring
      _ = _ := by rw [hm]
  simp_rw [hterm]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

#print axioms terminalFanEnvelope_summable
#print axioms terminalFanEnvelope_nonneg
#print axioms terminalFanEnvelope_le
#print axioms terminalFanEnvelope_dominates
#print axioms terminalFanEnvelope_fullMean

end
end CollatzCanonical.PeriodicCensusFloor
