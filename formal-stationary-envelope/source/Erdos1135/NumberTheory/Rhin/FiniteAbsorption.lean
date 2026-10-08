import Erdos1135.NumberTheory.Rhin.Irrationality
import Erdos1135.NumberTheory.Rhin.LargeHeight
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat

/-!
# Specialization and finite absorption for Rhin's phase bound

The first theorem in this file is the P1 pilot: it consumes the frozen
large-height statement as an ordinary theorem hypothesis and produces the
eventual nearest-integer bound.  Pointwise nonvanishing and the finite-minimum
absorption are added separately in P2.
-/

namespace Erdos1135
namespace NumberTheory
namespace Rhin

noncomputable section

/-- Specialize a large-height three-integer bound at
`(u₀,u₁,u₂) = (0,-round(q log_2 3),q)`.

The fixed height comparison factor is three.  Its exact value affects only the
unspecified positive witness, not the exponent. -/
theorem largeFrequencyPhaseBound_of_largeHeightBound
    (hRhin : LargeHeightBound) :
    LargeFrequencyPhaseBound := by
  rcases hRhin with
    ⟨sourceFactor, hSourceFactor, sourceThreshold,
      hTwoThreshold, hSource⟩
  let factor : ℝ :=
    sourceFactor * Real.rpow 3 (-(133 / 10 : ℝ)) / Real.log 2
  let threshold : ℕ := max sourceThreshold 2
  have hThreePow : 0 < Real.rpow 3 (-(133 / 10 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hFactor : 0 < factor := by
    dsimp only [factor]
    exact div_pos (mul_pos hSourceFactor hThreePow) log_two_pos
  refine ⟨factor, hFactor, threshold, le_max_right _ _, ?_⟩
  intro q hq
  have hTwoQ : 2 ≤ q :=
    (le_max_right sourceThreshold 2).trans hq
  have hSourceThresholdQ : sourceThreshold ≤ q :=
    (le_max_left sourceThreshold 2).trans hq
  let p : ℤ := round ((q : ℝ) * logTwoThree)
  let height : ℕ := linearFormHeight (-p) (q : ℤ)
  have hHeightLeNat : height ≤ 3 * q := by
    dsimp only [height, p]
    exact roundLogHeight_le_three_mul hTwoQ
  have hQLeHeight : q ≤ height := by
    dsimp only [height, linearFormHeight]
    simpa only [Int.natAbs_natCast] using
      (le_max_right (-p).natAbs q)
  have hSourceThresholdHeight : sourceThreshold ≤ height :=
    hSourceThresholdQ.trans hQLeHeight
  have hHeightPos : 0 < (height : ℝ) := by
    have hTwoHeight : (2 : ℝ) ≤ height := by
      exact_mod_cast hTwoThreshold.trans hSourceThresholdHeight
    linarith
  have hHeightLeReal : (height : ℝ) ≤ 3 * (q : ℝ) := by
    exact_mod_cast hHeightLeNat
  have hExponentNonpos : (-(133 / 10 : ℝ)) ≤ 0 := by norm_num
  have hPowCompare :
      Real.rpow (3 * (q : ℝ)) (-(133 / 10 : ℝ)) ≤
        Real.rpow (height : ℝ) (-(133 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hHeightPos hHeightLeReal hExponentNonpos
  have hSourceBound :
      sourceFactor *
          Real.rpow (height : ℝ) (-(133 / 10 : ℝ)) ≤
        |linearForm 0 (-p) (q : ℤ)| :=
    hSource 0 (-p) (q : ℤ) hSourceThresholdHeight
  have hScaledBound :
      sourceFactor *
          Real.rpow (3 * (q : ℝ)) (-(133 / 10 : ℝ)) ≤
        |linearForm 0 (-p) (q : ℤ)| :=
    (mul_le_mul_of_nonneg_left hPowCompare hSourceFactor.le).trans
      hSourceBound
  have hLogScaled :
      Real.log 2 *
          (factor * Real.rpow (q : ℝ) (-(133 / 10 : ℝ))) ≤
        |linearForm 0 (-p) (q : ℤ)| := by
    have hMulRpow :
        Real.rpow (3 * (q : ℝ)) (-(133 / 10 : ℝ)) =
          Real.rpow 3 (-(133 / 10 : ℝ)) *
            Real.rpow (q : ℝ) (-(133 / 10 : ℝ)) :=
      Real.mul_rpow (by norm_num) (Nat.cast_nonneg q)
    rw [show Real.log 2 *
        (factor * Real.rpow (q : ℝ) (-(133 / 10 : ℝ))) =
          sourceFactor *
            Real.rpow (3 * (q : ℝ)) (-(133 / 10 : ℝ)) by
      dsimp only [factor]
      rw [hMulRpow]
      field_simp [log_two_pos.ne']]
    exact hScaledBound
  have hFormIdentity :
      |linearForm 0 (-p) (q : ℤ)| =
        Real.log 2 *
          nearestIntegerNorm ((q : ℝ) * logTwoThree) := by
    dsimp only [p]
    exact abs_linearForm_round_eq q
  rw [hFormIdentity] at hLogScaled
  exact le_of_mul_le_mul_left hLogScaled log_two_pos

/-- Absorb a finite initial range into an eventual positive bound.

The finite set is seeded by frequency `1`, so this lemma remains valid when
`threshold` is `0` or `1`.  In particular, it never evaluates `weight 0`. -/
theorem exists_global_factor_of_eventually
    (gap weight : ℕ → ℝ) (threshold : ℕ)
    (hGap : ∀ q : ℕ, 0 < q → 0 < gap q)
    (hWeight : ∀ q : ℕ, 0 < q → 0 < weight q)
    {factor : ℝ} (hFactor : 0 < factor)
    (hEventually : ∀ q : ℕ, 0 < q → threshold ≤ q →
      factor * weight q ≤ gap q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ q : ℕ, 0 < q → c * weight q ≤ gap q := by
  let lowSet : Finset ℕ :=
    Finset.Icc 1 (max 1 (threshold - 1))
  have hLowSet : lowSet.Nonempty := by
    refine ⟨1, ?_⟩
    dsimp only [lowSet]
    exact Finset.mem_Icc.mpr ⟨le_rfl, le_max_left _ _⟩
  let lowMin : ℝ :=
    lowSet.inf' hLowSet (fun q => gap q / weight q)
  have hLowMin : 0 < lowMin := by
    dsimp only [lowMin]
    rw [Finset.lt_inf'_iff hLowSet]
    intro q hq
    have hqOne : 1 ≤ q :=
      (Finset.mem_Icc.mp hq).1
    exact div_pos (hGap q (by omega)) (hWeight q (by omega))
  let c : ℝ := min 1 (min factor lowMin)
  have hcPos : 0 < c := by
    dsimp only [c]
    exact lt_min zero_lt_one (lt_min hFactor hLowMin)
  have hcOne : c ≤ 1 := by
    dsimp only [c]
    exact min_le_left _ _
  have hcFactor : c ≤ factor := by
    dsimp only [c]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hcLowMin : c ≤ lowMin := by
    dsimp only [c]
    exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hcPos, hcOne, ?_⟩
  intro q hq
  by_cases hLarge : threshold ≤ q
  · exact
      (mul_le_mul_of_nonneg_right hcFactor (hWeight q hq).le).trans
        (hEventually q hq hLarge)
  · have hqLow : q ∈ lowSet := by
      dsimp only [lowSet]
      rw [Finset.mem_Icc]
      constructor
      · omega
      · apply le_max_of_le_right
        omega
    have hMinLe : lowMin ≤ gap q / weight q := by
      dsimp only [lowMin]
      exact Finset.inf'_le _ hqLow
    exact (le_div_iff₀ (hWeight q hq)).mp (hcLowMin.trans hMinLe)

/-- Combine P1 with pointwise nonvanishing to obtain a global unspecified
positive phase factor, capped by one. -/
theorem existsGlobalPhaseBound_of_largeHeightBound
    (hRhin : LargeHeightBound) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ q : ℕ, 0 < q →
        c * Real.rpow (q : ℝ) (-(133 / 10 : ℝ)) ≤
          nearestIntegerNorm ((q : ℝ) * logTwoThree) := by
  rcases largeFrequencyPhaseBound_of_largeHeightBound hRhin with
    ⟨factor, hFactor, threshold, _hTwoThreshold, hEventually⟩
  exact exists_global_factor_of_eventually
    (fun q => nearestIntegerNorm ((q : ℝ) * logTwoThree))
    (fun q => Real.rpow (q : ℝ) (-(133 / 10 : ℝ)))
    threshold
    nearestIntegerNorm_mul_logTwoThree_pos
    (fun q hq => Real.rpow_pos_of_pos (Nat.cast_pos.mpr hq) _)
    hFactor (fun q _hq hqLarge ↦ hEventually q hqLarge)

end

end Rhin
end NumberTheory
end Erdos1135
