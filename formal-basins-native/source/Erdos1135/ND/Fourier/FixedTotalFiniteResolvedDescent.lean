import Erdos1135.ND.Fourier.FixedTotalTerminalDescent

/-!
# Finite-Resolved Fixed-Total Descent

This leaf retains a finite endpoint index while assembling high- and
low-level residue tests.  Equal residues therefore add their coefficients;
no image, injectivity hypothesis, or choice of residue representative occurs.

The final theorem feeds these tests directly to the checked fixed-total
FM1/R1/D6 terminal descent while preserving its eta-proportional reference
row and its single separate absolute tail.
-/

namespace Erdos1135
namespace ND

open Tao

noncomputable section

/-- A finite-index test on the fine residue space.  Colliding indices retain
their separate coefficients in the displayed sum. -/
noncomputable def ndFiniteResolvedFineTest
    {ι : Type*} [Fintype ι] (n : ℕ)
    (a : ι → ZMod (3 ^ n)) (d : ι → ℝ) :
    ZMod (3 ^ n) → ℝ :=
  fun y => ∑ i, if a i = y then d i else 0

/-- The corresponding normalized coarse test, written with its endpoint
index still visible. -/
noncomputable def ndFiniteResolvedCoarseTest
    {ι : Type*} [Fintype ι] {m n : ℕ} (hmn : m ≤ n)
    (a : ι → ZMod (3 ^ n)) (d : ι → ℝ) :
    ZMod (3 ^ m) → ℝ :=
  fun x => Tao.zmodPowFiberAverageScale m n *
    ∑ i, if Tao.taoZModThreeProjection hmn (a i) = x then d i else 0

/-- Pairing a PMF with the fine test resolves exactly to the indexed weighted
sum.  No injectivity of the endpoint map is used. -/
theorem ndPMFWeightedExpectation_finiteResolvedFineTest
    {ι : Type*} [Fintype ι] {n : ℕ}
    (p : PMF (ZMod (3 ^ n)))
    (a : ι → ZMod (3 ^ n)) (d : ι → ℝ) :
    ndPMFWeightedExpectation p (ndFiniteResolvedFineTest n a d) =
      ∑ i, (p (a i)).toReal * d i := by
  classical
  unfold ndPMFWeightedExpectation ndFiniteResolvedFineTest
  rw [tsum_fintype]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  simp [eq_comm]

/-- Pairing a PMF with the coarse test produces the normalized indexed sum at
the projected residues. -/
theorem ndPMFWeightedExpectation_finiteResolvedCoarseTest
    {ι : Type*} [Fintype ι] {m n : ℕ} (hmn : m ≤ n)
    (p : PMF (ZMod (3 ^ m)))
    (a : ι → ZMod (3 ^ n)) (d : ι → ℝ) :
    ndPMFWeightedExpectation p
        (ndFiniteResolvedCoarseTest hmn a d) =
      Tao.zmodPowFiberAverageScale m n *
        ∑ i, (p (Tao.taoZModThreeProjection hmn (a i))).toReal * d i := by
  classical
  unfold ndPMFWeightedExpectation ndFiniteResolvedCoarseTest
  rw [tsum_fintype]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ i : ι, ∑ x : ZMod (3 ^ m),
        (p x).toReal *
          (Tao.zmodPowFiberAverageScale m n *
            if Tao.taoZModThreeProjection hmn (a i) = x then d i else 0)) =
      ∑ i : ι,
        Tao.zmodPowFiberAverageScale m n *
          ((p (Tao.taoZModThreeProjection hmn (a i))).toReal * d i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp [eq_comm]
      ring
    _ = _ := rfl

/-- Averaging the fine finite-index test over an exact projection fiber gives
the explicitly resolved coarse test, pointwise and without deduplicating
collisions. -/
theorem ndZModPowProjectionFiberAverage_finiteResolvedFineTest
    {ι : Type*} [Fintype ι] {m n : ℕ} (hmn : m ≤ n)
    (a : ι → ZMod (3 ^ n)) (d : ι → ℝ) :
    ndZModPowProjectionFiberAverage hmn
        (ndFiniteResolvedFineTest n a d) =
      ndFiniteResolvedCoarseTest hmn a d := by
  classical
  funext x
  unfold ndZModPowProjectionFiberAverage ndFiniteResolvedFineTest
    ndFiniteResolvedCoarseTest
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi : Tao.taoZModThreeProjection hmn (a i) = x
  · let y0 : {y : ZMod (3 ^ n) |
        Tao.taoZModThreeProjection hmn y = x} := ⟨a i, hi⟩
    have hsingle :
        (∑ y : {y : ZMod (3 ^ n) |
            Tao.taoZModThreeProjection hmn y = x},
          if a i = y.1 then d i else 0) = d i := by
      rw [Fintype.sum_eq_single y0]
      · simp [y0]
      · intro y hy
        have hne : a i ≠ y.1 := by
          intro hai
          apply hy
          apply Subtype.ext
          exact hai.symm
        simp [hne]
    rw [hsingle, if_pos hi]
  · have hzero :
        (∑ y : {y : ZMod (3 ^ n) |
            Tao.taoZModThreeProjection hmn y = x},
          if a i = y.1 then d i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro y _hy
      have hne : a i ≠ y.1 := by
        intro hai
        apply hi
        rw [hai]
        exact y.2
      simp [hne]
    rw [hzero, if_neg hi]

/-- The normalized projection scale converts a fine `3^n` coefficient to
the corresponding coarse `3^m` coefficient. -/
theorem ndZModPowFiberAverageScale_mul_threePow
    {m n : ℕ} (hmn : m ≤ n) :
    Tao.zmodPowFiberAverageScale m n * (3 : ℝ) ^ n = (3 : ℝ) ^ m := by
  have hpow : (3 : ℝ) ^ n = (3 : ℝ) ^ (n - m) * (3 : ℝ) ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hmn]
  rw [hpow, ← mul_assoc, Tao.zmodPowFiberAverageScale_mul_card hmn,
    one_mul]

/-- The collision-safe finite-index specialization of the fixed-total
FM1/R1/D6 descent.  The actual eta coefficient remains visible, and the
absolute tail is paid once after the entire finite test has been assembled. -/
theorem abs_ndSection7FiberPMF_finiteResolved_sub_syrac_le_fm1
    {ι : Type*} [Fintype ι]
    {A : ℕ} {K C : ℝ}
    (hFM1 : ndSection7ConditionedFM1NatAt A K C)
    {m n L : ℕ} (hm : 150 ≤ m) (hmn : 8 * m ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8)
    (hWindow : ndSection7M1Window K n L)
    (hDelta :
      ndFixedTotalRatioCenterOffset m n L ≤ ndFixedTotalRatioScale m)
    (hEta : ndFixedTotalRatioEps m n L + 8 / (m : ℝ) ^ 3 ≤ 1)
    (a : ι → ZMod (3 ^ n)) (d : ι → ℝ) (H : ℝ)
    (hc0 : ∀ y, 0 ≤ ndFiniteResolvedFineTest n a d y)
    (hcH : ∀ y, ndFiniteResolvedFineTest n a d y ≤ H) :
    |(∑ i,
          (ndSection7FiberPMF n L (by omega)
            (ndFixedTotalRatio_n_le_L hm hmn hD) (a i)).toReal * d i) -
        Tao.zmodPowFiberAverageScale m n *
          ∑ i,
            (Tao.syracPMF m
              (Tao.taoZModThreeProjection (show m ≤ n by omega)
                (a i))).toReal * d i| ≤
      H * (C / (m : ℝ) ^ A) +
        (43 / 25 : ℝ) *
          (ndFixedTotalRatioEps m n L + 8 / (m : ℝ) ^ 3) *
          (Tao.zmodPowFiberAverageScale m n *
            ∑ i,
              (Tao.syracPMF m
                (Tao.taoZModThreeProjection (show m ≤ n by omega)
                  (a i))).toReal * d i) +
        4 / (m : ℝ) ^ 3 * H := by
  have hbase :=
    abs_ndSection7FiberPMF_expectation_sub_syrac_projectionAverage_le_fm1
      hFM1 hm hmn hD hWindow hDelta hEta
        (ndFiniteResolvedFineTest n a d) H hc0 hcH
  rw [ndPMFWeightedExpectation_finiteResolvedFineTest,
    ndZModPowProjectionFiberAverage_finiteResolvedFineTest,
    ndPMFWeightedExpectation_finiteResolvedCoarseTest] at hbase
  exact hbase

/-! Exact multiplicity and scale canaries. -/

private noncomputable def ndFiniteResolvedCollisionWeights : Fin 2 → ℝ :=
  fun i => if i = 0 then 2 else 3

private noncomputable def ndFiniteResolvedCoarseCollisionAddresses :
    Fin 2 → ZMod (3 ^ 2) :=
  fun i => if i = 0 then 0 else 3

private theorem nd_finiteResolvedFine_sameResidue_adds :
    ndFiniteResolvedFineTest 1
        (fun _ : Fin 2 => (0 : ZMod (3 ^ 1)))
        ndFiniteResolvedCollisionWeights 0 = 5 := by
  norm_num [ndFiniteResolvedFineTest, ndFiniteResolvedCollisionWeights,
    Fin.sum_univ_two]

private theorem nd_finiteResolvedCoarse_collision_adds_and_scales :
    ndFiniteResolvedCoarseTest (show 1 ≤ 2 by omega)
        ndFiniteResolvedCoarseCollisionAddresses
        ndFiniteResolvedCollisionWeights 0 = (5 / 3 : ℝ) := by
  have hproj3 : Tao.taoZModThreeProjection (show 1 ≤ 2 by omega)
      (3 : ZMod (3 ^ 2)) = 0 := by
    change Tao.taoZModThreeProjection (show 1 ≤ 2 by omega)
      ((3 : ℕ) : ZMod (3 ^ 2)) = 0
    rw [Tao.taoZModThreeProjection_natCast]
    exact (by decide)
  norm_num [ndFiniteResolvedCoarseTest,
    ndFiniteResolvedCoarseCollisionAddresses,
    ndFiniteResolvedCollisionWeights, Tao.zmodPowFiberAverageScale,
    Fin.sum_univ_two, hproj3]

private theorem nd_projectionFiberAverage_coarse_collision_adds_and_scales :
    ndZModPowProjectionFiberAverage (show 1 ≤ 2 by omega)
        (ndFiniteResolvedFineTest 2
          ndFiniteResolvedCoarseCollisionAddresses
          ndFiniteResolvedCollisionWeights) 0 = (5 / 3 : ℝ) := by
  rw [congrFun
    (ndZModPowProjectionFiberAverage_finiteResolvedFineTest
      (show 1 ≤ 2 by omega) ndFiniteResolvedCoarseCollisionAddresses
        ndFiniteResolvedCollisionWeights) 0]
  exact nd_finiteResolvedCoarse_collision_adds_and_scales

end

end ND
end Erdos1135
