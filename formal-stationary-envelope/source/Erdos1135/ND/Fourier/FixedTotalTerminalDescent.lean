import Erdos1135.ND.Fourier.FixedTotalRatioD6
import Erdos1135.ND.Fourier.FixedTotalFM1

/-!
# Fixed-Total Terminal Descent

This leaf averages one already-assembled high-level test over the fibers of a
power-of-three projection.  Full-L1 conditioned FM1 controls the change from
the parent fiber to the projected law, after which the fixed-total ratio/D6
leaf compares that projected law with the common Syracuse reference.

The high-level test is formed before any absolute value, so neither the FM1
charge nor the absolute ratio tail is paid separately for its constituent
endpoints.
-/

namespace Erdos1135
namespace ND

open Tao

noncomputable section

/-- Normalized average of a high-level test over one exact projection fiber. -/
noncomputable def ndZModPowProjectionFiberAverage
    {m n : ℕ} (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ) :
    ZMod (3 ^ m) → ℝ :=
  fun x => Tao.zmodPowFiberAverageScale m n *
    ∑ y : {y : ZMod (3 ^ n) |
      Tao.taoZModThreeProjection hmn y = x}, c y.1

/-- A bounded nonnegative high-level test keeps the same bound after exact
projection-fiber averaging. -/
theorem ndZModPowProjectionFiberAverage_nonneg_le
    {m n : ℕ} (hmn : m ≤ n)
    (c : ZMod (3 ^ n) → ℝ) (H : ℝ)
    (hc0 : ∀ y, 0 ≤ c y) (hcH : ∀ y, c y ≤ H)
    (x : ZMod (3 ^ m)) :
    0 ≤ ndZModPowProjectionFiberAverage hmn c x ∧
      ndZModPowProjectionFiberAverage hmn c x ≤ H := by
  classical
  let s := Tao.zmodPowFiberAverageScale m n
  let F := {y : ZMod (3 ^ n) |
    Tao.taoZModThreeProjection hmn y = x}
  have hs0 : 0 ≤ s := by
    dsimp [s]
    unfold Tao.zmodPowFiberAverageScale
    positivity
  have hsum0 : 0 ≤ ∑ y : F, c y.1 :=
    Finset.sum_nonneg fun y _hy => hc0 y.1
  have hsumH : (∑ y : F, c y.1) ≤ (Fintype.card F : ℝ) * H := by
    calc
      (∑ y : F, c y.1) ≤ ∑ _y : F, H :=
        Finset.sum_le_sum fun y _hy => hcH y.1
      _ = (Fintype.card F : ℝ) * H := by simp
  have hcard : Fintype.card F = 3 ^ (n - m) := by
    simpa [F] using Tao.taoZModThreeProjection_fiber_card hmn x
  have hcancel : s * (Fintype.card F : ℝ) = 1 := by
    rw [hcard]
    simpa only [s, Nat.cast_pow, Nat.cast_ofNat] using
      Tao.zmodPowFiberAverageScale_mul_card hmn
  change 0 ≤ s * (∑ y : F, c y.1) ∧
    s * (∑ y : F, c y.1) ≤ H
  constructor
  · exact mul_nonneg hs0 hsum0
  · calc
      s * (∑ y : F, c y.1) ≤ s * ((Fintype.card F : ℝ) * H) :=
        mul_le_mul_of_nonneg_left hsumH hs0
      _ = (s * (Fintype.card F : ℝ)) * H := by ring
      _ = H := by rw [hcancel, one_mul]

/-- Normalized Fubini: pairing a lifted low vector with a high test equals
pairing the low vector with the normalized projection-fiber average. -/
theorem sum_taoZModPowUniformLift_mul_eq_sum_mul_projectionFiberAverage
    {m n : ℕ} (hmn : m ≤ n)
    (d : ZMod (3 ^ m) → ℝ) (c : ZMod (3 ^ n) → ℝ) :
    (∑ y : ZMod (3 ^ n),
        Tao.taoZModPowUniformLift hmn d y * c y) =
      ∑ x : ZMod (3 ^ m),
        d x * ndZModPowProjectionFiberAverage hmn c x := by
  classical
  let p : ZMod (3 ^ n) → ZMod (3 ^ m) :=
    fun y => Tao.taoZModThreeProjection hmn y
  calc
    (∑ y : ZMod (3 ^ n),
        Tao.taoZModPowUniformLift hmn d y * c y) =
      ∑ x : ZMod (3 ^ m),
        ∑ y : {y : ZMod (3 ^ n) | p y = x},
          Tao.taoZModPowUniformLift hmn d y.1 * c y.1 := by
      exact (Fintype.sum_fiberwise p
        (fun y => Tao.taoZModPowUniformLift hmn d y * c y)).symm
    _ = ∑ x : ZMod (3 ^ m),
        d x * ndZModPowProjectionFiberAverage hmn c x := by
      apply Finset.sum_congr rfl
      intro x _hx
      unfold ndZModPowProjectionFiberAverage
      simp only [Tao.taoZModPowUniformLift]
      simp_rw [show ∀ y : {y : ZMod (3 ^ n) | p y = x},
        Tao.taoZModThreeProjection hmn y.1 = x from fun y => y.2]
      rw [show d x *
            (Tao.zmodPowFiberAverageScale m n *
              ∑ y : {y : ZMod (3 ^ n) | p y = x}, c y.1) =
          (Tao.zmodPowFiberAverageScale m n * d x) *
            ∑ y : {y : ZMod (3 ^ n) | p y = x}, c y.1 by ring,
        Finset.mul_sum]

/-- The normalized ambient fiber average of a PMF mass vector is the uniform
lift of its projected PMF. -/
private theorem ndZModPowFiberAverage_pmfMass_eq_uniformLift
    {m n : ℕ} (hmn : m ≤ n) (p : PMF (ZMod (3 ^ n))) :
    Tao.zmodPowFiberAverage m n (fun y => (p y).toReal) =
      Tao.taoZModPowUniformLift hmn
        (fun x =>
          ((p.map (Tao.taoZModThreeProjection hmn)) x).toReal) := by
  classical
  funext y
  unfold Tao.zmodPowFiberAverage Tao.taoZModPowUniformLift
  congr 1
  unfold Tao.zmodPowFiberSum
  change (∑ y', if Tao.zmodSameResidueModPow m n y' y then
      (p y').toReal else 0) =
    ((p.map (Tao.taoZModThreeProjection hmn))
      (Tao.taoZModThreeProjection hmn y)).toReal
  rw [Tao.pmf_map_apply_toReal_tsum, tsum_fintype]
  apply Finset.sum_congr rfl
  intro z _hz
  rw [Tao.zmodSameResidueModPow_iff_projection_eq hmn]
  by_cases hzy : Tao.taoZModThreeProjection hmn z =
      Tao.taoZModThreeProjection hmn y
  · rw [if_pos hzy, if_pos hzy.symm]
  · have hyz : ¬ Tao.taoZModThreeProjection hmn y =
        Tao.taoZModThreeProjection hmn z := fun h => hzy h.symm
    rw [if_neg hzy, if_neg hyz]

/-- One bounded high-level test pairs with a PMF and its normalized projected
law to within its bound times Tao's full-L1 oscillation. -/
theorem abs_ndPMFWeightedExpectation_sub_projectionFiberAverage_le_oscillation
    {m n : ℕ} (hmn : m ≤ n)
    (p : PMF (ZMod (3 ^ n)))
    (c : ZMod (3 ^ n) → ℝ) (H : ℝ)
    (hc0 : ∀ y, 0 ≤ c y) (hcH : ∀ y, c y ≤ H) :
    |ndPMFWeightedExpectation p c -
        ndPMFWeightedExpectation
          (p.map (Tao.taoZModThreeProjection hmn))
          (ndZModPowProjectionFiberAverage hmn c)| ≤
      H * Tao.taoZModPowOscillation m n
        (fun y => (p y).toReal) := by
  classical
  let q : PMF (ZMod (3 ^ m)) :=
    p.map (Tao.taoZModThreeProjection hmn)
  let avgMass : ZMod (3 ^ n) → ℝ :=
    Tao.taoZModPowUniformLift hmn (fun x => (q x).toReal)
  have hcoarse :
      ndPMFWeightedExpectation q
          (ndZModPowProjectionFiberAverage hmn c) =
        ∑ y : ZMod (3 ^ n), avgMass y * c y := by
    unfold ndPMFWeightedExpectation
    rw [tsum_fintype]
    exact (sum_taoZModPowUniformLift_mul_eq_sum_mul_projectionFiberAverage
      hmn (fun x => (q x).toReal) c).symm
  have hdiff :
      ndPMFWeightedExpectation p c -
          ndPMFWeightedExpectation q
            (ndZModPowProjectionFiberAverage hmn c) =
        ∑ y : ZMod (3 ^ n), ((p y).toReal - avgMass y) * c y := by
    rw [hcoarse]
    unfold ndPMFWeightedExpectation
    rw [tsum_fintype, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _hy
    ring
  have hsum :
      |∑ y : ZMod (3 ^ n), ((p y).toReal - avgMass y) * c y| ≤
        H * ∑ y : ZMod (3 ^ n), |(p y).toReal - avgMass y| := by
    calc
      |∑ y : ZMod (3 ^ n), ((p y).toReal - avgMass y) * c y| ≤
          ∑ y : ZMod (3 ^ n),
            |((p y).toReal - avgMass y) * c y| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y : ZMod (3 ^ n),
          H * |(p y).toReal - avgMass y| := by
        apply Finset.sum_le_sum
        intro y _hy
        rw [abs_mul, abs_of_nonneg (hc0 y), mul_comm]
        exact mul_le_mul_of_nonneg_right (hcH y) (abs_nonneg _)
      _ = H * ∑ y : ZMod (3 ^ n), |(p y).toReal - avgMass y| := by
        rw [Finset.mul_sum]
  have hosc :
      Tao.taoZModPowOscillation m n (fun y => (p y).toReal) =
        ∑ y : ZMod (3 ^ n), |(p y).toReal - avgMass y| := by
    unfold Tao.taoZModPowOscillation
    change (∑ y : ZMod (3 ^ n),
      |(p y).toReal -
        Tao.zmodPowFiberAverage m n (fun z => (p z).toReal) y|) = _
    rw [ndZModPowFiberAverage_pmfMass_eq_uniformLift hmn p]
  rw [hdiff, hosc]
  exact hsum

/-- The local fixed-total terminal descent with FM1 still displayed as the
exact full-L1 oscillation.  The proportional reference term and the single
absolute ratio tail remain separate. -/
theorem abs_ndSection7FiberPMF_expectation_sub_syrac_projectionAverage_le
    {m n L : ℕ} (hm : 150 ≤ m) (hmn : 8 * m ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8)
    (hDelta :
      ndFixedTotalRatioCenterOffset m n L ≤ ndFixedTotalRatioScale m)
    (hEta : ndFixedTotalRatioEps m n L + 8 / (m : ℝ) ^ 3 ≤ 1)
    (c : ZMod (3 ^ n) → ℝ) (H : ℝ)
    (hc0 : ∀ y, 0 ≤ c y) (hcH : ∀ y, c y ≤ H) :
    |ndPMFWeightedExpectation
          (ndSection7FiberPMF n L (by omega)
            (ndFixedTotalRatio_n_le_L hm hmn hD)) c -
        ndPMFWeightedExpectation (Tao.syracPMF m)
          (ndZModPowProjectionFiberAverage (by omega) c)| ≤
      H * Tao.taoZModPowOscillation m n
          (fun y => (ndSection7FiberPMF n L (by omega)
            (ndFixedTotalRatio_n_le_L hm hmn hD) y).toReal) +
        (43 / 25 : ℝ) *
          (ndFixedTotalRatioEps m n L + 8 / (m : ℝ) ^ 3) *
          ndPMFWeightedExpectation (Tao.syracPMF m)
            (ndZModPowProjectionFiberAverage (by omega) c) +
        4 / (m : ℝ) ^ 3 * H := by
  let p : PMF (ZMod (3 ^ n)) :=
    ndSection7FiberPMF n L (by omega)
      (ndFixedTotalRatio_n_le_L hm hmn hD)
  let cbar : ZMod (3 ^ m) → ℝ :=
    ndZModPowProjectionFiberAverage (by omega) c
  have hcbar : ∀ x, 0 ≤ cbar x ∧ cbar x ≤ H := fun x =>
    ndZModPowProjectionFiberAverage_nonneg_le
      (by omega) c H hc0 hcH x
  have hmix :=
    abs_ndPMFWeightedExpectation_sub_projectionFiberAverage_le_oscillation
      (show m ≤ n by omega) p c H hc0 hcH
  have hratio :=
    abs_ndSection7FiberPMF_projection_expectation_sub_syrac_le_ratio
      hm hmn hD hDelta hEta cbar H
        (fun x => (hcbar x).1) (fun x => (hcbar x).2)
  calc
    |ndPMFWeightedExpectation p c -
        ndPMFWeightedExpectation (Tao.syracPMF m) cbar| ≤
      |ndPMFWeightedExpectation p c -
          ndPMFWeightedExpectation
            (p.map (Tao.taoZModThreeProjection (show m ≤ n by omega)))
            cbar| +
        |ndPMFWeightedExpectation
            (p.map (Tao.taoZModThreeProjection (show m ≤ n by omega)))
            cbar - ndPMFWeightedExpectation (Tao.syracPMF m) cbar| :=
      abs_sub_le _ _ _
    _ ≤ H * Tao.taoZModPowOscillation m n
          (fun y => (p y).toReal) +
        ((43 / 25 : ℝ) *
          (ndFixedTotalRatioEps m n L + 8 / (m : ℝ) ^ 3) *
          ndPMFWeightedExpectation (Tao.syracPMF m) cbar +
        4 / (m : ℝ) ^ 3 * H) := add_le_add hmix hratio
    _ = _ := by
      dsimp [p, cbar]
      ring

/-- Consumer-ready natural-exponent FM1 specialization of the local terminal
descent. -/
theorem abs_ndSection7FiberPMF_expectation_sub_syrac_projectionAverage_le_fm1
    {A : ℕ} {K C : ℝ}
    (hFM1 : ndSection7ConditionedFM1NatAt A K C)
    {m n L : ℕ} (hm : 150 ≤ m) (hmn : 8 * m ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8)
    (hWindow : ndSection7M1Window K n L)
    (hDelta :
      ndFixedTotalRatioCenterOffset m n L ≤ ndFixedTotalRatioScale m)
    (hEta : ndFixedTotalRatioEps m n L + 8 / (m : ℝ) ^ 3 ≤ 1)
    (c : ZMod (3 ^ n) → ℝ) (H : ℝ)
    (hc0 : ∀ y, 0 ≤ c y) (hcH : ∀ y, c y ≤ H) :
    |ndPMFWeightedExpectation
          (ndSection7FiberPMF n L (by omega)
            (ndFixedTotalRatio_n_le_L hm hmn hD)) c -
        ndPMFWeightedExpectation (Tao.syracPMF m)
          (ndZModPowProjectionFiberAverage (by omega) c)| ≤
      H * (C / (m : ℝ) ^ A) +
        (43 / 25 : ℝ) *
          (ndFixedTotalRatioEps m n L + 8 / (m : ℝ) ^ 3) *
          ndPMFWeightedExpectation (Tao.syracPMF m)
            (ndZModPowProjectionFiberAverage (by omega) c) +
        4 / (m : ℝ) ^ 3 * H := by
  have hbase :=
    abs_ndSection7FiberPMF_expectation_sub_syrac_projectionAverage_le
      hm hmn hD hDelta hEta c H hc0 hcH
  have hH0 : 0 ≤ H := (hc0 0).trans (hcH 0)
  have hosc :
      Tao.taoZModPowOscillation m n
          (fun y => (ndSection7FiberPMF n L (by omega)
            (ndFixedTotalRatio_n_le_L hm hmn hD) y).toReal) ≤
        C / (m : ℝ) ^ A :=
    hFM1 n (by omega) m (by omega) (by omega) L
      (ndFixedTotalRatio_n_le_L hm hmn hD) hWindow
  exact hbase.trans (by
    gcongr)

/-! Small exact normalization canaries. -/

private theorem nd_zmodPowFiberAverageScale_one_two :
    Tao.zmodPowFiberAverageScale 1 2 = (1 / 3 : ℝ) := by
  norm_num [Tao.zmodPowFiberAverageScale]

private theorem nd_projectionFiberAverage_const_one_two (k : ℝ)
    (x : ZMod (3 ^ 1)) :
    ndZModPowProjectionFiberAverage (show 1 ≤ 2 by omega)
        (fun _ : ZMod (3 ^ 2) => k) x = k := by
  unfold ndZModPowProjectionFiberAverage
  rw [nd_zmodPowFiberAverageScale_one_two]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show Fintype.card {y : ZMod (3 ^ 2) |
      Tao.taoZModThreeProjection (show 1 ≤ 2 by omega) y = x} = 3 by
    simpa using Tao.taoZModThreeProjection_fiber_card
      (show 1 ≤ 2 by omega) x]
  ring

end

end ND
end Erdos1135
