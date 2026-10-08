import Erdos1135.ND.Fourier.FixedTotalRatioNormalization

/-!
# Fixed-Total Ratio Descent Through D6

This leaf keeps a bounded nonnegative low-level test intact while the
fixed-total head law is compared with its Geom(2) reference.  The conditioned
head law binds back to the projected parent fiber, whereas the reference law
binds to the unconditional Syracuse law by the checked D6 identity.

The final half-absorption corollary has an explicit stronger hypothesis.  It
does not choose, or make a claim about, the frozen v10 reference scheduler.
-/

namespace Erdos1135
namespace ND

open Tao

noncomputable section

/-- Projecting a conditioned fixed-total fiber to a shorter level is exactly
the head-total mixture of the corresponding totalized shorter fibers. -/
theorem ndSection7FiberPMF_map_projection_eq_headTotalBind
    {m n L : ℕ} (hm : 0 < m) (hmn : m < n) (hnL : n ≤ L) :
    (ndSection7FiberPMF n L (by omega) hnL).map
        (Tao.taoZModThreeProjection hmn.le) =
      (ndFixedTotalHeadTotalPMF m n L hm hmn hnL).bind
        (ndSection7FiberPMFTotal m) := by
  have hsplit : m + (n - m) ≤ L := by omega
  calc
    (ndSection7FiberPMF n L (by omega) hnL).map
          (Tao.taoZModThreeProjection hmn.le) =
        (ndSection7FiberPMF (m + (n - m)) L (by omega) hsplit).map
          (Tao.taoZModThreeProjection
            (Nat.le_add_right m (n - m))) := by
      have hmnEq : m + (n - m) = n := Nat.add_sub_of_le hmn.le
      have hcongr : ∀ (a b : ℕ), a = b →
          ∀ (ha : 0 < a) (hb : 0 < b) (haL : a ≤ L) (hbL : b ≤ L)
            (hma : m ≤ a) (hmb : m ≤ b),
            (ndSection7FiberPMF a L ha haL).map
                (Tao.taoZModThreeProjection hma) =
              (ndSection7FiberPMF b L hb hbL).map
                (Tao.taoZModThreeProjection hmb) := by
        intro a b hab ha hb haL hbL hma hmb
        subst b
        rfl
      exact hcongr n (m + (n - m)) hmnEq.symm
        (by omega) (by omega) hnL hsplit hmn.le
        (Nat.le_add_right m (n - m))
    _ = (ndFixedTotalSplitIndexPMF m (n - m) L hm hsplit).bind
          (fun s => ndSection7FiberPMF
            m s.headTotal hm s.headLength_le) :=
      ndSection7FiberPMF_map_projection_eq_splitBind
        m (n - m) L hm hsplit
    _ = (ndFixedTotalSplitIndexPMF m (n - m) L hm hsplit).bind
          (fun s => ndSection7FiberPMFTotal m s.headTotal) := by
      apply congrArg
        (fun K => (ndFixedTotalSplitIndexPMF m (n - m) L hm hsplit).bind K)
      funext s
      exact (ndSection7FiberPMFTotal_eq_of_pos_of_le
        hm s.headLength_le).symm
    _ = (ndFixedTotalHeadTotalPMF m n L hm hmn hnL).bind
          (ndSection7FiberPMFTotal m) := by
      unfold ndFixedTotalHeadTotalPMF
      simp [PMF.bind_map, Function.comp_def]

/-- The real mass of a countable PMF bind is the corresponding real tower
sum. -/
private theorem ndPMF_bind_apply_toReal_eq_tsum
    {α β : Type*} (p : PMF α) (q : α → PMF β) (y : β) :
    ((p.bind q) y).toReal =
      ∑' u, (p u).toReal * (q u y).toReal := by
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro u
    rw [ENNReal.toReal_mul]
  · intro u
    exact ENNReal.mul_ne_top
      (p.apply_ne_top u) ((q u).apply_ne_top y)

/-- A fixed target atom, integrated through an arbitrary PMF kernel, is a
summable test on the outer PMF. -/
private theorem ndPMF_mul_kernel_apply_toReal_summable
    {α β : Type*} (p : PMF α) (q : α → PMF β) (y : β) :
    Summable fun u => (p u).toReal * (q u y).toReal := by
  apply Summable.of_nonneg_of_le
  · intro u
    positivity
  · intro u
    have hq : (q u y).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (by simp)
        ((q u).coe_le_one y)
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg hq
  · exact Tao.taoPMF_summable_toReal p

/-- Finite-target expectation commutes with a countable PMF bind. -/
theorem ndPMFWeightedExpectation_bind
    {α β : Type*} [Fintype β]
    (p : PMF α) (q : α → PMF β) (c : β → ℝ) :
    ndPMFWeightedExpectation (p.bind q) c =
      ndPMFWeightedExpectation p
        (fun u => ndPMFWeightedExpectation (q u) c) := by
  classical
  unfold ndPMFWeightedExpectation
  rw [tsum_fintype]
  simp_rw [ndPMF_bind_apply_toReal_eq_tsum]
  calc
    (∑ y, (∑' u, (p u).toReal * (q u y).toReal) * c y) =
        ∑ y, ∑' u, (p u).toReal * (q u y).toReal * c y := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [← tsum_mul_right]
    _ = ∑' u, ∑ y, (p u).toReal * (q u y).toReal * c y :=
      (Summable.tsum_finsetSum (fun y _hy =>
        (ndPMF_mul_kernel_apply_toReal_summable p q y).mul_right
          (c y))).symm
    _ = ∑' u, (p u).toReal * ∑' y, (q u y).toReal * c y := by
      apply tsum_congr
      intro u
      rw [tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _hy
      ring

/-- Exact expectation form of D6.  The common Geom(2) endpoint law followed
by its totalized conditioned fibers is the unconditional Syracuse law. -/
theorem ndPMFWeightedExpectation_endpoint_fiberTotal_eq_syrac
    (m : ℕ) (c : ZMod (3 ^ m) → ℝ) :
    ndPMFWeightedExpectation (ndGeom2EndpointPMF m)
        (fun u => ndPMFWeightedExpectation
          (ndSection7FiberPMFTotal m u) c) =
      ndPMFWeightedExpectation (Tao.syracPMF m) c := by
  rw [← ndPMFWeightedExpectation_bind]
  rw [ndGeom2EndpointPMF_bind_fiberTotal_eq_syracPMF]

/-- A bounded nonnegative finite test remains bounded after expectation under
any PMF. -/
theorem ndPMFWeightedExpectation_nonneg_le
    {α : Type*} [Fintype α]
    (p : PMF α) (c : α → ℝ) (H : ℝ)
    (hc0 : ∀ y, 0 ≤ c y) (hcH : ∀ y, c y ≤ H) :
    0 ≤ ndPMFWeightedExpectation p c ∧
      ndPMFWeightedExpectation p c ≤ H := by
  classical
  unfold ndPMFWeightedExpectation
  rw [tsum_fintype]
  constructor
  · exact Finset.sum_nonneg fun y _hy =>
      mul_nonneg ENNReal.toReal_nonneg (hc0 y)
  · calc
      (∑ y, (p y).toReal * c y) ≤
          ∑ y, (p y).toReal * H :=
        Finset.sum_le_sum fun y _hy =>
          mul_le_mul_of_nonneg_left (hcH y) ENNReal.toReal_nonneg
      _ = H := by
        rw [← Finset.sum_mul, Tao.pmf_sum_toReal, one_mul]

/-- Exact signed tower identity for the D5 comparison.  The conditioned
head-total mixture is the projected parent fiber and the reference mixture is
the unconditional Syracuse law. -/
theorem tsum_ndFixedTotalHeadTotalPMF_sub_reference_mul_fiberExpectation_eq
    {m n L : ℕ} (hm : 0 < m) (hmn : m < n) (hnL : n ≤ L)
    (c : ZMod (3 ^ m) → ℝ) (H : ℝ)
    (hc0 : ∀ y, 0 ≤ c y) (hcH : ∀ y, c y ≤ H) :
    (∑' u,
        ((ndFixedTotalHeadTotalPMF m n L hm hmn hnL u).toReal -
          (ndGeom2EndpointPMF m u).toReal) *
        ndPMFWeightedExpectation (ndSection7FiberPMFTotal m u) c) =
      ndPMFWeightedExpectation
          ((ndSection7FiberPMF n L (by omega) hnL).map
            (Tao.taoZModThreeProjection hmn.le)) c -
        ndPMFWeightedExpectation (Tao.syracPMF m) c := by
  let p : PMF ℕ := ndFixedTotalHeadTotalPMF m n L hm hmn hnL
  let q : PMF ℕ := ndGeom2EndpointPMF m
  let K : ℕ → PMF (ZMod (3 ^ m)) := ndSection7FiberPMFTotal m
  let phi : ℕ → ℝ := fun u => ndPMFWeightedExpectation (K u) c
  have hphi : ∀ u, 0 ≤ phi u ∧ phi u ≤ H := fun u =>
    ndPMFWeightedExpectation_nonneg_le (K u) c H hc0 hcH
  have hpPhi : Summable fun u => (p u).toReal * phi u := by
    have hp : Summable fun u => H * (p u).toReal :=
      (Tao.taoPMF_summable_toReal p).mul_left H
    exact Summable.of_nonneg_of_le
      (fun u => mul_nonneg ENNReal.toReal_nonneg (hphi u).1)
      (fun u => by
        have h := mul_le_mul_of_nonneg_left (hphi u).2
          (show 0 ≤ (p u).toReal from ENNReal.toReal_nonneg)
        simpa [mul_comm] using h)
      hp
  have hqPhi : Summable fun u => (q u).toReal * phi u := by
    have hq : Summable fun u => H * (q u).toReal :=
      (Tao.taoPMF_summable_toReal q).mul_left H
    exact Summable.of_nonneg_of_le
      (fun u => mul_nonneg ENNReal.toReal_nonneg (hphi u).1)
      (fun u => by
        have h := mul_le_mul_of_nonneg_left (hphi u).2
          (show 0 ≤ (q u).toReal from ENNReal.toReal_nonneg)
        simpa [mul_comm] using h)
      hq
  calc
    (∑' u, ((p u).toReal - (q u).toReal) * phi u) =
        (∑' u, (p u).toReal * phi u) -
          ∑' u, (q u).toReal * phi u := by
      rw [← hpPhi.tsum_sub hqPhi]
      apply tsum_congr
      intro u
      ring
    _ = ndPMFWeightedExpectation (p.bind K) c -
          ndPMFWeightedExpectation (q.bind K) c := by
      rw [ndPMFWeightedExpectation_bind, ndPMFWeightedExpectation_bind]
      rfl
    _ = ndPMFWeightedExpectation
          ((ndSection7FiberPMF n L (by omega) hnL).map
            (Tao.taoZModThreeProjection hmn.le)) c -
        ndPMFWeightedExpectation (Tao.syracPMF m) c := by
      rw [← ndSection7FiberPMF_map_projection_eq_headTotalBind
          hm hmn hnL,
        ndGeom2EndpointPMF_bind_fiberTotal_eq_syracPMF]

/-- Local D5/D6 comparison with the source-v10 decaying coefficient retained.
The bounded low-level test is resolved before the absolute value, so the
outside tail `4/m^3 * H` is paid only once. -/
theorem abs_ndSection7FiberPMF_projection_expectation_sub_syrac_le_ratio
    {m n L : ℕ} (hm : 150 ≤ m) (hmn : 8 * m ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8)
    (hDelta :
      ndFixedTotalRatioCenterOffset m n L ≤ ndFixedTotalRatioScale m)
    (hEta : ndFixedTotalRatioEps m n L + 8 / (m : ℝ) ^ 3 ≤ 1)
    (c : ZMod (3 ^ m) → ℝ) (H : ℝ)
    (hc0 : ∀ y, 0 ≤ c y) (hcH : ∀ y, c y ≤ H) :
    |ndPMFWeightedExpectation
          ((ndSection7FiberPMF n L (by omega)
            (ndFixedTotalRatio_n_le_L hm hmn hD)).map
            (Tao.taoZModThreeProjection (by omega))) c -
        ndPMFWeightedExpectation (Tao.syracPMF m) c| ≤
      (43 / 25 : ℝ) *
          (ndFixedTotalRatioEps m n L + 8 / (m : ℝ) ^ 3) *
          ndPMFWeightedExpectation (Tao.syracPMF m) c +
        4 / (m : ℝ) ^ 3 * H := by
  let phi : ℕ → ℝ := fun u =>
    ndPMFWeightedExpectation (ndSection7FiberPMFTotal m u) c
  have hphi : ∀ u, 0 ≤ phi u ∧ phi u ≤ H := fun u =>
    ndPMFWeightedExpectation_nonneg_le
      (ndSection7FiberPMFTotal m u) c H hc0 hcH
  have hratio := abs_ndFixedTotalHeadTotalPMF_weightedDifference_le_ratio
    hm hmn hD hDelta hEta phi H
      (fun u => (hphi u).1) (fun u => (hphi u).2)
  rw [tsum_ndFixedTotalHeadTotalPMF_sub_reference_mul_fiberExpectation_eq
      (m := m) (n := n) (L := L) (by omega) (by omega)
      (ndFixedTotalRatio_n_le_L hm hmn hD) c H hc0 hcH] at hratio
  rw [ndPMFWeightedExpectation_endpoint_fiberTotal_eq_syrac] at hratio
  exact hratio

/-- Schedule-neutral half absorption for the local D5/D6 comparison.  The
hypothesis is deliberately stronger than the source-v10 displayed `eta ≤ 1`
guard, and the absolute outside-tail term remains separate. -/
theorem abs_ndSection7FiberPMF_projection_expectation_sub_syrac_le_half
    {m n L : ℕ} (hm : 150 ≤ m) (hmn : 8 * m ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8)
    (hDelta :
      ndFixedTotalRatioCenterOffset m n L ≤ ndFixedTotalRatioScale m)
    (hAbsorb :
      (43 / 25 : ℝ) *
          (ndFixedTotalRatioEps m n L + 8 / (m : ℝ) ^ 3) ≤ 1 / 2)
    (c : ZMod (3 ^ m) → ℝ) (H : ℝ)
    (hc0 : ∀ y, 0 ≤ c y) (hcH : ∀ y, c y ≤ H) :
    |ndPMFWeightedExpectation
          ((ndSection7FiberPMF n L (by omega)
            (ndFixedTotalRatio_n_le_L hm hmn hD)).map
            (Tao.taoZModThreeProjection (by omega))) c -
        ndPMFWeightedExpectation (Tao.syracPMF m) c| ≤
      (1 / 2 : ℝ) * ndPMFWeightedExpectation (Tao.syracPMF m) c +
        4 / (m : ℝ) ^ 3 * H := by
  have heta0 :
      0 ≤ ndFixedTotalRatioEps m n L + 8 / (m : ℝ) ^ 3 := by
    unfold ndFixedTotalRatioEps ndFixedTotalRatioCenterOffset
    have hlog : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
    positivity
  have hEta : ndFixedTotalRatioEps m n L + 8 / (m : ℝ) ^ 3 ≤ 1 := by
    have hCoeff : (0 : ℝ) < 43 / 25 := by norm_num
    have hhalf : (1 / 2 : ℝ) ≤ 43 / 25 := by norm_num
    calc
      ndFixedTotalRatioEps m n L + 8 / (m : ℝ) ^ 3 ≤
          (43 / 25 : ℝ) *
            (ndFixedTotalRatioEps m n L + 8 / (m : ℝ) ^ 3) := by
        nlinarith
      _ ≤ 1 / 2 := hAbsorb
      _ ≤ 1 := by norm_num
  have hraw :=
    abs_ndSection7FiberPMF_projection_expectation_sub_syrac_le_ratio
      hm hmn hD hDelta hEta c H hc0 hcH
  have href0 :
      0 ≤ ndPMFWeightedExpectation (Tao.syracPMF m) c :=
    (ndPMFWeightedExpectation_nonneg_le
      (Tao.syracPMF m) c H hc0 hcH).1
  exact hraw.trans (by
    gcongr)

end

end ND
end Erdos1135
