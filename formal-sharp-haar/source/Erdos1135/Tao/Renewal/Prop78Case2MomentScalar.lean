import Erdos1135.Tao.Renewal.Prop78Boundary
import Erdos1135.Tao.Renewal.Prop78Case1Scalar

/-!
# Proposition 7.8 Case 2 Moment Absorption

This leaf proves that the exact Geom(4) MGF accumulated over a near-top
first-passage horizon is eventually at most `1 + epsilon^3 / 8`.
-/

open scoped BigOperators Topology

namespace Erdos1135
namespace Tao

noncomputable section

private theorem one_sub_inv_le_exp_two_mul_case2
    {x : ℝ} (hx : 0 ≤ x) (hxhalf : 2 * x ≤ 1) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have hden : 0 < 1 - x := by linarith
  calc
    (1 - x)⁻¹ ≤ 1 + 2 * x := (inv_le_iff_one_le_mul₀ hden).2 (by
      nlinarith [mul_nonneg hx (by linarith : 0 ≤ 1 - 2 * x)])
    _ = 2 * x + 1 := by ring
    _ ≤ Real.exp (2 * x) := Real.add_one_le_exp (2 * x)

/-- At a sufficiently small nonnegative rate, the Geom(4) MGF is bounded by
one exponential with a fixed absolute slope. -/
theorem taoSection7Geom4ExpMoment_le_exp_eight_mul
    {t : ℝ} (ht0 : 0 ≤ t) (htsmall : 8 * t ≤ 1) :
    3 * Real.exp t < 4 ∧
      taoSection7Geom4ExpMoment t ≤ Real.exp (8 * t) := by
  have ht1 : t < 1 := by linarith
  have hden1 : 0 < 1 - t := by linarith
  have hexpInv : Real.exp t ≤ (1 - t)⁻¹ := by
    simpa [one_div] using
      Real.exp_bound_div_one_sub_of_interval ht0 ht1
  have hinv87 : (1 - t)⁻¹ ≤ (8 / 7 : ℝ) := by
    rw [inv_le_iff_one_le_mul₀ hden1]
    nlinarith
  have hadm : 3 * Real.exp t < 4 := by
    nlinarith [hexpInv.trans hinv87]
  have hdenM : 0 < 4 - 3 * Real.exp t := by linarith
  have hden4 : 0 < 1 - 4 * t := by linarith
  have hprod : Real.exp t * (1 - t) ≤ 1 := by
    calc
      Real.exp t * (1 - t) ≤ (1 - t)⁻¹ * (1 - t) := by
        exact mul_le_mul_of_nonneg_right hexpInv hden1.le
      _ = 1 := by field_simp
  have hmgfInv :
      taoSection7Geom4ExpMoment t ≤ (1 - 4 * t)⁻¹ := by
    rw [taoSection7Geom4ExpMoment_eq hadm]
    rw [show (1 - 4 * t)⁻¹ = 1 / (1 - 4 * t) by
      rw [one_div]]
    rw [div_le_div_iff₀ hdenM hden4]
    nlinarith
  have hinvExp : (1 - 4 * t)⁻¹ ≤ Real.exp (8 * t) := by
    simpa only [show 2 * (4 * t) = 8 * t by ring] using
      one_sub_inv_le_exp_two_mul_case2
        (show 0 ≤ 4 * t by positivity) (by nlinarith)
  exact ⟨hadm, hmgfInv.trans hinvExp⟩

/-- The Case 1 rate times the largest near-top horizon tends to zero. -/
theorem tendsto_taoSection7Case1Rate_mul_boundaryThreshold_add_one
    (A : ℕ) :
    Filter.Tendsto
      (fun m : ℕ =>
        8 * taoSection7Case1Rate A m *
          (taoSection7Prop78BoundaryThreshold m + 1))
      Filter.atTop (nhds 0) := by
  have hlog : Filter.Tendsto (fun m : ℕ => Real.log (m : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto
      (fun m : ℕ => (Real.log (m : ℝ))⁻¹)
      Filter.atTop (nhds 0) := hlog.inv_tendsto_atTop
  have hmodel : Filter.Tendsto
      (fun m : ℕ =>
        32 * (A : ℝ) *
            ((Real.log (m : ℝ))⁻¹ ^ 2 +
              (Real.log (m : ℝ))⁻¹) +
          8 * taoSection7Case1Rate A m)
      Filter.atTop (nhds 0) := by
    simpa using
      (((hinv.pow 2).add hinv).const_mul (32 * (A : ℝ))).add
        ((tendsto_taoSection7Case1Rate A).const_mul 8)
  refine hmodel.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hlog0 : Real.log (m : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
  unfold taoSection7Case1Rate taoSection7Prop78BoundaryThreshold
  field_simp [hm0, hlog0]
  ring

/-- Uniform near-top MGF absorption at every sufficiently large boundary
level.  The threshold depends only on `A` and the already fixed `epsilon`. -/
theorem exists_taoSection7Prop78_nearTopGeom4ExpMoment_threshold
    (A : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, ∀ m ≥ C, ∀ s : ℕ,
      (s : ℝ) ≤ taoSection7Prop78BoundaryThreshold m →
        0 ≤ taoSection7Case1Rate A m ∧
        3 * Real.exp (taoSection7Case1Rate A m) < 4 ∧
        taoSection7Geom4ExpMoment
            (taoSection7Case1Rate A m) ^ (s + 1) ≤
          1 + epsilon ^ 3 / 8 := by
  let q : ℝ := 1 + epsilon ^ 3 / 8
  have hq1 : 1 < q := by
    dsimp [q]
    have hepsilonCube : 0 < epsilon ^ 3 := by positivity
    linarith
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hrateSmall : ∀ᶠ m : ℕ in Filter.atTop,
      8 * taoSection7Case1Rate A m < 1 := by
    have h := (tendsto_taoSection7Case1Rate A).const_mul 8
    have h0 : Filter.Tendsto
        (fun m : ℕ => 8 * taoSection7Case1Rate A m)
        Filter.atTop (nhds 0) := by simpa using h
    exact h0.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)
  have hproductSmall : ∀ᶠ m : ℕ in Filter.atTop,
      8 * taoSection7Case1Rate A m *
          (taoSection7Prop78BoundaryThreshold m + 1) <
        Real.log q :=
    (tendsto_taoSection7Case1Rate_mul_boundaryThreshold_add_one A)
      |>.eventually_lt_const hlogq
  have hboth : ∀ᶠ m : ℕ in Filter.atTop,
      2 ≤ m ∧
      8 * taoSection7Case1Rate A m < 1 ∧
      8 * taoSection7Case1Rate A m *
          (taoSection7Prop78BoundaryThreshold m + 1) <
        Real.log q := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ), hrateSmall,
      hproductSmall] with m hm hr hp
    exact ⟨hm, hr, hp⟩
  rcases Filter.eventually_atTop.1 hboth with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro m hm s hs
  rcases hC m hm with ⟨hm2, hrateSmall', hproductSmall'⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hrate0 : 0 ≤ taoSection7Case1Rate A m := by
    unfold taoSection7Case1Rate
    have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
    positivity
  have henv := taoSection7Geom4ExpMoment_le_exp_eight_mul
    hrate0 hrateSmall'.le
  have hmgf0 :
      0 ≤ taoSection7Geom4ExpMoment (taoSection7Case1Rate A m) := by
    unfold taoSection7Geom4ExpMoment
    exact tsum_nonneg fun r =>
      mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  have hs1 : ((s + 1 : ℕ) : ℝ) ≤
      taoSection7Prop78BoundaryThreshold m + 1 := by
    push_cast
    linarith
  have hexponent :
      8 * taoSection7Case1Rate A m * ((s + 1 : ℕ) : ℝ) ≤
        Real.log q := by
    calc
      8 * taoSection7Case1Rate A m * ((s + 1 : ℕ) : ℝ) ≤
          8 * taoSection7Case1Rate A m *
            (taoSection7Prop78BoundaryThreshold m + 1) := by gcongr
      _ ≤ Real.log q := hproductSmall'.le
  refine ⟨hrate0, henv.1, ?_⟩
  calc
    taoSection7Geom4ExpMoment
          (taoSection7Case1Rate A m) ^ (s + 1) ≤
        Real.exp (8 * taoSection7Case1Rate A m) ^ (s + 1) :=
      pow_le_pow_left₀
        hmgf0 henv.2 (s + 1)
    _ = Real.exp
        (8 * taoSection7Case1Rate A m * ((s + 1 : ℕ) : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (Real.log q) := Real.exp_le_exp.mpr hexponent
    _ = 1 + epsilon ^ 3 / 8 := by
      rw [Real.exp_log (show 0 < q from hq1.trans' zero_lt_one)]

end

end Tao
end Erdos1135
