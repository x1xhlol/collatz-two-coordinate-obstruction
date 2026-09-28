import Erdos1135.ND.Fourier.FixedTotalRatioWindow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Fixed-Total Ratio Telescope

This leaf consumes the literal fixed-total ratio window.  It proves the
ordered `Finset.Ico` logarithmic telescope, symmetrizes it, and retains the
frozen `57/1021` endpoint.  The two outside-tail estimates and countable R1
normalization are separate later interfaces.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- The literal closed ratio window contains every natural point between two
of its members. -/
theorem ndFixedTotalRatioGood_between
    {j a b k : ℕ} (ha : ndFixedTotalRatioGood j a)
    (hb : ndFixedTotalRatioGood j b) (hak : a ≤ k) (hkb : k ≤ b) :
    ndFixedTotalRatioGood j k := by
  rcases ha with ⟨hja, ha⟩
  rcases hb with ⟨_, hb⟩
  have hakR : (a : ℝ) ≤ (k : ℝ) := by exact_mod_cast hak
  have hkbR : (k : ℝ) ≤ (b : ℝ) := by exact_mod_cast hkb
  constructor
  · omega
  · rw [abs_le] at ha hb ⊢
    constructor <;> linarith

/-- H2 and `8*j <= n` already put the parent total on feasible support. -/
theorem ndFixedTotalRatio_n_le_L
    {j n L : ℕ} (hj : 150 ≤ j) (hjn : 8 * j ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8) :
    n ≤ L := by
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hneg := neg_le_of_abs_le hD
  have hnLR : (n : ℝ) ≤ (L : ℝ) := by nlinarith
  exact_mod_cast hnLR

/-- Uniform central denominator lower bound in real displacement notation. -/
theorem six_fifths_mul_le_fixedTotalRatio_denominator
    {j n L u : ℕ} (hj : 150 ≤ j) (hjn : 8 * j ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8)
    (hu : ndFixedTotalRatioGood j u) :
    (6 / 5 : ℝ) * (n : ℝ) ≤ (L : ℝ) - (u : ℝ) - 1 := by
  have hn1200 : 1200 ≤ n := by omega
  have hneg := neg_le_of_abs_le hD
  have hu5 : u ≤ 5 * j := ndFixedTotalRatioGood_le_five_mul hj hu
  have hn1200R : (1200 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1200
  have hjnR : (8 * j : ℕ) ≤ n := hjn
  have hjnR' : (8 : ℝ) * (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjnR
  have hu5R : (u : ℝ) ≤ 5 * (j : ℝ) := by exact_mod_cast hu5
  nlinarith

/-- Uniform central numerator bound, with enough slack to retain `9/20`. -/
theorem fixedTotalRatio_numerator_le_twentySeven_fiftieths
    {j n L u : ℕ} (hj : 150 ≤ j) (hjn : 8 * j ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8)
    (hu : ndFixedTotalRatioGood j u) :
    |(L : ℝ) - 2 * (n : ℝ)| +
        |(u : ℝ) - 2 * (j : ℝ)| + 1 ≤
      (27 / 50 : ℝ) * (n : ℝ) := by
  have hn1200 : 1200 ≤ n := by omega
  have hradius := ndFixedTotalRatioRadius_le_three_mul hj
  have hradiusR :
      (ndFixedTotalRatioRadius j : ℝ) ≤ 3 * (j : ℝ) := by
    exact_mod_cast hradius
  have hjnR : (8 : ℝ) * (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
  have hn1200R : (1200 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1200
  have huCenter :
      |(u : ℝ) - 2 * (j : ℝ)| ≤ 3 * (j : ℝ) :=
    hu.2.trans hradiusR
  nlinarith

/-- The adjacent multiplier remains in the fixed logarithmic neighborhood of
one throughout the literal central window. -/
theorem abs_ndFixedTotalHeadLikelihoodStep_sub_one_le_nine_twentieths
    {j n L u : ℕ} (hj : 150 ≤ j) (hjn : 8 * j ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8)
    (hu : ndFixedTotalRatioGood j u) :
    |ndFixedTotalHeadLikelihoodStep j n L u - 1| ≤ (9 / 20 : ℝ) := by
  have hjn' : j < n := by omega
  have hroom := ndFixedTotalRatioGood_strict_suffix_room hj hjn hD hu
  have hbase := abs_ndFixedTotalHeadLikelihoodStep_sub_one_le hjn' hroom
  have hnum := fixedTotalRatio_numerator_le_twentySeven_fiftieths hj hjn hD hu
  have hden := six_fifths_mul_le_fixedTotalRatio_denominator hj hjn hD hu
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdenPos : (0 : ℝ) < (L : ℝ) - (u : ℝ) - 1 := by
    nlinarith
  apply hbase.trans
  rw [div_le_iff₀ hdenPos]
  nlinarith

/-- A local logarithm is at most twice its displacement from one in the
central `9/20` neighborhood. -/
theorem abs_log_le_two_mul_abs_sub_one
    {x : ℝ} (_hx : 0 < x) (hclose : |x - 1| ≤ (9 / 20 : ℝ)) :
    |Real.log x| ≤ 2 * |x - 1| := by
  let y : ℝ := 1 - x
  have hy : |y| ≤ (9 / 20 : ℝ) := by
    simpa only [y, abs_sub_comm] using hclose
  have hylt : |y| < 1 := hy.trans_lt (by norm_num)
  have hseries := Real.abs_log_sub_add_sum_range_le hylt 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_one] at hseries
  have hden : (0 : ℝ) < 1 - |y| := by linarith
  have hfrac : |y| / (1 - |y|) ≤ 2 * |y| := by
    rw [div_le_iff₀ hden]
    nlinarith [abs_nonneg y]
  have hlog : |Real.log (1 - y)| ≤ 2 * |y| := hseries.trans hfrac
  simpa only [y, sub_sub_cancel, abs_sub_comm] using hlog

/-- The local log step retains the scale-sensitive numerator needed by the
finite telescope. -/
theorem abs_log_ndFixedTotalHeadLikelihoodStep_le
    {j n L u : ℕ} (hj : 150 ≤ j) (hjn : 8 * j ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8)
    (hu : ndFixedTotalRatioGood j u) :
    |Real.log (ndFixedTotalHeadLikelihoodStep j n L u)| ≤
      (5 / 3 : ℝ) *
        (|(L : ℝ) - 2 * (n : ℝ)| +
          (ndFixedTotalRatioRadius j : ℝ) + 1) / (n : ℝ) := by
  have hjn' : j < n := by omega
  have hroom := ndFixedTotalRatioGood_strict_suffix_room hj hjn hD hu
  have hstep : 0 < ndFixedTotalHeadLikelihoodStep j n L u :=
    ndFixedTotalHeadLikelihoodStep_pos hjn' hroom
  have hclose :=
    abs_ndFixedTotalHeadLikelihoodStep_sub_one_le_nine_twentieths hj hjn hD hu
  have hlog := abs_log_le_two_mul_abs_sub_one hstep hclose
  have htriangle := abs_ndFixedTotalHeadLikelihoodStep_sub_one_le hjn' hroom
  have hden := six_fifths_mul_le_fixedTotalRatio_denominator hj hjn hD hu
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdenPos : (0 : ℝ) < (L : ℝ) - (u : ℝ) - 1 := by nlinarith
  have hnum :
      0 ≤ |(L : ℝ) - 2 * (n : ℝ)| +
        (ndFixedTotalRatioRadius j : ℝ) + 1 := by positivity
  calc
    |Real.log (ndFixedTotalHeadLikelihoodStep j n L u)| ≤
        2 * |ndFixedTotalHeadLikelihoodStep j n L u - 1| := hlog
    _ ≤ 2 *
        ((|(L : ℝ) - 2 * (n : ℝ)| +
            |(u : ℝ) - 2 * (j : ℝ)| + 1) /
          ((L : ℝ) - (u : ℝ) - 1)) := by
      gcongr
    _ ≤ 2 *
        ((|(L : ℝ) - 2 * (n : ℝ)| +
            (ndFixedTotalRatioRadius j : ℝ) + 1) /
          ((L : ℝ) - (u : ℝ) - 1)) := by
      gcongr
      exact hu.2
    _ ≤ 2 *
        ((|(L : ℝ) - 2 * (n : ℝ)| +
            (ndFixedTotalRatioRadius j : ℝ) + 1) /
          ((6 / 5 : ℝ) * (n : ℝ))) := by
      gcongr
    _ = (5 / 3 : ℝ) *
        (|(L : ℝ) - 2 * (n : ℝ)| +
          (ndFixedTotalRatioRadius j : ℝ) + 1) / (n : ℝ) := by
      field_simp
      ring

/-- Exact ordered logarithmic factor telescope.  The edge set is `Ico`, so
the right endpoint is never used as a successor edge. -/
theorem log_ndFixedTotalHeadLikelihoodFactor_sub_eq_sum_Ico
    {j n L u v : ℕ} (hjn : j < n) (hnL : n ≤ L) (huv : u ≤ v)
    (hvTail : v + (n - j) ≤ L) :
    Real.log (ndFixedTotalHeadLikelihoodFactor j n L v) -
        Real.log (ndFixedTotalHeadLikelihoodFactor j n L u) =
      ∑ k ∈ Finset.Ico u v,
        Real.log (ndFixedTotalHeadLikelihoodStep j n L k) := by
  rw [← Finset.sum_Ico_sub
    (f := fun k => Real.log (ndFixedTotalHeadLikelihoodFactor j n L k)) huv]
  apply Finset.sum_congr rfl
  intro k hk
  have hkIco := Finset.mem_Ico.mp hk
  exact log_ndFixedTotalHeadLikelihoodFactor_succ_sub_eq_log_step
    hjn hnL (by omega)

/-- Ordered factor oscillation before the literal window length is absorbed. -/
theorem abs_log_ndFixedTotalHeadLikelihoodFactor_sub_le_ordered
    {j n L u v : ℕ} (hj : 150 ≤ j) (hjn : 8 * j ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8)
    (hu : ndFixedTotalRatioGood j u) (hv : ndFixedTotalRatioGood j v)
    (huv : u ≤ v) :
    |Real.log (ndFixedTotalHeadLikelihoodFactor j n L v) -
        Real.log (ndFixedTotalHeadLikelihoodFactor j n L u)| ≤
      ((v - u : ℕ) : ℝ) * (5 / 3 : ℝ) *
        (|(L : ℝ) - 2 * (n : ℝ)| +
          (ndFixedTotalRatioRadius j : ℝ) + 1) / (n : ℝ) := by
  have hjn' : j < n := by omega
  have hnL := ndFixedTotalRatio_n_le_L hj hjn hD
  have hvRoom := ndFixedTotalRatioGood_strict_suffix_room hj hjn hD hv
  have htel := log_ndFixedTotalHeadLikelihoodFactor_sub_eq_sum_Ico
    hjn' hnL huv (Nat.le_of_lt hvRoom)
  calc
    |Real.log (ndFixedTotalHeadLikelihoodFactor j n L v) -
        Real.log (ndFixedTotalHeadLikelihoodFactor j n L u)| =
        |∑ k ∈ Finset.Ico u v,
          Real.log (ndFixedTotalHeadLikelihoodStep j n L k)| := by
      rw [htel]
    _ ≤ ∑ k ∈ Finset.Ico u v,
        |Real.log (ndFixedTotalHeadLikelihoodStep j n L k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Ico u v,
        (5 / 3 : ℝ) *
          (|(L : ℝ) - 2 * (n : ℝ)| +
            (ndFixedTotalRatioRadius j : ℝ) + 1) / (n : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkIco := Finset.mem_Ico.mp hk
      exact abs_log_ndFixedTotalHeadLikelihoodStep_le hj hjn hD
        (ndFixedTotalRatioGood_between hu hv hkIco.1 (Nat.le_of_lt hkIco.2))
    _ = ((v - u : ℕ) : ℝ) * (5 / 3 : ℝ) *
        (|(L : ℝ) - 2 * (n : ℝ)| +
          (ndFixedTotalRatioRadius j : ℝ) + 1) / (n : ℝ) := by
      simp [Nat.card_Ico]
      ring

/-- Ordered factor oscillation with the frozen raw `57/1021` constants. -/
theorem abs_log_ndFixedTotalHeadLikelihoodFactor_sub_le_raw_ordered
    {j n L u v : ℕ} (hj : 150 ≤ j) (hjn : 8 * j ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8)
    (hu : ndFixedTotalRatioGood j u) (hv : ndFixedTotalRatioGood j v)
    (huv : u ≤ v) :
    |Real.log (ndFixedTotalHeadLikelihoodFactor j n L v) -
        Real.log (ndFixedTotalHeadLikelihoodFactor j n L u)| ≤
      57 * ndFixedTotalRatioScale j *
          |(L : ℝ) - 2 * (n : ℝ)| / (n : ℝ) +
        1021 * ndFixedTotalRatioScale j ^ 2 / (n : ℝ) := by
  have hordered :=
    abs_log_ndFixedTotalHeadLikelihoodFactor_sub_le_ordered
      hj hjn hD hu hv huv
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have huAbs := hu.2
  have hvAbs := hv.2
  rw [abs_le] at huAbs hvAbs
  have huvR : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huv
  have hcountRadius :
      ((v - u : ℕ) : ℝ) ≤
        2 * (ndFixedTotalRatioRadius j : ℝ) + 1 := by
    rw [Nat.cast_sub huv]
    nlinarith
  have hcount :
      ((v - u : ℕ) : ℝ) ≤ 34 * ndFixedTotalRatioScale j :=
    hcountRadius.trans (two_mul_radius_add_one_le_thirtyFour_mul_scale hj)
  have hradius := radius_add_one_le_eighteen_mul_scale hj
  have hscale : 0 ≤ ndFixedTotalRatioScale j :=
    ndFixedTotalRatioScale_nonneg j
  have hDnonneg : 0 ≤ |(L : ℝ) - 2 * (n : ℝ)| := abs_nonneg _
  have hsum :
      |(L : ℝ) - 2 * (n : ℝ)| +
          (ndFixedTotalRatioRadius j : ℝ) + 1 ≤
        |(L : ℝ) - 2 * (n : ℝ)| +
          18 * ndFixedTotalRatioScale j := by
    linarith
  have hprod :
      ((v - u : ℕ) : ℝ) * (5 / 3 : ℝ) *
          (|(L : ℝ) - 2 * (n : ℝ)| +
            (ndFixedTotalRatioRadius j : ℝ) + 1) ≤
        (34 * ndFixedTotalRatioScale j) * (5 / 3 : ℝ) *
          (|(L : ℝ) - 2 * (n : ℝ)| +
            18 * ndFixedTotalRatioScale j) := by
    calc
      ((v - u : ℕ) : ℝ) * (5 / 3 : ℝ) *
          (|(L : ℝ) - 2 * (n : ℝ)| +
            (ndFixedTotalRatioRadius j : ℝ) + 1) =
          ((v - u : ℕ) : ℝ) *
            ((5 / 3 : ℝ) *
              (|(L : ℝ) - 2 * (n : ℝ)| +
                (ndFixedTotalRatioRadius j : ℝ) + 1)) := by ring
      _ ≤ (34 * ndFixedTotalRatioScale j) *
            ((5 / 3 : ℝ) *
              (|(L : ℝ) - 2 * (n : ℝ)| +
                (ndFixedTotalRatioRadius j : ℝ) + 1)) := by
        gcongr
      _ ≤ (34 * ndFixedTotalRatioScale j) *
            ((5 / 3 : ℝ) *
              (|(L : ℝ) - 2 * (n : ℝ)| +
                18 * ndFixedTotalRatioScale j)) := by
        gcongr
      _ = (34 * ndFixedTotalRatioScale j) * (5 / 3 : ℝ) *
          (|(L : ℝ) - 2 * (n : ℝ)| +
            18 * ndFixedTotalRatioScale j) := by ring
  have hconstants :
      (34 * ndFixedTotalRatioScale j) * (5 / 3 : ℝ) *
          (|(L : ℝ) - 2 * (n : ℝ)| +
            18 * ndFixedTotalRatioScale j) ≤
        57 * ndFixedTotalRatioScale j *
            |(L : ℝ) - 2 * (n : ℝ)| +
          1021 * ndFixedTotalRatioScale j ^ 2 := by
    nlinarith [mul_nonneg hscale hDnonneg,
      sq_nonneg (ndFixedTotalRatioScale j)]
  calc
    |Real.log (ndFixedTotalHeadLikelihoodFactor j n L v) -
        Real.log (ndFixedTotalHeadLikelihoodFactor j n L u)| ≤
        ((v - u : ℕ) : ℝ) * (5 / 3 : ℝ) *
          (|(L : ℝ) - 2 * (n : ℝ)| +
            (ndFixedTotalRatioRadius j : ℝ) + 1) / (n : ℝ) := hordered
    _ ≤ ((34 * ndFixedTotalRatioScale j) * (5 / 3 : ℝ) *
          (|(L : ℝ) - 2 * (n : ℝ)| +
            18 * ndFixedTotalRatioScale j)) / (n : ℝ) :=
      div_le_div_of_nonneg_right hprod hnR.le
    _ ≤ (57 * ndFixedTotalRatioScale j *
            |(L : ℝ) - 2 * (n : ℝ)| +
          1021 * ndFixedTotalRatioScale j ^ 2) / (n : ℝ) :=
      div_le_div_of_nonneg_right hconstants hnR.le
    _ = 57 * ndFixedTotalRatioScale j *
          |(L : ℝ) - 2 * (n : ℝ)| / (n : ℝ) +
        1021 * ndFixedTotalRatioScale j ^ 2 / (n : ℝ) := by ring

/-- Symmetric raw pairwise log-likelihood oscillation with the frozen
constants. -/
theorem abs_log_ndFixedTotalHeadLikelihoodFactor_sub_le_raw
    {j n L u v : ℕ} (hj : 150 ≤ j) (hjn : 8 * j ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8)
    (hu : ndFixedTotalRatioGood j u) (hv : ndFixedTotalRatioGood j v) :
    |Real.log (ndFixedTotalHeadLikelihoodFactor j n L u) -
        Real.log (ndFixedTotalHeadLikelihoodFactor j n L v)| ≤
      57 * ndFixedTotalRatioScale j *
          |(L : ℝ) - 2 * (n : ℝ)| / (n : ℝ) +
        1021 * ndFixedTotalRatioScale j ^ 2 / (n : ℝ) := by
  rcases le_total u v with huv | hvu
  · simpa only [abs_sub_comm] using
      abs_log_ndFixedTotalHeadLikelihoodFactor_sub_le_raw_ordered
        hj hjn hD hu hv huv
  · exact abs_log_ndFixedTotalHeadLikelihoodFactor_sub_le_raw_ordered
      hj hjn hD hv hu hvu

/-- The exact parent-center displacement used in the frozen normalized
epsilon. -/
noncomputable def ndFixedTotalRatioCenterOffset (j n L : ℕ) : ℝ :=
  (j : ℝ) / (n : ℝ) * |(L : ℝ) - 2 * (n : ℝ)|

/-- The normalized displacement is exactly the manuscript's head-center
offset. -/
theorem ndFixedTotalRatioCenterOffset_eq_abs
    {j n L : ℕ} (hn : 0 < n) :
    ndFixedTotalRatioCenterOffset j n L =
      |(j : ℝ) * (L : ℝ) / (n : ℝ) - 2 * (j : ℝ)| := by
  have hjR : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  unfold ndFixedTotalRatioCenterOffset
  calc
    (j : ℝ) / (n : ℝ) * |(L : ℝ) - 2 * (n : ℝ)| =
        |((j : ℝ) / (n : ℝ)) *
          ((L : ℝ) - 2 * (n : ℝ))| := by
      rw [abs_mul, abs_of_nonneg (div_nonneg hjR hnR.le)]
    _ = |(j : ℝ) * (L : ℝ) / (n : ℝ) - 2 * (j : ℝ)| := by
      congr 1
      field_simp [hnR.ne']

/-- The normalized `57/1021` likelihood-ratio oscillation parameter. -/
noncomputable def ndFixedTotalRatioEps (j n L : ℕ) : ℝ :=
  57 * Real.sqrt (Real.log (j : ℝ)) *
      ndFixedTotalRatioCenterOffset j n L / Real.sqrt (j : ℝ) +
    1021 * ((j : ℝ) * Real.log (j : ℝ)) / (n : ℝ)

theorem ndFixedTotalRatioScale_sq
    {j : ℕ} (hj : 1 ≤ j) :
    ndFixedTotalRatioScale j ^ 2 =
      (j : ℝ) * Real.log (j : ℝ) := by
  unfold ndFixedTotalRatioScale
  exact Real.sq_sqrt
    (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hj)))

/-- The raw and manuscript-normalized `57/1021` expressions agree exactly. -/
theorem ndFixedTotalRatio_raw_eq_ratioEps
    {j n L : ℕ} (hj : 150 ≤ j) (hn : 0 < n) :
    57 * ndFixedTotalRatioScale j *
          |(L : ℝ) - 2 * (n : ℝ)| / (n : ℝ) +
        1021 * ndFixedTotalRatioScale j ^ 2 / (n : ℝ) =
      ndFixedTotalRatioEps j n L := by
  have hjPos : (0 : ℝ) < (j : ℝ) := by positivity
  have hnPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsqrtj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.2 hjPos
  have hscale :
      ndFixedTotalRatioScale j =
        Real.sqrt (j : ℝ) * Real.sqrt (Real.log (j : ℝ)) := by
    unfold ndFixedTotalRatioScale
    rw [Real.sqrt_mul (by positivity)]
  have hfirst :
      57 * ndFixedTotalRatioScale j *
          |(L : ℝ) - 2 * (n : ℝ)| / (n : ℝ) =
        57 * Real.sqrt (Real.log (j : ℝ)) *
          ndFixedTotalRatioCenterOffset j n L / Real.sqrt (j : ℝ) := by
    unfold ndFixedTotalRatioCenterOffset
    rw [hscale]
    calc
      57 * (Real.sqrt (j : ℝ) * Real.sqrt (Real.log (j : ℝ))) *
          |(L : ℝ) - 2 * (n : ℝ)| / (n : ℝ) =
        57 * Real.sqrt (Real.log (j : ℝ)) *
          (Real.sqrt (j : ℝ) * Real.sqrt (j : ℝ) / (n : ℝ) *
            |(L : ℝ) - 2 * (n : ℝ)|) / Real.sqrt (j : ℝ) := by
        field_simp [hnPos.ne', hsqrtj.ne']
      _ = 57 * Real.sqrt (Real.log (j : ℝ)) *
          ((j : ℝ) / (n : ℝ) * |(L : ℝ) - 2 * (n : ℝ)|) /
            Real.sqrt (j : ℝ) := by
        rw [Real.mul_self_sqrt hjPos.le]
  unfold ndFixedTotalRatioEps
  rw [← hfirst, ndFixedTotalRatioScale_sq (by omega)]

/-- Frozen normalized pairwise factor oscillation. -/
theorem abs_log_ndFixedTotalHeadLikelihoodFactor_sub_le_ratioEps
    {j n L u v : ℕ} (hj : 150 ≤ j) (hjn : 8 * j ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8)
    (hu : ndFixedTotalRatioGood j u) (hv : ndFixedTotalRatioGood j v) :
    |Real.log (ndFixedTotalHeadLikelihoodFactor j n L u) -
        Real.log (ndFixedTotalHeadLikelihoodFactor j n L v)| ≤
      ndFixedTotalRatioEps j n L := by
  rw [← ndFixedTotalRatio_raw_eq_ratioEps hj (by omega)]
  exact abs_log_ndFixedTotalHeadLikelihoodFactor_sub_le_raw
    hj hjn hD hu hv

/-- Both conditioned and reference atoms are positive on the literal ratio
window, ready for countable R1 normalization. -/
theorem ndFixedTotalHeadTotalPMF_and_reference_pos_of_ratioGood
    {j n L u : ℕ} (hj : 150 ≤ j) (hjn : 8 * j ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8)
    (hu : ndFixedTotalRatioGood j u) :
    0 < (ndFixedTotalHeadTotalPMF j n L (by omega) (by omega)
          (ndFixedTotalRatio_n_le_L hj hjn hD) u).toReal ∧
      0 < (ndGeom2EndpointPMF j u).toReal := by
  have hjPos : 0 < j := by omega
  have hjn' : j < n := by omega
  have hnL := ndFixedTotalRatio_n_le_L hj hjn hD
  have hroom := ndFixedTotalRatioGood_strict_suffix_room hj hjn hD hu
  have hQ : 0 < (ndGeom2EndpointPMF j u).toReal := by
    rw [ndGeom2EndpointPMF_apply_toReal_eq_endpointMass]
    exact ndGeom2EndpointMass_pos hjPos hu.1
  have hfactor : 0 < ndFixedTotalHeadLikelihoodFactor j n L u :=
    ndFixedTotalHeadLikelihoodFactor_pos hjn' hnL (Nat.le_of_lt hroom)
  constructor
  · rw [ndFixedTotalHeadTotalPMF_apply_toReal_eq_endpoint_mul_factor]
    positivity
  · exact hQ

/-- Public source-facing `log(P/Q)` pairwise oscillation. -/
theorem abs_log_ndFixedTotalHeadTotalPMF_likelihoodRatio_sub_le_ratioEps
    {j n L u v : ℕ} (hj : 150 ≤ j) (hjn : 8 * j ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8)
    (hu : ndFixedTotalRatioGood j u) (hv : ndFixedTotalRatioGood j v) :
    |Real.log
          ((ndFixedTotalHeadTotalPMF j n L (by omega) (by omega)
              (ndFixedTotalRatio_n_le_L hj hjn hD) u).toReal /
            (ndGeom2EndpointPMF j u).toReal) -
        Real.log
          ((ndFixedTotalHeadTotalPMF j n L (by omega) (by omega)
              (ndFixedTotalRatio_n_le_L hj hjn hD) v).toReal /
            (ndGeom2EndpointPMF j v).toReal)| ≤
      ndFixedTotalRatioEps j n L := by
  have hjPos : 0 < j := by omega
  have hjn' : j < n := by omega
  have hnL := ndFixedTotalRatio_n_le_L hj hjn hD
  rw [ndFixedTotalHeadTotalPMF_likelihoodRatio_eq_factor
      hjPos hjn' hnL hu.1,
    ndFixedTotalHeadTotalPMF_likelihoodRatio_eq_factor
      hjPos hjn' hnL hv.1]
  exact abs_log_ndFixedTotalHeadLikelihoodFactor_sub_le_ratioEps
    hj hjn hD hu hv

end

end ND
end Erdos1135
