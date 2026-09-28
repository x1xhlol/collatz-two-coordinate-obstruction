import SyracuseBlockNormalization

set_option autoImplicit false
open Filter Topology Asymptotics

namespace CollatzCanonical.GreenKernelScalars

theorem blockKappa_denominator_exponential (s : ℝ) :
    2 * (2 : ℝ) ^ (-s) = Real.exp (-Real.log 2 * (s - 1)) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    show Real.log 2 * (-s) = -Real.log 2 * (s - 1) - Real.log 2 by ring,
    Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  ring

theorem blockKappa_quadratic_remainder_eventually :
    ∀ᶠ s : ℝ in 𝓝 1,
      |1 - blockKappa s - Real.log (4 / 3 : ℝ) * (s - 1)| ≤
        4 * (((Real.log 2) ^ 2 + (Real.log (3 / 2 : ℝ)) ^ 2) / 2 +
          2 * |delta| * |Real.log 2|) * (s - 1) ^ 2 := by
  let K : ℝ := ((Real.log 2) ^ 2 + (Real.log (3 / 2 : ℝ)) ^ 2) / 2
  let C : ℝ := K + 2 * |delta| * |Real.log 2|
  have ht : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 0) := by
    simpa only [sub_self] using (tendsto_id.sub_const (1 : ℝ) :
      Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 (1 - 1)))
  have hsmall : ∀ᶠ s : ℝ in 𝓝 1, |(-Real.log 2) * (s - 1)| ≤ 1 := by
    have h : Tendsto (fun s : ℝ => |(-Real.log 2) * (s - 1)|) (𝓝 1) (𝓝 0) := by
      simpa only [mul_zero, abs_zero] using
        ((tendsto_const_nhds (x := -Real.log 2)).mul ht).abs
    exact (h.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ hs => hs.le
  have hden : ∀ᶠ s : ℝ in 𝓝 1, (1 / 4 : ℝ) ≤ 1 - (2 : ℝ) ^ (-s) := by
    have h : Tendsto (fun s : ℝ => 1 - (2 : ℝ) ^ (-s)) (𝓝 1) (𝓝 (1 / 2 : ℝ)) := by
      have hc : Continuous (fun s : ℝ => 1 - (2 : ℝ) ^ (-s)) := by fun_prop (disch := norm_num)
      convert hc.continuousAt.tendsto using 1
      norm_num
    exact (h.eventually (Ioi_mem_nhds (by norm_num : (1 / 4 : ℝ) < 1 / 2))).mono fun _ hs => hs.le
  filter_upwards [kappa_quadratic_remainder_eventually, hsmall, hden,
    Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with s hk hu hd hs
  have hexp : |Real.exp (-Real.log 2 * (s - 1)) - 1| ≤
      2 * |Real.log 2| * |s - 1| := by
    let u : ℝ := -Real.log 2 * (s - 1)
    have hur : |u| ≤ 1 := hu
    have hsq : u ^ 2 ≤ |u| := by
      have h := mul_le_mul_of_nonneg_left hur (abs_nonneg u)
      nlinarith [sq_abs u]
    calc
      |Real.exp u - 1| = |(Real.exp u - 1 - u) + u| := by congr 1; ring
      _ ≤ |Real.exp u - 1 - u| + |u| := abs_add_le _ _
      _ ≤ u ^ 2 + |u| := add_le_add (Real.abs_exp_sub_one_sub_id_le hur) le_rfl
      _ ≤ 2 * |u| := by linarith
      _ = _ := by dsimp [u]; rw [abs_mul, abs_neg]; ring
  have hnum : |(1 - kappa s - delta * (s - 1)) +
      delta * (s - 1) * (2 * (2 : ℝ) ^ (-s) - 1)| ≤ C * (s - 1) ^ 2 := by
    calc
      _ ≤ |1 - kappa s - delta * (s - 1)| +
          |delta * (s - 1) * (2 * (2 : ℝ) ^ (-s) - 1)| := abs_add_le _ _
      _ ≤ K * (s - 1) ^ 2 + |delta| * |s - 1| *
          (2 * |Real.log 2| * |s - 1|) := by
        apply add_le_add hk
        rw [abs_mul, abs_mul, blockKappa_denominator_exponential]
        exact mul_le_mul_of_nonneg_left hexp (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = K * (s - 1) ^ 2 + (2 * |delta| * |Real.log 2|) * |s - 1| ^ 2 := by ring
      _ = C * (s - 1) ^ 2 := by rw [sq_abs]; dsimp [C]; ring
  have hdpos : 0 < 1 - (2 : ℝ) ^ (-s) := by linarith
  have he : 1 - blockKappa s - Real.log (4 / 3 : ℝ) * (s - 1) =
      ((1 - kappa s - delta * (s - 1)) +
        delta * (s - 1) * (2 * (2 : ℝ) ^ (-s) - 1)) / (1 - (2 : ℝ) ^ (-s)) := by
    rw [blockKappa_normalization hs]
    have hδ : Real.log (4 / 3 : ℝ) = 2 * delta := by unfold delta; ring
    rw [hδ]
    field_simp
    ring
  rw [he, abs_div, abs_of_pos hdpos]
  have hC : 0 ≤ C := by dsimp [C, K]; positivity
  calc
    _ ≤ (C * (s - 1) ^ 2) / (1 - (2 : ℝ) ^ (-s)) :=
      div_le_div_of_nonneg_right hnum hdpos.le
    _ ≤ (C * (s - 1) ^ 2) / (1 / 4 : ℝ) :=
      div_le_div_of_nonneg_left (mul_nonneg hC (sq_nonneg _)) (by norm_num) hd
    _ = _ := by dsimp [C, K]; ring

theorem blockKappa_quadratic_remainder_isBigO :
    (fun s : ℝ => 1 - blockKappa s - Real.log (4 / 3 : ℝ) * (s - 1)) =O[𝓝 1]
      (fun s : ℝ => (s - 1) ^ 2) := by
  apply IsBigO.of_bound
    (4 * (((Real.log 2) ^ 2 + (Real.log (3 / 2 : ℝ)) ^ 2) / 2 +
      2 * |delta| * |Real.log 2|))
  filter_upwards [blockKappa_quadratic_remainder_eventually] with s hs
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (s - 1))] using hs

end CollatzCanonical.GreenKernelScalars

#print axioms CollatzCanonical.GreenKernelScalars.blockKappa_denominator_exponential
#print axioms CollatzCanonical.GreenKernelScalars.blockKappa_quadratic_remainder_eventually
#print axioms CollatzCanonical.GreenKernelScalars.blockKappa_quadratic_remainder_isBigO
