import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set

namespace CollatzCanonical.PackingParameters

noncomputable def threshold : ℝ := Real.log 2 / Real.log 3

noncomputable def entropy (ρ : ℝ) : ℝ :=
  (-ρ * Real.log ρ - (1 - ρ) * Real.log (1 - ρ)) / Real.log 2

noncomputable def beta : ℝ := entropy threshold

/-- The zero-drift parity proportion is strictly between one half and one. -/
theorem threshold_mem : 1 / 2 < threshold ∧ threshold < 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have h34 : Real.log 3 < 2 * Real.log 2 := by
    have hh := Real.log_lt_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) < 4)
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rwa [he] at hh
  constructor
  · exact (lt_div_iff₀ hlog3).mpr (by linarith)
  · exact (div_lt_one hlog3).mpr h23

/-- Binary entropy is positive away from its endpoints. -/
theorem entropy_pos (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : 0 < entropy ρ := by
  have hc : 0 < 1 - ρ := sub_pos.mpr hρ1
  have hl : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  have hlc : Real.log (1 - ρ) < 0 := Real.log_neg hc (by linarith)
  have hnum : 0 < -ρ * Real.log ρ - (1 - ρ) * Real.log (1 - ρ) := by
    nlinarith [mul_neg_of_pos_of_neg hρ0 hl, mul_neg_of_pos_of_neg hc hlc]
  exact div_pos hnum (Real.log_pos (by norm_num))

/-- The entropy at one half is exactly one. -/
theorem entropy_half : entropy (1 / 2) = 1 := by
  have hl : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  dsimp [entropy]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, hl]
  field_simp
  ring

/-- Strict entropy loss above one half, proved by the elementary logarithm inequality. -/
theorem entropy_lt_one (ρ : ℝ) (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1) : entropy ρ < 1 := by
  have hρ0 : 0 < ρ := by linarith
  have hc : 0 < 1 - ρ := sub_pos.mpr hρ1
  have hx : 0 < (2 * ρ)⁻¹ := inv_pos.mpr (by positivity)
  have hy : 0 < (2 * (1 - ρ))⁻¹ := inv_pos.mpr (by positivity)
  have hx1 : (2 * ρ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr (by linarith)
  have hlx := Real.log_lt_sub_one_of_pos hx (ne_of_lt hx1)
  have hly := Real.log_le_sub_one_of_pos hy
  have hh := add_lt_add_of_lt_of_le
    (mul_lt_mul_of_pos_left hlx hρ0) (mul_le_mul_of_nonneg_left hly hc.le)
  have hrhs : ρ * ((2 * ρ)⁻¹ - 1) + (1 - ρ) * ((2 * (1 - ρ))⁻¹ - 1) = 0 := by
    field_simp
    ring
  rw [hrhs] at hh
  have hlx' : Real.log ((2 * ρ)⁻¹) = -Real.log 2 - Real.log ρ := by
    rw [Real.log_inv, Real.log_mul (by norm_num) hρ0.ne']
    ring
  have hly' : Real.log ((2 * (1 - ρ))⁻¹) = -Real.log 2 - Real.log (1 - ρ) := by
    rw [Real.log_inv, Real.log_mul (by norm_num) hc.ne']
    ring
  rw [hlx', hly'] at hh
  apply (div_lt_one (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  nlinarith

/-- Entropy is continuous throughout the closed interval used to choose the packing exponent. -/
theorem continuousOn_entropy : ContinuousOn entropy (Icc (1 / 2) threshold) := by
  have hid : ContinuousOn (fun x : ℝ => x) (Icc (1 / 2) threshold) := continuousOn_id
  have hlog : ContinuousOn (fun x : ℝ => Real.log x) (Icc (1 / 2) threshold) :=
    hid.log (fun x hx => ne_of_gt (by linarith [hx.1]))
  have hc : ContinuousOn (fun x : ℝ => 1 - x) (Icc (1 / 2) threshold) :=
    continuousOn_const.sub hid
  have hlogc : ContinuousOn (fun x : ℝ => Real.log (1 - x)) (Icc (1 / 2) threshold) :=
    hc.log (fun x hx => ne_of_gt (by linarith [hx.2, threshold_mem.2]))
  exact ((hid.neg.mul hlog).sub (hc.mul hlogc)).div_const (Real.log 2)

theorem beta_pos : 0 < beta :=
  entropy_pos threshold (by linarith [threshold_mem.1]) threshold_mem.2

theorem beta_lt_one : beta < 1 := entropy_lt_one threshold threshold_mem.1 threshold_mem.2

/-- Every exponent strictly above beta and below one is attained by an admissible parity cutoff. -/
theorem exists_entropy_parameter (b : ℝ) (hbβ : beta < b) (hb1 : b < 1) :
    ∃ ρ : ℝ, 1 / 2 < ρ ∧ ρ < threshold ∧ entropy ρ = b := by
  have hmem : b ∈ Icc (entropy threshold) (entropy (1 / 2)) := by
    rw [entropy_half]
    exact ⟨hbβ.le, hb1.le⟩
  obtain ⟨ρ, hρ, he⟩ := intermediate_value_Icc' threshold_mem.1.le continuousOn_entropy hmem
  refine ⟨ρ, ?_, ?_, he⟩
  · by_contra hh
    have heq : ρ = 1 / 2 := le_antisymm (le_of_not_gt hh) hρ.1
    rw [heq, entropy_half] at he
    linarith
  · by_contra hh
    have heq : ρ = threshold := le_antisymm hρ.2 (le_of_not_gt hh)
    rw [heq] at he
    change entropy threshold < b at hbβ
    linarith

/-- An admissible parity cutoff gives a positive contraction exponent and positive entropy. -/
theorem admissible_parameter_bounds (ρ : ℝ) (hρ : 1 / 2 < ρ) (hρq : ρ < threshold) :
    0 < ρ * Real.log 3 / Real.log 2 ∧
      ρ * Real.log 3 / Real.log 2 < 1 ∧ 0 < entropy ρ := by
  have hρ0 : 0 < ρ := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hmul : ρ * Real.log 3 < Real.log 2 := (lt_div_iff₀ hlog3).mp hρq
  exact ⟨div_pos (mul_pos hρ0 hlog3) hlog2, (div_lt_one hlog2).mpr hmul,
    entropy_pos ρ hρ0 (hρq.trans threshold_mem.2)⟩

/-- The exact existential parameter choice used by the uniform trajectory-packing theorem. -/
theorem exists_packing_parameters (b : ℝ) (hbβ : beta < b) (hb1 : b < 1) :
    ∃ ρ : ℝ, 1 / 2 < ρ ∧ ρ < Real.log 2 / Real.log 3 ∧ entropy ρ = b ∧
      0 < ρ * Real.log 3 / Real.log 2 ∧ ρ * Real.log 3 / Real.log 2 < 1 := by
  obtain ⟨ρ, hρ, hρq, he⟩ := exists_entropy_parameter b hbβ hb1
  have hc := admissible_parameter_bounds ρ hρ hρq
  exact ⟨ρ, hρ, hρq, he, hc.1, hc.2.1⟩

end CollatzCanonical.PackingParameters
