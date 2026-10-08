import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace Erdos1135.Tao

variable {α : Type*} [MeasurableSpace α]

theorem positive_overlap_integral (μ : Measure α) [IsFiniteMeasure μ]
    {f a b : α → ℝ}
    (ha : AEMeasurable a μ)
    (ha_nonneg : 0 ≤ᵐ[μ] a) (hb_nonneg : 0 ≤ᵐ[μ] b)
    (hsum : f =ᵐ[μ] fun x => a x + b x)
    (hsupport : μ {x | 0 < a x} = μ {x | 0 < f x})
    (hb_pos : 0 < ∫ x, b x ∂μ)
    (hab_int : Integrable (fun x => a x * b x) μ) :
    0 < ∫ x, a x * b x ∂μ := by
  have hsubset : {x | 0 < a x} ≤ᵐ[μ] {x | 0 < f x} := by
    filter_upwards [hsum, hb_nonneg] with x hx hbx
    change (0 < a x) → (0 < f x)
    intro hax
    change 0 ≤ b x at hbx
    linarith
  have hsets : {x | 0 < a x} =ᵐ[μ] {x | 0 < f x} :=
    ae_eq_of_ae_subset_of_measure_ge hsubset hsupport.symm.le
      (nullMeasurableSet_lt aemeasurable_const ha) (measure_ne_top μ _)
  have hab_nonneg : 0 ≤ᵐ[μ] fun x => a x * b x := by
    filter_upwards [ha_nonneg, hb_nonneg] with x hax hbx
    exact mul_nonneg hax hbx
  by_contra! hnot
  have hab_zero : (fun x => a x * b x) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hab_nonneg hab_int).mp
      (le_antisymm hnot (integral_nonneg_of_ae hab_nonneg))
  have hb_zero : b =ᵐ[μ] 0 := by
    filter_upwards [hab_zero, hsum, ha_nonneg, hb_nonneg, hsets]
      with x hprod hx hax hbx hset
    change b x = 0
    change a x * b x = 0 at hprod
    change 0 ≤ a x at hax
    change 0 ≤ b x at hbx
    change (0 < a x) = (0 < f x) at hset
    by_contra hb_ne
    have hb_positive : 0 < b x := lt_of_le_of_ne hbx (Ne.symm hb_ne)
    have hf_positive : 0 < f x := by linarith
    have ha_positive : 0 < a x := hset.mpr hf_positive
    exact (ne_of_gt (mul_pos ha_positive hb_positive)) hprod
  have hb_integral_zero : (∫ x, b x ∂μ) = 0 := by
    calc
      (∫ x, b x ∂μ) = ∫ _ : α, (0 : ℝ) ∂μ := integral_congr_ae hb_zero
      _ = 0 := by simp
  linarith

theorem critical_sq_identity_impossible (μ : Measure α) [IsFiniteMeasure μ]
    {f a b : α → ℝ}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (ha_nonneg : 0 ≤ᵐ[μ] a) (hb_nonneg : 0 ≤ᵐ[μ] b)
    (hsum : f =ᵐ[μ] fun x => a x + b x)
    (hsupport : μ {x | 0 < a x} = μ {x | 0 < f x})
    (hb_pos : 0 < ∫ x, b x ∂μ)
    (hcritical : (∫ x, (f x) ^ 2 ∂μ) =
      (∫ x, (a x) ^ 2 ∂μ) + (∫ x, (b x) ^ 2 ∂μ)) :
    False := by
  have hab_int : Integrable (fun x => a x * b x) μ := ha.integrable_mul hb
  have hab_pos := positive_overlap_integral μ ha.1.aemeasurable ha_nonneg hb_nonneg
    hsum hsupport hb_pos hab_int
  have hsq_add : Integrable (fun x => (a x) ^ 2 + (b x) ^ 2) μ :=
    ha.integrable_sq.add hb.integrable_sq
  have hexpand : (∫ x, (f x) ^ 2 ∂μ) =
      (∫ x, (a x) ^ 2 ∂μ) + (∫ x, (b x) ^ 2 ∂μ) +
        2 * (∫ x, a x * b x ∂μ) := by
    calc
      (∫ x, (f x) ^ 2 ∂μ) =
          ∫ x, (a x) ^ 2 + (b x) ^ 2 + 2 * (a x * b x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hsum] with x hx
        rw [hx]
        ring
      _ = _ := by
        rw [integral_add hsq_add (hab_int.const_mul 2),
          integral_add ha.integrable_sq hb.integrable_sq, integral_const_mul]
  linarith

#print axioms positive_overlap_integral
#print axioms critical_sq_identity_impossible

end Erdos1135.Tao
