import ForwardOddPrefix
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.RawOccupation

noncomputable def oddForwardLogLength (a : ℝ) (R : ℕ) : ℕ :=
  ⌊a * Real.log (R : ℝ) / Real.log (3 / 2 : ℝ)⌋₊

theorem oddForwardLogLength_div_log_tendsto {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun R : ℕ => (oddForwardLogLength a R : ℝ) / Real.log (R : ℝ))
      atTop (𝓝 (a / Real.log (3 / 2 : ℝ))) := by
  have hb : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have hi : Tendsto (fun R : ℕ => (Real.log (R : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlo : Tendsto (fun R : ℕ => a / Real.log (3 / 2 : ℝ) -
      (Real.log (R : ℝ))⁻¹) atTop (𝓝 (a / Real.log (3 / 2 : ℝ))) := by
    simpa only [sub_zero] using hi.const_sub (a / Real.log (3 / 2 : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with R hR
    have hR1 : 1 < (R : ℝ) := by exact_mod_cast (show 1 < R by omega)
    have hlog : 0 < Real.log (R : ℝ) := Real.log_pos hR1
    have hf := (Nat.lt_floor_add_one (a * Real.log (R : ℝ) / Real.log (3 / 2 : ℝ))).le
    have hf' : a * Real.log (R : ℝ) / Real.log (3 / 2 : ℝ) - 1 ≤
        (oddForwardLogLength a R : ℝ) := by
      unfold oddForwardLogLength
      linarith
    have hd := div_le_div_of_nonneg_right hf' hlog.le
    convert hd using 1
    field_simp
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with R hR
    have hR1 : 1 < (R : ℝ) := by exact_mod_cast (show 1 < R by omega)
    have hlog : 0 < Real.log (R : ℝ) := Real.log_pos hR1
    have hf := Nat.floor_le (div_nonneg (mul_nonneg ha hlog.le) hb.le)
    have hd := div_le_div_of_nonneg_right hf hlog.le
    unfold oddForwardLogLength
    convert hd using 1
    field_simp

theorem oddForwardLogLength_eventual_growth_budget {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) (u : ℕ) :
    ∀ᶠ R : ℕ in atTop,
      (3 / 2 : ℝ) ^ oddForwardLogLength a R * ((u : ℝ) + 1) ≤ (R : ℝ) + 1 := by
  have hb : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have hi : Tendsto (fun R : ℕ => (Real.log (R : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hl : Tendsto (fun R : ℕ => Real.log ((u : ℝ) + 1) / Real.log (R : ℝ) + a)
      atTop (𝓝 a) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_add] using
      (hi.const_mul (Real.log ((u : ℝ) + 1))).add_const a
  filter_upwards [hl.eventually_lt_const ha1, eventually_ge_atTop (2 : ℕ)] with R hsmall hR
  have hR1 : 1 < (R : ℝ) := by exact_mod_cast (show 1 < R by omega)
  have hRpos : 0 < (R : ℝ) := zero_lt_one.trans hR1
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos hR1
  have hf : (oddForwardLogLength a R : ℝ) ≤
      a * Real.log (R : ℝ) / Real.log (3 / 2 : ℝ) :=
    Nat.floor_le (div_nonneg (mul_nonneg ha hlog.le) hb.le)
  have hf' : (oddForwardLogLength a R : ℝ) * Real.log (3 / 2 : ℝ) ≤
      a * Real.log (R : ℝ) := (le_div_iff₀ hb).mp hf
  have hs : Real.log ((u : ℝ) + 1) + a * Real.log (R : ℝ) < Real.log (R : ℝ) := by
    have hid : Real.log ((u : ℝ) + 1) / Real.log (R : ℝ) + a =
        (Real.log ((u : ℝ) + 1) + a * Real.log (R : ℝ)) / Real.log (R : ℝ) := by
      field_simp
    rw [hid] at hsmall
    simpa only [one_mul] using (div_lt_iff₀ hlog).mp hsmall
  have hbudget : (3 / 2 : ℝ) ^ oddForwardLogLength a R * ((u : ℝ) + 1) ≤ (R : ℝ) := by
    apply (Real.log_le_log_iff (by positivity) hRpos).mp
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    linarith
  linarith

#print axioms oddForwardLogLength_div_log_tendsto
#print axioms oddForwardLogLength_eventual_growth_budget

end CollatzCanonical.RawOccupation
