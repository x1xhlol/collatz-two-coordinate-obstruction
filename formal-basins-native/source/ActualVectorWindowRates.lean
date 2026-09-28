import FirstScaleVectorRealRate
import SecondScaleVectorRealRate
import NativeVectorCoordinates

open Filter
open scoped Topology

namespace CollatzCanonical.LabelLaw
open CollatzCanonical.BanachWindow
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

section FirstScale
open Erdos1135.Tao CollatzClockAudit

theorem first_scale_normalized_vector_rate (F : ℕ → V)
    (hF : ∀ q, ‖F q‖ ≤ 1) (hpass : EventuallyPassageInvariant F) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ c ≤ 1 ∧ ∀ᶠ t : ℝ in atTop,
      ‖closedOddVectorExpectation F (taoAlpha * t) (taoAlpha * (taoAlpha * t)) -
        closedOddVectorExpectation F t (taoAlpha * t)‖ ≤ C * t ^ (-c) := by
  obtain ⟨C, c, hC, hc, hc1, hrate⟩ := first_scale_eventual_vector_real_rate F hF hpass
  refine ⟨C * taoAlpha ^ c, c, mul_nonneg hC (Real.rpow_nonneg taoAlpha_pos.le _),
    hc, hc1, ?_⟩
  apply closed_vector_rate_of_logscale_rate F taoAlpha_pos
  filter_upwards [hrate, eventually_ge_atTop (1 : ℝ)] with x hxrate hx
  let hm₁ := hxrate.1 .alpha
  let hm₂ := hxrate.1 .alphaSq
  have he := hxrate.2 hm₁ hm₂
  have he₁ := native_iterated_power_window_vector_expectation F
    (a := taoAlpha) (d := taoAlpha) hx taoAlpha_pos.le hm₁
  have he₂ := native_iterated_power_window_vector_expectation F
    (a := taoAlpha) (d := taoAlpha ^ 2) hx taoAlpha_sq_pos.le hm₂
  rw [← pow_two] at he₁
  rw [show taoAlpha * taoAlpha ^ 2 = taoAlpha ^ 3 by ring] at he₂
  dsimp only [realClockSourceLo, realClockSourceHi, realClockSourceY,
    taoSection5BranchExponent] at he
  rw [← he₁, ← he₂, norm_sub_rev]
  exact he

end FirstScale

section SecondScale
open Erdos1135SecondScale.Tao CollatzClockSecondScale

theorem second_scale_normalized_vector_rate (F : ℕ → V)
    (hF : ∀ q, ‖F q‖ ≤ 1) (hpass : EventuallyPassageInvariant F) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ c ≤ 1 ∧ ∀ᶠ t : ℝ in atTop,
      ‖closedOddVectorExpectation F (taoAlpha * t) (taoAlpha * (taoAlpha * t)) -
        closedOddVectorExpectation F t (taoAlpha * t)‖ ≤ C * t ^ (-c) := by
  obtain ⟨C, c, hC, hc, hc1, hrate⟩ := second_scale_eventual_vector_real_rate F hF hpass
  refine ⟨C * taoAlpha ^ c, c, mul_nonneg hC (Real.rpow_nonneg taoAlpha_pos.le _),
    hc, hc1, ?_⟩
  apply closed_vector_rate_of_logscale_rate F taoAlpha_pos
  filter_upwards [hrate, eventually_ge_atTop (1 : ℝ)] with x hxrate hx
  let hm₁ := hxrate.1 .alpha
  let hm₂ := hxrate.1 .alphaSq
  have he := hxrate.2 hm₁ hm₂
  have he₁ := native_iterated_power_window_vector_expectation F
    (a := taoAlpha) (d := taoAlpha) hx taoAlpha_pos.le hm₁
  have he₂ := native_iterated_power_window_vector_expectation F
    (a := taoAlpha) (d := taoAlpha ^ 2) hx taoAlpha_sq_pos.le hm₂
  rw [← pow_two] at he₁
  rw [show taoAlpha * taoAlpha ^ 2 = taoAlpha ^ 3 by ring] at he₂
  dsimp only [realClockSourceLo, realClockSourceHi, realClockSourceY,
    taoSection5BranchExponent] at he
  rw [← he₁, ← he₂, norm_sub_rev]
  exact he

end SecondScale

end CollatzCanonical.LabelLaw
#print axioms CollatzCanonical.LabelLaw.first_scale_normalized_vector_rate
#print axioms CollatzCanonical.LabelLaw.second_scale_normalized_vector_rate
