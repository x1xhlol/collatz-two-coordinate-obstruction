import NativeBasinClosedWindowRate
import ClosedWindowRateConversion

set_option autoImplicit false

open Filter
open scoped Topology

namespace CollatzCanonical.NativeTao

open Erdos1135.Tao CollatzCylinderPacking.Arithmetic
open CollatzCanonical.DirichletAbelian

/-- The actual native first scale now supplies the normalized-window
power estimate required by the two-scale bounded-weight mean theorem. -/
theorem native_basin_first_scale_normalized_window_rate :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ c ≤ 1 ∧ ∀ N : ℕ, ∀ᶠ t : ℝ in atTop,
      |closedOddWindowExpectation (basinIndicator N)
          (taoAlpha * t) (taoAlpha * (taoAlpha * t)) -
        closedOddWindowExpectation (basinIndicator N) t (taoAlpha * t)| ≤
        C * t ^ (-c) := by
  obtain ⟨C, c, hC, hc, hc1, hrate⟩ := native_eventual_basin_closed_window_log_rate
  refine ⟨C * taoAlpha ^ c, c, mul_nonneg hC (Real.rpow_nonneg taoAlpha_pos.le _),
    hc, hc1, ?_⟩
  intro N
  exact closed_window_rate_of_logscale_rate (basinIndicator N) taoAlpha_pos (hrate N)

#print axioms native_basin_first_scale_normalized_window_rate

end CollatzCanonical.NativeTao
