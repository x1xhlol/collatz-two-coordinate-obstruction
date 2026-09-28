import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# The denominator `lcm(1, ..., N)`

This leaf owns the elementary finite-LCM surface shared by the p. 159 row
construction and the independent table-free growth proof.  Starting the
interval at one is essential: folding in zero would make every positive-scale
denominator vanish.
-/

namespace Erdos1135
namespace NumberTheory
namespace Rhin

/-- The denominator `lcm(1, ..., N)`, with the empty range at `N = 0`
evaluating to one. -/
def rangeLCM (N : ℕ) : ℕ :=
  (Finset.Icc 1 N).lcm id

/-- The denominator scale is positive, including at `N = 0`. -/
theorem rangeLCM_pos (N : ℕ) : 0 < rangeLCM N := by
  apply Nat.pos_of_ne_zero
  rw [rangeLCM, Finset.lcm_ne_zero_iff]
  intro d hd
  have hdPos : 0 < d := (Finset.mem_Icc.mp hd).1
  simpa only [id_eq] using hdPos.ne'

theorem rangeLCM_ne_zero (N : ℕ) : rangeLCM N ≠ 0 :=
  (rangeLCM_pos N).ne'

/-- Every positive integer at most `N` divides `rangeLCM N`. -/
theorem denominator_dvd_rangeLCM
    {N d : ℕ} (hd : 1 ≤ d) (hdN : d ≤ N) :
    d ∣ rangeLCM N := by
  apply Finset.dvd_lcm
  exact Finset.mem_Icc.mpr ⟨hd, hdN⟩

end Rhin
end NumberTheory
end Erdos1135
