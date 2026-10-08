import Erdos1135.ND.Band.A5ReferenceSchedule
import Erdos1135.ND.Band.A5Physical

/-!
# Integer room for the common A5 reference level

This leaf transports the scalar reference schedule into every `(t2)` cell.
It remains independent of terminal totals, bands, laws, and FM1 witnesses.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped Topology

noncomputable section

/-- Eventually the one common reference level is above the fixed-total
threshold, below `m0`, and at most one eighth of every `(t2)` physical
length. -/
theorem eventually_ndA5ReferenceLevel_integer_room :
    ∀ᶠ B : ℕ in atTop,
      150 ≤ ndA5ReferenceLevel B ∧
      ndA5ReferenceLevel B ≤ Tao.taoSection5M0 B ∧
      ∀ {n : ℕ} {C : ℝ}, NDA5T2ScaleFacts B n C →
        8 * ndA5ReferenceLevel B ≤ n - Tao.taoSection5M0 B := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [eventually_one_hundred_fifty_le_ndA5ReferenceLevel,
      eventually_ndA5ReferenceLevel_cast_sandwich,
      hlog.eventually_ge_atTop (1 : ℝ)]
      with B hm hscale hlogOne
  have hmLeM0 : ndA5ReferenceLevel B ≤ Tao.taoSection5M0 B := by
    unfold ndA5ReferenceLevel
    apply Nat.ceil_le.mpr
    have hrpowLe :
        Real.rpow (Real.log B) (-(2 / 5 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hlogOne (by norm_num)
    calc
      (Tao.taoSection5M0 B : ℝ) *
          Real.rpow (Real.log B) (-(2 / 5 : ℝ)) ≤
        (Tao.taoSection5M0 B : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hrpowLe (Nat.cast_nonneg _)
      _ = (Tao.taoSection5M0 B : ℝ) := mul_one _
  refine ⟨hm, hmLeM0, ?_⟩
  intro n C ht2
  have hpowLe :
      Real.rpow (Real.log B) (3 / 5 : ℝ) ≤ Real.log B := by
    calc
      Real.rpow (Real.log B) (3 / 5 : ℝ) ≤
          Real.rpow (Real.log B) (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlogOne (by norm_num)
      _ = Real.log B := Real.rpow_one _
  have hcast :
      ((8 * ndA5ReferenceLevel B : ℕ) : ℝ) ≤
        ((n - Tao.taoSection5M0 B : ℕ) : ℝ) := by
    calc
      ((8 * ndA5ReferenceLevel B : ℕ) : ℝ) =
          8 * (ndA5ReferenceLevel B : ℝ) := by norm_num
      _ ≤ 8 * ((1 / 50000 : ℝ) *
          Real.rpow (Real.log B) (3 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_left hscale.2 (by norm_num)
      _ ≤ 8 * ((1 / 50000 : ℝ) * Real.log B) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpowLe (by norm_num)) (by norm_num)
      _ ≤ (340 / 100000 : ℝ) * Real.log B := by
        nlinarith
      _ ≤ ((n - Tao.taoSection5M0 B : ℕ) : ℝ) := ht2.nu_lower
  exact_mod_cast hcast

end
end ND
end Erdos1135
