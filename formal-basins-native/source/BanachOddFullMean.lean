import BanachHalfShiftMean
import VectorLogParity

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.BanachWindow

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem fullVectorCumulative_normalized_bound {F : ℕ → V} (hF : ∀ q, ‖F q‖ ≤ 1)
    {t : ℝ} (ht : 1 ≤ t) : ‖t⁻¹ • fullVectorCumulative F t‖ ≤ 2 := by
  have ht0 : 0 < t := by linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
  calc
    _ ≤ t⁻¹ * (t + 1) :=
      mul_le_mul_of_nonneg_left (fullVectorCumulative_growth hF ht0.le) (inv_nonneg.mpr ht0.le)
    _ = (t + 1) / t := by ring
    _ ≤ 2 := (div_le_iff₀ ht0).mpr (by linarith)

theorem fullVectorCumulative_halving [CompleteSpace V] (F : ℕ → V)
    (hF : ∀ q : ℕ, 0 < q → F (2 * q) = F q) (t : ℝ) :
    fullVectorCumulative F (t + Real.log 2) = oddVectorCumulative F (t + Real.log 2) +
      (1 / 2 : ℝ) • fullVectorCumulative F t := by
  rw [fullVectorCumulative_parity, fullVectorCumulative_congr_positive hF]
  simp

theorem fullVector_mean_of_odd_mean [CompleteSpace V] (F : ℕ → V)
    (hF : ∀ q, ‖F q‖ ≤ 1) (hhalf : ∀ q : ℕ, 0 < q → F (2 * q) = F q)
    (p : V) (hodd : Tendsto (fun t : ℝ => t⁻¹ • oddVectorCumulative F t) atTop (𝓝 p)) :
    Tendsto (fun t : ℝ => t⁻¹ • fullVectorCumulative F t) atTop (𝓝 ((2 : ℝ) • p)) := by
  apply vector_mean_tendsto_twice_of_half_shift (fullVectorCumulative F)
    (oddVectorCumulative F) (Real.log 2) 2 0 p (Real.log_nonneg (by norm_num))
    (fun _ ht => fullVectorCumulative_normalized_bound hF ht) _ hodd
  intro t _
  rw [fullVectorCumulative_halving F hhalf t]
  simp only [add_sub_cancel_left, sub_self, norm_zero, le_refl]

end CollatzCanonical.BanachWindow

#print axioms CollatzCanonical.BanachWindow.fullVectorCumulative_halving
#print axioms CollatzCanonical.BanachWindow.fullVector_mean_of_odd_mean
