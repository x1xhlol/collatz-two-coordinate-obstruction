import LogarithmicCumulative
import DirichletPowerPerturbation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter Topology Set MeasureTheory
open scoped BigOperators

namespace CollatzCanonical.DirichletAbelian

noncomputable def laplaceIndicatorTerm (w : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℝ → ℝ :=
  (Ici (Real.log (n + 1 : ℕ))).indicator
    (fun t => Real.exp (-ε * t) * (w (n + 1) / (n + 1 : ℕ)))

theorem laplaceIndicatorTerm_integrable (w : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    IntegrableOn (laplaceIndicatorTerm w ε n) (Ioi 0) := by
  exact ((integrableOn_exp_mul_Ioi (a := -ε) (by linarith) 0).mul_const
    (w (n + 1) / (n + 1 : ℕ))).indicator measurableSet_Ici

theorem laplaceIndicatorTerm_nonneg {w : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n)
    (ε : ℝ) (n : ℕ) (t : ℝ) : 0 ≤ laplaceIndicatorTerm w ε n t := by
  apply Set.indicator_nonneg
  intro t _
  exact mul_nonneg (Real.exp_pos _).le (div_nonneg (hw0 _) (by positivity))

theorem integral_laplaceIndicatorTerm (w : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    (∫ t : ℝ in Ioi 0, laplaceIndicatorTerm w ε n t) =
      w (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ) / ε := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hlog : 0 ≤ Real.log (n + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  have hinter : Ici (0 : ℝ) ∩ Ici (Real.log (n + 1 : ℕ)) =
      Ici (Real.log (n + 1 : ℕ)) :=
    inter_eq_right.mpr (Ici_subset_Ici.mpr hlog)
  rw [← integral_Ici_eq_integral_Ioi, laplaceIndicatorTerm,
    setIntegral_indicator measurableSet_Ici, hinter, integral_Ici_eq_integral_Ioi,
    integral_mul_const, integral_exp_mul_Ioi (by linarith : -ε < 0)]
  have hpow : ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ) =
      ((n + 1 : ℕ) : ℝ)⁻¹ * Real.exp (-ε * Real.log (n + 1 : ℕ)) := by
    rw [Real.rpow_def_of_pos hn]
    have he : Real.log (n + 1 : ℕ) * (-1 - ε) =
        -Real.log (n + 1 : ℕ) + -ε * Real.log (n + 1 : ℕ) := by ring
    rw [he, Real.exp_add, Real.exp_neg, Real.exp_log hn]
  rw [hpow]
  field_simp [hε.ne']

theorem integral_laplaceIndicatorTerm_norm_summable {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => ∫ t : ℝ in Ioi 0, ‖laplaceIndicatorTerm w ε n t‖) := by
  have heq (n : ℕ) : (fun t : ℝ => ‖laplaceIndicatorTerm w ε n t‖) =
      laplaceIndicatorTerm w ε n := by
    ext t
    exact Real.norm_of_nonneg (laplaceIndicatorTerm_nonneg hw0 ε n t)
  simp_rw [heq, integral_laplaceIndicatorTerm w hε]
  exact (weighted_dirichlet_summable hw0 hw1 hε).div_const ε

theorem laplaceIndicatorTerm_tsum (w : ℕ → ℝ) (ε t : ℝ) :
    (∑' n : ℕ, laplaceIndicatorTerm w ε n t) =
      Real.exp (-ε * t) * logarithmicCumulative w t := by
  rw [logarithmicCumulative_eq_tsum, ← tsum_mul_left]
  apply tsum_congr
  intro n
  simp [laplaceIndicatorTerm, Set.indicator]

/-- The Laplace representation includes the positive integer 1, whose logarithm is zero. -/
theorem dirichlet_laplace_identity {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ε * (∑' n : ℕ, w (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ)) =
      ε ^ 2 * (∫ t : ℝ in Ioi 0, Real.exp (-(ε * t)) * logarithmicCumulative w t) := by
  have h := integral_tsum_of_summable_integral_norm
    (fun n => laplaceIndicatorTerm_integrable w hε n)
    (integral_laplaceIndicatorTerm_norm_summable hw0 hw1 hε)
  simp_rw [integral_laplaceIndicatorTerm w hε, laplaceIndicatorTerm_tsum,
    tsum_div_const, neg_mul] at h
  rw [← h]
  field_simp [hε.ne']

#print axioms laplaceIndicatorTerm_integrable
#print axioms laplaceIndicatorTerm_nonneg
#print axioms integral_laplaceIndicatorTerm
#print axioms integral_laplaceIndicatorTerm_norm_summable
#print axioms laplaceIndicatorTerm_tsum
#print axioms dirichlet_laplace_identity

end CollatzCanonical.DirichletAbelian
