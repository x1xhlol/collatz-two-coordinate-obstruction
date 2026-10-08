import Erdos1135.ND.Fourier.FiberEndpointFloor
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Fixed-Total Drift Domination

This leaf proves the scalar drift comparison in frozen-v10 Lemma T4.  It is
kept separate from the T3 probability bound and the later FM1 telescope.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Frozen-v10 Lemma T4: a central window at length `n` controls the drift of
the conditional center at every `3 ≤ j ≤ n`. -/
theorem ndSection7M1Window_drift
    {K : ℝ} {j n L : ℕ}
    (hj : 3 ≤ j) (hjn : j ≤ n)
    (hwin : ndSection7M1Window K n L) :
    |(j : ℝ) * (L : ℝ) / (n : ℝ) - 2 * (j : ℝ)| ≤
      K * Real.sqrt ((j : ℝ) * Real.log (j : ℝ)) := by
  have hj0 : 0 < j := by omega
  have hn0 : 0 < n := hj0.trans_le hjn
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj0
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hjnR : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
  have hjexp : Real.exp 1 ≤ (j : ℝ) := by
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hj)
  have hnexp : Real.exp 1 ≤ (n : ℝ) := hjexp.trans hjnR
  have hmono :
      Real.log (n : ℝ) / (n : ℝ) ≤
        Real.log (j : ℝ) / (j : ℝ) :=
    Real.log_div_self_antitoneOn hjexp hnexp hjnR
  have hcross :
      Real.log (n : ℝ) * (j : ℝ) ≤
        Real.log (j : ℝ) * (n : ℝ) :=
    (div_le_div_iff₀ hnR hjR).mp hmono
  have hjlog0 : 0 ≤ Real.log (j : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ j by omega))
  have hnlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hnlog0 : 0 ≤ Real.log (n : ℝ) := hnlog.le
  have hjprod0 : 0 ≤ (j : ℝ) * Real.log (j : ℝ) :=
    mul_nonneg hjR.le hjlog0
  have hnprod0 : 0 ≤ (n : ℝ) * Real.log (n : ℝ) :=
    mul_nonneg hnR.le hnlog0
  have hsqrtN : 0 < Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
    Real.sqrt_pos.2 (mul_pos hnR hnlog)
  have hKsqrt :
      0 ≤ K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
    (abs_nonneg ((L : ℝ) - 2 * (n : ℝ))).trans hwin
  have hK : 0 ≤ K := nonneg_of_mul_nonneg_left hKsqrt hsqrtN
  have hratio0 : 0 ≤ (j : ℝ) / (n : ℝ) :=
    div_nonneg hjR.le hnR.le
  have hscale :
      (j : ℝ) / (n : ℝ) *
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        Real.sqrt ((j : ℝ) * Real.log (j : ℝ)) := by
    apply (sq_le_sq₀ (mul_nonneg hratio0 (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hnprod0, Real.sq_sqrt hjprod0]
    calc
      ((j : ℝ) / (n : ℝ)) ^ 2 *
          ((n : ℝ) * Real.log (n : ℝ)) =
        ((j : ℝ) / (n : ℝ)) *
          ((j : ℝ) * Real.log (n : ℝ)) := by
            field_simp [hnR.ne']
      _ ≤ ((j : ℝ) / (n : ℝ)) *
          ((n : ℝ) * Real.log (j : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ hratio0
            simpa [mul_comm] using hcross
      _ = (j : ℝ) * Real.log (j : ℝ) := by
            field_simp [hnR.ne']
  have hdrift :
      |(j : ℝ) * (L : ℝ) / (n : ℝ) - 2 * (j : ℝ)| =
        (j : ℝ) / (n : ℝ) *
          |(L : ℝ) - 2 * (n : ℝ)| := by
    calc
      |(j : ℝ) * (L : ℝ) / (n : ℝ) - 2 * (j : ℝ)| =
          |((j : ℝ) / (n : ℝ)) *
            ((L : ℝ) - 2 * (n : ℝ))| := by
              congr 1
              field_simp [hnR.ne']
      _ = |(j : ℝ) / (n : ℝ)| *
          |(L : ℝ) - 2 * (n : ℝ)| := abs_mul _ _
      _ = (j : ℝ) / (n : ℝ) *
          |(L : ℝ) - 2 * (n : ℝ)| := by
            rw [abs_of_nonneg hratio0]
  rw [hdrift]
  calc
    (j : ℝ) / (n : ℝ) * |(L : ℝ) - 2 * (n : ℝ)| ≤
        (j : ℝ) / (n : ℝ) *
          (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hwin hratio0
    _ = K * ((j : ℝ) / (n : ℝ) *
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) := by ring
    _ ≤ K * Real.sqrt ((j : ℝ) * Real.log (j : ℝ)) :=
      mul_le_mul_of_nonneg_left hscale hK

end
end ND
end Erdos1135
