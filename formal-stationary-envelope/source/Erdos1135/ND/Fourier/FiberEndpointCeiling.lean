import Erdos1135.ND.Fourier.FiberConditioning
import Erdos1135.Tao.Renewal.Lemma77PascalGaussian

/-!
# Fixed-Fiber Endpoint Ceiling

This leaf turns the exact negative-binomial endpoint mass into the uniform
inverse-square-root ceiling used by the frozen v10 BG and A5 X.4 arguments.
The bridge retains the extra factor `1/2` between the Geom(2) endpoint and
the corresponding fair-binomial point mass.

The result is deliberately unnormalized.  A later A5 weight module must
supply the tube support and the separate lower bound for its normalizer.
-/

namespace Erdos1135
namespace ND

private theorem ndGeom2EndpointMass_eq_half_lemma77FairBinomialMass
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L) :
    ndGeom2EndpointMass n L =
      (1 / 2 : ℝ) *
        Tao.TaoSection7Lemma77.lemma77FairBinomialMass
          (L - 1) (n - 1) := by
  rw [ndGeom2EndpointMass_eq_choose_mul_pow hn hL]
  have hpow :
      (1 / 2 : ℝ) ^ L =
        (1 / 2 : ℝ) ^ (L - 1) * (1 / 2 : ℝ) := by
    calc
      (1 / 2 : ℝ) ^ L = (1 / 2 : ℝ) ^ ((L - 1) + 1) := by
        congr 1
        omega
      _ = _ := by rw [pow_succ]
  unfold Tao.TaoSection7Lemma77.lemma77FairBinomialMass
  rw [hpow]
  ring

private theorem ndGeom2EndpointMass_le_half_mul_rpow
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L) :
    ndGeom2EndpointMass n L ≤
      (1 / 2 : ℝ) * Real.rpow (L : ℝ) (-(1 / 2 : ℝ)) := by
  rw [ndGeom2EndpointMass_eq_half_lemma77FairBinomialMass hn hL]
  have hfair :=
    Tao.TaoSection7Lemma77.lemma77FairBinomialMass_le_rpow
      (L - 1) (n - 1)
  have hrow : (((L - 1 + 1 : ℕ) : ℝ)) = (L : ℝ) := by
    congr 1
    omega
  rw [hrow] at hfair
  exact mul_le_mul_of_nonneg_left hfair (by norm_num)

/-- Every positive fixed-fiber Geom(2) endpoint has the source-facing
inverse-square-root ceiling.  The bound is uniform in the total `L` once
`n ≤ L`; no local-limit or Stirling estimate is introduced here. -/
theorem ndGeom2EndpointMass_le_one_div_two_mul_sqrt
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L) :
    ndGeom2EndpointMass n L ≤
      1 / (2 * Real.sqrt (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnLR : (n : ℝ) ≤ L := by exact_mod_cast hL
  calc
    ndGeom2EndpointMass n L ≤
        (1 / 2 : ℝ) * Real.rpow (L : ℝ) (-(1 / 2 : ℝ)) :=
      ndGeom2EndpointMass_le_half_mul_rpow hn hL
    _ ≤ (1 / 2 : ℝ) * Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_nonpos hnR hnLR (by norm_num)
    _ = 1 / (2 * Real.sqrt (n : ℝ)) := by
      rw [Real.rpow_eq_pow]
      rw [Real.rpow_neg hnR.le (1 / 2 : ℝ)]
      rw [← Real.sqrt_eq_rpow]
      field_simp [(Real.sqrt_pos.2 hnR).ne']

end ND
end Erdos1135
