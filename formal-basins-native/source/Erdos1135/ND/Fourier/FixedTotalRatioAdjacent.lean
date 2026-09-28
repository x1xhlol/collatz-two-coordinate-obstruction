import Erdos1135.ND.Fourier.FixedTotalReferenceRatio
import Erdos1135.ND.Fourier.FiberEndpointFloor

/-!
# Adjacent Fixed-Total Likelihood Factor

This leaf begins Stage 2 of the direct SL-D-RAT pilot.  It separates the
conditioned head-total atom into the unconditioned endpoint atom and a
positive suffix likelihood factor, then proves the exact adjacent recurrence
for that factor.  No logarithmic estimate or central-window bound is asserted
here.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- The likelihood factor left after cancelling the length-`j` endpoint
mass from the fixed-total head law. -/
noncomputable def ndFixedTotalHeadLikelihoodFactor
    (j n L u : ℕ) : ℝ :=
  ndGeom2EndpointMass (n - j) (L - u) /
    ndGeom2EndpointMass n L

/-- The conditioned head atom is the reference endpoint atom times the
suffix likelihood factor. -/
theorem ndFixedTotalHeadTotalPMF_apply_toReal_eq_endpoint_mul_factor
    {j n L : ℕ} (hj : 0 < j) (hjn : j < n) (hnL : n ≤ L)
    (u : ℕ) :
    (ndFixedTotalHeadTotalPMF j n L hj hjn hnL u).toReal =
      (ndGeom2EndpointPMF j u).toReal *
        ndFixedTotalHeadLikelihoodFactor j n L u := by
  rw [ndFixedTotalHeadTotalPMF_apply_toReal hj hjn hnL,
    ndGeom2EndpointPMF_apply_toReal_eq_endpointMass]
  simp only [ndFixedTotalHeadLikelihoodFactor, div_eq_mul_inv,
    mul_assoc]

/-- The likelihood factor is positive throughout the feasible support. -/
theorem ndFixedTotalHeadLikelihoodFactor_pos
    {j n L u : ℕ} (hjn : j < n) (hnL : n ≤ L)
    (huTail : u + (n - j) ≤ L) :
    0 < ndFixedTotalHeadLikelihoodFactor j n L u := by
  exact div_pos
    (ndGeom2EndpointMass_pos (by omega) (by omega))
    (ndGeom2EndpointMass_pos (by omega) hnL)

/-- Exact one-step multiplier for the fixed-total likelihood factor. -/
noncomputable def ndFixedTotalHeadLikelihoodStep
    (j n L u : ℕ) : ℝ :=
  2 * ((L - u - (n - j) : ℕ) : ℝ) /
    ((L - u - 1 : ℕ) : ℝ)

/-- Exact adjacent recurrence.  The strict suffix-room guard is precisely
what makes both adjacent suffix endpoint masses positive. -/
theorem ndFixedTotalHeadLikelihoodFactor_succ
    {j n L u : ℕ} (hjn : j < n)
    (huTail : u + (n - j) < L) :
    ndFixedTotalHeadLikelihoodFactor j n L (u + 1) =
      ndFixedTotalHeadLikelihoodFactor j n L u *
        ndFixedTotalHeadLikelihoodStep j n L u := by
  have ht : 0 < n - j := by omega
  have hbase : n - j ≤ L - (u + 1) := by omega
  have hrec := ndGeom2EndpointMass_eq_succ_mul ht hbase
  have hnext : L - (u + 1) + 1 = L - u := by omega
  have hnum : L - (u + 1) - (n - j) + 1 =
      L - u - (n - j) := by omega
  have hden : L - (u + 1) = L - u - 1 := by omega
  unfold ndFixedTotalHeadLikelihoodFactor
  rw [hrec, hnext, hnum, hden]
  unfold ndFixedTotalHeadLikelihoodStep
  ring

/-- Source-facing adjacent likelihood-ratio recurrence.  Positivity is kept
visible so the cancellation of the two reference endpoint atoms is honest. -/
theorem ndFixedTotalHeadTotalPMF_likelihoodRatio_succ
    {j n L u : ℕ} (hj : 0 < j) (hjn : j < n) (hnL : n ≤ L)
    (hju : j ≤ u) (huTail : u + (n - j) < L) :
    (ndFixedTotalHeadTotalPMF j n L hj hjn hnL (u + 1)).toReal /
        (ndGeom2EndpointPMF j (u + 1)).toReal =
      ((ndFixedTotalHeadTotalPMF j n L hj hjn hnL u).toReal /
          (ndGeom2EndpointPMF j u).toReal) *
        ndFixedTotalHeadLikelihoodStep j n L u := by
  have hQ : 0 < (ndGeom2EndpointPMF j u).toReal := by
    rw [ndGeom2EndpointPMF_apply_toReal_eq_endpointMass]
    exact ndGeom2EndpointMass_pos hj hju
  have hQsucc : 0 < (ndGeom2EndpointPMF j (u + 1)).toReal := by
    rw [ndGeom2EndpointPMF_apply_toReal_eq_endpointMass]
    exact ndGeom2EndpointMass_pos hj (by omega)
  rw [ndFixedTotalHeadTotalPMF_apply_toReal_eq_endpoint_mul_factor,
    ndFixedTotalHeadTotalPMF_apply_toReal_eq_endpoint_mul_factor]
  field_simp [hQ.ne', hQsucc.ne']
  exact ndFixedTotalHeadLikelihoodFactor_succ hjn huTail

/-- The exact source numerator for the adjacent multiplier minus one.  All
subtractions on the right are real, so negative parent-center displacement is
retained. -/
theorem ndFixedTotalHeadLikelihoodStep_sub_one_eq
    {j n L u : ℕ} (hjn : j < n)
    (huTail : u + (n - j) < L) :
    ndFixedTotalHeadLikelihoodStep j n L u - 1 =
      (((L : ℝ) - 2 * (n : ℝ)) -
          ((u : ℝ) - 2 * (j : ℝ)) + 1) /
        ((L : ℝ) - (u : ℝ) - 1) := by
  have hLu : u ≤ L := by omega
  have hnj : j ≤ n := by omega
  have htail : n - j ≤ L - u := by omega
  have hone : 1 ≤ L - u := by omega
  have hnum :
      ((L - u - (n - j) : ℕ) : ℝ) =
        (L : ℝ) - (u : ℝ) - ((n : ℝ) - (j : ℝ)) := by
    rw [Nat.cast_sub htail, Nat.cast_sub hLu, Nat.cast_sub hnj]
  have hden :
      ((L - u - 1 : ℕ) : ℝ) = (L : ℝ) - (u : ℝ) - 1 := by
    rw [Nat.cast_sub hone, Nat.cast_sub hLu]
    norm_num
  have hdenNat : 0 < L - u - 1 := by omega
  have hdenPos : 0 < (L : ℝ) - (u : ℝ) - 1 := by
    rw [← hden]
    exact_mod_cast hdenNat
  rw [ndFixedTotalHeadLikelihoodStep, hnum, hden]
  field_simp [hdenPos.ne']
  ring

/-- Triangle form of the adjacent numerator, ready for the central-window
denominator estimate. -/
theorem abs_ndFixedTotalHeadLikelihoodStep_sub_one_le
    {j n L u : ℕ} (hjn : j < n)
    (huTail : u + (n - j) < L) :
    |ndFixedTotalHeadLikelihoodStep j n L u - 1| ≤
      (|(L : ℝ) - 2 * (n : ℝ)| +
          |(u : ℝ) - 2 * (j : ℝ)| + 1) /
        ((L : ℝ) - (u : ℝ) - 1) := by
  have hLu : u ≤ L := by omega
  have hone : 1 ≤ L - u := by omega
  have hden :
      ((L - u - 1 : ℕ) : ℝ) = (L : ℝ) - (u : ℝ) - 1 := by
    rw [Nat.cast_sub hone, Nat.cast_sub hLu]
    norm_num
  have hdenNat : 0 < L - u - 1 := by omega
  have hdenPos : 0 < (L : ℝ) - (u : ℝ) - 1 := by
    rw [← hden]
    exact_mod_cast hdenNat
  rw [ndFixedTotalHeadLikelihoodStep_sub_one_eq hjn huTail, abs_div,
    abs_of_pos hdenPos]
  apply div_le_div_of_nonneg_right _ hdenPos.le
  calc
    |((L : ℝ) - 2 * (n : ℝ)) -
        ((u : ℝ) - 2 * (j : ℝ)) + 1| ≤
        |(L : ℝ) - 2 * (n : ℝ)| +
          |(u : ℝ) - 2 * (j : ℝ)| + |(1 : ℝ)| := by
      calc
        |((L : ℝ) - 2 * (n : ℝ)) -
            ((u : ℝ) - 2 * (j : ℝ)) + 1| ≤
            |((L : ℝ) - 2 * (n : ℝ)) -
              ((u : ℝ) - 2 * (j : ℝ))| + |(1 : ℝ)| := abs_add_le _ _
        _ ≤ |(L : ℝ) - 2 * (n : ℝ)| +
              |(u : ℝ) - 2 * (j : ℝ)| + |(1 : ℝ)| := by
          gcongr
          exact abs_sub _ _
    _ = |(L : ℝ) - 2 * (n : ℝ)| +
          |(u : ℝ) - 2 * (j : ℝ)| + 1 := by norm_num

end

end ND
end Erdos1135
