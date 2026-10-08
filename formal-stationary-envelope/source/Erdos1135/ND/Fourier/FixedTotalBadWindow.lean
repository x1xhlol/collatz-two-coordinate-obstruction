import Erdos1135.ND.Fourier.FixedTotalT3
import Erdos1135.ND.Fourier.FixedTotalT4

/-!
# Fixed-Total Bad-Window Probability

This leaf combines frozen-v10 Lemmas T3 and T4 at the exact enlarged window
used by the FM1 telescope.  It exposes both the mapped endpoint event and its
immediate split-source preimage, but contains no oscillation algebra.
-/

namespace Erdos1135
namespace ND

noncomputable section

private theorem ndFixedTotalBadWindow_eight_le_u
    (A j : ℕ) (hj : 3 ≤ j) :
    (8 : ℝ) ≤
      Real.sqrt (63 * ((A : ℝ) + 2)) *
        Real.sqrt ((j : ℝ) * Real.log (j : ℝ)) := by
  have hj0 : 0 < j := by omega
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj0
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
      Real.exp_one_lt_three
  have hlogj : (1 : ℝ) ≤ Real.log (j : ℝ) := by
    exact hlog3.le.trans
      (Real.log_le_log (by norm_num : (0 : ℝ) < 3)
        (by exact_mod_cast hj))
  have hleft :
      (126 : ℝ) ≤ 63 * ((A : ℝ) + 2) := by
    have hA0 : (0 : ℝ) ≤ (A : ℝ) := by positivity
    nlinarith
  have hright :
      (3 : ℝ) ≤ (j : ℝ) * Real.log (j : ℝ) := by
    calc
      (3 : ℝ) = 3 * 1 := by ring
      _ ≤ (j : ℝ) * Real.log (j : ℝ) :=
        mul_le_mul (by exact_mod_cast hj) hlogj (by norm_num) hjR.le
  have hprod :
      (64 : ℝ) ≤
        (63 * ((A : ℝ) + 2)) *
          ((j : ℝ) * Real.log (j : ℝ)) := by
    calc
      (64 : ℝ) ≤ 126 * 3 := by norm_num
      _ ≤ (63 * ((A : ℝ) + 2)) *
          ((j : ℝ) * Real.log (j : ℝ)) :=
        mul_le_mul hleft hright (by norm_num) (by positivity)
  have hdelta0 : (0 : ℝ) ≤ 63 * ((A : ℝ) + 2) := by positivity
  have hscale0 : (0 : ℝ) ≤ (j : ℝ) * Real.log (j : ℝ) :=
    mul_nonneg hjR.le (zero_le_one.trans hlogj)
  apply (sq_le_sq₀ (by norm_num)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hdelta0, Real.sq_sqrt hscale0]
  norm_num
  exact hprod

private theorem ndFixedTotalBadWindow_exp_eq_pow
    (A j : ℕ) (hj : 3 ≤ j) :
    2 * Real.exp
        (-((Real.sqrt (63 * ((A : ℝ) + 2)) *
          Real.sqrt ((j : ℝ) * Real.log (j : ℝ))) ^ 2) /
            (63 * (j : ℝ))) =
      2 / (j : ℝ) ^ (A + 2) := by
  have hj0 : 0 < j := by omega
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj0
  have hdelta0 : (0 : ℝ) ≤ 63 * ((A : ℝ) + 2) := by positivity
  have hjlog0 : 0 ≤ Real.log (j : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ j by omega))
  have hscale0 : (0 : ℝ) ≤ (j : ℝ) * Real.log (j : ℝ) :=
    mul_nonneg hjR.le hjlog0
  have huSq :
      (Real.sqrt (63 * ((A : ℝ) + 2)) *
          Real.sqrt ((j : ℝ) * Real.log (j : ℝ))) ^ 2 =
        (63 * ((A : ℝ) + 2)) *
          ((j : ℝ) * Real.log (j : ℝ)) := by
    rw [mul_pow, Real.sq_sqrt hdelta0, Real.sq_sqrt hscale0]
  have hexponent :
      -((Real.sqrt (63 * ((A : ℝ) + 2)) *
          Real.sqrt ((j : ℝ) * Real.log (j : ℝ))) ^ 2) /
          (63 * (j : ℝ)) =
        -(((A : ℝ) + 2) * Real.log (j : ℝ)) := by
    rw [huSq]
    field_simp [hjR.ne']
  rw [hexponent]
  have hcast : ((A : ℝ) + 2) = ((A + 2 : ℕ) : ℝ) := by norm_num
  rw [hcast, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hjR,
    div_eq_mul_inv]

/-- The enlarged-window bad endpoint has the exact polynomial mass consumed
by the frozen FM1 telescope.  The lower T3 guard is derived uniformly from
`A : ℕ` and `j ≥ 3`; only its upper guard remains visible. -/
theorem ndFixedTotalSplitIndexPMF_map_headTotal_badWindow_le
    (A n j L : ℕ) (K : ℝ)
    (hj : 3 ≤ j) (hjn : j < n)
    (hnL : n ≤ L) (hL3n : L ≤ 3 * n)
    (hwin : ndSection7M1Window K n L)
    (hu3 :
      Real.sqrt (63 * ((A : ℝ) + 2)) *
          Real.sqrt ((j : ℝ) * Real.log (j : ℝ)) ≤
        3 * (j : ℝ)) :
    (((ndFixedTotalSplitIndexPMF j (n - j) L
          (by omega) (by omega)).map
        (fun s => s.headTotal)).toOuterMeasure
      {m : ℕ | ¬ ndSection7M1Window
        (K + Real.sqrt (63 * ((A : ℝ) + 2))) j m}).toReal ≤
      2 / (j : ℝ) ^ (A + 2) := by
  letI : Fintype (NDFixedTotalSplitIndex j (n - j) L) :=
    ndFixedTotalSplitIndexFintypeOfLe j (n - j) L (by omega)
  let delta : ℝ := Real.sqrt (63 * ((A : ℝ) + 2))
  let S : ℝ := Real.sqrt ((j : ℝ) * Real.log (j : ℝ))
  let u : ℝ := delta * S
  let center : ℝ := (j : ℝ) * (L : ℝ) / (n : ℝ)
  have hu8 : 8 ≤ u := by
    simpa only [u, delta, S] using
      ndFixedTotalBadWindow_eight_le_u A j hj
  have ht3 := ndFixedTotalSplitIndexPMF_map_headTotal_absTail_le
    n j L (by omega) (by omega) hjn hnL hL3n u hu8
      (by simpa only [u, delta, S] using hu3)
  rw [PMF.toOuterMeasure_map_apply,
    ← Tao.pmfProb_eq_toOuterMeasure_toReal] at ht3 ⊢
  change Tao.pmfProb
      (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
      {s | ¬ ndSection7M1Window
        (K + Real.sqrt (63 * ((A : ℝ) + 2))) j s.headTotal} ≤
    2 / (j : ℝ) ^ (A + 2)
  change Tao.pmfProb
      (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
      {s | u ≤ |(s.headTotal : ℝ) - center|} ≤
    2 * Real.exp (-(u ^ 2) / (63 * (j : ℝ))) at ht3
  have hsubset :
      {s : NDFixedTotalSplitIndex j (n - j) L |
        ¬ ndSection7M1Window
          (K + Real.sqrt (63 * ((A : ℝ) + 2))) j s.headTotal} ⊆
      {s | u ≤ |(s.headTotal : ℝ) - center|} := by
    intro s hs
    have hdrift :
        |center - 2 * (j : ℝ)| ≤ K * S := by
      simpa only [center, S] using
        ndSection7M1Window_drift
          (K := K) (j := j) (n := n) (L := L)
          hj hjn.le hwin
    have hbad :
        (K + delta) * S <
          |(s.headTotal : ℝ) - 2 * (j : ℝ)| := by
      simpa only [ndSection7M1Window, not_le, delta, S] using hs
    have htriangle :
        |(s.headTotal : ℝ) - 2 * (j : ℝ)| ≤
          |(s.headTotal : ℝ) - center| +
            |center - 2 * (j : ℝ)| := by
      calc
        |(s.headTotal : ℝ) - 2 * (j : ℝ)| =
            |((s.headTotal : ℝ) - center) +
              (center - 2 * (j : ℝ))| := by
                congr 1
                ring
        _ ≤ |(s.headTotal : ℝ) - center| +
            |center - 2 * (j : ℝ)| := abs_add_le _ _
    have hsum :
        K * S + delta * S <
          K * S + |(s.headTotal : ℝ) - center| := by
      calc
        K * S + delta * S = (K + delta) * S := by ring
        _ < |(s.headTotal : ℝ) - 2 * (j : ℝ)| := hbad
        _ ≤ |(s.headTotal : ℝ) - center| +
            |center - 2 * (j : ℝ)| := htriangle
        _ ≤ |(s.headTotal : ℝ) - center| + K * S :=
          add_le_add le_rfl hdrift
        _ = K * S + |(s.headTotal : ℝ) - center| := by ring
    change u ≤ |(s.headTotal : ℝ) - center|
    exact ((add_lt_add_iff_left (K * S)).mp hsum).le
  calc
    Tao.pmfProb
        (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
        {s | ¬ ndSection7M1Window
          (K + Real.sqrt (63 * ((A : ℝ) + 2))) j s.headTotal} ≤
      Tao.pmfProb
        (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
        {s | u ≤ |(s.headTotal : ℝ) - center|} :=
      Tao.pmfProb_mono _ hsubset
    _ ≤ 2 * Real.exp (-(u ^ 2) / (63 * (j : ℝ))) := ht3
    _ = 2 / (j : ℝ) ^ (A + 2) := by
      simpa only [u, delta, S] using
        ndFixedTotalBadWindow_exp_eq_pow A j hj

/-- Split-source form of the enlarged-window bad-mass bound, ready for the
T2 bind/mixture consumer. -/
theorem ndFixedTotalSplitIndexPMF_badWindow_le
    (A n j L : ℕ) (K : ℝ)
    (hj : 3 ≤ j) (hjn : j < n)
    (hnL : n ≤ L) (hL3n : L ≤ 3 * n)
    (hwin : ndSection7M1Window K n L)
    (hu3 :
      Real.sqrt (63 * ((A : ℝ) + 2)) *
          Real.sqrt ((j : ℝ) * Real.log (j : ℝ)) ≤
        3 * (j : ℝ)) :
    ((ndFixedTotalSplitIndexPMF j (n - j) L
        (by omega) (by omega)).toOuterMeasure
      {s | ¬ ndSection7M1Window
        (K + Real.sqrt (63 * ((A : ℝ) + 2))) j s.headTotal}).toReal ≤
      2 / (j : ℝ) ^ (A + 2) := by
  have h := ndFixedTotalSplitIndexPMF_map_headTotal_badWindow_le
    A n j L K hj hjn hnL hL3n hwin hu3
  rw [PMF.toOuterMeasure_map_apply] at h
  exact h

end
end ND
end Erdos1135
