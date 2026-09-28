import Erdos1135.ND.Fourier.FixedTotalRatioTelescope
import Erdos1135.ND.Fourier.FixedTotalT3
import Erdos1135.Tao.Probability.FullL1
import Erdos1135.Tao.Probability.Geom2CenteredMoment

/-!
# Fixed-Total Ratio Outside Tails

This leaf converts the native countable outside-mass convention to PMF outer
mass and proves the conditioned `2 / j^3` tail in the literal ratio window.
The reference Geom(2) tail is added at the same endpoint-shaped boundary.
-/

namespace Erdos1135
namespace ND

open Tao

noncomputable section

/-- Native countable outside mass is exactly PMF mass of the complement. -/
theorem ndPMFOutsideMass_eq_pmfOuterMass_compl
    {α : Type*} (p : PMF α) (Good : α → Prop) :
    ndPMFOutsideMass p Good =
      (p.toOuterMeasure {u | ¬ Good u}).toReal := by
  classical
  unfold ndPMFOutsideMass
  rw [Tao.pmfOuterMass_toReal_eq_tsum_indicator]
  apply tsum_congr
  intro u
  by_cases hu : Good u <;> simp [Set.indicator, hu]

private theorem two_mul_exp_fixedTotalRatio_conditioned_le_cube
    {j : ℕ} (hj : 150 ≤ j) :
    2 * Real.exp
        (-((15 * ndFixedTotalRatioScale j) ^ 2) /
          (63 * (j : ℝ))) ≤
      2 / (j : ℝ) ^ 3 := by
  have hjPos : 0 < j := by omega
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hjPos
  have hlog : 0 ≤ Real.log (j : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ j by omega))
  have hscaleSq := ndFixedTotalRatioScale_sq (show 1 ≤ j by omega)
  have hfrac :
      3 * Real.log (j : ℝ) ≤
        (15 * ndFixedTotalRatioScale j) ^ 2 / (63 * (j : ℝ)) := by
    rw [show (15 * ndFixedTotalRatioScale j) ^ 2 =
      225 * ndFixedTotalRatioScale j ^ 2 by ring, hscaleSq]
    field_simp [hjR.ne']
    nlinarith
  have hneg :
      -((15 * ndFixedTotalRatioScale j) ^ 2) / (63 * (j : ℝ)) ≤
        -(3 * Real.log (j : ℝ)) := by
    rw [neg_div]
    exact neg_le_neg hfrac
  calc
    2 * Real.exp
        (-((15 * ndFixedTotalRatioScale j) ^ 2) /
          (63 * (j : ℝ))) ≤
        2 * Real.exp (-(3 * Real.log (j : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hneg) (by norm_num)
    _ = 2 / (j : ℝ) ^ 3 := by
      rw [show 3 * Real.log (j : ℝ) =
          ((3 : ℕ) : ℝ) * Real.log (j : ℝ) by norm_num,
        Real.exp_neg, Real.exp_nat_mul, Real.exp_log hjR]
      simp [div_eq_mul_inv]

/-- The conditioned prefix-total law has at most `2/j^3` mass outside the
literal ratio window under H1--H3. -/
theorem ndFixedTotalHeadTotalPMF_outside_ratioGood_le_two_div_cube
    {j n L : ℕ} (hj : 150 ≤ j) (hjn : 8 * j ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8)
    (hDelta :
      ndFixedTotalRatioCenterOffset j n L ≤ ndFixedTotalRatioScale j) :
    ndPMFOutsideMass
        (ndFixedTotalHeadTotalPMF j n L (by omega) (by omega)
          (ndFixedTotalRatio_n_le_L hj hjn hD))
        (ndFixedTotalRatioGood j) ≤
      2 / (j : ℝ) ^ 3 := by
  let S : ℝ := ndFixedTotalRatioScale j
  have hnL := ndFixedTotalRatio_n_le_L hj hjn hD
  let base : PMF (NDFixedTotalSplitIndex j (n - j) L) :=
    ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega)
  letI : Fintype (NDFixedTotalSplitIndex j (n - j) L) :=
    ndFixedTotalSplitIndexFintypeOfLe j (n - j) L (by omega)
  have hL3nR : (L : ℝ) ≤ 3 * (n : ℝ) := by
    have hupper := le_of_abs_le hD
    nlinarith
  have hL3n : L ≤ 3 * n := by exact_mod_cast hL3nR
  have hS2 : (2 : ℝ) ≤ S := by
    simpa only [S] using two_le_ndFixedTotalRatioScale hj
  have hu8 : (8 : ℝ) ≤ 15 * S := by nlinarith
  have h16 : 16 * S ≤ (ndFixedTotalRatioRadius j : ℝ) := by
    simpa only [S] using sixteen_mul_scale_le_radius j
  have hRadius3j :
      (ndFixedTotalRatioRadius j : ℝ) ≤ 3 * (j : ℝ) := by
    exact_mod_cast ndFixedTotalRatioRadius_le_three_mul hj
  have hu3j : 15 * S ≤ 3 * (j : ℝ) := by nlinarith
  have hcenter :
      |(j : ℝ) * (L : ℝ) / (n : ℝ) - 2 * (j : ℝ)| ≤ S := by
    rw [← ndFixedTotalRatioCenterOffset_eq_abs (by omega)]
    exact hDelta
  have ht3 := ndFixedTotalSplitIndexPMF_map_headTotal_absTail_le
    n j L (by omega) (by omega) (by omega) hnL hL3n
      (15 * S) hu8 hu3j
  rw [PMF.toOuterMeasure_map_apply,
    ← Tao.pmfProb_eq_toOuterMeasure_toReal] at ht3
  change Tao.pmfProb base
      {s | 15 * S ≤
        |(s.headTotal : ℝ) -
          (j : ℝ) * (L : ℝ) / (n : ℝ)|} ≤
    2 * Real.exp (-((15 * S) ^ 2) / (63 * (j : ℝ))) at ht3
  have hsubset :
      {s : NDFixedTotalSplitIndex j (n - j) L |
        ¬ ndFixedTotalRatioGood j s.headTotal} ⊆
      {s | 15 * S ≤
        |(s.headTotal : ℝ) -
          (j : ℝ) * (L : ℝ) / (n : ℝ)|} := by
    intro s hs
    have hhead : j ≤ s.headTotal := s.headLength_le
    have hwindow :
        (ndFixedTotalRatioRadius j : ℝ) <
          |(s.headTotal : ℝ) - 2 * (j : ℝ)| := by
      apply lt_of_not_ge
      intro hle
      exact hs ⟨hhead, hle⟩
    have htriangle :
        |(s.headTotal : ℝ) - 2 * (j : ℝ)| ≤
          |(s.headTotal : ℝ) -
              (j : ℝ) * (L : ℝ) / (n : ℝ)| +
            |(j : ℝ) * (L : ℝ) / (n : ℝ) - 2 * (j : ℝ)| := by
      calc
        |(s.headTotal : ℝ) - 2 * (j : ℝ)| =
            |((s.headTotal : ℝ) -
                (j : ℝ) * (L : ℝ) / (n : ℝ)) +
              ((j : ℝ) * (L : ℝ) / (n : ℝ) - 2 * (j : ℝ))| := by
          congr 1
          ring
        _ ≤ |(s.headTotal : ℝ) -
                (j : ℝ) * (L : ℝ) / (n : ℝ)| +
              |(j : ℝ) * (L : ℝ) / (n : ℝ) - 2 * (j : ℝ)| :=
          abs_add_le _ _
    have h16lt :
        16 * S < |(s.headTotal : ℝ) - 2 * (j : ℝ)| :=
      h16.trans_lt hwindow
    have hsumlt :
        16 * S <
          |(s.headTotal : ℝ) -
              (j : ℝ) * (L : ℝ) / (n : ℝ)| +
            |(j : ℝ) * (L : ℝ) / (n : ℝ) - 2 * (j : ℝ)| :=
      h16lt.trans_le htriangle
    have hsumlt' :
        16 * S <
          |(s.headTotal : ℝ) -
              (j : ℝ) * (L : ℝ) / (n : ℝ)| + S :=
      hsumlt.trans_le (add_le_add_right hcenter _)
    change 15 * S ≤
      |(s.headTotal : ℝ) - (j : ℝ) * (L : ℝ) / (n : ℝ)|
    linarith
  rw [ndPMFOutsideMass_eq_pmfOuterMass_compl]
  change ((((base.map fun s => s.headTotal).toOuterMeasure
      {u | ¬ ndFixedTotalRatioGood j u}).toReal) ≤
        2 / (j : ℝ) ^ 3)
  rw [PMF.toOuterMeasure_map_apply,
    ← Tao.pmfProb_eq_toOuterMeasure_toReal]
  exact (Tao.pmfProb_mono base hsubset).trans
    (ht3.trans (by
      simpa only [S] using
        two_mul_exp_fixedTotalRatio_conditioned_le_cube hj))

private theorem two_mul_exp_fixedTotalRatio_reference_le_cube
    {j : ℕ} (hj : 150 ≤ j) :
    2 * Real.exp
        (-min
          ((ndFixedTotalRatioRadius j : ℝ) ^ 2 / (32 * (j : ℝ)))
          ((ndFixedTotalRatioRadius j : ℝ) / 8)) ≤
      2 / (j : ℝ) ^ 3 := by
  let S : ℝ := ndFixedTotalRatioScale j
  let R : ℝ := (ndFixedTotalRatioRadius j : ℝ)
  have hjPos : 0 < j := by omega
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hjPos
  have hlog : 0 ≤ Real.log (j : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ j by omega))
  have hlogBound := real_log_nat_le_div_twentyNine hj
  have hscaleSq : S ^ 2 = (j : ℝ) * Real.log (j : ℝ) := by
    simpa only [S] using ndFixedTotalRatioScale_sq (show 1 ≤ j by omega)
  have hS0 : 0 ≤ S := by
    simpa only [S] using ndFixedTotalRatioScale_nonneg j
  have hR0 : 0 ≤ R := by positivity
  have h16 : 16 * S ≤ R := by
    simpa only [S, R] using sixteen_mul_scale_le_radius j
  have hR2 : (16 * S) ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (by norm_num) hS0) hR0).2 h16
  have hquad :
      3 * Real.log (j : ℝ) ≤ R ^ 2 / (32 * (j : ℝ)) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hjR)]
    nlinarith
  have hlogScale : 3 * Real.log (j : ℝ) ≤ 2 * S := by
    have hprod :
        0 ≤ Real.log (j : ℝ) *
          ((j : ℝ) / 29 - Real.log (j : ℝ)) :=
      mul_nonneg hlog (sub_nonneg.mpr hlogBound)
    have hsq :
        (3 * Real.log (j : ℝ)) ^ 2 ≤ (2 * S) ^ 2 := by
      nlinarith
    exact (sq_le_sq₀ (mul_nonneg (by norm_num) hlog)
      (mul_nonneg (by norm_num) hS0)).1 hsq
  have hlinear :
      3 * Real.log (j : ℝ) ≤ R / 8 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    nlinarith
  have hmin :
      3 * Real.log (j : ℝ) ≤
        min (R ^ 2 / (32 * (j : ℝ))) (R / 8) :=
    le_min hquad hlinear
  have hneg :
      -min (R ^ 2 / (32 * (j : ℝ))) (R / 8) ≤
        -(3 * Real.log (j : ℝ)) := neg_le_neg hmin
  calc
    2 * Real.exp
        (-min
          ((ndFixedTotalRatioRadius j : ℝ) ^ 2 / (32 * (j : ℝ)))
          ((ndFixedTotalRatioRadius j : ℝ) / 8)) =
        2 * Real.exp (-min (R ^ 2 / (32 * (j : ℝ))) (R / 8)) := by
      rfl
    _ ≤ 2 * Real.exp (-(3 * Real.log (j : ℝ))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hneg) (by norm_num)
    _ = 2 / (j : ℝ) ^ 3 := by
      rw [show 3 * Real.log (j : ℝ) =
          ((3 : ℕ) : ℝ) * Real.log (j : ℝ) by norm_num,
        Real.exp_neg, Real.exp_nat_mul, Real.exp_log hjR]
      simp [div_eq_mul_inv]

/-- The unconditioned Geom(2) endpoint reference has at most `2/j^3` mass
outside the same literal ratio window. -/
theorem ndGeom2EndpointPMF_outside_ratioGood_le_two_div_cube
    {j : ℕ} (hj : 150 ≤ j) :
    ndPMFOutsideMass (ndGeom2EndpointPMF j)
        (ndFixedTotalRatioGood j) ≤
      2 / (j : ℝ) ^ 3 := by
  let q : PMF ℕ := ndGeom2EndpointPMF j
  let source : PMF (List ℕ+) := Tao.geom2PNatListPMF j
  let R : ℝ := (ndFixedTotalRatioRadius j : ℝ)
  let bad : Set ℕ := {u | ¬ ndFixedTotalRatioGood j u}
  let radiusEvent : Set ℕ :=
    {u | R < |(u : ℝ) - 2 * (j : ℝ)|}
  have hbadRadius : bad ∩ q.support = radiusEvent ∩ q.support := by
    ext u
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨huBad, huSupport⟩
      have hju : j ≤ u :=
        ndGeom2EndpointPMF_support_subset_Ici j huSupport
      have hradius : R < |(u : ℝ) - 2 * (j : ℝ)| := by
        apply lt_of_not_ge
        intro huCenter
        exact huBad ⟨hju, huCenter⟩
      exact ⟨hradius, huSupport⟩
    · rintro ⟨huRadius, huSupport⟩
      have huBad : ¬ ndFixedTotalRatioGood j u := by
        intro huGood
        exact (not_lt_of_ge huGood.2) huRadius
      exact ⟨huBad, huSupport⟩
  have hmassBadRadius :
      q.toOuterMeasure bad = q.toOuterMeasure radiusEvent :=
    q.toOuterMeasure_apply_eq_of_inter_support_eq hbadRadius
  rw [ndPMFOutsideMass_eq_pmfOuterMass_compl]
  change (q.toOuterMeasure bad).toReal ≤ 2 / (j : ℝ) ^ 3
  rw [hmassBadRadius]
  change (((source.map Tao.taoTupleWeight).toOuterMeasure radiusEvent).toReal ≤
    2 / (j : ℝ) ^ 3)
  rw [PMF.toOuterMeasure_map_apply]
  let pulled : Set (List ℕ+) :=
    {as | R <
      |(Tao.taoTupleWeight as : ℝ) - 2 * (j : ℝ)|}
  let centered : Set (List ℕ+) :=
    {as | R < |Tao.taoGeom2CenteredListWeight as|}
  change (source.toOuterMeasure pulled).toReal ≤ 2 / (j : ℝ) ^ 3
  have hpulledCentered :
      pulled ∩ source.support = centered ∩ source.support := by
    ext as
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨hasPulled, hasSupport⟩
      have hlength : as.length = j :=
        Tao.geom2PNatListPMF_support_length_eq hasSupport
      have hcentered :
          Tao.taoGeom2CenteredListWeight as =
            (Tao.taoTupleWeight as : ℝ) - 2 * (j : ℝ) := by
        unfold Tao.taoGeom2CenteredListWeight
        rw [hlength]
      have hasPulled' :
          R < |(Tao.taoTupleWeight as : ℝ) - 2 * (j : ℝ)| := by
        simpa only [pulled, Set.mem_setOf_eq] using hasPulled
      have hasCentered' : R < |Tao.taoGeom2CenteredListWeight as| := by
        rw [hcentered]
        exact hasPulled'
      exact ⟨by simpa only [centered, Set.mem_setOf_eq] using hasCentered',
        hasSupport⟩
    · rintro ⟨hasCentered, hasSupport⟩
      have hlength : as.length = j :=
        Tao.geom2PNatListPMF_support_length_eq hasSupport
      have hcentered :
          Tao.taoGeom2CenteredListWeight as =
            (Tao.taoTupleWeight as : ℝ) - 2 * (j : ℝ) := by
        unfold Tao.taoGeom2CenteredListWeight
        rw [hlength]
      have hasCentered' : R < |Tao.taoGeom2CenteredListWeight as| := by
        simpa only [centered, Set.mem_setOf_eq] using hasCentered
      have hasPulled' :
          R < |(Tao.taoTupleWeight as : ℝ) - 2 * (j : ℝ)| := by
        rw [← hcentered]
        exact hasCentered'
      exact ⟨by simpa only [pulled, Set.mem_setOf_eq] using hasPulled',
        hasSupport⟩
  have hmassPulledCentered :
      source.toOuterMeasure pulled = source.toOuterMeasure centered :=
    source.toOuterMeasure_apply_eq_of_inter_support_eq hpulledCentered
  rw [hmassPulledCentered]
  have hS2 := two_le_ndFixedTotalRatioScale hj
  have h16 := sixteen_mul_scale_le_radius j
  have hRpos : 0 < R := by
    dsimp [R]
    nlinarith
  have htail := Tao.geom2PNatListPMF_centeredWeight_absTail_le_min
    (show 0 < j by omega) hRpos
  change (source.toOuterMeasure centered).toReal ≤
    2 * Real.exp (-min (R ^ 2 / (32 * (j : ℝ))) (R / 8)) at htail
  exact htail.trans (by
    simpa only [R] using two_mul_exp_fixedTotalRatio_reference_le_cube hj)

end

end ND
end Erdos1135
