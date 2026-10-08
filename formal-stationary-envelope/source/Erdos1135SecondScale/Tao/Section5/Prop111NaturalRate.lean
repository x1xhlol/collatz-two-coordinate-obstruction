/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

/-
Modified 2026-09-28 for the independent alpha = 2001/2000 replay of
Mazur's Proposition 1.11 formalization, pinned at ca3dd0d63920.
The changes are documented in alpha-2001-2000.patch and the replay report.
Original copyright and license notices are retained; see LICENSE and NOTICE.
-/

import Erdos1135SecondScale.Tao.Fourier.Prop114CanonicalAssembly
import Erdos1135SecondScale.Tao.Section5.BranchPassTV
import Erdos1135SecondScale.Tao.Section5.NoHitEndpoint

/-!
# Section 5 Natural Proposition 1.11 Rate

This leaf specializes the checked fine-scale mixing theorem at exponent one,
absorbs the canonical branch passage comparison into a logarithmic rate, and
patches the finite threshold prefix with the universal full-L1 bound. It then
combines that pass-TV rate with the checked canonical no-hit rate.
-/

namespace Erdos1135SecondScale
namespace Tao

open Filter
open scoped Topology

noncomputable section

private theorem natCast_log_nonneg_prop111Rate (B : ℕ) :
    0 ≤ Real.log (B : ℝ) := by
  by_cases hB : B = 0
  · simp [hB]
  · exact Real.log_nonneg (by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hB))

/-- The floor defining the Section 5 step-back time eventually retains at
least half of its real main term. -/
theorem eventually_log_div_four_hundred_thousand_le_taoSection5M0 :
    ∀ᶠ B : ℕ in atTop,
      Real.log B / 400000 ≤ (taoSection5M0 B : ℝ) := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop (400000 : ℝ)] with B hlarge
  have hfloor :
      Real.log B / 200000 - 1 < (taoSection5M0 B : ℝ) := by
    have h := Nat.lt_floor_add_one (Real.log B / 200000)
    rw [← taoSection5M0_eq_floor_log B] at h
    have h' :
        Real.log B / 200000 < (taoSection5M0 B : ℝ) + 1 := by
      exact_mod_cast h
    linarith
  nlinarith

/-- Every fixed exponent-one mixing constant is eventually absorbed by the
repaired interior rate. -/
theorem eventually_mix_div_taoSection5M0_le_powerInteriorDelta
    {Cmix : ℝ} (hCmix : 0 ≤ Cmix) :
    ∀ᶠ B : ℕ in atTop,
      Cmix / (taoSection5M0 B : ℝ) ≤
        taoSection5PowerInteriorDelta B := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgrowth :
      Tendsto
        (fun B : ℕ => Real.rpow (Real.log B) (9 / 10 : ℝ))
        atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 10)).comp hlog
  filter_upwards
    [eventually_log_div_four_hundred_thousand_le_taoSection5M0,
      hgrowth.eventually_ge_atTop (400000 * Cmix),
      hlog.eventually_ge_atTop (1 : ℝ)]
      with B hm0Lower hgrowthB hlogOne
  let L := Real.log B
  have hLpos : 0 < L := zero_lt_one.trans_le hlogOne
  have hm0BasePos : 0 < L / 400000 := div_pos hLpos (by norm_num)
  have hdenominator :
      Cmix / (taoSection5M0 B : ℝ) ≤ Cmix / (L / 400000) :=
    div_le_div_of_nonneg_left hCmix hm0BasePos
      (by simpa only [L] using hm0Lower)
  have hfactor :
      Real.rpow L (-1 / 10 : ℝ) * L =
        Real.rpow L (9 / 10 : ℝ) := by
    calc
      Real.rpow L (-1 / 10 : ℝ) * L =
          Real.rpow L (-1 / 10 : ℝ) * Real.rpow L (1 : ℝ) := by
        congr 1
        exact (Real.rpow_one L).symm
      _ = Real.rpow L ((-1 / 10 : ℝ) + 1) :=
        (Real.rpow_add hLpos (-1 / 10 : ℝ) 1).symm
      _ = Real.rpow L (9 / 10 : ℝ) := by norm_num
  have hbaseRate :
      Cmix / (L / 400000) ≤ Real.rpow L (-1 / 10 : ℝ) := by
    apply (div_le_iff₀ hm0BasePos).2
    have hgrowthB' :
        400000 * Cmix ≤ Real.rpow L (9 / 10 : ℝ) := by
      simpa only [L] using hgrowthB
    rw [← hfactor] at hgrowthB'
    nlinarith
  exact hdenominator.trans (by
    simpa only [L, taoSection5PowerInteriorDelta] using hbaseRate)

/-- Once the mixing quotient is at the repaired-interior scale, all four raw
passage-TV errors are bounded by the single exact coefficient `3744366`. -/
theorem taoSection5_passWindowTV_rawError_le_log_rate
    {B : ℕ} {Cmix : ℝ}
    (hlogOne : 1 ≤ Real.log B)
    (hmixRate :
      Cmix / (taoSection5M0 B : ℝ) ≤
        taoSection5PowerInteriorDelta B) :
    64184 * taoSection5PowerInteriorDelta B +
          180 * (Cmix / (taoSection5M0 B : ℝ)) +
          3680000 * Real.rpow (Real.log B) (-1 / 5 : ℝ) +
          2 * (B : ℝ) ^ (-(4 / 5 : ℝ)) ≤
      3744366 * taoSection5PowerInteriorDelta B := by
  let L := Real.log B
  let rate := Real.rpow L (-1 / 10 : ℝ)
  have hLpos : 0 < L := by
    dsimp only [L]
    exact zero_lt_one.trans_le hlogOne
  have hlogRate :
      Real.rpow L (-1 / 5 : ℝ) ≤ rate := by
    dsimp only [rate]
    exact Real.rpow_le_rpow_of_exponent_le
      (by simpa only [L] using hlogOne) (by norm_num)
  have hBgt : (1 : ℝ) < (B : ℝ) :=
    (Real.log_pos_iff (Nat.cast_nonneg B)).mp
      (by simpa only [L] using hLpos)
  have hBpos : (0 : ℝ) < (B : ℝ) := zero_lt_one.trans hBgt
  have hlogLeB : L ≤ (B : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hBpos
    dsimp only [L]
    linarith
  have hthresholdExponent :
      (B : ℝ) ^ (-(4 / 5 : ℝ)) ≤
        (B : ℝ) ^ (-1 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hBgt.le (by norm_num)
  have hthresholdBase :
      (B : ℝ) ^ (-1 / 10 : ℝ) ≤ rate := by
    dsimp only [rate]
    exact Real.rpow_le_rpow_of_nonpos hLpos hlogLeB (by norm_num)
  have hthresholdRate :
      (B : ℝ) ^ (-(4 / 5 : ℝ)) ≤ rate :=
    hthresholdExponent.trans hthresholdBase
  have hdelta : taoSection5PowerInteriorDelta B = rate := by
    rfl
  rw [hdelta] at hmixRate ⊢
  calc
    64184 * rate + 180 * (Cmix / (taoSection5M0 B : ℝ)) +
          3680000 * Real.rpow (Real.log B) (-1 / 5 : ℝ) +
          2 * (B : ℝ) ^ (-(4 / 5 : ℝ)) ≤
        64184 * rate + 180 * rate + 3680000 * rate + 2 * rate := by
      gcongr
    _ = 3744366 * rate := by ring

/-- The canonical alpha/alpha-squared passage laws satisfy the unconditional
natural-threshold logarithmic rate for all sufficiently large thresholds. -/
theorem eventually_taoSection5_passWindowTV_alpha_alphaSq_le_log_rate :
    ∀ᶠ B : ℕ in atTop,
      ∀ (hB : 1 ≤ B)
        (hmassAlpha :
          0 < logFinsetMass
            (oddLogWindow (taoSection5SourceLo B .alpha)
              (taoSection5SourceHi B .alpha)))
        (hmassAlphaSq :
          0 < logFinsetMass
            (oddLogWindow (taoSection5SourceLo B .alphaSq)
              (taoSection5SourceHi B .alphaSq))),
        syracusePassWindowTV B
            (taoSection5SourceLo B .alpha)
            (taoSection5SourceHi B .alpha)
            (taoSection5SourceLo B .alphaSq)
            (taoSection5SourceHi B .alphaSq)
            hB hmassAlpha hmassAlphaSq ≤
          3744366 * taoSection5PowerInteriorDelta B := by
  obtain ⟨Cmix, hCmix, hmix⟩ :=
    TaoProp114FineScaleMixingStatement.bound
      taoProp114FineScaleMixing (A := 1) (by norm_num)
  filter_upwards
    [eventually_taoSection5PassEventPartitionFacts,
      eventually_taoSection5AffineSourceScaleFacts,
      eventually_taoSection5PowerInteriorBoundaryMassFacts,
      eventually_taoSection5PassTypicalFailureFacts,
      eventually_taoSection5_passTimeRatio_le_nine,
      eventually_mix_div_taoSection5M0_le_powerInteriorDelta hCmix]
      with B partitionFacts affineFacts boundaryFacts failureFacts
        hratio hmixRate
  intro hB hmassAlpha hmassAlphaSq
  have hraw :=
    taoSection5_passWindowTV_alpha_alphaSq_le_capped_of_mixing
      (A := 1) (Cmix := Cmix)
      partitionFacts affineFacts boundaryFacts failureFacts
      hmix hCmix (hratio .alpha) (hratio .alphaSq)
  have hlogOne : 1 ≤ Real.log B := by
    linarith [boundaryFacts.log_large]
  calc
    syracusePassWindowTV B
        (taoSection5SourceLo B .alpha)
        (taoSection5SourceHi B .alpha)
        (taoSection5SourceLo B .alphaSq)
        (taoSection5SourceHi B .alphaSq)
        hB hmassAlpha hmassAlphaSq ≤
      64184 * taoSection5PowerInteriorDelta B +
        180 * (Cmix / (taoSection5M0 B : ℝ)) +
        3680000 * Real.rpow (Real.log B) (-1 / 5 : ℝ) +
        2 * (B : ℝ) ^ (-(4 / 5 : ℝ)) := by
          simpa only [pow_one] using hraw
    _ ≤ 3744366 * taoSection5PowerInteriorDelta B :=
      taoSection5_passWindowTV_rawError_le_log_rate hlogOne hmixRate

/-- All-threshold rate statement for the canonical pair of Section 5 passage
laws. -/
def TaoSection5CanonicalPassTVRateStatement : Prop :=
  ∃ tvErr : ℕ → ℝ, ∃ C c : ℝ,
    0 ≤ C ∧ 0 < c ∧
      (∀ᶠ B : ℕ in atTop,
        0 ≤ tvErr B ∧
          tvErr B ≤ C * (Real.log (B : ℝ)) ^ (-c)) ∧
        ∀ B : ℕ, ∀ (hB : 1 ≤ B),
          ∀ (hmassAlpha :
            0 < logFinsetMass
              (oddLogWindow (taoSection5SourceLo B .alpha)
                (taoSection5SourceHi B .alpha)))
            (hmassAlphaSq :
              0 < logFinsetMass
                (oddLogWindow (taoSection5SourceLo B .alphaSq)
                  (taoSection5SourceHi B .alphaSq))),
            syracusePassWindowTV B
                (taoSection5SourceLo B .alpha)
                (taoSection5SourceHi B .alpha)
                (taoSection5SourceLo B .alphaSq)
                (taoSection5SourceHi B .alphaSq)
                hB hmassAlpha hmassAlphaSq ≤ tvErr B

/-- The finite prefix is capped by `2`; above one cutoff the error is exactly
the checked `3744366 * log(B)^(-1/10)` rate. -/
theorem taoSection5CanonicalPassTVRateStatement_checked :
    TaoSection5CanonicalPassTVRateStatement := by
  rcases eventually_atTop.1
      eventually_taoSection5_passWindowTV_alpha_alphaSq_le_log_rate with
    ⟨B0, hB0⟩
  let tvErr : ℕ → ℝ := fun B =>
    if B0 ≤ B then 3744366 * taoSection5PowerInteriorDelta B else 2
  refine ⟨tvErr, 3744366, (1 / 10 : ℝ), by norm_num, by norm_num, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop B0] with B hlarge
    rw [show tvErr B = 3744366 * taoSection5PowerInteriorDelta B by
      simp [tvErr, hlarge]]
    constructor
    · exact mul_nonneg (by norm_num)
        (Real.rpow_nonneg (natCast_log_nonneg_prop111Rate B) _)
    · simp only [taoSection5PowerInteriorDelta]
      norm_num
  · intro B hB hmassAlpha hmassAlphaSq
    by_cases hlarge : B0 ≤ B
    · rw [show tvErr B = 3744366 * taoSection5PowerInteriorDelta B by
        simp [tvErr, hlarge]]
      exact hB0 B hlarge hB hmassAlpha hmassAlphaSq
    · rw [show tvErr B = 2 by simp [tvErr, hlarge]]
      unfold syracusePassWindowTV
      exact taoTV_le_two _ _

/-- Pass-TV rate over the endpoint relation consumed by the concrete natural
Proposition 1.11 socket. -/
def TaoSection5CanonicalPairPassTVRateStatement : Prop :=
  ∃ tvErr : ℕ → ℝ, ∃ C c : ℝ,
    0 ≤ C ∧ 0 < c ∧
      (∀ᶠ B : ℕ in atTop,
        0 ≤ tvErr B ∧
          tvErr B ≤ C * (Real.log (B : ℝ)) ^ (-c)) ∧
        ∀ B lo1 hi1 lo2 hi2 : ℕ,
          (hB : 1 ≤ B) →
            TaoProp111WindowPair B lo1 hi1 lo2 hi2 →
              ∀ (hmass1 : 0 < logFinsetMass (oddLogWindow lo1 hi1))
                (hmass2 : 0 < logFinsetMass (oddLogWindow lo2 hi2)),
                  syracusePassWindowTV B lo1 hi1 lo2 hi2 hB hmass1 hmass2 ≤
                    tvErr B

theorem TaoSection5CanonicalPassTVRateStatement.to_pair
    (h : TaoSection5CanonicalPassTVRateStatement) :
    TaoSection5CanonicalPairPassTVRateStatement := by
  rcases h with ⟨tvErr, C, c, hC, hc, hrate, hbound⟩
  refine ⟨tvErr, C, c, hC, hc, hrate, ?_⟩
  intro B lo1 hi1 lo2 hi2 hB hpair hmass1 hmass2
  rcases hpair with ⟨rfl, rfl, rfl, rfl⟩
  simpa only [taoSection5SourceLo_alpha_eq_prop111Y1,
      taoSection5SourceHi_alpha_eq_prop111Y1,
      taoSection5SourceLo_alphaSq_eq_prop111Y2,
      taoSection5SourceHi_alphaSq_eq_prop111Y2] using
    hbound B hB hmass1 hmass2

theorem taoSection5CanonicalPairPassTVRateStatement_checked :
    TaoSection5CanonicalPairPassTVRateStatement :=
  TaoSection5CanonicalPassTVRateStatement.to_pair
    taoSection5CanonicalPassTVRateStatement_checked

/-- Two rate packets with the same endpoint relation combine after weakening
to the minimum exponent and maximum coefficient. -/
theorem taoProp111ConcreteFirstPassageStabilizationRate_of_pair_rates
    (hnoHit : TaoSection5CanonicalPairNoHitRateStatement)
    (hpassTV : TaoSection5CanonicalPairPassTVRateStatement) :
    TaoProp111ConcreteFirstPassageStabilizationRateStatement := by
  rcases hnoHit with
    ⟨noHitErr, CnoHit, cnoHit, hCnoHit, hcnoHit, hnoHitRate, hnoHitBound⟩
  rcases hpassTV with
    ⟨tvErr, Ctv, ctv, hCtv, hctv, htvRate, htvBound⟩
  let C := max CnoHit Ctv
  let c := min cnoHit ctv
  refine ⟨noHitErr, tvErr, C, c, ?_, ?_, ?_, ?_⟩
  · exact hCnoHit.trans (le_max_left _ _)
  · exact lt_min hcnoHit hctv
  · have hlog :
        Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards
      [hnoHitRate, htvRate, eventually_ge_atTop 1,
        hlog.eventually_ge_atTop (1 : ℝ)]
        with B hno htv hB hlogOne
    have hBOne : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    have hnoPow :
        (B : ℝ) ^ (-cnoHit) ≤ (B : ℝ) ^ (-c) :=
      Real.rpow_le_rpow_of_exponent_le hBOne
        (neg_le_neg (min_le_left cnoHit ctv))
    have htvPow :
        (Real.log (B : ℝ)) ^ (-ctv) ≤
          (Real.log (B : ℝ)) ^ (-c) :=
      Real.rpow_le_rpow_of_exponent_le hlogOne
        (neg_le_neg (min_le_right cnoHit ctv))
    refine ⟨hno.1, htv.1, ?_, ?_⟩
    · calc
        noHitErr B ≤ CnoHit * (B : ℝ) ^ (-cnoHit) := hno.2
        _ ≤ CnoHit * (B : ℝ) ^ (-c) :=
          mul_le_mul_of_nonneg_left hnoPow hCnoHit
        _ ≤ C * (B : ℝ) ^ (-c) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.rpow_nonneg (Nat.cast_nonneg B) _)
    · calc
        tvErr B ≤ Ctv * (Real.log (B : ℝ)) ^ (-ctv) := htv.2
        _ ≤ Ctv * (Real.log (B : ℝ)) ^ (-c) :=
          mul_le_mul_of_nonneg_left htvPow hCtv
        _ ≤ C * (Real.log (B : ℝ)) ^ (-c) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Real.rpow_nonneg (natCast_log_nonneg_prop111Rate B) _)
  · intro B lo1 hi1 lo2 hi2 hB hpair hmass1 hmass2
    rcases hnoHitBound B lo1 hi1 lo2 hi2 hpair hmass1 hmass2 with
      ⟨hno1, hno2⟩
    exact ⟨hno1, hno2,
      htvBound B lo1 hi1 lo2 hi2 hB hpair hmass1 hmass2⟩

/-- Checked rate-bearing natural-threshold Proposition 1.11. -/
theorem taoProp111ConcreteFirstPassageStabilizationRate_checked :
    TaoProp111ConcreteFirstPassageStabilizationRateStatement :=
  taoProp111ConcreteFirstPassageStabilizationRate_of_pair_rates
    taoSection5CanonicalPairNoHitRateStatement_checked
    taoSection5CanonicalPairPassTVRateStatement_checked

end

end Tao
end Erdos1135SecondScale
