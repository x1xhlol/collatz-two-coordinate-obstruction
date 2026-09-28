import Erdos1135.Tao.Renewal.QEndpointFreshOutsideEprimeSourceWidth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Canonical Outside-Eprime Source Margin

This source-facing leaf proves the remaining scalar row margin for the
canonical outside-`E'_p` estimate.  For each fixed offset scale, the
`S^(3/5)` horizontal error and fixed vertical error are eventually absorbed
by Tao's positive linear logarithmic margin.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open Filter Topology
open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Two half-budget estimates combine into the exact row-margin premise used
by the canonical outside-`E'_p` mass theorem. -/
theorem lemma79OutsideEprimeErrorMargin_of_split_absorption
    {Aweight p : ℕ} {S : ℝ}
    (hJ :
      2 * S ^ (3 / 5 : ℝ) ≤
        S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) / 2)
    (hL :
      (Real.log 2 / Real.log 9) *
          (2 * lemma79OutsideEprimeScale Aweight p) + 1 ≤
        S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) / 2) :
    2 * S ^ (3 / 5 : ℝ) +
        ((Real.log 2 / Real.log 9) *
          (2 * lemma79OutsideEprimeScale Aweight p) + 1) ≤
      S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) := by
  linarith

/-- For each fixed sharp offset scale, Tao's exact source row margin holds
eventually in the natural first-passage gap. -/
theorem lemma79OutsideEprimeErrorMargin_eventually
    (Aweight p : ℕ) :
    ∀ᶠ fpGap : ℕ in atTop,
      2 * (fpGap : ℝ) ^ (3 / 5 : ℝ) +
          ((Real.log 2 / Real.log 9) *
            (2 * lemma79OutsideEprimeScale Aweight p) + 1) ≤
        (fpGap : ℝ) *
          (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) := by
  let delta : ℝ :=
    Real.log 2 / Real.log 9 - (1 / 4 : ℝ)
  let fixedError : ℝ :=
    (Real.log 2 / Real.log 9) *
      (2 * lemma79OutsideEprimeScale Aweight p) + 1
  have hdelta : 0 < delta := lemma710_log_margin_pos
  have hrpow :
      Tendsto
        (fun S : ℕ =>
          (S : ℝ) ^ (3 / 5 : ℝ) / (S : ℝ))
        atTop (𝓝 0) := by
    refine
      ((tendsto_rpow_neg_atTop
          (by norm_num : 0 < (2 / 5 : ℝ))).comp
        tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with S hS
    have hSpos : 0 < (S : ℝ) := by
      exact_mod_cast hS
    change
      (S : ℝ) ^ (-(2 / 5 : ℝ)) =
        (S : ℝ) ^ (3 / 5 : ℝ) / (S : ℝ)
    calc
      (S : ℝ) ^ (-(2 / 5 : ℝ)) =
          (S : ℝ) ^ ((3 / 5 : ℝ) - 1) := by norm_num
      _ = (S : ℝ) ^ (3 / 5 : ℝ) / (S : ℝ) ^ (1 : ℝ) :=
        Real.rpow_sub hSpos (3 / 5 : ℝ) 1
      _ = (S : ℝ) ^ (3 / 5 : ℝ) / (S : ℝ) := by
        rw [Real.rpow_one]
  have hnormalized :
      Tendsto
        (fun S : ℕ =>
          2 * ((S : ℝ) ^ (3 / 5 : ℝ) / (S : ℝ)) +
            fixedError / (S : ℝ))
        atTop (𝓝 0) := by
    simpa using
      (hrpow.const_mul 2).add
        (tendsto_const_div_atTop_nhds_zero_nat fixedError)
  filter_upwards
    [hnormalized.eventually_le_const hdelta,
      eventually_gt_atTop (0 : ℕ)]
      with S hbound hS
  have hS0 : (S : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hS)
  have hmul :=
    mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg S)
  dsimp [fixedError, delta] at hmul ⊢
  calc
    2 * (S : ℝ) ^ (3 / 5 : ℝ) +
        ((Real.log 2 / Real.log 9) *
          (2 * lemma79OutsideEprimeScale Aweight p) + 1) =
      (2 * ((S : ℝ) ^ (3 / 5 : ℝ) / (S : ℝ)) +
        ((Real.log 2 / Real.log 9) *
          (2 * lemma79OutsideEprimeScale Aweight p) + 1) /
            (S : ℝ)) * (S : ℝ) := by
        field_simp [hS0]
        <;> ring
    _ ≤ (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) *
        (S : ℝ) := hmul
    _ = (S : ℝ) *
        (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) := by ring

/-- Natural threshold form consumed after the finite offset range has been
fixed and before the boundary sample is selected. -/
theorem exists_lemma79OutsideEprimeErrorMargin_threshold
    (Aweight p : ℕ) :
    ∃ S0 : ℕ, ∀ fpGap : ℕ, S0 ≤ fpGap →
      2 * (fpGap : ℝ) ^ (3 / 5 : ℝ) +
          ((Real.log 2 / Real.log 9) *
            (2 * lemma79OutsideEprimeScale Aweight p) + 1) ≤
        (fpGap : ℝ) *
          (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) := by
  exact eventually_atTop.1
    (lemma79OutsideEprimeErrorMargin_eventually Aweight p)

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
