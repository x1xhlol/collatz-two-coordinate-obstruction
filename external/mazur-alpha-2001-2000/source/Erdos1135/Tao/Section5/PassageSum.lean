import Erdos1135.Tao.Section5.AffineIdealSumRegroup
import Erdos1135.Tao.Section5.FixedTimeMixing
import Erdos1135.Tao.Section5.PassScheduleFacts

/-!
# Section 5 Denominator-Preserving Passage Sum

This leaf sums a uniform fixed-time comparison without replacing the source
normalizer.  The only multiplicity factor is the passage-time cardinality
divided by that exact normalizer.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

/-- A finite family uniformly within `e` of `Z` remains within
`card / D * e` after averaging by the exact positive denominator `D`. -/
theorem taoSection5_abs_inv_mul_fintype_sum_sub_card_div_mul_le
    {alpha : Type*} [Fintype alpha] (T : alpha → ℝ) {D Z e : ℝ}
    (hD : 0 < D) (hT : ∀ i, |T i - Z| ≤ e) :
    |(1 / D) * ∑ i, T i - ((Fintype.card alpha : ℕ) : ℝ) / D * Z| ≤
      (((Fintype.card alpha : ℕ) : ℝ) / D) * e := by
  classical
  have hDinv : 0 ≤ (1 / D : ℝ) := by positivity
  have hsumSub :
      (∑ i, (T i - Z)) =
        (∑ i, T i) - ((Fintype.card alpha : ℕ) : ℝ) * Z := by
    rw [Finset.sum_sub_distrib]
    simp
  have hrearrange :
      (1 / D) * ∑ i, T i -
          ((Fintype.card alpha : ℕ) : ℝ) / D * Z =
        (1 / D) * ∑ i, (T i - Z) := by
    rw [hsumSub, div_eq_mul_inv]
    ring
  rw [hrearrange, abs_mul, abs_of_nonneg hDinv]
  calc
    (1 / D) * |∑ i, (T i - Z)| ≤
        (1 / D) * ∑ i, |T i - Z| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hDinv
    _ ≤ (1 / D) * ∑ _i : alpha, e := by
      apply mul_le_mul_of_nonneg_left _ hDinv
      exact Finset.sum_le_sum fun i _hi => hT i
    _ = (((Fintype.card alpha : ℕ) : ℝ) / D) * e := by
      rw [div_eq_mul_inv]
      simp
      ring

/-- The actual scheduled fixed-time terms sum with the exact logarithmic
source mass still in place.  No endpoint, atom, or raw time count appears
outside `card(passTimes) / sourceMass`. -/
theorem abs_taoSection5_normalizedTypicalPassageSum_sub_commonZ_le_of_mixing
    {A B : ℕ} {Cmix : ℝ} (branch : TaoSection5SourceBranch)
    (E : Set ℕ)
    (hmass :
      0 < logFinsetMass
        (oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch)))
    (schedule : TaoSection5PassScheduleFacts B)
    (lost : TaoSection5PassLostWindowFacts B)
    (failure : TaoSection5PassTypicalFailureFacts B)
    (hmix : syracFineScaleMixingAt A Cmix) :
    let D := logFinsetMass
      (oddLogWindow
        (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch))
    let I := {n // n ∈ taoSection5PassTimes B branch}
    |(1 / D) * ∑ n : I,
        taoSection5TypicalAffineCoefficientSum
          B (n.1 - taoSection5M0 B) E -
      ((Fintype.card I : ℕ) : ℝ) / D *
        taoSection5PayloadFreeCommonZ (taoSection5M0 B)
          (taoSection5EPrime B E)| ≤
      (((Fintype.card I : ℕ) : ℝ) / D) *
        (5 * taoSection5PowerInteriorDelta B +
          5 * (Cmix / (taoSection5M0 B : ℝ) ^ A)) := by
  dsimp only
  refine taoSection5_abs_inv_mul_fintype_sum_sub_card_div_mul_le
    (alpha := {n // n ∈ taoSection5PassTimes B branch})
    (T := fun n => taoSection5TypicalAffineCoefficientSum
      B (n.1 - taoSection5M0 B) E)
    (D := logFinsetMass
      (oddLogWindow
        (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch)))
    (Z := taoSection5PayloadFreeCommonZ (taoSection5M0 B)
      (taoSection5EPrime B E))
    (e := 5 * taoSection5PowerInteriorDelta B +
      5 * (Cmix / (taoSection5M0 B : ℝ) ^ A)) hmass ?_
  intro n
  have hnRange := schedule.range branch n.1 n.2
  have hindex :
      taoSection5M0 B + (n.1 - taoSection5M0 B) ≤
        taoSection5N0 B := by
    have hm0n := schedule.m0_le n.2
    omega
  exact abs_taoSection5TypicalAffineCoefficientSum_sub_commonZ_le_of_mixing
    lost failure hindex schedule.one_le_m0 (schedule.m0_le_sub n.2) hmix

/-- Route-facing form: the complete denominator-simplified affine atom sum is
within the exact normalized passage error of the branch-independent Common-Z
term. -/
theorem abs_taoSection5_idealAffineAtomSum_sub_commonZ_le_of_mixing
    {A B : ℕ} {Cmix : ℝ} (branch : TaoSection5SourceBranch)
    (E : Set ℕ)
    (hmass :
      0 < logFinsetMass
        (oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch)))
    (schedule : TaoSection5PassScheduleFacts B)
    (lost : TaoSection5PassLostWindowFacts B)
    (failure : TaoSection5PassTypicalFailureFacts B)
    (hmix : syracFineScaleMixingAt A Cmix) :
    let D := logFinsetMass
      (oddLogWindow
        (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch))
    let I := {n // n ∈ taoSection5PassTimes B branch}
    |(∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
          taoSection5IdealAffineAtomMass hmass i) -
      ((Fintype.card I : ℕ) : ℝ) / D *
        taoSection5PayloadFreeCommonZ (taoSection5M0 B)
          (taoSection5EPrime B E)| ≤
      (((Fintype.card I : ℕ) : ℝ) / D) *
        (5 * taoSection5PowerInteriorDelta B +
          5 * (Cmix / (taoSection5M0 B : ℝ) ^ A)) := by
  dsimp only
  rw [taoSection5_sum_idealAffineAtomMass_eq_regrouped branch E hmass]
  simpa only [taoSection5TypicalAffineCoefficientSum] using
    (abs_taoSection5_normalizedTypicalPassageSum_sub_commonZ_le_of_mixing
      branch E hmass schedule lost failure hmix)

end

end Tao
end Erdos1135
