import Erdos1135.ND.Band.A5SourceMixture
import Erdos1135.ND.Discrepancy.A5ReferenceGenuineBandRate

/-!
# Genuine A5 whole-source passage rate at the common center

This leaf averages the checked factor-seven band estimates through the exact
whole-source mixtures.  The possible inclusive top endpoint costs one further
copy of the reference rate.  The results concern genuine passage events; the
later common-target totalizer is intentionally separate.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped BigOperators Topology

noncomputable section

private theorem abs_top_sub_weight_mul_le_forty_mul
    {t w Z : ℝ}
    (ht0 : 0 ≤ t) (htw : t ≤ w) (hw0 : 0 ≤ w)
    (hZ : Z ∈ Set.Icc (0 : ℝ) 40) :
    |t - w * Z| ≤ 40 * w := by
  rw [abs_le]
  have hwZ0 : 0 ≤ w * Z := mul_nonneg hw0 hZ.1
  have hwZ40 : w * Z ≤ w * 40 :=
    mul_le_mul_of_nonneg_left hZ.2 hw0
  constructor <;> nlinarith

private theorem abs_weighted_sum_add_top_sub_center_le_eight
    {ι : Type*} (S : Finset ι) (w f : ι → ℝ)
    (t p Z R : ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hpoint : ∀ i ∈ S, |f i - Z| ≤ 7 * R)
    (hnorm : (∑ i ∈ S, w i) + p = 1)
    (hp0 : 0 ≤ p) (htop : |t - p * Z| ≤ R) (hR0 : 0 ≤ R) :
    |(∑ i ∈ S, w i * f i) + t - Z| ≤ 8 * R := by
  have hweighted :=
    abs_sum_mul_sub_center_mul_sum_le S w f (fun _ ↦ 7 * R) Z hw hpoint
  have hsum_le_one : (∑ i ∈ S, w i) ≤ 1 := by
    linarith
  have hweighted' :
      |(∑ i ∈ S, w i * f i) - Z * (∑ i ∈ S, w i)| ≤
        7 * R := by
    calc
      |(∑ i ∈ S, w i * f i) - Z * (∑ i ∈ S, w i)| ≤
          ∑ i ∈ S, w i * (7 * R) := hweighted
      _ = (∑ i ∈ S, w i) * (7 * R) := by
        rw [Finset.sum_mul]
      _ ≤ 1 * (7 * R) :=
        mul_le_mul_of_nonneg_right hsum_le_one (mul_nonneg (by norm_num) hR0)
      _ = 7 * R := by ring
  calc
    |(∑ i ∈ S, w i * f i) + t - Z| =
        |((∑ i ∈ S, w i * f i) - Z * (∑ i ∈ S, w i)) +
          (t - p * Z)| := by
      congr 1
      linear_combination Z * hnorm
    _ ≤ |(∑ i ∈ S, w i * f i) - Z * (∑ i ∈ S, w i)| +
        |t - p * Z| := abs_add_le _ _
    _ ≤ 7 * R + R := add_le_add hweighted' htop
    _ = 8 * R := by ring

/-- Every valid whole harmonic and flat A5 source has genuine passage mass
within eight reference-rate copies of the common target. -/
theorem eventually_ndA5GenuineSourcePassDecay_referenceLevel_le_eight
    {c kappa d : ℝ}
    (hPhase : PhaseGap c kappa)
    (hd : 0 < d) (hd20 : d < 1 / 20)
    (hdk : d < 1 / (2 * kappa)) :
    ∀ᶠ B : ℕ in atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch) (E : Set ℕ)
        (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch),
        (|((ndA5HarmonicSourcePMF B branch hB hcount).toOuterMeasure
              (Tao.taoSection5PassEvent B E)).toReal -
            ndA5ReferenceCommonProfile B E| ≤
          8 * ndA5ReferenceInteriorScalarRate B d) ∧
        (|((ndA5FlatSourcePMF B branch hB hcount).toOuterMeasure
              (Tao.taoSection5PassEvent B E)).toReal -
            ndA5ReferenceCommonProfile B E| ≤
          8 * ndA5ReferenceInteriorScalarRate B d) := by
  filter_upwards
      [eventually_ndA5GenuineBandPassDecay_referenceLevel_le_seven
        hPhase hd hd20 hdk,
        eventually_ndA5ReferenceCommonProfile_mem_Icc_forty,
        eventually_one_hundred_sixty_div_natCast_le_ndA5ReferenceInteriorScalarRate d]
      with B hband hprofile htopRate
  intro branch E hB hcount
  let A : Set Tao.TaoOddNat := Tao.taoSection5PassEvent B E
  let Z : ℝ := ndA5ReferenceCommonProfile B E
  let R : ℝ := ndA5ReferenceInteriorScalarRate B d
  have hR0 : 0 ≤ R := by
    dsimp only [R, ndA5ReferenceInteriorScalarRate]
    exact Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast hB)) _
  have hpointH : ∀ j ∈ Finset.range (ndA5BandCount B branch),
      |((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure A).toReal - Z| ≤
        7 * R := by
    intro j hj
    simpa only [A, Z, R] using
      (hband branch j E hB hcount (Finset.mem_range.mp hj)).1
  have hpointF : ∀ j ∈ Finset.range (ndA5BandCount B branch),
      |((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure A).toReal - Z| ≤
        7 * R := by
    intro j hj
    simpa only [A, Z, R] using
      (hband branch j E hB hcount (Finset.mem_range.mp hj)).2
  have htopH40 :
      |ndA5HarmonicTopRestrictedMass B branch A -
          ndA5HarmonicTopWeight B branch * Z| ≤
        40 * ndA5HarmonicTopWeight B branch :=
    abs_top_sub_weight_mul_le_forty_mul
      (ndA5HarmonicTopRestrictedMass_nonneg hB hcount A)
      (ndA5HarmonicTopRestrictedMass_le_weight hB hcount A)
      (ndA5HarmonicTopWeight_nonneg B branch) (hprofile E)
  have htopH :
      |ndA5HarmonicTopRestrictedMass B branch A -
          ndA5HarmonicTopWeight B branch * Z| ≤ R := by
    calc
      _ ≤ 40 * ndA5HarmonicTopWeight B branch := htopH40
      _ ≤ 40 * (4 / (B : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (ndA5HarmonicTopWeight_le_four_div hB branch hcount) (by norm_num)
      _ = 160 / (B : ℝ) := by ring
      _ = 160 * Real.rpow (B : ℝ) (-1) := by
        simpa only [div_eq_mul_inv] using
          congrArg (fun x : ℝ ↦ 160 * x)
            (Real.rpow_neg_one (B : ℝ)).symm
      _ ≤ R := by simpa only [R] using htopRate
  have htopF40 :
      |ndA5FlatTopRestrictedMass B branch A -
          ndA5FlatTopWeight B branch * Z| ≤
        40 * ndA5FlatTopWeight B branch :=
    abs_top_sub_weight_mul_le_forty_mul
      (ndA5FlatTopRestrictedMass_nonneg hB hcount A)
      (ndA5FlatTopRestrictedMass_le_weight hB hcount A)
      (ndA5FlatTopWeight_nonneg B branch) (hprofile E)
  have htopF :
      |ndA5FlatTopRestrictedMass B branch A -
          ndA5FlatTopWeight B branch * Z| ≤ R := by
    calc
      _ ≤ 40 * ndA5FlatTopWeight B branch := htopF40
      _ ≤ 40 * (4 / (B : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (ndA5FlatTopWeight_le_four_div hB branch hcount) (by norm_num)
      _ = 160 / (B : ℝ) := by ring
      _ = 160 * Real.rpow (B : ℝ) (-1) := by
        simpa only [div_eq_mul_inv] using
          congrArg (fun x : ℝ ↦ 160 * x)
            (Real.rpow_neg_one (B : ℝ)).symm
      _ ≤ R := by simpa only [R] using htopRate
  constructor
  · rw [ndA5HarmonicSourcePMF_eventMass_eq_band_mixture_add_top hB hcount A]
    exact abs_weighted_sum_add_top_sub_center_le_eight
      (Finset.range (ndA5BandCount B branch))
      (ndA5HarmonicBandWeight B branch)
      (fun j ↦
        ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure A).toReal)
      (ndA5HarmonicTopRestrictedMass B branch A)
      (ndA5HarmonicTopWeight B branch) Z R
      (fun j _ ↦ ndA5HarmonicBandWeight_nonneg B branch j) hpointH
      (sum_ndA5HarmonicBandWeight_add_topWeight_eq_one hB branch hcount)
      (ndA5HarmonicTopWeight_nonneg B branch) htopH hR0
  · rw [ndA5FlatSourcePMF_eventMass_eq_band_mixture_add_top hB hcount A]
    exact abs_weighted_sum_add_top_sub_center_le_eight
      (Finset.range (ndA5BandCount B branch))
      (ndA5FlatBandWeight B branch)
      (fun j ↦
        ((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure A).toReal)
      (ndA5FlatTopRestrictedMass B branch A)
      (ndA5FlatTopWeight B branch) Z R
      (fun j _ ↦ ndA5FlatBandWeight_nonneg B branch j) hpointF
      (sum_ndA5FlatBandWeight_add_topWeight_eq_one hB branch hcount)
      (ndA5FlatTopWeight_nonneg B branch) htopF hR0

/-- On one source branch, the genuine harmonic and flat passage masses differ
by at most sixteen reference-rate copies. -/
theorem eventually_abs_ndA5HarmonicSourcePassMass_sub_flat_le_sixteen
    {c kappa d : ℝ}
    (hPhase : PhaseGap c kappa)
    (hd : 0 < d) (hd20 : d < 1 / 20)
    (hdk : d < 1 / (2 * kappa)) :
    ∀ᶠ B : ℕ in atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch) (E : Set ℕ)
        (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch),
        |((ndA5HarmonicSourcePMF B branch hB hcount).toOuterMeasure
              (Tao.taoSection5PassEvent B E)).toReal -
          ((ndA5FlatSourcePMF B branch hB hcount).toOuterMeasure
              (Tao.taoSection5PassEvent B E)).toReal| ≤
            16 * ndA5ReferenceInteriorScalarRate B d := by
  filter_upwards
      [eventually_ndA5GenuineSourcePassDecay_referenceLevel_le_eight
        hPhase hd hd20 hdk]
      with B hsource
  intro branch E hB hcount
  have hpair := hsource branch E hB hcount
  calc
    |((ndA5HarmonicSourcePMF B branch hB hcount).toOuterMeasure
          (Tao.taoSection5PassEvent B E)).toReal -
        ((ndA5FlatSourcePMF B branch hB hcount).toOuterMeasure
          (Tao.taoSection5PassEvent B E)).toReal| =
      |(((ndA5HarmonicSourcePMF B branch hB hcount).toOuterMeasure
            (Tao.taoSection5PassEvent B E)).toReal -
          ndA5ReferenceCommonProfile B E) -
        (((ndA5FlatSourcePMF B branch hB hcount).toOuterMeasure
            (Tao.taoSection5PassEvent B E)).toReal -
          ndA5ReferenceCommonProfile B E)| := by ring
    _ ≤ |((ndA5HarmonicSourcePMF B branch hB hcount).toOuterMeasure
            (Tao.taoSection5PassEvent B E)).toReal -
          ndA5ReferenceCommonProfile B E| +
        |((ndA5FlatSourcePMF B branch hB hcount).toOuterMeasure
            (Tao.taoSection5PassEvent B E)).toReal -
          ndA5ReferenceCommonProfile B E| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le
          (((ndA5HarmonicSourcePMF B branch hB hcount).toOuterMeasure
            (Tao.taoSection5PassEvent B E)).toReal -
              ndA5ReferenceCommonProfile B E)
          (-(((ndA5FlatSourcePMF B branch hB hcount).toOuterMeasure
            (Tao.taoSection5PassEvent B E)).toReal -
              ndA5ReferenceCommonProfile B E)))
    _ ≤ 8 * ndA5ReferenceInteriorScalarRate B d +
        8 * ndA5ReferenceInteriorScalarRate B d := add_le_add hpair.1 hpair.2
    _ = 16 * ndA5ReferenceInteriorScalarRate B d := by ring

/-- Across two source branches, the genuine harmonic passage masses differ by
at most sixteen reference-rate copies. -/
theorem eventually_abs_ndA5HarmonicSourcePassMass_sub_harmonic_le_sixteen
    {c kappa d : ℝ}
    (hPhase : PhaseGap c kappa)
    (hd : 0 < d) (hd20 : d < 1 / 20)
    (hdk : d < 1 / (2 * kappa)) :
    ∀ᶠ B : ℕ in atTop,
      ∀ (branch₁ branch₂ : Tao.TaoSection5SourceBranch) (E : Set ℕ)
        (hB : 1 ≤ B)
        (hcount₁ : 0 < ndA5BandCount B branch₁)
        (hcount₂ : 0 < ndA5BandCount B branch₂),
        |((ndA5HarmonicSourcePMF B branch₁ hB hcount₁).toOuterMeasure
              (Tao.taoSection5PassEvent B E)).toReal -
          ((ndA5HarmonicSourcePMF B branch₂ hB hcount₂).toOuterMeasure
              (Tao.taoSection5PassEvent B E)).toReal| ≤
            16 * ndA5ReferenceInteriorScalarRate B d := by
  filter_upwards
      [eventually_ndA5GenuineSourcePassDecay_referenceLevel_le_eight
        hPhase hd hd20 hdk]
      with B hsource
  intro branch₁ branch₂ E hB hcount₁ hcount₂
  have h₁ := (hsource branch₁ E hB hcount₁).1
  have h₂ := (hsource branch₂ E hB hcount₂).1
  calc
    |((ndA5HarmonicSourcePMF B branch₁ hB hcount₁).toOuterMeasure
          (Tao.taoSection5PassEvent B E)).toReal -
        ((ndA5HarmonicSourcePMF B branch₂ hB hcount₂).toOuterMeasure
          (Tao.taoSection5PassEvent B E)).toReal| =
      |(((ndA5HarmonicSourcePMF B branch₁ hB hcount₁).toOuterMeasure
            (Tao.taoSection5PassEvent B E)).toReal -
          ndA5ReferenceCommonProfile B E) -
        (((ndA5HarmonicSourcePMF B branch₂ hB hcount₂).toOuterMeasure
            (Tao.taoSection5PassEvent B E)).toReal -
          ndA5ReferenceCommonProfile B E)| := by ring
    _ ≤ |((ndA5HarmonicSourcePMF B branch₁ hB hcount₁).toOuterMeasure
            (Tao.taoSection5PassEvent B E)).toReal -
          ndA5ReferenceCommonProfile B E| +
        |((ndA5HarmonicSourcePMF B branch₂ hB hcount₂).toOuterMeasure
            (Tao.taoSection5PassEvent B E)).toReal -
          ndA5ReferenceCommonProfile B E| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le
          (((ndA5HarmonicSourcePMF B branch₁ hB hcount₁).toOuterMeasure
            (Tao.taoSection5PassEvent B E)).toReal -
              ndA5ReferenceCommonProfile B E)
          (-(((ndA5HarmonicSourcePMF B branch₂ hB hcount₂).toOuterMeasure
            (Tao.taoSection5PassEvent B E)).toReal -
              ndA5ReferenceCommonProfile B E)))
    _ ≤ 8 * ndA5ReferenceInteriorScalarRate B d +
        8 * ndA5ReferenceInteriorScalarRate B d := add_le_add h₁ h₂
    _ = 16 * ndA5ReferenceInteriorScalarRate B d := by ring

end
end ND
end Erdos1135
