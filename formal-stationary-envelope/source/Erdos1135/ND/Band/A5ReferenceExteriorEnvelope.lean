import Erdos1135.ND.Band.A5ReferencePhysicalSplit
import Erdos1135.ND.Band.A5BandNormalizerRatios
import Erdos1135.ND.Band.A5PhysicalWindowCard
import Erdos1135.ND.Fourier.FiberEndpointCeiling

/-!
# A5 global reference-profile envelope

This leaf proves the all-endpoint bounded-profile input needed before the
original-endpoint exterior harmonic tail is summed.  It does not replace the
exterior carrier by an intrinsic tube: every raw atom remains restricted by
its own strict support indicator and is summed only over the physical window.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

noncomputable section

/-- Common all-endpoint envelope for the two normalized physical profiles. -/
def ndA5ReferenceExteriorProfileEnvelope (B : ℕ) (C : ℝ) : ℝ :=
  672 * ndA5TubeWidth B C /
    Real.sqrt (Tao.taoSection5N0 B : ℝ)

/-- A raw atom on the physical carrier obeys the source-scale inverse-root
ceiling for every affine phase, including exterior phases. -/
theorem ndA5RawQ_le_four_div_sqrt_taoSection5N0_of_physical
    {B j nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {C A : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hj : j < ndA5BandCount B branch)
    (hnu : nu ∈ ndA5PhysicalNuWindow B branch C j) :
    ndA5RawQ A (ndA5TubeWidth B C) nu ≤
      4 / Real.sqrt (Tao.taoSection5N0 B : ℝ) := by
  by_cases hTube : nu ∈ ndA5FullTube A (ndA5TubeWidth B C)
  · have hphysical := mem_ndA5PhysicalNuWindow_iff.mp hnu
    have ht2 := ndA5PaddedBandWindow_t2_of_guards
      hB hlogB hpadding hj hphysical.2
    have hsub :
        nu + Tao.taoSection5M0 B - Tao.taoSection5M0 B = nu := by
      omega
    have hWle := ht2.width_le_nu_div_eight
    have hratioUpper := ht2.n0_div_nu_upper
    have hratioLower := ht2.n0_div_nu_lower
    rw [hsub] at hWle hratioUpper hratioLower
    have hlevel := ndA5PhysicalLevelFacts_of_mem_fullTube
      hphysical.1 hWle hTube
    have hraw :
        ndA5RawQ A (ndA5TubeWidth B C) nu ≤
          1 / (2 * Real.sqrt (nu : ℝ)) := by
      rw [ndA5RawQ_of_mem hTube]
      exact ndGeom2EndpointMass_le_one_div_two_mul_sqrt
        hphysical.1 hlevel.nu_le_nat
    let N : ℝ := Tao.taoSection5N0 B
    have hnuReal : (0 : ℝ) < nu := by exact_mod_cast hphysical.1
    have hNle : N ≤ 49 * (nu : ℝ) := by
      apply (div_le_iff₀ hnuReal).mp
      calc
        N / (nu : ℝ) ≤ (4244 / 100 : ℝ) := by
          simpa only [N] using hratioUpper
        _ ≤ 49 := by norm_num
    have hNlower : (1374 / 100 : ℝ) * (nu : ℝ) ≤ N := by
      apply (le_div_iff₀ hnuReal).mp
      simpa only [N] using hratioLower
    have hNpos : 0 < N := by nlinarith
    have hsqrtLe : Real.sqrt N ≤ 7 * Real.sqrt (nu : ℝ) := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [Real.sq_sqrt hnuReal.le]
    have hfrac :
        1 / (2 * Real.sqrt (nu : ℝ)) ≤ 4 / Real.sqrt N := by
      apply (div_le_div_iff₀
        (by positivity : (0 : ℝ) < 2 * Real.sqrt (nu : ℝ))
        (Real.sqrt_pos.2 hNpos)).2
      nlinarith [Real.sqrt_nonneg (nu : ℝ)]
    exact hraw.trans (by simpa only [N] using hfrac)
  · rw [ndA5RawQ_of_not_mem hTube]
    positivity

theorem ndA5NominalStrictBandRawQTerm_nonneg
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (A W : ℝ) (nu r : ℕ) :
    0 ≤ ndA5NominalStrictBandRawQTerm B branch A W nu r := by
  unfold ndA5NominalStrictBandRawQTerm
  split_ifs
  · exact ndA5RawQ_nonneg _ _ _
  · exact le_rfl

theorem ndA5NominalStrictBandFlatRawQTerm_nonneg
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (A W : ℝ) (nu r : ℕ) :
    0 ≤ ndA5NominalStrictBandFlatRawQTerm B branch A W nu r := by
  unfold ndA5NominalStrictBandFlatRawQTerm
  exact mul_nonneg
    (ndA5NominalStrictBandRawQTerm_nonneg B branch A W nu r)
    (Real.exp_nonneg _)

theorem ndA5NominalStrictBandRawQTerm_le_four_div_sqrt
    {B j nu r : ℕ} {branch : Tao.TaoSection5SourceBranch} {C A : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hj : j < ndA5BandCount B branch)
    (hnu : nu ∈ ndA5PhysicalNuWindow B branch C j) :
    ndA5NominalStrictBandRawQTerm B branch A
        (ndA5TubeWidth B C) nu r ≤
      4 / Real.sqrt (Tao.taoSection5N0 B : ℝ) := by
  unfold ndA5NominalStrictBandRawQTerm
  split_ifs
  · exact ndA5RawQ_le_four_div_sqrt_taoSection5N0_of_physical
      hB hlogB hpadding hj hnu
  · exact div_nonneg (by norm_num) (Real.sqrt_nonneg _)

theorem ndA5NominalStrictBandFlatRawQTerm_le_sixteen_div_sqrt
    {B j nu r : ℕ} {branch : Tao.TaoSection5SourceBranch} {C A : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hj : j < ndA5BandCount B branch)
    (hnu : nu ∈ ndA5PhysicalNuWindow B branch C j)
    (hr : r ∈ Finset.range 2) :
    ndA5NominalStrictBandFlatRawQTerm B branch A
        (ndA5TubeWidth B C) nu r ≤
      16 / Real.sqrt (Tao.taoSection5N0 B : ℝ) := by
  let t := Int.fract (A + (nu : ℝ) * logTwoThree)
  have hrTwo : r < 2 := Finset.mem_range.mp hr
  have hrReal : ((r + 1 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (by omega : r + 1 ≤ 2)
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have harg :
      ((((r + 1 : ℕ) : ℝ) - t) * Real.log 2) ≤
        2 * Real.log 2 := by
    have ht0 : 0 ≤ t := by
      dsimp only [t]
      exact Int.fract_nonneg _
    nlinarith
  have hexp :
      Real.exp (((((r + 1 : ℕ) : ℝ) - t) * Real.log 2)) ≤ 4 := by
    calc
      Real.exp (((((r + 1 : ℕ) : ℝ) - t) * Real.log 2)) ≤
          Real.exp (2 * Real.log 2) := Real.exp_le_exp.mpr harg
      _ = 4 := by
        rw [two_mul, Real.exp_add, Real.exp_log (by norm_num)]
        norm_num
  have hraw := ndA5NominalStrictBandRawQTerm_le_four_div_sqrt
    (A := A) (r := r) hB hlogB hpadding hj hnu
  have hraw0 := ndA5NominalStrictBandRawQTerm_nonneg
    B branch A (ndA5TubeWidth B C) nu r
  have hroot0 :
      0 ≤ 4 / Real.sqrt (Tao.taoSection5N0 B : ℝ) := by
    exact div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  unfold ndA5NominalStrictBandFlatRawQTerm
  change
    ndA5NominalStrictBandRawQTerm B branch A
        (ndA5TubeWidth B C) nu r *
        Real.exp (((((r + 1 : ℕ) : ℝ) - t) * Real.log 2)) ≤ _
  calc
    _ ≤ (4 / Real.sqrt (Tao.taoSection5N0 B : ℝ)) * 4 :=
      mul_le_mul hraw hexp (Real.exp_nonneg _) hroot0
    _ = 16 / Real.sqrt (Tao.taoSection5N0 B : ℝ) := by ring

theorem sum_ndA5NominalStrictBandRawQTerm_le_eight_div_sqrt
    {B j nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {C A : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hj : j < ndA5BandCount B branch)
    (hnu : nu ∈ ndA5PhysicalNuWindow B branch C j) :
    (∑ r ∈ Finset.range 2,
      ndA5NominalStrictBandRawQTerm B branch A
        (ndA5TubeWidth B C) nu r) ≤
      8 / Real.sqrt (Tao.taoSection5N0 B : ℝ) := by
  calc
    _ ≤ ∑ _r ∈ Finset.range 2,
        4 / Real.sqrt (Tao.taoSection5N0 B : ℝ) := by
      apply Finset.sum_le_sum
      intro r _hr
      exact ndA5NominalStrictBandRawQTerm_le_four_div_sqrt
        hB hlogB hpadding hj hnu
    _ = 8 / Real.sqrt (Tao.taoSection5N0 B : ℝ) := by
      norm_num
      ring

theorem sum_ndA5NominalStrictBandFlatRawQTerm_le_thirty_two_div_sqrt
    {B j nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {C A : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hj : j < ndA5BandCount B branch)
    (hnu : nu ∈ ndA5PhysicalNuWindow B branch C j) :
    (∑ r ∈ Finset.range 2,
      ndA5NominalStrictBandFlatRawQTerm B branch A
        (ndA5TubeWidth B C) nu r) ≤
      32 / Real.sqrt (Tao.taoSection5N0 B : ℝ) := by
  calc
    _ ≤ ∑ _r ∈ Finset.range 2,
        16 / Real.sqrt (Tao.taoSection5N0 B : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      exact ndA5NominalStrictBandFlatRawQTerm_le_sixteen_div_sqrt
        hB hlogB hpadding hj hnu hr
    _ = 32 / Real.sqrt (Tao.taoSection5N0 B : ℝ) := by
      norm_num
      ring

theorem sum_physical_ndA5NominalStrictBandRawQTerm_le
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C A : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hC : (1 / 2 : ℝ) ≤ C)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hj : j < ndA5BandCount B branch) :
    (∑ nu ∈ ndA5PhysicalNuWindow B branch C j,
      ∑ r ∈ Finset.range 2,
        ndA5NominalStrictBandRawQTerm B branch A
          (ndA5TubeWidth B C) nu r) ≤
      56 * ndA5TubeWidth B C /
        Real.sqrt (Tao.taoSection5N0 B : ℝ) := by
  have hcard := ndA5PhysicalNuWindow_card_le_seven_mul_width
    hB hlogB hC hpadding hj
  have hroot0 :
      0 ≤ 8 / Real.sqrt (Tao.taoSection5N0 B : ℝ) := by positivity
  calc
    _ ≤ ∑ _nu ∈ ndA5PhysicalNuWindow B branch C j,
        8 / Real.sqrt (Tao.taoSection5N0 B : ℝ) := by
      apply Finset.sum_le_sum
      intro nu hnu
      exact sum_ndA5NominalStrictBandRawQTerm_le_eight_div_sqrt
        hB hlogB hpadding hj hnu
    _ = ((ndA5PhysicalNuWindow B branch C j).card : ℝ) *
        (8 / Real.sqrt (Tao.taoSection5N0 B : ℝ)) := by simp
    _ ≤ (7 * ndA5TubeWidth B C) *
        (8 / Real.sqrt (Tao.taoSection5N0 B : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard hroot0
    _ = 56 * ndA5TubeWidth B C /
        Real.sqrt (Tao.taoSection5N0 B : ℝ) := by ring

theorem sum_physical_ndA5NominalStrictBandFlatRawQTerm_le
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C A : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hC : (1 / 2 : ℝ) ≤ C)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hj : j < ndA5BandCount B branch) :
    (∑ nu ∈ ndA5PhysicalNuWindow B branch C j,
      ∑ r ∈ Finset.range 2,
        ndA5NominalStrictBandFlatRawQTerm B branch A
          (ndA5TubeWidth B C) nu r) ≤
      224 * ndA5TubeWidth B C /
        Real.sqrt (Tao.taoSection5N0 B : ℝ) := by
  have hcard := ndA5PhysicalNuWindow_card_le_seven_mul_width
    hB hlogB hC hpadding hj
  have hroot0 :
      0 ≤ 32 / Real.sqrt (Tao.taoSection5N0 B : ℝ) := by positivity
  calc
    _ ≤ ∑ _nu ∈ ndA5PhysicalNuWindow B branch C j,
        32 / Real.sqrt (Tao.taoSection5N0 B : ℝ) := by
      apply Finset.sum_le_sum
      intro nu hnu
      exact sum_ndA5NominalStrictBandFlatRawQTerm_le_thirty_two_div_sqrt
        hB hlogB hpadding hj hnu
    _ = ((ndA5PhysicalNuWindow B branch C j).card : ℝ) *
        (32 / Real.sqrt (Tao.taoSection5N0 B : ℝ)) := by simp
    _ ≤ (7 * ndA5TubeWidth B C) *
        (32 / Real.sqrt (Tao.taoSection5N0 B : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard hroot0
    _ = 224 * ndA5TubeWidth B C /
        Real.sqrt (Tao.taoSection5N0 B : ℝ) := by ring

/-- The harmonic physical factor attached to any natural endpoint is
nonnegative and bounded by the common all-endpoint envelope. -/
theorem ndA5HarmonicReferencePhysicalPoint_mem_Icc_envelope
    {B j M : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hC : (1 / 2 : ℝ) ≤ C)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hj : j < ndA5BandCount B branch) :
    let z := ndA5BandLower B branch j
    let W := ndA5TubeWidth B C
    let H := Tao.logFinsetMass (ndA5OddBand B branch j)
    ((∑ nu ∈ ndA5PhysicalNuWindow B branch C j,
        ∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandRawQTerm B branch
            (ndA5PhysicalPhase z M) W nu r) / H) ∈
      Set.Icc (0 : ℝ) (ndA5ReferenceExteriorProfileEnvelope B C) := by
  dsimp only
  have hcount : 0 < ndA5BandCount B branch := Nat.zero_lt_of_lt hj
  have hHpos := logFinsetMass_ndA5OddBand_pos hB j hcount
  have hinvH := one_div_logFinsetMass_ndA5OddBand_le_four
    hB j hcount
  have hinvH' :
      (Tao.logFinsetMass (ndA5OddBand B branch j))⁻¹ ≤ 4 := by
    simpa only [one_div] using hinvH
  have hsum := sum_physical_ndA5NominalStrictBandRawQTerm_le
    (A := ndA5PhysicalPhase (ndA5BandLower B branch j) M)
    hB hlogB hC hpadding hj
  have hsum0 :
      0 ≤ ∑ nu ∈ ndA5PhysicalNuWindow B branch C j,
        ∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandRawQTerm B branch
            (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
              (ndA5TubeWidth B C) nu r := by
    exact Finset.sum_nonneg fun nu _ => Finset.sum_nonneg fun r _ =>
      ndA5NominalStrictBandRawQTerm_nonneg _ _ _ _ _ _
  have hsumMajor0 :
      0 ≤ 56 * ndA5TubeWidth B C /
        Real.sqrt (Tao.taoSection5N0 B : ℝ) := hsum0.trans hsum
  constructor
  · exact div_nonneg hsum0 hHpos.le
  · rw [div_eq_mul_inv]
    calc
      _ ≤ (56 * ndA5TubeWidth B C /
          Real.sqrt (Tao.taoSection5N0 B : ℝ)) * 4 :=
        mul_le_mul hsum hinvH' (inv_nonneg.mpr hHpos.le) hsumMajor0
      _ = 224 * ndA5TubeWidth B C /
          Real.sqrt (Tao.taoSection5N0 B : ℝ) := by ring
      _ ≤ ndA5ReferenceExteriorProfileEnvelope B C := by
        unfold ndA5ReferenceExteriorProfileEnvelope
        have hroot0 :
            0 ≤ ndA5TubeWidth B C /
              Real.sqrt (Tao.taoSection5N0 B : ℝ) := by
          have hW0 : 0 ≤ ndA5TubeWidth B C := by
            unfold ndA5TubeWidth
            positivity
          exact div_nonneg hW0 (Real.sqrt_nonneg _)
        calc
          224 * ndA5TubeWidth B C /
              Real.sqrt (Tao.taoSection5N0 B : ℝ) =
              224 * (ndA5TubeWidth B C /
                Real.sqrt (Tao.taoSection5N0 B : ℝ)) := by ring
          _ ≤ 672 * (ndA5TubeWidth B C /
                Real.sqrt (Tao.taoSection5N0 B : ℝ)) := by
              nlinarith
          _ = 672 * ndA5TubeWidth B C /
              Real.sqrt (Tao.taoSection5N0 B : ℝ) := by ring

/-- The flat physical factor attached to any natural endpoint is nonnegative
and bounded by the same all-endpoint envelope. -/
theorem ndA5FlatReferencePhysicalPoint_mem_Icc_envelope
    {B j M : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hC : (1 / 2 : ℝ) ≤ C)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hj : j < ndA5BandCount B branch) :
    let z := ndA5BandLower B branch j
    let W := ndA5TubeWidth B C
    let card := ((ndA5OddBand B branch j).card : ℝ)
    ((z / card) *
      ∑ nu ∈ ndA5PhysicalNuWindow B branch C j,
        ∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandFlatRawQTerm B branch
            (ndA5PhysicalPhase z M) W nu r) ∈
      Set.Icc (0 : ℝ) (ndA5ReferenceExteriorProfileEnvelope B C) := by
  dsimp only
  have hcount : 0 < ndA5BandCount B branch := Nat.zero_lt_of_lt hj
  have hz : 0 < ndA5BandLower B branch j := by
    linarith [six_le_ndA5BandLower hB j hcount]
  have hcardNat := ndA5OddBand_card_pos hB j hcount
  have hcard : (0 : ℝ) < ((ndA5OddBand B branch j).card : ℝ) := by
    exact_mod_cast hcardNat
  have hratio :=
    (ndA5BandLower_div_card_lt_three hB j hcount).le
  have hsum := sum_physical_ndA5NominalStrictBandFlatRawQTerm_le
    (A := ndA5PhysicalPhase (ndA5BandLower B branch j) M)
    hB hlogB hC hpadding hj
  have hsum0 :
      0 ≤ ∑ nu ∈ ndA5PhysicalNuWindow B branch C j,
        ∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandFlatRawQTerm B branch
            (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
              (ndA5TubeWidth B C) nu r := by
    exact Finset.sum_nonneg fun nu _ => Finset.sum_nonneg fun r _ =>
      ndA5NominalStrictBandFlatRawQTerm_nonneg _ _ _ _ _ _
  constructor
  · exact mul_nonneg (div_nonneg hz.le hcard.le) hsum0
  · calc
      _ ≤ 3 * (224 * ndA5TubeWidth B C /
          Real.sqrt (Tao.taoSection5N0 B : ℝ)) :=
        mul_le_mul hratio hsum hsum0
          (by positivity)
      _ = ndA5ReferenceExteriorProfileEnvelope B C := by
        unfold ndA5ReferenceExteriorProfileEnvelope
        ring

private theorem ndA5ReferencePhysicalProfileOn_le_envelope_mul_commonZ
    {B : ℕ} {C : ℝ}
    {S : Finset ℕ} {P : ℕ → ℝ}
    (hpoint : ∀ M ∈ S,
      P M ≤ ndA5ReferenceExteriorProfileEnvelope B C) :
    ndA5ReferencePhysicalProfileOn (ndA5ReferenceLevel B) S P ≤
      ndA5ReferenceExteriorProfileEnvelope B C *
        Tao.taoSection5PayloadFreeCommonZ (ndA5ReferenceLevel B) S := by
  unfold ndA5ReferencePhysicalProfileOn
  calc
    _ ≤ ∑ M ∈ S, ndA5ReferenceEndpointKernel (ndA5ReferenceLevel B) M *
        ndA5ReferenceExteriorProfileEnvelope B C := by
      apply Finset.sum_le_sum
      intro M hM
      exact mul_le_mul_of_nonneg_left (hpoint M hM)
        (ndA5ReferenceEndpointKernel_nonneg _ _)
    _ = ndA5ReferenceExteriorProfileEnvelope B C *
        (∑ M ∈ S, ndA5ReferenceEndpointKernel (ndA5ReferenceLevel B) M) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _hM
      ring
    _ = ndA5ReferenceExteriorProfileEnvelope B C *
        Tao.taoSection5PayloadFreeCommonZ (ndA5ReferenceLevel B) S := by
      rw [sum_ndA5ReferenceEndpointKernel_eq_commonZ]

/-- The original-endpoint exterior harmonic profile is at most the global
profile envelope times the exterior CommonZ mass. -/
theorem ndA5HarmonicReferenceExteriorPhysicalProfile_le_envelope_mul_commonZ
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    {E : Set ℕ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hC : (1 / 2 : ℝ) ≤ C)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hj : j < ndA5BandCount B branch) :
    ndA5HarmonicReferenceExteriorPhysicalProfile B
        (ndA5ReferenceLevel B) branch C j E ≤
      ndA5ReferenceExteriorProfileEnvelope B C *
        Tao.taoSection5PayloadFreeCommonZ (ndA5ReferenceLevel B)
          (ndA5ReferenceExteriorEndpoints B C E) := by
  unfold ndA5HarmonicReferenceExteriorPhysicalProfile
    ndA5HarmonicReferencePhysicalProfileOn
  apply ndA5ReferencePhysicalProfileOn_le_envelope_mul_commonZ
  intro M _hM
  exact (ndA5HarmonicReferencePhysicalPoint_mem_Icc_envelope
    (M := M) hB hlogB hC hpadding hj).2

/-- The original-endpoint exterior flat profile obeys the same envelope times
the exterior CommonZ mass. -/
theorem ndA5FlatReferenceExteriorPhysicalProfile_le_envelope_mul_commonZ
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    {E : Set ℕ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hC : (1 / 2 : ℝ) ≤ C)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hj : j < ndA5BandCount B branch) :
    ndA5FlatReferenceExteriorPhysicalProfile B
        (ndA5ReferenceLevel B) branch C j E ≤
      ndA5ReferenceExteriorProfileEnvelope B C *
        Tao.taoSection5PayloadFreeCommonZ (ndA5ReferenceLevel B)
          (ndA5ReferenceExteriorEndpoints B C E) := by
  unfold ndA5FlatReferenceExteriorPhysicalProfile
    ndA5FlatReferencePhysicalProfileOn
  apply ndA5ReferencePhysicalProfileOn_le_envelope_mul_commonZ
  intro M _hM
  exact (ndA5FlatReferencePhysicalPoint_mem_Icc_envelope
    (M := M) hB hlogB hC hpadding hj).2

/-- Exterior harmonic profile nonnegativity, needed by the exact center
splice without introducing absolute values around the envelope. -/
theorem ndA5HarmonicReferenceExteriorPhysicalProfile_nonneg
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (C : ℝ)
    (j : ℕ) (E : Set ℕ) :
    0 ≤ ndA5HarmonicReferenceExteriorPhysicalProfile B
      (ndA5ReferenceLevel B) branch C j E := by
  unfold ndA5HarmonicReferenceExteriorPhysicalProfile
    ndA5HarmonicReferencePhysicalProfileOn
    ndA5ReferencePhysicalProfileOn
  exact Finset.sum_nonneg fun M _ =>
    mul_nonneg (ndA5ReferenceEndpointKernel_nonneg _ _)
      (div_nonneg
        (Finset.sum_nonneg fun nu _ => Finset.sum_nonneg fun r _ =>
          ndA5NominalStrictBandRawQTerm_nonneg _ _ _ _ _ _)
        (Tao.logFinsetMass_nonneg _))

/-- Exterior flat profile nonnegativity. -/
theorem ndA5FlatReferenceExteriorPhysicalProfile_nonneg
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (C : ℝ)
    (j : ℕ) (E : Set ℕ) :
    0 ≤ ndA5FlatReferenceExteriorPhysicalProfile B
      (ndA5ReferenceLevel B) branch C j E := by
  unfold ndA5FlatReferenceExteriorPhysicalProfile
    ndA5FlatReferencePhysicalProfileOn
    ndA5ReferencePhysicalProfileOn
  have hz0 : 0 ≤ ndA5BandLower B branch j := by
    unfold ndA5BandLower
    apply mul_nonneg
    · rw [Tao.taoSection5SourceY_eq_branch_rpow]
      exact Real.rpow_nonneg (Nat.cast_nonneg B) _
    · exact Real.exp_nonneg _
  have hcard0 :
      0 ≤ ((ndA5OddBand B branch j).card : ℝ) := by positivity
  exact Finset.sum_nonneg fun M _ =>
    mul_nonneg (ndA5ReferenceEndpointKernel_nonneg _ _)
      (mul_nonneg (div_nonneg hz0 hcard0)
        (Finset.sum_nonneg fun nu _ => Finset.sum_nonneg fun r _ =>
          ndA5NominalStrictBandFlatRawQTerm_nonneg _ _ _ _ _ _))

end
end ND
end Erdos1135
