import Erdos1135.ND.Band.A5ReferencePhysicalSplit
import Erdos1135.ND.Discrepancy.A5TwoProfileNormalizedA6

/-!
# A5 kernel-weighted interior aggregate

This leaf consumes the normalized physical A6 packet pointwise on the closed
original-endpoint interior carrier.  The resulting errors remain literal
endpoint-dependent sums against the nonnegative common reference kernel.
No scalar rate and no exterior estimate is asserted here.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

noncomputable section

/-- The literal normalized harmonic A6 error at one original endpoint. -/
def ndA5HarmonicReferenceInteriorA6Error
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j M : ℕ) (c kappa : ℝ) : ℝ :=
  let EA6 := 3650000 * (C + C ^ 3) * ndA6PhysicalRate B
  ndA5HarmonicTwoProfileNormalizedA6Error B branch j
    (ndA5ReciprocalTwoProfileA6Error
      B branch C j (M : ℝ) EA6 c kappa)

/-- The literal normalized flat A6 error at one original endpoint. -/
def ndA5FlatReferenceInteriorA6Error
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j M : ℕ) (c kappa : ℝ) : ℝ :=
  let EA6 := 3650000 * (C + C ^ 3) * ndA6PhysicalRate B
  ndA5FlatTwoProfileNormalizedA6Error B branch j
    (ndA5FlatTwoProfileA6Error
      B branch C j (M : ℝ) EA6 c kappa)

/-- Finite nonnegative-weight centering with a varying pointwise error. -/
theorem abs_sum_mul_sub_center_mul_sum_le
    { ι : Type* } (S : Finset ι) (w f e : ι → ℝ) (mu : ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hpoint : ∀ i ∈ S, |f i - mu| ≤ e i) :
    |(∑ i ∈ S, w i * f i) - mu * (∑ i ∈ S, w i)| ≤
      ∑ i ∈ S, w i * e i := by
  classical
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    |∑ i ∈ S, (w i * f i - mu * w i)| ≤
        ∑ i ∈ S, |w i * f i - mu * w i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ S, w i * |f i - mu| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show w i * f i - mu * w i = w i * (f i - mu) by ring,
        abs_mul, abs_of_nonneg (hw i hi)]
    _ ≤ ∑ i ∈ S, w i * e i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hpoint i hi) (hw i hi)

/-- Generic endpoint-kernel transport from pointwise centering to CommonZ. -/
theorem abs_ndA5ReferencePhysicalProfileOn_sub_commonZ_le
    {m : ℕ} {S : Finset ℕ} {f e : ℕ → ℝ} {mu : ℝ}
    (hpoint : ∀ M ∈ S, |f M - mu| ≤ e M) :
    |ndA5ReferencePhysicalProfileOn m S f -
        mu * Tao.taoSection5PayloadFreeCommonZ m S| ≤
      ndA5ReferencePhysicalProfileOn m S e := by
  rw [ndA5ReferencePhysicalProfileOn,
    ← sum_ndA5ReferenceEndpointKernel_eq_commonZ]
  exact abs_sum_mul_sub_center_mul_sum_le S
    (ndA5ReferenceEndpointKernel m) f e mu
    (fun M _hM => ndA5ReferenceEndpointKernel_nonneg m M) hpoint

/-- The harmonic `ProfileOn` integrand is definitionally the committed
normalized physical value at the original endpoint. -/
theorem ndA5HarmonicReferencePhysicalProfileOn_eq_normalized
    (B m : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (S : Finset ℕ) :
    ndA5HarmonicReferencePhysicalProfileOn B m branch C j S =
      ndA5ReferencePhysicalProfileOn m S fun M =>
        ndA5HarmonicTwoProfileNormalizedPhysicalValue
          B branch C j (M : ℝ) := by
  rfl

/-- The flat `ProfileOn` integrand is definitionally the committed normalized
physical value, with its exponential still inside the raw profile. -/
theorem ndA5FlatReferencePhysicalProfileOn_eq_normalized
    (B m : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (S : Finset ℕ) :
    ndA5FlatReferencePhysicalProfileOn B m branch C j S =
      ndA5ReferencePhysicalProfileOn m S fun M =>
        ndA5FlatTwoProfileNormalizedPhysicalValue
          B branch C j (M : ℝ) := by
  rfl

/-- Kernel-weighted harmonic A6 on the closed original-endpoint interior. -/
theorem abs_ndA5HarmonicReferenceInteriorPhysicalProfile_sub_commonZ_le
    {B m : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C c kappa : ℝ} {j : ℕ} {E : Set ℕ}
    (hA6 : NDA5TwoProfileNormalizedA6At B C c kappa)
    (hj : j < ndA5BandCount B branch) :
    let Int := ndA5ReferenceInteriorEndpoints B C E
    |ndA5HarmonicReferencePhysicalProfileOn B m branch C j Int -
        (2 / ndA5LogFourThirds) *
          Tao.taoSection5PayloadFreeCommonZ m Int| ≤
      ∑ M ∈ Int, ndA5ReferenceEndpointKernel m M *
        ndA5HarmonicReferenceInteriorA6Error
          B branch C j M c kappa := by
  classical
  dsimp only
  let Int := ndA5ReferenceInteriorEndpoints B C E
  have hA6' := hA6
  rw [NDA5TwoProfileNormalizedA6At] at hA6'
  have hpoint : ∀ M ∈ Int,
      |ndA5HarmonicTwoProfileNormalizedPhysicalValue
            B branch C j (M : ℝ) - 2 / ndA5LogFourThirds| ≤
        ndA5HarmonicReferenceInteriorA6Error
          B branch C j M c kappa := by
    intro M hM
    have hMdata := mem_ndA5ReferenceInteriorEndpoints_iff.mp hM
    have hMposNat : 0 < M :=
      Odd.pos (Tao.mem_taoSection5EPrime_iff.mp hMdata.1).2.2.1
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMposNat
    have hpair := hA6' branch j hj (M : ℝ) hMpos hMdata.2
    simpa only [ndA5HarmonicReferenceInteriorA6Error] using hpair.1
  rw [ndA5HarmonicReferencePhysicalProfileOn_eq_normalized]
  simpa only [ndA5ReferencePhysicalProfileOn, Int] using
    (abs_ndA5ReferencePhysicalProfileOn_sub_commonZ_le
      (m := m) (S := Int) hpoint)

/-- Kernel-weighted flat A6 on the same closed original-endpoint interior. -/
theorem abs_ndA5FlatReferenceInteriorPhysicalProfile_sub_commonZ_le
    {B m : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C c kappa : ℝ} {j : ℕ} {E : Set ℕ}
    (hA6 : NDA5TwoProfileNormalizedA6At B C c kappa)
    (hj : j < ndA5BandCount B branch) :
    let Int := ndA5ReferenceInteriorEndpoints B C E
    |ndA5FlatReferencePhysicalProfileOn B m branch C j Int -
        (2 / ndA5LogFourThirds) *
          Tao.taoSection5PayloadFreeCommonZ m Int| ≤
      ∑ M ∈ Int, ndA5ReferenceEndpointKernel m M *
        ndA5FlatReferenceInteriorA6Error
          B branch C j M c kappa := by
  classical
  dsimp only
  let Int := ndA5ReferenceInteriorEndpoints B C E
  have hA6' := hA6
  rw [NDA5TwoProfileNormalizedA6At] at hA6'
  have hpoint : ∀ M ∈ Int,
      |ndA5FlatTwoProfileNormalizedPhysicalValue
            B branch C j (M : ℝ) - 2 / ndA5LogFourThirds| ≤
        ndA5FlatReferenceInteriorA6Error
          B branch C j M c kappa := by
    intro M hM
    have hMdata := mem_ndA5ReferenceInteriorEndpoints_iff.mp hM
    have hMposNat : 0 < M :=
      Odd.pos (Tao.mem_taoSection5EPrime_iff.mp hMdata.1).2.2.1
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMposNat
    have hpair := hA6' branch j hj (M : ℝ) hMpos hMdata.2
    simpa only [ndA5FlatReferenceInteriorA6Error] using hpair.2
  rw [ndA5FlatReferencePhysicalProfileOn_eq_normalized]
  simpa only [ndA5ReferencePhysicalProfileOn, Int] using
    (abs_ndA5ReferencePhysicalProfileOn_sub_commonZ_le
      (m := m) (S := Int) hpoint)

/-- Named paired interior aggregate packet at one base. -/
def NDA5ReferenceInteriorAggregateAt
    (B : ℕ) (C c kappa : ℝ) : Prop :=
  ∀ (m : ℕ) (branch : Tao.TaoSection5SourceBranch)
      (j : ℕ) (E : Set ℕ),
    j < ndA5BandCount B branch →
      let Int := ndA5ReferenceInteriorEndpoints B C E
      (|ndA5HarmonicReferencePhysicalProfileOn B m branch C j Int -
            (2 / ndA5LogFourThirds) *
              Tao.taoSection5PayloadFreeCommonZ m Int| ≤
          ∑ M ∈ Int, ndA5ReferenceEndpointKernel m M *
            ndA5HarmonicReferenceInteriorA6Error
              B branch C j M c kappa) ∧
        (|ndA5FlatReferencePhysicalProfileOn B m branch C j Int -
            (2 / ndA5LogFourThirds) *
              Tao.taoSection5PayloadFreeCommonZ m Int| ≤
          ∑ M ∈ Int, ndA5ReferenceEndpointKernel m M *
            ndA5FlatReferenceInteriorA6Error
              B branch C j M c kappa)

/-- Fixed-`C` eventual kernel-weighted interior aggregate.  Its error remains
the exact endpoint-dependent finite sum. -/
theorem eventually_ndA5ReferenceInteriorAggregate
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C)
    {c kappa : ℝ} (hPhase : PhaseGap c kappa) :
    ∀ᶠ B : ℕ in Filter.atTop,
      NDA5ReferenceInteriorAggregateAt B C c kappa := by
  filter_upwards [eventually_ndA5TwoProfileNormalizedA6 C hC hPhase]
    with B hA6
  rw [NDA5ReferenceInteriorAggregateAt]
  intro m branch j E hj
  exact
    ⟨abs_ndA5HarmonicReferenceInteriorPhysicalProfile_sub_commonZ_le
        hA6 hj,
      abs_ndA5FlatReferenceInteriorPhysicalProfile_sub_commonZ_le
        hA6 hj⟩

end
end ND
end Erdos1135
