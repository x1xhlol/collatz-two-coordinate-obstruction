import Erdos1135.ND.Band.A5ReferenceTerminalAggregate
import Erdos1135.Tao.Section5.CommonZ

/-!
# A5 original-endpoint reference split

This leaf splits the literal natural endpoint carrier `EPrime` at the closed
interior cutoff consumed by physical A6.  The complementary exterior cutoff
is strict.  It also exposes the exact endpoint-kernel/CommonZ identity and
finset-parametric versions of both physical reference profiles.

The split is always on the original natural endpoint `M`.  It has no branch,
band, time, residue, or proof-local shifted endpoint parameter.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

noncomputable section

/-- Closed interior predicate on the original natural endpoint. -/
def ndA5ReferenceEndpointInteriorAt (B : ℕ) (C : ℝ) (M : ℕ) : Prop :=
  |ndA5InteriorShift B (M : ℝ)| ≤
    (4 / 25 : ℝ) * ndA5TubeWidth B C

/-- Strict exterior predicate complementary to the closed interior cutoff. -/
def ndA5ReferenceEndpointExteriorAt (B : ℕ) (C : ℝ) (M : ℕ) : Prop :=
  (4 / 25 : ℝ) * ndA5TubeWidth B C <
    |ndA5InteriorShift B (M : ℝ)|

/-- Interior original endpoints in the literal inherited target carrier. -/
def ndA5ReferenceInteriorEndpoints
    (B : ℕ) (C : ℝ) (E : Set ℕ) : Finset ℕ := by
  classical
  exact (Tao.taoSection5EPrime B E).filter
    (ndA5ReferenceEndpointInteriorAt B C)

/-- Exterior original endpoints in the literal inherited target carrier. -/
def ndA5ReferenceExteriorEndpoints
    (B : ℕ) (C : ℝ) (E : Set ℕ) : Finset ℕ := by
  classical
  exact (Tao.taoSection5EPrime B E).filter
    (ndA5ReferenceEndpointExteriorAt B C)

@[simp] theorem mem_ndA5ReferenceInteriorEndpoints_iff
    {B M : ℕ} {C : ℝ} {E : Set ℕ} :
    M ∈ ndA5ReferenceInteriorEndpoints B C E ↔
      M ∈ Tao.taoSection5EPrime B E ∧
        |ndA5InteriorShift B (M : ℝ)| ≤
          (4 / 25 : ℝ) * ndA5TubeWidth B C := by
  simp [ndA5ReferenceInteriorEndpoints,
    ndA5ReferenceEndpointInteriorAt]

@[simp] theorem mem_ndA5ReferenceExteriorEndpoints_iff
    {B M : ℕ} {C : ℝ} {E : Set ℕ} :
    M ∈ ndA5ReferenceExteriorEndpoints B C E ↔
      M ∈ Tao.taoSection5EPrime B E ∧
        (4 / 25 : ℝ) * ndA5TubeWidth B C <
          |ndA5InteriorShift B (M : ℝ)| := by
  simp [ndA5ReferenceExteriorEndpoints,
    ndA5ReferenceEndpointExteriorAt]

/-- The closed interior and strict exterior endpoint carriers are disjoint. -/
theorem ndA5ReferenceInteriorEndpoints_disjoint_exterior
    (B : ℕ) (C : ℝ) (E : Set ℕ) :
    Disjoint (ndA5ReferenceInteriorEndpoints B C E)
      (ndA5ReferenceExteriorEndpoints B C E) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro M hMInt hMExt
  have hInt := (mem_ndA5ReferenceInteriorEndpoints_iff.mp hMInt).2
  have hExt := (mem_ndA5ReferenceExteriorEndpoints_iff.mp hMExt).2
  exact (not_lt_of_ge hInt) hExt

/-- The two endpoint filters exactly partition the literal `EPrime`. -/
theorem ndA5ReferenceInteriorEndpoints_union_exterior
    (B : ℕ) (C : ℝ) (E : Set ℕ) :
    ndA5ReferenceInteriorEndpoints B C E ∪
        ndA5ReferenceExteriorEndpoints B C E =
      Tao.taoSection5EPrime B E := by
  classical
  ext M
  simp only [Finset.mem_union,
    mem_ndA5ReferenceInteriorEndpoints_iff,
    mem_ndA5ReferenceExteriorEndpoints_iff]
  constructor
  · rintro (⟨hM, _hInt⟩ | ⟨hM, _hExt⟩) <;> exact hM
  · intro hM
    rcases lt_or_ge
        ((4 / 25 : ℝ) * ndA5TubeWidth B C)
        |ndA5InteriorShift B (M : ℝ)| with hExt | hInt
    · exact Or.inr ⟨hM, hExt⟩
    · exact Or.inl ⟨hM, hInt⟩

/-- Arbitrary signed endpoint sums split at the original-`M` cutoff. -/
theorem sum_taoSection5EPrime_eq_interior_add_exterior
    (B : ℕ) (C : ℝ) (E : Set ℕ) (f : ℕ → ℝ) :
    (∑ M ∈ Tao.taoSection5EPrime B E, f M) =
      (∑ M ∈ ndA5ReferenceInteriorEndpoints B C E, f M) +
        ∑ M ∈ ndA5ReferenceExteriorEndpoints B C E, f M := by
  classical
  calc
    (∑ M ∈ Tao.taoSection5EPrime B E, f M) =
        ∑ M ∈ ndA5ReferenceInteriorEndpoints B C E ∪
            ndA5ReferenceExteriorEndpoints B C E, f M := by
      rw [ndA5ReferenceInteriorEndpoints_union_exterior]
    _ = (∑ M ∈ ndA5ReferenceInteriorEndpoints B C E, f M) +
          ∑ M ∈ ndA5ReferenceExteriorEndpoints B C E, f M := by
      rw [Finset.sum_union
        (ndA5ReferenceInteriorEndpoints_disjoint_exterior B C E)]

/-- The common reference kernel is nonnegative, including at `M = 0`. -/
theorem ndA5ReferenceEndpointKernel_nonneg (m M : ℕ) :
    0 ≤ ndA5ReferenceEndpointKernel m M := by
  unfold ndA5ReferenceEndpointKernel
  positivity

/-- The endpoint-kernel sum is definitionally Tao's finite CommonZ. -/
theorem sum_ndA5ReferenceEndpointKernel_eq_commonZ
    (m : ℕ) (S : Finset ℕ) :
    (∑ M ∈ S, ndA5ReferenceEndpointKernel m M) =
      Tao.taoSection5PayloadFreeCommonZ m S := by
  classical
  unfold ndA5ReferenceEndpointKernel
    Tao.taoSection5PayloadFreeCommonZ Tao.syracPMFMassVector
  apply Finset.sum_congr rfl
  intro M _hM
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- CommonZ is nonnegative on every finite endpoint carrier. -/
theorem ndA5ReferenceCommonZ_nonneg (m : ℕ) (S : Finset ℕ) :
    0 ≤ Tao.taoSection5PayloadFreeCommonZ m S := by
  rw [← sum_ndA5ReferenceEndpointKernel_eq_commonZ]
  exact Finset.sum_nonneg fun M _hM =>
    ndA5ReferenceEndpointKernel_nonneg m M

/-- CommonZ is monotone under inclusion of finite endpoint carriers. -/
theorem ndA5ReferenceCommonZ_mono
    {m : ℕ} {S T : Finset ℕ} (hST : S ⊆ T) :
    Tao.taoSection5PayloadFreeCommonZ m S ≤
      Tao.taoSection5PayloadFreeCommonZ m T := by
  rw [← sum_ndA5ReferenceEndpointKernel_eq_commonZ,
    ← sum_ndA5ReferenceEndpointKernel_eq_commonZ]
  exact Finset.sum_le_sum_of_subset_of_nonneg hST
    (fun M _hMT _hMS => ndA5ReferenceEndpointKernel_nonneg m M)

/-- CommonZ splits exactly into the closed interior and strict exterior
parts of the original endpoint carrier. -/
theorem ndA5ReferenceCommonZ_ePrime_eq_interior_add_exterior
    (m B : ℕ) (C : ℝ) (E : Set ℕ) :
    Tao.taoSection5PayloadFreeCommonZ m (Tao.taoSection5EPrime B E) =
      Tao.taoSection5PayloadFreeCommonZ m
          (ndA5ReferenceInteriorEndpoints B C E) +
        Tao.taoSection5PayloadFreeCommonZ m
          (ndA5ReferenceExteriorEndpoints B C E) := by
  rw [← sum_ndA5ReferenceEndpointKernel_eq_commonZ,
    ← sum_ndA5ReferenceEndpointKernel_eq_commonZ,
    ← sum_ndA5ReferenceEndpointKernel_eq_commonZ]
  exact sum_taoSection5EPrime_eq_interior_add_exterior B C E
    (ndA5ReferenceEndpointKernel m)

/-- A generic physical reference profile on an explicit endpoint finset. -/
def ndA5ReferencePhysicalProfileOn
    (m : ℕ) (S : Finset ℕ) (P : ℕ → ℝ) : ℝ :=
  ∑ M ∈ S, ndA5ReferenceEndpointKernel m M * P M

/-- Harmonic physical reference profile on an explicit endpoint finset. -/
def ndA5HarmonicReferencePhysicalProfileOn
    (B m : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (S : Finset ℕ) : ℝ :=
  let z := ndA5BandLower B branch j
  let W := ndA5TubeWidth B C
  let H := Tao.logFinsetMass (ndA5OddBand B branch j)
  ndA5ReferencePhysicalProfileOn m S fun M =>
    (∑ nu ∈ ndA5PhysicalNuWindow B branch C j,
        ∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandRawQTerm B branch
            (ndA5PhysicalPhase z M) W nu r) / H

/-- Flat physical reference profile on an explicit endpoint finset.  Its
exponential remains inside the original flat raw-Q term. -/
def ndA5FlatReferencePhysicalProfileOn
    (B m : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (S : Finset ℕ) : ℝ :=
  let z := ndA5BandLower B branch j
  let W := ndA5TubeWidth B C
  let card := ((ndA5OddBand B branch j).card : ℝ)
  ndA5ReferencePhysicalProfileOn m S fun M =>
    (z / card) *
      ∑ nu ∈ ndA5PhysicalNuWindow B branch C j,
        ∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandFlatRawQTerm B branch
            (ndA5PhysicalPhase z M) W nu r

/-- The existing harmonic profile is the explicit-`EPrime` specialization. -/
theorem ndA5HarmonicReferencePhysicalProfile_eq_profileOn_ePrime
    (B m : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (E : Set ℕ) :
    ndA5HarmonicReferencePhysicalProfile B m branch C j E =
      ndA5HarmonicReferencePhysicalProfileOn B m branch C j
        (Tao.taoSection5EPrime B E) := by
  rfl

/-- The existing flat profile is the explicit-`EPrime` specialization. -/
theorem ndA5FlatReferencePhysicalProfile_eq_profileOn_ePrime
    (B m : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (E : Set ℕ) :
    ndA5FlatReferencePhysicalProfile B m branch C j E =
      ndA5FlatReferencePhysicalProfileOn B m branch C j
        (Tao.taoSection5EPrime B E) := by
  rfl

/-- Harmonic profile restricted to the original interior endpoints. -/
def ndA5HarmonicReferenceInteriorPhysicalProfile
    (B m : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (E : Set ℕ) : ℝ :=
  ndA5HarmonicReferencePhysicalProfileOn B m branch C j
    (ndA5ReferenceInteriorEndpoints B C E)

/-- Harmonic profile restricted to the original exterior endpoints. -/
def ndA5HarmonicReferenceExteriorPhysicalProfile
    (B m : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (E : Set ℕ) : ℝ :=
  ndA5HarmonicReferencePhysicalProfileOn B m branch C j
    (ndA5ReferenceExteriorEndpoints B C E)

/-- Flat profile restricted to the original interior endpoints. -/
def ndA5FlatReferenceInteriorPhysicalProfile
    (B m : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (E : Set ℕ) : ℝ :=
  ndA5FlatReferencePhysicalProfileOn B m branch C j
    (ndA5ReferenceInteriorEndpoints B C E)

/-- Flat profile restricted to the original exterior endpoints. -/
def ndA5FlatReferenceExteriorPhysicalProfile
    (B m : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (E : Set ℕ) : ℝ :=
  ndA5FlatReferencePhysicalProfileOn B m branch C j
    (ndA5ReferenceExteriorEndpoints B C E)

/-- Exact harmonic full-profile split on the original endpoint. -/
theorem ndA5HarmonicReferencePhysicalProfile_eq_interior_add_exterior
    (B m : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (E : Set ℕ) :
    ndA5HarmonicReferencePhysicalProfile B m branch C j E =
      ndA5HarmonicReferenceInteriorPhysicalProfile B m branch C j E +
        ndA5HarmonicReferenceExteriorPhysicalProfile B m branch C j E := by
  classical
  unfold ndA5HarmonicReferencePhysicalProfile
    ndA5HarmonicReferenceInteriorPhysicalProfile
    ndA5HarmonicReferenceExteriorPhysicalProfile
    ndA5HarmonicReferencePhysicalProfileOn
    ndA5ReferencePhysicalProfileOn
  exact sum_taoSection5EPrime_eq_interior_add_exterior B C E _

/-- Exact flat full-profile split on the original endpoint. -/
theorem ndA5FlatReferencePhysicalProfile_eq_interior_add_exterior
    (B m : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (E : Set ℕ) :
    ndA5FlatReferencePhysicalProfile B m branch C j E =
      ndA5FlatReferenceInteriorPhysicalProfile B m branch C j E +
        ndA5FlatReferenceExteriorPhysicalProfile B m branch C j E := by
  classical
  unfold ndA5FlatReferencePhysicalProfile
    ndA5FlatReferenceInteriorPhysicalProfile
    ndA5FlatReferenceExteriorPhysicalProfile
    ndA5FlatReferencePhysicalProfileOn
    ndA5ReferencePhysicalProfileOn
  exact sum_taoSection5EPrime_eq_interior_add_exterior B C E _

end
end ND
end Erdos1135
