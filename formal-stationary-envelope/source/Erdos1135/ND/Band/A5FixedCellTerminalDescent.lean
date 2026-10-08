import Erdos1135.ND.Fourier.FixedTotalFiniteResolvedDescent
import Erdos1135.ND.Band.A5TerminalAtomReconstruction
import Erdos1135.Tao.Section5.EndpointCoefficientBound
import Erdos1135.Tao.Section5.CommonZ

/-!
# A5 Fixed-Cell Terminal Descent

This downstream Band leaf specializes the collision-safe fixed-total descent
to the endpoint loads in one fixed `(nu,L)` A5 cell.  The strict activity
predicate remains attached to each original endpoint.  The harmonic load is
identified with Tao's checked payload-free coefficient, which supplies its
aggregate cap without residue injectivity or deduplication.
-/

namespace Erdos1135
namespace ND

open Tao

noncomputable section

/-- Endpoints active in one strict nominal `(nu,L)` cell. -/
noncomputable def ndA5FixedCellEndpoints
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ)
    (E : Set ℕ) (nu L : ℕ) : Finset ℕ := by
  classical
  exact (Tao.taoSection5EPrime B E).filter fun M =>
    ndA5NominalStrictBandLevel
      (ndA5BandBeta B branch)
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu (L : ℤ)

theorem ndA5FixedCellEndpoints_subset_ePrime
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ)
    (E : Set ℕ) (nu L : ℕ) :
    ndA5FixedCellEndpoints B branch j E nu L ⊆
      Tao.taoSection5EPrime B E := by
  classical
  intro M hM
  unfold ndA5FixedCellEndpoints at hM
  exact (Finset.mem_filter.mp hM).1

/-- Harmonic coefficient attached to one retained endpoint. -/
noncomputable def ndA5FixedCellHarmonicWeight
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ)
    (nu : ℕ) (M : ℕ) : ℝ :=
  ((3 : ℝ) ^ nu / (M : ℝ)) /
    Tao.logFinsetMass (ndA5OddBand B branch j)

/-- The collision-preserving harmonic high test in one fixed cell. -/
noncomputable def ndA5FixedCellHarmonicTest
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ)
    (E : Set ℕ) (nu L : ℕ) : ZMod (3 ^ nu) → ℝ :=
  ndFiniteResolvedFineTest nu
    (fun M : {M // M ∈ ndA5FixedCellEndpoints B branch j E nu L} =>
      (M.1 : ZMod (3 ^ nu)))
    (fun M => ndA5FixedCellHarmonicWeight B branch j nu M.1)

/-- Payload coefficients are monotone in their finite endpoint set. -/
theorem ndPayloadFreeCoefficient_mono
    {q : ℕ} {S T : Finset ℕ} (hST : S ⊆ T)
    (X : ZMod (3 ^ q)) :
    Tao.taoSection5PayloadFreeCoefficient q S X ≤
      Tao.taoSection5PayloadFreeCoefficient q T X := by
  classical
  unfold Tao.taoSection5PayloadFreeCoefficient
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro M hM
    rcases Finset.mem_filter.mp hM with ⟨hMS, hMX⟩
    exact Finset.mem_filter.mpr ⟨hST hMS, hMX⟩
  · intro M _hMT _hnot
    positivity

/-- The finite-resolved harmonic test is exactly the native payload
coefficient of the filtered endpoint set, divided by the band mass. -/
theorem ndA5FixedCellHarmonicTest_eq_payload
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ)
    (E : Set ℕ) (nu L : ℕ) :
    ndA5FixedCellHarmonicTest B branch j E nu L =
      fun X =>
        Tao.taoSection5PayloadFreeCoefficient nu
            (ndA5FixedCellEndpoints B branch j E nu L) X /
          Tao.logFinsetMass (ndA5OddBand B branch j) := by
  classical
  funext X
  let S := ndA5FixedCellEndpoints B branch j E nu L
  let H := Tao.logFinsetMass (ndA5OddBand B branch j)
  unfold ndA5FixedCellHarmonicTest ndFiniteResolvedFineTest
  change (∑ M : {M // M ∈ S},
      if (M.1 : ZMod (3 ^ nu)) = X then
        ((3 : ℝ) ^ nu / (M.1 : ℝ)) / H else 0) = _
  calc
    _ = ∑ M ∈ S,
        if (M : ZMod (3 ^ nu)) = X then
          ((3 : ℝ) ^ nu / (M : ℝ)) / H else 0 := by
      rw [← Finset.attach_eq_univ]
      exact Finset.sum_attach S (fun M =>
        if (M : ZMod (3 ^ nu)) = X then
          ((3 : ℝ) ^ nu / (M : ℝ)) / H else 0)
    _ = ∑ M ∈ S,
        (((3 : ℝ) ^ nu) *
          (if (M : ZMod (3 ^ nu)) = X then 1 / (M : ℝ) else 0)) / H := by
      apply Finset.sum_congr rfl
      intro M _hM
      by_cases hMX : (M : ZMod (3 ^ nu)) = X
      · simp [hMX]
        ring
      · simp [hMX]
    _ = (((3 : ℝ) ^ nu) *
          ∑ M ∈ S,
            if (M : ZMod (3 ^ nu)) = X then 1 / (M : ℝ) else 0) / H := by
      rw [Finset.mul_sum, Finset.sum_div]
    _ = Tao.taoSection5PayloadFreeCoefficient nu S X / H := by
      unfold Tao.taoSection5PayloadFreeCoefficient
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [Finset.sum_filter]
    _ = _ := by rfl

/-- The checked native coefficient bound five and the A5 band-mass floor
give the aggregate harmonic cap twenty. -/
theorem ndA5FixedCellHarmonicTest_mem_Icc_twenty
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    {E : Set ℕ} {nu L : ℕ}
    (lost : Tao.TaoSection5PassLostWindowFacts B)
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (hindex : Tao.taoSection5M0 B + nu ≤ Tao.taoSection5N0 B)
    (X : ZMod (3 ^ nu)) :
    ndA5FixedCellHarmonicTest B branch j E nu L X ∈
      Set.Icc (0 : ℝ) 20 := by
  rw [ndA5FixedCellHarmonicTest_eq_payload]
  let S := ndA5FixedCellEndpoints B branch j E nu L
  let H := Tao.logFinsetMass (ndA5OddBand B branch j)
  have hHfloor : (1 / 4 : ℝ) ≤ H :=
    one_fourth_le_logFinsetMass_ndA5OddBand hB j hcount
  have hHpos : 0 < H := by linarith
  have hmono :
      Tao.taoSection5PayloadFreeCoefficient nu S X ≤
        Tao.taoSection5PayloadFreeCoefficient nu
          (Tao.taoSection5EPrime B E) X :=
    ndPayloadFreeCoefficient_mono
      (ndA5FixedCellEndpoints_subset_ePrime B branch j E nu L) X
  have hfull :=
    Tao.taoSection5PayloadFreeCoefficient_ePrime_mem_Icc_five
      lost (E := E) (q := nu) (X := X) hindex
  constructor
  · exact div_nonneg
      (Tao.taoSection5PayloadFreeCoefficient_nonneg nu S X) hHpos.le
  · apply (div_le_iff₀ hHpos).2
    have hfive :
        Tao.taoSection5PayloadFreeCoefficient nu S X ≤ 5 :=
      hmono.trans hfull.2
    nlinarith

/-- Exact normalized coarsening of the harmonic test.  The high coefficient
`3^nu` becomes `3^m`, while all endpoint collisions remain in the same
filtered finite set. -/
theorem ndZModPowProjectionFiberAverage_ndA5FixedCellHarmonicTest
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    {E : Set ℕ} {m nu L : ℕ} (hmnu : m ≤ nu) :
    ndZModPowProjectionFiberAverage hmnu
        (ndA5FixedCellHarmonicTest B branch j E nu L) =
      fun X =>
        Tao.taoSection5PayloadFreeCoefficient m
            (ndA5FixedCellEndpoints B branch j E nu L) X /
          Tao.logFinsetMass (ndA5OddBand B branch j) := by
  classical
  let S := ndA5FixedCellEndpoints B branch j E nu L
  let H := Tao.logFinsetMass (ndA5OddBand B branch j)
  rw [ndA5FixedCellHarmonicTest]
  rw [ndZModPowProjectionFiberAverage_finiteResolvedFineTest]
  funext X
  unfold ndFiniteResolvedCoarseTest ndA5FixedCellHarmonicWeight
  change Tao.zmodPowFiberAverageScale m nu *
      (∑ M : {M // M ∈ S},
        if Tao.taoZModThreeProjection hmnu (M.1 : ZMod (3 ^ nu)) = X
        then ((3 : ℝ) ^ nu / (M.1 : ℝ)) / H else 0) = _
  simp_rw [Tao.taoZModThreeProjection_natCast]
  calc
    _ = Tao.zmodPowFiberAverageScale m nu *
        ∑ M ∈ S,
          if (M : ZMod (3 ^ m)) = X
          then ((3 : ℝ) ^ nu / (M : ℝ)) / H else 0 := by
      congr 1
      rw [← Finset.attach_eq_univ]
      exact Finset.sum_attach S (fun M =>
        if (M : ZMod (3 ^ m)) = X
        then ((3 : ℝ) ^ nu / (M : ℝ)) / H else 0)
    _ = ∑ M ∈ S,
        if (M : ZMod (3 ^ m)) = X
        then ((3 : ℝ) ^ m / (M : ℝ)) / H else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _hM
      by_cases hMX : (M : ZMod (3 ^ m)) = X
      · simp [hMX]
        calc
          Tao.zmodPowFiberAverageScale m nu *
              ((3 : ℝ) ^ nu / (M : ℝ) / H) =
            (Tao.zmodPowFiberAverageScale m nu * (3 : ℝ) ^ nu) /
              (M : ℝ) / H := by ring
          _ = (3 : ℝ) ^ m / (M : ℝ) / H := by
            rw [ndZModPowFiberAverageScale_mul_threePow hmnu]
      · simp [hMX]
    _ = Tao.taoSection5PayloadFreeCoefficient m S X / H := by
      unfold Tao.taoSection5PayloadFreeCoefficient
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [Finset.sum_filter, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro M _hM
      by_cases hMX : (M : ZMod (3 ^ m)) = X
      · simp [hMX]
        ring
      · simp [hMX]
    _ = _ := by rfl

/-- Flat coefficient attached to one retained endpoint.  Its exponential
keeps the original high-level `(nu,L,M)` position. -/
noncomputable def ndA5FixedCellFlatWeight
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ)
    (nu L M : ℕ) : ℝ :=
  (ndA5BandLower B branch j * (3 : ℝ) ^ nu) /
      ((M : ℝ) * ((ndA5OddBand B branch j).card : ℝ)) *
    Real.exp
      (ndA5NominalAffinePosition
        (ndA5BandLower B branch j) M nu L)

/-- The collision-preserving flat high test in one fixed cell. -/
noncomputable def ndA5FixedCellFlatTest
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ)
    (E : Set ℕ) (nu L : ℕ) : ZMod (3 ^ nu) → ℝ :=
  ndFiniteResolvedFineTest nu
    (fun M : {M // M ∈ ndA5FixedCellEndpoints B branch j E nu L} =>
      (M.1 : ZMod (3 ^ nu)))
    (fun M => ndA5FixedCellFlatWeight B branch j nu L M.1)

theorem ndA5FixedCellEndpoint_pos
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    {E : Set ℕ} {nu L : ℕ}
    (M : {M // M ∈ ndA5FixedCellEndpoints B branch j E nu L}) :
    0 < M.1 := by
  have hE : M.1 ∈ Tao.taoSection5EPrime B E :=
    ndA5FixedCellEndpoints_subset_ePrime B branch j E nu L M.2
  exact Odd.pos (Tao.mem_taoSection5EPrime_iff.mp hE).2.2.1

/-- The actual A5 exponential width is below four, proved here from the
upstream Band width theorem to avoid a reverse Discrepancy import. -/
theorem nd_exp_ndA5BandBeta_lt_four
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B) :
    Real.exp (ndA5BandBeta B branch) < 4 := by
  calc
    Real.exp (ndA5BandBeta B branch) <
        Real.exp (2 * Real.log 2) :=
      Real.exp_lt_exp.mpr
        (ndA5BandBeta_lt_two_mul_logTwo
          (branch := branch) hB hlogB)
    _ = 4 := by
      rw [two_mul, Real.exp_add,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num

/-- On strict support, each flat endpoint weight is nonnegative and at most
four times its harmonic endpoint weight.  This is an error-test domination,
not an identity between the two reference main terms. -/
theorem ndA5FixedCellFlatWeight_nonneg_le_four_mul_harmonic
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    {E : Set ℕ} {nu L : ℕ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hcount : 0 < ndA5BandCount B branch)
    (M : {M // M ∈ ndA5FixedCellEndpoints B branch j E nu L}) :
    0 ≤ ndA5FixedCellFlatWeight B branch j nu L M.1 ∧
      ndA5FixedCellFlatWeight B branch j nu L M.1 ≤
        4 * ndA5FixedCellHarmonicWeight B branch j nu M.1 := by
  classical
  let z := ndA5BandLower B branch j
  let H := Tao.logFinsetMass (ndA5OddBand B branch j)
  let card := ((ndA5OddBand B branch j).card : ℝ)
  let u := ndA5NominalAffinePosition z M.1 nu L
  have hMpos : (0 : ℝ) < M.1 := by
    exact_mod_cast ndA5FixedCellEndpoint_pos M
  have hz : 0 < z := by
    dsimp [z]
    linarith [six_le_ndA5BandLower hB j hcount]
  have hHpos : 0 < H := by
    dsimp [H]
    exact logFinsetMass_ndA5OddBand_pos hB j hcount
  have hcardNat : 0 < (ndA5OddBand B branch j).card :=
    ndA5OddBand_card_pos hB j hcount
  have hcard : 0 < card := by
    dsimp [card]
    exact_mod_cast hcardNat
  have hstrict :
      ndA5NominalStrictBandLevel
        (ndA5BandBeta B branch)
        (ndA5PhysicalPhase z M.1) nu (L : ℤ) := by
    have hfilter := Finset.mem_filter.mp M.2
    simpa [ndA5FixedCellEndpoints, z] using hfilter.2
  have hu :=
    (ndA5NominalStrictBandLevel_iff_nominalPosition
      (ndA5BandBeta B branch) z M.1 nu L).mp hstrict
  have hexpFour : Real.exp u ≤ 4 :=
    (Real.exp_lt_exp.mpr hu.2).le.trans
      (nd_exp_ndA5BandBeta_lt_four
        (branch := branch) hB hlogB).le
  have hmassCard : H ≤ card / z := by
    dsimp [H, card, z]
    exact logFinsetMass_ndA5OddBand_le_card_div_lower
      hB j hcount
  have hzH : z * H ≤ card := by
    have := (le_div_iff₀ hz).mp hmassCard
    simpa [mul_comm] using this
  have hratio0 : 0 ≤ z * H / card := by positivity
  have hratio1 : z * H / card ≤ 1 := by
    apply (div_le_iff₀ hcard).2
    simpa using hzH
  have hfactor : z * H / card * Real.exp u ≤ 4 := by
    calc
      z * H / card * Real.exp u ≤ 1 * 4 :=
        mul_le_mul hratio1 hexpFour (Real.exp_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have hHarmonic0 :
      0 ≤ ndA5FixedCellHarmonicWeight B branch j nu M.1 := by
    unfold ndA5FixedCellHarmonicWeight
    positivity
  have hrewrite :
      ndA5FixedCellFlatWeight B branch j nu L M.1 =
        (z * H / card * Real.exp u) *
          ndA5FixedCellHarmonicWeight B branch j nu M.1 := by
    change (z * (3 : ℝ) ^ nu) / ((M.1 : ℝ) * card) *
        Real.exp u =
      (z * H / card * Real.exp u) *
        (((3 : ℝ) ^ nu / (M.1 : ℝ)) / H)
    field_simp [ne_of_gt hMpos, ne_of_gt hHpos, ne_of_gt hcard]
  constructor
  · unfold ndA5FixedCellFlatWeight
    positivity
  · rw [hrewrite]
    exact mul_le_mul_of_nonneg_right hfactor hHarmonic0

/-- Flat-test collisions are controlled only after summing them: the full
flat high test is pointwise at most four times the harmonic high test. -/
theorem ndA5FixedCellFlatTest_nonneg_le_four_mul_harmonic
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    {E : Set ℕ} {nu L : ℕ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hcount : 0 < ndA5BandCount B branch)
    (X : ZMod (3 ^ nu)) :
    0 ≤ ndA5FixedCellFlatTest B branch j E nu L X ∧
      ndA5FixedCellFlatTest B branch j E nu L X ≤
        4 * ndA5FixedCellHarmonicTest B branch j E nu L X := by
  classical
  unfold ndA5FixedCellFlatTest ndA5FixedCellHarmonicTest
    ndFiniteResolvedFineTest
  constructor
  · apply Finset.sum_nonneg
    intro M _hM
    by_cases hMX : (M.1 : ZMod (3 ^ nu)) = X
    · simp [hMX,
        (ndA5FixedCellFlatWeight_nonneg_le_four_mul_harmonic
          hB hlogB hcount M).1]
    · simp [hMX]
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro M _hM
    by_cases hMX : (M.1 : ZMod (3 ^ nu)) = X
    · simp [hMX]
      exact (ndA5FixedCellFlatWeight_nonneg_le_four_mul_harmonic
        hB hlogB hcount M).2
    · simp [hMX]

/-- Aggregate flat cap eighty, obtained from the aggregate harmonic cap
twenty. -/
theorem ndA5FixedCellFlatTest_mem_Icc_eighty
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    {E : Set ℕ} {nu L : ℕ}
    (lost : Tao.TaoSection5PassLostWindowFacts B)
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hcount : 0 < ndA5BandCount B branch)
    (hindex : Tao.taoSection5M0 B + nu ≤ Tao.taoSection5N0 B)
    (X : ZMod (3 ^ nu)) :
    ndA5FixedCellFlatTest B branch j E nu L X ∈
      Set.Icc (0 : ℝ) 80 := by
  have hdom := ndA5FixedCellFlatTest_nonneg_le_four_mul_harmonic
    (B := B) (branch := branch) (j := j) (E := E)
      (nu := nu) (L := L) hB hlogB hcount X
  have hH := ndA5FixedCellHarmonicTest_mem_Icc_twenty
    (B := B) (branch := branch) (j := j) (E := E)
      (nu := nu) (L := L) lost hB hcount hindex X
  constructor
  · exact hdom.1
  · exact hdom.2.trans (by nlinarith [hH.2])

/-- Exact endpoint expansion of the harmonic high-test expectation. -/
theorem ndPMFWeightedExpectation_ndA5FixedCellHarmonicTest
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    {E : Set ℕ} {nu L : ℕ} (p : PMF (ZMod (3 ^ nu))) :
    ndPMFWeightedExpectation p
        (ndA5FixedCellHarmonicTest B branch j E nu L) =
      ∑ M : {M // M ∈ ndA5FixedCellEndpoints B branch j E nu L},
        (p (M.1 : ZMod (3 ^ nu))).toReal *
          ndA5FixedCellHarmonicWeight B branch j nu M.1 := by
  unfold ndA5FixedCellHarmonicTest
  exact ndPMFWeightedExpectation_finiteResolvedFineTest _ _ _

/-- Exact endpoint expansion of the flat high-test expectation. -/
theorem ndPMFWeightedExpectation_ndA5FixedCellFlatTest
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    {E : Set ℕ} {nu L : ℕ} (p : PMF (ZMod (3 ^ nu))) :
    ndPMFWeightedExpectation p
        (ndA5FixedCellFlatTest B branch j E nu L) =
      ∑ M : {M // M ∈ ndA5FixedCellEndpoints B branch j E nu L},
        (p (M.1 : ZMod (3 ^ nu))).toReal *
          ndA5FixedCellFlatWeight B branch j nu L M.1 := by
  unfold ndA5FixedCellFlatTest
  exact ndPMFWeightedExpectation_finiteResolvedFineTest _ _ _

/-- The harmonic high-test expectation is exactly the original all-`EPrime`
sum with the strict predicate kept on each endpoint. -/
theorem sum_ePrime_harmonicFixedCell_eq_expectation
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    {E : Set ℕ} {nu L : ℕ} (p : PMF (ZMod (3 ^ nu))) :
    (∑ M ∈ Tao.taoSection5EPrime B E,
        (p (M : ZMod (3 ^ nu))).toReal *
          (((3 : ℝ) ^ nu /
              ((M : ℝ) *
                Tao.logFinsetMass (ndA5OddBand B branch j))) *
            @ite ℝ
              (ndA5NominalStrictBandLevel
                (ndA5BandBeta B branch)
                (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
                nu (L : ℤ))
              (Classical.propDecidable _) 1 0)) =
      ndPMFWeightedExpectation p
        (ndA5FixedCellHarmonicTest B branch j E nu L) := by
  classical
  rw [ndPMFWeightedExpectation_ndA5FixedCellHarmonicTest]
  let S := ndA5FixedCellEndpoints B branch j E nu L
  calc
    _ = ∑ M ∈ S,
        (p (M : ZMod (3 ^ nu))).toReal *
          ndA5FixedCellHarmonicWeight B branch j nu M := by
      unfold S ndA5FixedCellEndpoints
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro M _hM
      by_cases hstrict : ndA5NominalStrictBandLevel
          (ndA5BandBeta B branch)
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          nu (L : ℤ)
      · simp only [if_pos hstrict, mul_one]
        unfold ndA5FixedCellHarmonicWeight
        ring
      · simp only [if_neg hstrict, mul_zero]
    _ = _ := by
      rw [← Finset.attach_eq_univ]
      exact (Finset.sum_attach S (fun M =>
        (p (M : ZMod (3 ^ nu))).toReal *
          ndA5FixedCellHarmonicWeight B branch j nu M)).symm

/-- The flat high-test expectation is exactly the original all-`EPrime` sum
with its strict predicate and exponential retained endpointwise. -/
theorem sum_ePrime_flatFixedCell_eq_expectation
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    {E : Set ℕ} {nu L : ℕ} (p : PMF (ZMod (3 ^ nu))) :
    (∑ M ∈ Tao.taoSection5EPrime B E,
        (p (M : ZMod (3 ^ nu))).toReal *
          (((ndA5BandLower B branch j * (3 : ℝ) ^ nu) /
              ((M : ℝ) * ((ndA5OddBand B branch j).card : ℝ))) *
            @ite ℝ
              (ndA5NominalStrictBandLevel
                (ndA5BandBeta B branch)
                (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
                nu (L : ℤ))
              (Classical.propDecidable _)
              (Real.exp
                (ndA5NominalAffinePosition
                  (ndA5BandLower B branch j) M nu L)) 0)) =
      ndPMFWeightedExpectation p
        (ndA5FixedCellFlatTest B branch j E nu L) := by
  classical
  rw [ndPMFWeightedExpectation_ndA5FixedCellFlatTest]
  let S := ndA5FixedCellEndpoints B branch j E nu L
  calc
    _ = ∑ M ∈ S,
        (p (M : ZMod (3 ^ nu))).toReal *
          ndA5FixedCellFlatWeight B branch j nu L M := by
      unfold S ndA5FixedCellEndpoints
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro M _hM
      by_cases hstrict : ndA5NominalStrictBandLevel
          (ndA5BandBeta B branch)
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          nu (L : ℤ)
      · simp only [if_pos hstrict]
        unfold ndA5FixedCellFlatWeight
        ring
      · simp only [if_neg hstrict, mul_zero]
    _ = _ := by
      rw [← Finset.attach_eq_univ]
      exact (Finset.sum_attach S (fun M =>
        (p (M : ZMod (3 ^ nu))).toReal *
          ndA5FixedCellFlatWeight B branch j nu L M)).symm

/-- The complete geometry and coefficient-room packet supplied by one T2
time and one retained terminal total.  Scheduler-specific guards remain
outside this declaration. -/
theorem ndA5FixedCellGuards_of_t2_terminal
    {B n L : ℕ} {C : ℝ}
    (ht2 : NDA5T2ScaleFacts B n C) (hB : 1 ≤ B)
    (hL : L ∈ ndA5TerminalTotals B C n) :
    let q := n - Tao.taoSection5M0 B
    0 < q ∧ q ≤ L ∧
      |(L : ℝ) - 2 * (q : ℝ)| ≤ (q : ℝ) / 8 ∧
      Tao.taoSection5M0 B + q = n ∧
      Tao.taoSection5M0 B + q ≤ Tao.taoSection5N0 B := by
  dsimp only
  let q := n - Tao.taoSection5M0 B
  have hmem := mem_ndA5TerminalTotals_iff.mp hL
  have hqEq : Tao.taoSection5M0 B + q = n := by
    dsimp [q]
    exact Nat.add_sub_of_le ht2.m0_le
  refine ⟨ht2.nu_pos, hmem.1, ?_, hqEq, ?_⟩
  · exact hmem.2.2.le.trans ht2.width_le_nu_div_eight
  · rw [hqEq]
    exact ht2.le_n0 hB

/-- The literal harmonic terminal sum in one fixed `(n,L)` cell is one
endpoint mass times the already aggregated collision-preserving high test. -/
theorem sum_ndA5HarmonicTerminalAtomNominalIdealMass_fixedCell_eq_expectation
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (n : {n // n ∈ ndA5PaddedBandWindow B branch C j})
    (L : {L // L ∈ ndA5TerminalTotals B C n.1})
    (ht2 : NDA5T2ScaleFacts B n.1 C) :
    let nu := n.1 - Tao.taoSection5M0 B
    (∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
        ∑ u : Sym (Fin nu) (L.1 - nu),
          ndA5HarmonicTerminalAtomNominalIdealMass
            (⟨n, ⟨L, (u, M)⟩⟩ :
              NDA5TerminalAtomIndex B branch C j E)) =
      ndGeom2EndpointMass nu L.1 *
        ndPMFWeightedExpectation
          (ndSection7FiberPMF nu L.1 ht2.nu_pos
            (mem_ndA5TerminalTotals_iff.mp L.2).1)
          (ndA5FixedCellHarmonicTest B branch j E nu L.1) := by
  classical
  dsimp only
  let nu := n.1 - Tao.taoSection5M0 B
  have hnuL : nu ≤ L.1 := (mem_ndA5TerminalTotals_iff.mp L.2).1
  let p := ndSection7FiberPMF nu L.1 ht2.nu_pos hnuL
  calc
    _ = ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
        ndGeom2EndpointMass nu L.1 *
          ((ndSection7FiberPMFTotal nu L.1
              (M.1 : ZMod (3 ^ nu))).toReal *
            (((3 : ℝ) ^ nu /
                ((M.1 : ℝ) *
                  Tao.logFinsetMass (ndA5OddBand B branch j))) *
              @ite ℝ
                (ndA5NominalStrictBandLevel
                  (ndA5BandBeta B branch)
                  (ndA5PhysicalPhase
                    (ndA5BandLower B branch j) M.1)
                  nu (L.1 : ℤ))
                (Classical.propDecidable _) 1 0)) := by
      apply Finset.sum_congr rfl
      intro M _hM
      simpa [nu] using
        (sum_ndA5HarmonicTerminalAtomNominalIdealMass_fixedFiber_eq
          n L M ht2.nu_pos)
    _ = ndGeom2EndpointMass nu L.1 *
        ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
          (p (M.1 : ZMod (3 ^ nu))).toReal *
            (((3 : ℝ) ^ nu /
                ((M.1 : ℝ) *
                  Tao.logFinsetMass (ndA5OddBand B branch j))) *
              @ite ℝ
                (ndA5NominalStrictBandLevel
                  (ndA5BandBeta B branch)
                  (ndA5PhysicalPhase
                    (ndA5BandLower B branch j) M.1)
                  nu (L.1 : ℤ))
                (Classical.propDecidable _) 1 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _hM
      rw [ndSection7FiberPMFTotal_eq_of_pos_of_le ht2.nu_pos hnuL]
    _ = _ := by
      congr 1
      rw [← sum_ePrime_harmonicFixedCell_eq_expectation p]
      rw [← Finset.attach_eq_univ]
      exact Finset.sum_attach (Tao.taoSection5EPrime B E) (fun M =>
        (p (M : ZMod (3 ^ nu))).toReal *
          (((3 : ℝ) ^ nu /
              ((M : ℝ) *
                Tao.logFinsetMass (ndA5OddBand B branch j))) *
            @ite ℝ
              (ndA5NominalStrictBandLevel
                (ndA5BandBeta B branch)
                (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
                nu (L.1 : ℤ))
              (Classical.propDecidable _) 1 0))

/-- The literal flat terminal sum in one fixed `(n,L)` cell is one endpoint
mass times the exact flat high test; its exponential occurs once. -/
theorem sum_ndA5FlatTerminalAtomNominalIdealMass_fixedCell_eq_expectation
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (n : {n // n ∈ ndA5PaddedBandWindow B branch C j})
    (L : {L // L ∈ ndA5TerminalTotals B C n.1})
    (ht2 : NDA5T2ScaleFacts B n.1 C) :
    let nu := n.1 - Tao.taoSection5M0 B
    (∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
        ∑ u : Sym (Fin nu) (L.1 - nu),
          ndA5FlatTerminalAtomNominalIdealMass
            (⟨n, ⟨L, (u, M)⟩⟩ :
              NDA5TerminalAtomIndex B branch C j E)) =
      ndGeom2EndpointMass nu L.1 *
        ndPMFWeightedExpectation
          (ndSection7FiberPMF nu L.1 ht2.nu_pos
            (mem_ndA5TerminalTotals_iff.mp L.2).1)
          (ndA5FixedCellFlatTest B branch j E nu L.1) := by
  classical
  dsimp only
  let nu := n.1 - Tao.taoSection5M0 B
  have hnuL : nu ≤ L.1 := (mem_ndA5TerminalTotals_iff.mp L.2).1
  let p := ndSection7FiberPMF nu L.1 ht2.nu_pos hnuL
  calc
    _ = ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
        ndGeom2EndpointMass nu L.1 *
          ((ndSection7FiberPMFTotal nu L.1
              (M.1 : ZMod (3 ^ nu))).toReal *
            (((ndA5BandLower B branch j * (3 : ℝ) ^ nu) /
                ((M.1 : ℝ) *
                  ((ndA5OddBand B branch j).card : ℝ))) *
              @ite ℝ
                (ndA5NominalStrictBandLevel
                  (ndA5BandBeta B branch)
                  (ndA5PhysicalPhase
                    (ndA5BandLower B branch j) M.1)
                  nu (L.1 : ℤ))
                (Classical.propDecidable _)
                (Real.exp
                  (ndA5NominalAffinePosition
                    (ndA5BandLower B branch j) M.1 nu L.1)) 0)) := by
      apply Finset.sum_congr rfl
      intro M _hM
      simpa [nu] using
        (sum_ndA5FlatTerminalAtomNominalIdealMass_fixedFiber_eq
          n L M ht2.nu_pos)
    _ = ndGeom2EndpointMass nu L.1 *
        ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
          (p (M.1 : ZMod (3 ^ nu))).toReal *
            (((ndA5BandLower B branch j * (3 : ℝ) ^ nu) /
                ((M.1 : ℝ) *
                  ((ndA5OddBand B branch j).card : ℝ))) *
              @ite ℝ
                (ndA5NominalStrictBandLevel
                  (ndA5BandBeta B branch)
                  (ndA5PhysicalPhase
                    (ndA5BandLower B branch j) M.1)
                  nu (L.1 : ℤ))
                (Classical.propDecidable _)
                (Real.exp
                  (ndA5NominalAffinePosition
                    (ndA5BandLower B branch j) M.1 nu L.1)) 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _hM
      rw [ndSection7FiberPMFTotal_eq_of_pos_of_le ht2.nu_pos hnuL]
    _ = _ := by
      congr 1
      rw [← sum_ePrime_flatFixedCell_eq_expectation p]
      rw [← Finset.attach_eq_univ]
      exact Finset.sum_attach (Tao.taoSection5EPrime B E) (fun M =>
        (p (M : ZMod (3 ^ nu))).toReal *
          (((ndA5BandLower B branch j * (3 : ℝ) ^ nu) /
              ((M : ℝ) * ((ndA5OddBand B branch j).card : ℝ))) *
            @ite ℝ
              (ndA5NominalStrictBandLevel
                (ndA5BandBeta B branch)
                (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
                nu (L.1 : ℤ))
              (Classical.propDecidable _)
              (Real.exp
                (ndA5NominalAffinePosition
                  (ndA5BandLower B branch j) M nu L.1)) 0))

/-- The exact flat coarse test.  Its activity and exponential still depend on
the original high-level cell and endpoint. -/
noncomputable def ndA5FixedCellFlatCoarseTest
    {m nu : ℕ} (hmnu : m ≤ nu)
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ)
    (E : Set ℕ) (L : ℕ) : ZMod (3 ^ m) → ℝ :=
  ndFiniteResolvedCoarseTest hmnu
    (fun M : {M // M ∈ ndA5FixedCellEndpoints B branch j E nu L} =>
      (M.1 : ZMod (3 ^ nu)))
    (fun M => ndA5FixedCellFlatWeight B branch j nu L M.1)

theorem ndZModPowProjectionFiberAverage_ndA5FixedCellFlatTest
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    {E : Set ℕ} {m nu L : ℕ} (hmnu : m ≤ nu) :
    ndZModPowProjectionFiberAverage hmnu
        (ndA5FixedCellFlatTest B branch j E nu L) =
      ndA5FixedCellFlatCoarseTest hmnu B branch j E L := by
  unfold ndA5FixedCellFlatTest ndA5FixedCellFlatCoarseTest
  exact ndZModPowProjectionFiberAverage_finiteResolvedFineTest _ _ _

/-- The flat Syracuse reference expands M-first with exactly one normalized
scale and the original high-level exponential coefficient. -/
theorem ndPMFWeightedExpectation_ndA5FixedCellFlatCoarseTest
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    {E : Set ℕ} {m nu L : ℕ} (hmnu : m ≤ nu)
    (p : PMF (ZMod (3 ^ m))) :
    ndPMFWeightedExpectation p
        (ndA5FixedCellFlatCoarseTest hmnu B branch j E L) =
      Tao.zmodPowFiberAverageScale m nu *
        ∑ M : {M // M ∈ ndA5FixedCellEndpoints B branch j E nu L},
          (p (M.1 : ZMod (3 ^ m))).toReal *
            ndA5FixedCellFlatWeight B branch j nu L M.1 := by
  unfold ndA5FixedCellFlatCoarseTest
  simpa using
    (ndPMFWeightedExpectation_finiteResolvedCoarseTest hmnu p
      (fun M : {M // M ∈ ndA5FixedCellEndpoints B branch j E nu L} =>
        (M.1 : ZMod (3 ^ nu)))
      (fun M => ndA5FixedCellFlatWeight B branch j nu L M.1))

/-- Source-facing M-first expansion of the flat Syracuse reference.  The
single normalized projection scale has converted `3^nu` to `3^m`; the strict
activity set and exponential remain attached to the original high cell. -/
theorem ndPMFWeightedExpectation_ndA5FixedCellFlatCoarseTest_low
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    {E : Set ℕ} {m nu L : ℕ} (hmnu : m ≤ nu)
    (p : PMF (ZMod (3 ^ m))) :
    ndPMFWeightedExpectation p
        (ndA5FixedCellFlatCoarseTest hmnu B branch j E L) =
      ∑ M : {M // M ∈ ndA5FixedCellEndpoints B branch j E nu L},
        (p (M.1 : ZMod (3 ^ m))).toReal *
          ((ndA5BandLower B branch j * (3 : ℝ) ^ m) /
              ((M.1 : ℝ) * ((ndA5OddBand B branch j).card : ℝ)) *
            Real.exp
              (ndA5NominalAffinePosition
                (ndA5BandLower B branch j) M.1 nu L)) := by
  rw [ndPMFWeightedExpectation_ndA5FixedCellFlatCoarseTest hmnu,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M _hM
  unfold ndA5FixedCellFlatWeight
  calc
    Tao.zmodPowFiberAverageScale m nu *
          ((p (M.1 : ZMod (3 ^ m))).toReal *
            ((ndA5BandLower B branch j * (3 : ℝ) ^ nu) /
                ((M.1 : ℝ) * ((ndA5OddBand B branch j).card : ℝ)) *
              Real.exp
                (ndA5NominalAffinePosition
                  (ndA5BandLower B branch j) M.1 nu L))) =
        (p (M.1 : ZMod (3 ^ m))).toReal *
          ((ndA5BandLower B branch j *
                (Tao.zmodPowFiberAverageScale m nu * (3 : ℝ) ^ nu)) /
              ((M.1 : ℝ) * ((ndA5OddBand B branch j).card : ℝ)) *
            Real.exp
              (ndA5NominalAffinePosition
                (ndA5BandLower B branch j) M.1 nu L)) := by ring
    _ = _ := by
      rw [ndZModPowFiberAverageScale_mul_threePow hmnu]

/-- Mixed-level M-first expansion of the harmonic Syracuse reference.  Only
the residue and power descend to `m`; strict activity remains at the original
top cell `(nu,L,M)`. -/
theorem ndPMFWeightedExpectation_ndA5FixedCellHarmonicReference_low
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    {E : Set ℕ} {m nu L : ℕ} :
    ndPMFWeightedExpectation (Tao.syracPMF m)
        (fun X =>
          Tao.taoSection5PayloadFreeCoefficient m
              (ndA5FixedCellEndpoints B branch j E nu L) X /
            Tao.logFinsetMass (ndA5OddBand B branch j)) =
      ∑ M ∈ Tao.taoSection5EPrime B E,
        (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
          (((3 : ℝ) ^ m /
              ((M : ℝ) *
                Tao.logFinsetMass (ndA5OddBand B branch j))) *
            @ite ℝ
              (ndA5NominalStrictBandLevel
                (ndA5BandBeta B branch)
                (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
                nu (L : ℤ))
              (Classical.propDecidable _) 1 0) := by
  classical
  let S := ndA5FixedCellEndpoints B branch j E nu L
  let H := Tao.logFinsetMass (ndA5OddBand B branch j)
  calc
    ndPMFWeightedExpectation (Tao.syracPMF m)
        (fun X => Tao.taoSection5PayloadFreeCoefficient m S X / H) =
        Tao.taoSection5PayloadFreeCommonZ m S / H := by
      unfold ndPMFWeightedExpectation
      rw [tsum_fintype,
        Tao.taoSection5PayloadFreeCommonZ_eq_fineSyracWeightedTerm]
      unfold Tao.taoSection5FineSyracWeightedTerm
        Tao.syracPMFMassVector
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro X _hX
      ring
    _ = ∑ M ∈ S,
        (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
          ((3 : ℝ) ^ m / ((M : ℝ) * H)) := by
      unfold Tao.taoSection5PayloadFreeCommonZ
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro M _hM
      change
        (((3 ^ m : ℕ) : ℝ) *
              (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
              (1 / (M : ℝ))) / H = _
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      ring
    _ = ∑ M ∈ Tao.taoSection5EPrime B E,
        (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
          (((3 : ℝ) ^ m / ((M : ℝ) * H)) *
            @ite ℝ
              (ndA5NominalStrictBandLevel
                (ndA5BandBeta B branch)
                (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
                nu (L : ℤ))
              (Classical.propDecidable _) 1 0) := by
      unfold S ndA5FixedCellEndpoints
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro M _hM
      by_cases hstrict : ndA5NominalStrictBandLevel
          (ndA5BandBeta B branch)
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          nu (L : ℤ)
      · simp [hstrict]
      · simp [hstrict]
    _ = _ := by rfl

/-- Mixed-level M-first expansion of the flat Syracuse reference over the
full inherited endpoint carrier.  The low coefficient is `3^m`, while the
strict predicate and exponential remain attached to `(nu,L,M)`. -/
theorem ndPMFWeightedExpectation_ndA5FixedCellFlatReference_low
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    {E : Set ℕ} {m nu L : ℕ} (hmnu : m ≤ nu) :
    ndPMFWeightedExpectation (Tao.syracPMF m)
        (ndA5FixedCellFlatCoarseTest hmnu B branch j E L) =
      ∑ M ∈ Tao.taoSection5EPrime B E,
        (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
          (((ndA5BandLower B branch j * (3 : ℝ) ^ m) /
              ((M : ℝ) * ((ndA5OddBand B branch j).card : ℝ))) *
            @ite ℝ
              (ndA5NominalStrictBandLevel
                (ndA5BandBeta B branch)
                (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
                nu (L : ℤ))
              (Classical.propDecidable _)
              (Real.exp
                (ndA5NominalAffinePosition
                  (ndA5BandLower B branch j) M nu L)) 0) := by
  classical
  rw [ndPMFWeightedExpectation_ndA5FixedCellFlatCoarseTest_low hmnu]
  let S := ndA5FixedCellEndpoints B branch j E nu L
  calc
    (∑ M : {M // M ∈ S},
        (Tao.syracPMF m (M.1 : ZMod (3 ^ m))).toReal *
          ((ndA5BandLower B branch j * (3 : ℝ) ^ m) /
              ((M.1 : ℝ) * ((ndA5OddBand B branch j).card : ℝ)) *
            Real.exp
              (ndA5NominalAffinePosition
                (ndA5BandLower B branch j) M.1 nu L))) =
        ∑ M ∈ S,
          (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
            ((ndA5BandLower B branch j * (3 : ℝ) ^ m) /
                ((M : ℝ) * ((ndA5OddBand B branch j).card : ℝ)) *
              Real.exp
                (ndA5NominalAffinePosition
                  (ndA5BandLower B branch j) M nu L)) := by
      rw [← Finset.attach_eq_univ]
      exact Finset.sum_attach S (fun M =>
        (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
          ((ndA5BandLower B branch j * (3 : ℝ) ^ m) /
              ((M : ℝ) * ((ndA5OddBand B branch j).card : ℝ)) *
            Real.exp
              (ndA5NominalAffinePosition
                (ndA5BandLower B branch j) M nu L)))
    _ = _ := by
      unfold S ndA5FixedCellEndpoints
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro M _hM
      by_cases hstrict : ndA5NominalStrictBandLevel
          (ndA5BandBeta B branch)
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          nu (L : ℤ)
      · simp [hstrict]
      · simp [hstrict]

/-- Harmonic fixed-cell FM1/R1/D6 descent.  The reference is the common
low-level payload coefficient on the original strict endpoint set. -/
theorem abs_ndA5FixedCellHarmonicExpectation_sub_syrac_le_fm1
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    {E : Set ℕ} {nu L : ℕ}
    (lost : Tao.TaoSection5PassLostWindowFacts B)
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (hindex : Tao.taoSection5M0 B + nu ≤ Tao.taoSection5N0 B)
    {A : ℕ} {K C : ℝ}
    (hFM1 : ndSection7ConditionedFM1NatAt A K C)
    {m : ℕ} (hm : 150 ≤ m) (hmnu : 8 * m ≤ nu)
    (hD : |(L : ℝ) - 2 * (nu : ℝ)| ≤ (nu : ℝ) / 8)
    (hWindow : ndSection7M1Window K nu L)
    (hDelta :
      ndFixedTotalRatioCenterOffset m nu L ≤ ndFixedTotalRatioScale m)
    (hEta : ndFixedTotalRatioEps m nu L + 8 / (m : ℝ) ^ 3 ≤ 1) :
    |ndPMFWeightedExpectation
          (ndSection7FiberPMF nu L (by omega)
            (ndFixedTotalRatio_n_le_L hm hmnu hD))
          (ndA5FixedCellHarmonicTest B branch j E nu L) -
        ndPMFWeightedExpectation (Tao.syracPMF m)
          (fun X =>
            Tao.taoSection5PayloadFreeCoefficient m
                (ndA5FixedCellEndpoints B branch j E nu L) X /
              Tao.logFinsetMass (ndA5OddBand B branch j))| ≤
      20 * (C / (m : ℝ) ^ A) +
        (43 / 25 : ℝ) *
          (ndFixedTotalRatioEps m nu L + 8 / (m : ℝ) ^ 3) *
          ndPMFWeightedExpectation (Tao.syracPMF m)
            (fun X =>
              Tao.taoSection5PayloadFreeCoefficient m
                  (ndA5FixedCellEndpoints B branch j E nu L) X /
                Tao.logFinsetMass (ndA5OddBand B branch j)) +
        4 / (m : ℝ) ^ 3 * 20 := by
  have hcap : ∀ X,
      ndA5FixedCellHarmonicTest B branch j E nu L X ∈
        Set.Icc (0 : ℝ) 20 := fun X =>
    ndA5FixedCellHarmonicTest_mem_Icc_twenty
      lost hB hcount hindex X
  have hbase :=
    abs_ndSection7FiberPMF_expectation_sub_syrac_projectionAverage_le_fm1
      hFM1 hm hmnu hD hWindow hDelta hEta
        (ndA5FixedCellHarmonicTest B branch j E nu L) 20
        (fun X => (hcap X).1) (fun X => (hcap X).2)
  rw [ndZModPowProjectionFiberAverage_ndA5FixedCellHarmonicTest]
    at hbase
  exact hbase

/-- Flat fixed-cell FM1/R1/D6 descent.  Cap domination is used only in the
error rows; the Syracuse reference retains the exact flat coarse test. -/
theorem abs_ndA5FixedCellFlatExpectation_sub_syrac_le_fm1
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    {E : Set ℕ} {nu L : ℕ}
    (lost : Tao.TaoSection5PassLostWindowFacts B)
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hcount : 0 < ndA5BandCount B branch)
    (hindex : Tao.taoSection5M0 B + nu ≤ Tao.taoSection5N0 B)
    {A : ℕ} {K C : ℝ}
    (hFM1 : ndSection7ConditionedFM1NatAt A K C)
    {m : ℕ} (hm : 150 ≤ m) (hmnu : 8 * m ≤ nu)
    (hD : |(L : ℝ) - 2 * (nu : ℝ)| ≤ (nu : ℝ) / 8)
    (hWindow : ndSection7M1Window K nu L)
    (hDelta :
      ndFixedTotalRatioCenterOffset m nu L ≤ ndFixedTotalRatioScale m)
    (hEta : ndFixedTotalRatioEps m nu L + 8 / (m : ℝ) ^ 3 ≤ 1) :
    |ndPMFWeightedExpectation
          (ndSection7FiberPMF nu L (by omega)
            (ndFixedTotalRatio_n_le_L hm hmnu hD))
          (ndA5FixedCellFlatTest B branch j E nu L) -
        ndPMFWeightedExpectation (Tao.syracPMF m)
          (ndA5FixedCellFlatCoarseTest (show m ≤ nu by omega)
            B branch j E L)| ≤
      80 * (C / (m : ℝ) ^ A) +
        (43 / 25 : ℝ) *
          (ndFixedTotalRatioEps m nu L + 8 / (m : ℝ) ^ 3) *
          ndPMFWeightedExpectation (Tao.syracPMF m)
            (ndA5FixedCellFlatCoarseTest (show m ≤ nu by omega)
              B branch j E L) +
        4 / (m : ℝ) ^ 3 * 80 := by
  have hcap : ∀ X,
      ndA5FixedCellFlatTest B branch j E nu L X ∈
        Set.Icc (0 : ℝ) 80 := fun X =>
    ndA5FixedCellFlatTest_mem_Icc_eighty
      lost hB hlogB hcount hindex X
  have hbase :=
    abs_ndSection7FiberPMF_expectation_sub_syrac_projectionAverage_le_fm1
      hFM1 hm hmnu hD hWindow hDelta hEta
        (ndA5FixedCellFlatTest B branch j E nu L) 80
        (fun X => (hcap X).1) (fun X => (hcap X).2)
  rw [ndZModPowProjectionFiberAverage_ndA5FixedCellFlatTest] at hbase
  exact hbase

/-- Source-facing harmonic fixed-cell descent.  T2 supplies the coefficient
room and terminal discrepancy guard, and the single endpoint mass multiplies
the entire FM1/R1/D6 bracket exactly once. -/
theorem abs_sum_ndA5HarmonicTerminalAtomNominalIdealMass_fixedCell_sub_syrac_le_fm1
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {Cband : ℝ} {j : ℕ} {E : Set ℕ}
    (n : {n // n ∈ ndA5PaddedBandWindow B branch Cband j})
    (L : {L // L ∈ ndA5TerminalTotals B Cband n.1})
    (ht2 : NDA5T2ScaleFacts B n.1 Cband)
    (lost : Tao.TaoSection5PassLostWindowFacts B)
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    {A : ℕ} {K C : ℝ}
    (hFM1 : ndSection7ConditionedFM1NatAt A K C)
    {m : ℕ} (hm : 150 ≤ m)
    (hmnu : 8 * m ≤ n.1 - Tao.taoSection5M0 B)
    (hWindow : ndSection7M1Window K
      (n.1 - Tao.taoSection5M0 B) L.1)
    (hDelta :
      ndFixedTotalRatioCenterOffset m
          (n.1 - Tao.taoSection5M0 B) L.1 ≤
        ndFixedTotalRatioScale m)
    (hEta :
      ndFixedTotalRatioEps m
          (n.1 - Tao.taoSection5M0 B) L.1 +
          8 / (m : ℝ) ^ 3 ≤ 1) :
    let nu := n.1 - Tao.taoSection5M0 B
    let RH :=
      ∑ M ∈ Tao.taoSection5EPrime B E,
        (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
          (((3 : ℝ) ^ m /
              ((M : ℝ) *
                Tao.logFinsetMass (ndA5OddBand B branch j))) *
            @ite ℝ
              (ndA5NominalStrictBandLevel
                (ndA5BandBeta B branch)
                (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
                nu (L.1 : ℤ))
              (Classical.propDecidable _) 1 0)
    |(∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
          ∑ u : Sym (Fin nu) (L.1 - nu),
            ndA5HarmonicTerminalAtomNominalIdealMass
              (⟨n, ⟨L, (u, M)⟩⟩ :
                NDA5TerminalAtomIndex B branch Cband j E)) -
        ndGeom2EndpointMass nu L.1 * RH| ≤
      ndGeom2EndpointMass nu L.1 *
        (20 * (C / (m : ℝ) ^ A) +
          (43 / 25 : ℝ) *
            (ndFixedTotalRatioEps m nu L.1 + 8 / (m : ℝ) ^ 3) * RH +
          4 / (m : ℝ) ^ 3 * 20) := by
  classical
  dsimp only
  let nu := n.1 - Tao.taoSection5M0 B
  have hguards := ndA5FixedCellGuards_of_t2_terminal ht2 hB L.2
  have hD : |(L.1 : ℝ) - 2 * (nu : ℝ)| ≤ (nu : ℝ) / 8 :=
    hguards.2.2.1
  have hindex : Tao.taoSection5M0 B + nu ≤ Tao.taoSection5N0 B :=
    hguards.2.2.2.2
  have hdesc :=
    abs_ndA5FixedCellHarmonicExpectation_sub_syrac_le_fm1
      (B := B) (branch := branch) (j := j) (E := E)
      (nu := nu) (L := L.1) lost hB hcount hindex
      hFM1 hm hmnu hD hWindow hDelta hEta
  rw [ndPMFWeightedExpectation_ndA5FixedCellHarmonicReference_low]
    at hdesc
  rw [sum_ndA5HarmonicTerminalAtomNominalIdealMass_fixedCell_eq_expectation
    n L ht2]
  have hmass : 0 ≤ ndGeom2EndpointMass nu L.1 :=
    ndGeom2EndpointMass_nonneg nu L.1
  rw [← mul_sub, abs_mul, abs_of_nonneg hmass]
  exact mul_le_mul_of_nonneg_left hdesc hmass

/-- Source-facing flat fixed-cell descent.  The exact exponential reference
is retained, while cap `80` is used only in the FM1 and absolute-tail rows. -/
theorem abs_sum_ndA5FlatTerminalAtomNominalIdealMass_fixedCell_sub_syrac_le_fm1
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {Cband : ℝ} {j : ℕ} {E : Set ℕ}
    (n : {n // n ∈ ndA5PaddedBandWindow B branch Cband j})
    (L : {L // L ∈ ndA5TerminalTotals B Cband n.1})
    (ht2 : NDA5T2ScaleFacts B n.1 Cband)
    (lost : Tao.TaoSection5PassLostWindowFacts B)
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hcount : 0 < ndA5BandCount B branch)
    {A : ℕ} {K C : ℝ}
    (hFM1 : ndSection7ConditionedFM1NatAt A K C)
    {m : ℕ} (hm : 150 ≤ m)
    (hmnu : 8 * m ≤ n.1 - Tao.taoSection5M0 B)
    (hWindow : ndSection7M1Window K
      (n.1 - Tao.taoSection5M0 B) L.1)
    (hDelta :
      ndFixedTotalRatioCenterOffset m
          (n.1 - Tao.taoSection5M0 B) L.1 ≤
        ndFixedTotalRatioScale m)
    (hEta :
      ndFixedTotalRatioEps m
          (n.1 - Tao.taoSection5M0 B) L.1 +
          8 / (m : ℝ) ^ 3 ≤ 1) :
    let nu := n.1 - Tao.taoSection5M0 B
    let RF :=
      ∑ M ∈ Tao.taoSection5EPrime B E,
        (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
          (((ndA5BandLower B branch j * (3 : ℝ) ^ m) /
              ((M : ℝ) * ((ndA5OddBand B branch j).card : ℝ))) *
            @ite ℝ
              (ndA5NominalStrictBandLevel
                (ndA5BandBeta B branch)
                (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
                nu (L.1 : ℤ))
              (Classical.propDecidable _)
              (Real.exp
                (ndA5NominalAffinePosition
                  (ndA5BandLower B branch j) M nu L.1)) 0)
    |(∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
          ∑ u : Sym (Fin nu) (L.1 - nu),
            ndA5FlatTerminalAtomNominalIdealMass
              (⟨n, ⟨L, (u, M)⟩⟩ :
                NDA5TerminalAtomIndex B branch Cband j E)) -
        ndGeom2EndpointMass nu L.1 * RF| ≤
      ndGeom2EndpointMass nu L.1 *
        (80 * (C / (m : ℝ) ^ A) +
          (43 / 25 : ℝ) *
            (ndFixedTotalRatioEps m nu L.1 + 8 / (m : ℝ) ^ 3) * RF +
          4 / (m : ℝ) ^ 3 * 80) := by
  classical
  dsimp only
  let nu := n.1 - Tao.taoSection5M0 B
  have hguards := ndA5FixedCellGuards_of_t2_terminal ht2 hB L.2
  have hD : |(L.1 : ℝ) - 2 * (nu : ℝ)| ≤ (nu : ℝ) / 8 :=
    hguards.2.2.1
  have hindex : Tao.taoSection5M0 B + nu ≤ Tao.taoSection5N0 B :=
    hguards.2.2.2.2
  have hdesc :=
    abs_ndA5FixedCellFlatExpectation_sub_syrac_le_fm1
      (B := B) (branch := branch) (j := j) (E := E)
      (nu := nu) (L := L.1) lost hB hlogB hcount hindex
      hFM1 hm hmnu hD hWindow hDelta hEta
  rw [ndPMFWeightedExpectation_ndA5FixedCellFlatReference_low]
    at hdesc
  rw [sum_ndA5FlatTerminalAtomNominalIdealMass_fixedCell_eq_expectation
    n L ht2]
  have hmass : 0 ≤ ndGeom2EndpointMass nu L.1 :=
    ndGeom2EndpointMass_nonneg nu L.1
  rw [← mul_sub, abs_mul, abs_of_nonneg hmass]
  exact mul_le_mul_of_nonneg_left hdesc hmass

end

end ND
end Erdos1135
