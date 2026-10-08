import Erdos1135.ND.Band.A5BandNormalizer
import Erdos1135.ND.Conventions
import Erdos1135.Tao.Syracuse.OddSource
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Exact A5 Band Source PMFs

This leaf puts the flat and harmonic laws for one exact half-open A5 band on
one common finite carrier, then maps both laws to Tao's odd-source type.  It
also records their exact support and the intersection-removal interface used
by the terminal-coverage probability theorem.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- The common finite value carrier for both exact A5 band laws. -/
abbrev NDA5BandCarrier
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ) :=
  {N : ℕ // N ∈ ndA5OddBand B branch j}

/-- Forget the finite-band witness while retaining oddness. -/
def ndA5BandValueToOddNat
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ} :
    NDA5BandCarrier B branch j → Tao.TaoOddNat :=
  fun N =>
    ⟨N.1, Nat.odd_iff.mpr (mem_ndA5OddBand.mp N.2).2.2⟩

/-- Uniform counting law on the common exact-band carrier. -/
noncomputable def ndA5FlatBandCarrierPMF
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ)
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch) :
    PMF (NDA5BandCarrier B branch j) :=
  uniformFinsetPMF (ndA5OddBand B branch j)
    (ndA5OddBand_nonempty hB j hcount)

/-- Reciprocal-weight law on the same exact-band carrier. -/
noncomputable def ndA5HarmonicBandCarrierPMF
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ)
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch) :
    PMF (NDA5BandCarrier B branch j) :=
  Tao.logFinsetPMF (ndA5OddBand B branch j)
    (logFinsetMass_ndA5OddBand_pos hB j hcount)

/-- Exact flat A5 band law on Tao's odd-source type. -/
noncomputable def ndA5FlatBandPMF
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ)
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch) :
    PMF Tao.TaoOddNat :=
  (ndA5FlatBandCarrierPMF B branch j hB hcount).map
    ndA5BandValueToOddNat

/-- Exact harmonic A5 band law on Tao's odd-source type. -/
noncomputable def ndA5HarmonicBandPMF
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ)
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch) :
    PMF Tao.TaoOddNat :=
  (ndA5HarmonicBandCarrierPMF B branch j hB hcount).map
    ndA5BandValueToOddNat

/-- Any law mapped from the exact-band carrier is supported in the physical
half-open band. -/
theorem ndA5BandMappedPMF_support_subset
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (q : PMF (NDA5BandCarrier B branch j)) :
    (q.map ndA5BandValueToOddNat).support ⊆
      {N : Tao.TaoOddNat | N.1 ∈ ndA5OddBand B branch j} := by
  rw [PMF.support_map]
  rintro _ ⟨N, _hN, rfl⟩
  exact N.2

theorem ndA5FlatBandPMF_support_subset
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch) :
    (ndA5FlatBandPMF B branch j hB hcount).support ⊆
      {N : Tao.TaoOddNat | N.1 ∈ ndA5OddBand B branch j} := by
  simpa only [ndA5FlatBandPMF] using
    ndA5BandMappedPMF_support_subset
      (ndA5FlatBandCarrierPMF B branch j hB hcount)

theorem ndA5HarmonicBandPMF_support_subset
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch) :
    (ndA5HarmonicBandPMF B branch j hB hcount).support ⊆
      {N : Tao.TaoOddNat | N.1 ∈ ndA5OddBand B branch j} := by
  simpa only [ndA5HarmonicBandPMF] using
    ndA5BandMappedPMF_support_subset
      (ndA5HarmonicBandCarrierPMF B branch j hB hcount)

/-- A mapped exact-band law ignores a redundant intersection with its
physical band. -/
theorem ndA5BandMappedPMF_toOuterMeasure_inter_band
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (q : PMF (NDA5BandCarrier B branch j))
    (A : Set Tao.TaoOddNat) :
    (q.map ndA5BandValueToOddNat).toOuterMeasure
        (A ∩ {N | N.1 ∈ ndA5OddBand B branch j}) =
      (q.map ndA5BandValueToOddNat).toOuterMeasure A := by
  apply (q.map ndA5BandValueToOddNat).toOuterMeasure_apply_eq_of_inter_support_eq
  ext N
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨hA, _hband⟩, hsupp⟩
    exact ⟨hA, hsupp⟩
  · rintro ⟨hA, hsupp⟩
    exact
      ⟨⟨hA, ndA5BandMappedPMF_support_subset q hsupp⟩, hsupp⟩

theorem ndA5FlatBandPMF_toOuterMeasure_inter_band
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (A : Set Tao.TaoOddNat) :
    (ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure
        (A ∩ {N | N.1 ∈ ndA5OddBand B branch j}) =
      (ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure A := by
  simpa only [ndA5FlatBandPMF] using
    ndA5BandMappedPMF_toOuterMeasure_inter_band
      (ndA5FlatBandCarrierPMF B branch j hB hcount) A

theorem ndA5HarmonicBandPMF_toOuterMeasure_inter_band
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (A : Set Tao.TaoOddNat) :
    (ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure
        (A ∩ {N | N.1 ∈ ndA5OddBand B branch j}) =
      (ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure A := by
  simpa only [ndA5HarmonicBandPMF] using
    ndA5BandMappedPMF_toOuterMeasure_inter_band
      (ndA5HarmonicBandCarrierPMF B branch j hB hcount) A

/-- Pull mapped flat event mass back to the common finite carrier. -/
theorem ndA5FlatBandPMF_toOuterMeasure_apply
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (A : Set Tao.TaoOddNat) :
    (ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure A =
      (ndA5FlatBandCarrierPMF B branch j hB hcount).toOuterMeasure
        (ndA5BandValueToOddNat ⁻¹' A) := by
  rw [ndA5FlatBandPMF, PMF.toOuterMeasure_map_apply]

/-- Pull mapped harmonic event mass back to the same finite carrier. -/
theorem ndA5HarmonicBandPMF_toOuterMeasure_apply
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (A : Set Tao.TaoOddNat) :
    (ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure A =
      (ndA5HarmonicBandCarrierPMF B branch j hB hcount).toOuterMeasure
        (ndA5BandValueToOddNat ⁻¹' A) := by
  rw [ndA5HarmonicBandPMF, PMF.toOuterMeasure_map_apply]

/-- Exact bridge from one A5 half-open band to Tao's inclusive odd window. -/
theorem ndA5OddBand_eq_oddLogWindow
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch}
    (j : ℕ) (hcount : 0 < ndA5BandCount B branch) :
    ndA5OddBand B branch j =
      Tao.oddLogWindow (Nat.ceil (ndA5BandLower B branch j))
        (Nat.ceil (ndA5BandLower B branch (j + 1)) - 1) := by
  simpa only [ndA5OddBand] using
    oddHalfOpenRealWindow_eq_oddLogWindow
      (ndA5BandLower_ceil_lt_ceil_succ hB j hcount)

/-- Every flat carrier atom has the reciprocal cardinality weight. -/
theorem ndA5FlatBandCarrierPMF_apply_toReal
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (N : NDA5BandCarrier B branch j) :
    (ndA5FlatBandCarrierPMF B branch j hB hcount N).toReal =
      1 / ((ndA5OddBand B branch j).card : ℝ) := by
  simp [ndA5FlatBandCarrierPMF, uniformFinsetPMF,
    PMF.uniformOfFintype_apply, Fintype.card_coe, one_div]

/-- Every harmonic carrier atom has its exact normalized reciprocal weight. -/
theorem ndA5HarmonicBandCarrierPMF_apply_toReal
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (N : NDA5BandCarrier B branch j) :
    (ndA5HarmonicBandCarrierPMF B branch j hB hcount N).toReal =
      (1 / (N.1 : ℝ)) /
        Tao.logFinsetMass (ndA5OddBand B branch j) := by
  have hNpos : 0 < N.1 := by
    have hmod := (mem_ndA5OddBand.mp N.2).2.2
    omega
  simpa only [ndA5HarmonicBandCarrierPMF,
    Tao.logNatWeight_eq_one_div_of_pos hNpos] using
    (Tao.logFinsetPMF_apply_toReal
      (logFinsetMass_ndA5OddBand_pos hB j hcount) N)

/-- The total reciprocal mass of one band is at most its cardinality divided
by the lower real endpoint. -/
theorem logFinsetMass_ndA5OddBand_le_card_div_lower
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch}
    (j : ℕ) (hcount : 0 < ndA5BandCount B branch) :
    Tao.logFinsetMass (ndA5OddBand B branch j) ≤
      ((ndA5OddBand B branch j).card : ℝ) /
        ndA5BandLower B branch j := by
  have hz : 0 < ndA5BandLower B branch j := by
    linarith [six_le_ndA5BandLower hB j hcount]
  rw [Tao.logFinsetMass]
  calc
    (∑ N ∈ ndA5OddBand B branch j, Tao.logNatWeight N) =
        ∑ N ∈ ndA5OddBand B branch j, 1 / (N : ℝ) := by
          apply Finset.sum_congr rfl
          intro N hN
          rw [Tao.logNatWeight_eq_one_div_of_pos]
          have hmod := (mem_ndA5OddBand.mp hN).2.2
          omega
    _ ≤ ∑ _N ∈ ndA5OddBand B branch j,
        1 / ndA5BandLower B branch j := by
          apply Finset.sum_le_sum
          intro N hN
          exact one_div_le_one_div_of_le hz (mem_ndA5OddBand.mp hN).1
    _ = ((ndA5OddBand B branch j).card : ℝ) /
        ndA5BandLower B branch j := by
          simp [div_eq_mul_inv]

/-- On their common carrier, flat density is bounded by the harmonic density
times the exact within-band distortion `exp beta`. -/
theorem ndA5FlatBandCarrierPMF_apply_toReal_lt_exp_mul_harmonic
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (N : NDA5BandCarrier B branch j) :
    (ndA5FlatBandCarrierPMF B branch j hB hcount N).toReal <
      Real.exp (ndA5BandBeta B branch) *
        (ndA5HarmonicBandCarrierPMF B branch j hB hcount N).toReal := by
  let S := ndA5OddBand B branch j
  let z := ndA5BandLower B branch j
  let H := Tao.logFinsetMass S
  let c : ℝ := S.card
  let n : ℝ := N.1
  let e := Real.exp (ndA5BandBeta B branch)
  have hz : 0 < z := by
    dsimp [z]
    linarith [six_le_ndA5BandLower hB j hcount]
  have hH : 0 < H := by
    simpa only [H, S] using
      logFinsetMass_ndA5OddBand_pos hB j hcount
  have hc : 0 < c := by
    dsimp [c, S]
    exact_mod_cast ndA5OddBand_card_pos hB j hcount
  have hn : 0 < n := by
    dsimp [n]
    have hmod := (mem_ndA5OddBand.mp N.2).2.2
    exact_mod_cast (show 0 < N.1 by omega)
  have hHupper : H ≤ c / z := by
    simpa only [H, c, S, z] using
      logFinsetMass_ndA5OddBand_le_card_div_lower hB j hcount
  have hnUpper : n < z * e := by
    simpa only [n, z, e] using
      (mem_ndA5OddBand_exp_iff.mp N.2).2.1
  have hcz : 0 < c / z := div_pos hc hz
  have hnH : n * H < e * c := by
    calc
      n * H ≤ n * (c / z) :=
        mul_le_mul_of_nonneg_left hHupper hn.le
      _ < (z * e) * (c / z) :=
        mul_lt_mul_of_pos_right hnUpper hcz
      _ = e * c := by field_simp
  rw [ndA5FlatBandCarrierPMF_apply_toReal hB hcount,
    ndA5HarmonicBandCarrierPMF_apply_toReal hB hcount]
  change 1 / c < e * ((1 / n) / H)
  have heq : e * ((1 / n) / H) = e / (n * H) := by
    field_simp
  rw [heq]
  exact (div_lt_div_iff₀ hc (mul_pos hn hH)).2 (by simpa using hnH)

/-- Every event on the common carrier has flat mass at most `exp beta` times
its harmonic mass. -/
theorem ndA5FlatBandCarrier_eventMass_le_exp_mul_harmonic
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (A : Set (NDA5BandCarrier B branch j)) :
    Tao.pmfProb (ndA5FlatBandCarrierPMF B branch j hB hcount) A ≤
      Real.exp (ndA5BandBeta B branch) *
        Tao.pmfProb
          (ndA5HarmonicBandCarrierPMF B branch j hB hcount) A := by
  classical
  unfold Tao.pmfProb
  calc
    (∑ N, if N ∈ A then
        (ndA5FlatBandCarrierPMF B branch j hB hcount N).toReal else 0) ≤
      ∑ N, if N ∈ A then
        Real.exp (ndA5BandBeta B branch) *
          (ndA5HarmonicBandCarrierPMF B branch j hB hcount N).toReal else 0 := by
            apply Finset.sum_le_sum
            intro N _hN
            by_cases hNA : N ∈ A
            · simp only [hNA, if_true]
              exact
                (ndA5FlatBandCarrierPMF_apply_toReal_lt_exp_mul_harmonic
                  hB hcount N).le
            · simp [hNA]
    _ = Real.exp (ndA5BandBeta B branch) *
        ∑ N, if N ∈ A then
          (ndA5HarmonicBandCarrierPMF B branch j hB hcount N).toReal else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro N _hN
            by_cases hNA : N ∈ A <;> simp [hNA]

/-- The same event domination after mapping both laws to Tao's odd-source
type. No injectivity of the value map is needed. -/
theorem ndA5FlatBandPMF_eventMass_le_exp_mul_harmonic
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (A : Set Tao.TaoOddNat) :
    ((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure A).toReal ≤
      Real.exp (ndA5BandBeta B branch) *
        ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure A).toReal := by
  rw [ndA5FlatBandPMF_toOuterMeasure_apply,
    ndA5HarmonicBandPMF_toOuterMeasure_apply,
    ← Tao.pmfProb_eq_toOuterMeasure_toReal,
    ← Tao.pmfProb_eq_toOuterMeasure_toReal]
  exact ndA5FlatBandCarrier_eventMass_le_exp_mul_harmonic hB hcount _

end

end ND
end Erdos1135
