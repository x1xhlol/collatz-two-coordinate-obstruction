import Erdos1135.ND.Band.A5BandSourceWindow
import Erdos1135.ND.Band.A5HarmonicProp19
import Erdos1135.ND.Band.A5SourceMixture
import Erdos1135.ND.Band.A5StrictBandLevels
import Erdos1135.Tao.Section5.NoHitRate

/-!
# Standalone uniform-source no-hit rate

This leaf proves ND-M2(i) at the natural target.  It transfers the checked
harmonic exact-band Proposition 1.9 estimate through deterministic descent,
dominates the flat band law one-sidedly, and averages exact band weights.
The possible top endpoint is charged once.  Passage total variation is not
used because totalization cannot distinguish a genuine hit at `1` from no
hit.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped Topology

noncomputable section

/-- Monotonicity of PMF outer mass after taking real values, without a
finiteness assumption on the source type. -/
private theorem pmfOuterMass_toReal_mono
    {ι : Type*} (p : PMF ι) {A D : Set ι} (hAD : A ⊆ D) :
    (p.toOuterMeasure A).toReal ≤ (p.toOuterMeasure D).toReal := by
  have hfinite : p.toOuterMeasure D ≠ ⊤ := by
    apply ne_of_lt
    calc
      p.toOuterMeasure D ≤ p.toOuterMeasure Set.univ :=
        p.toOuterMeasure.mono (Set.subset_univ D)
      _ = 1 := (p.toOuterMeasure_apply_eq_one_iff Set.univ).2
        (Set.subset_univ _)
      _ < ⊤ := ENNReal.one_lt_top
  exact ENNReal.toReal_mono hfinite (p.toOuterMeasure.mono hAD)

/-- The source-facing no-hit event at a natural passage threshold. -/
def ndA5NoHitEvent (B : ℕ) : Set Tao.TaoOddNat :=
  {N | ¬ Tao.syracuseHitsAtMost N.1 B}

/-- On a valid exact band, harmonic no-hit mass is bounded by the same raw
strict-low error as the inherited canonical source window. -/
theorem ndA5HarmonicBandNoHitMass_le_error
    {B : ℕ} (descent : Tao.TaoSection5DescentScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (hj : j < ndA5BandCount B branch) :
    ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure
        (ndA5NoHitEvent B)).toReal ≤
      Tao.taoSection5NoHitError B := by
  let μ := ndA5HarmonicBandPMF B branch j hB hcount
  let n := Tao.taoSection5N0 B
  let E := Tao.taoLowValuationWeightEvent n
  have hsupport :
      μ.toOuterMeasure
          (ndA5NoHitEvent B ∩ {N | N.1 ∈ ndA5OddBand B branch j}) =
        μ.toOuterMeasure (ndA5NoHitEvent B) := by
    simpa only [μ] using
      (ndA5HarmonicBandPMF_toOuterMeasure_inter_band
        hB hcount (ndA5NoHitEvent B))
  have hmap :
      (μ.toOuterMeasure (ndA5NoHitEvent B)).toReal ≤
        ((Tao.taoProp19ActualValuationLaw μ n).toOuterMeasure E).toReal := by
    calc
      (μ.toOuterMeasure (ndA5NoHitEvent B)).toReal =
          (μ.toOuterMeasure
            (ndA5NoHitEvent B ∩
              {N | N.1 ∈ ndA5OddBand B branch j})).toReal :=
        congrArg ENNReal.toReal hsupport.symm
      _ ≤ (μ.toOuterMeasure
          {N | Tao.syracuseValuationPNatList n N.1 N.2 ∈ E}).toReal := by
        apply pmfOuterMass_toReal_mono
        rintro N ⟨hno, hband⟩
        apply descent.actualValuations_mem_low_of_not_hitsAtMost
          (branch := branch)
        · exact ndA5OddBand_mem_taoSection5SourceWindow hB hj hband
        · exact hno
      _ = ((Tao.taoProp19ActualValuationLaw μ n).toOuterMeasure E).toReal := by
        unfold Tao.taoProp19ActualValuationLaw
        rw [PMF.toOuterMeasure_map_apply]
        apply congrArg ENNReal.toReal
        apply congrArg μ.toOuterMeasure
        rfl
  have hM : 1 ≤ Tao.taoSection5NPrime B := by
    have hn0 := descent.five_le_n0
    unfold Tao.taoSection5NPrime
    omega
  have hvaluation :=
    taoProp19ValuationTV_ndA5HarmonicBandPMF_le
      hB j hcount hM
  unfold Tao.taoProp19ValuationTV at hvaluation
  have hcompare :
      ((Tao.taoProp19ActualValuationLaw μ n).toOuterMeasure E).toReal ≤
        ((Tao.geom2PNatListPMF n).toOuterMeasure E).toReal +
          4 * (2 : ℝ) ^
            (-((1 / 128 : ℝ) * (n : ℝ))) := by
    apply Tao.pmfOuterMass_le_add_of_taoPMFFullL1_le
    simpa only [μ, n] using hvaluation
  have hideal := Tao.geom2PNatListPMF_lowWeightEvent_le_exp n
  calc
    ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure
        (ndA5NoHitEvent B)).toReal ≤
        ((Tao.taoProp19ActualValuationLaw μ n).toOuterMeasure E).toReal := by
      simpa only [μ] using hmap
    _ ≤ ((Tao.geom2PNatListPMF n).toOuterMeasure E).toReal +
        4 * (2 : ℝ) ^ (-((1 / 128 : ℝ) * (n : ℝ))) := hcompare
    _ ≤ Real.exp (-((n : ℝ) / 3200)) +
        4 * (2 : ℝ) ^ (-((1 / 128 : ℝ) * (n : ℝ))) := by
      exact add_le_add (by simpa only [E] using hideal) le_rfl
    _ = Tao.taoSection5NoHitError B := by
      rfl

/-- One-sided within-band density comparison transfers the raw harmonic
no-hit estimate to the flat law. -/
theorem ndA5FlatBandNoHitMass_le_exp_mul_error
    {B : ℕ} (descent : Tao.TaoSection5DescentScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (hj : j < ndA5BandCount B branch) :
    ((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure
        (ndA5NoHitEvent B)).toReal ≤
      Real.exp (ndA5BandBeta B branch) *
        Tao.taoSection5NoHitError B := by
  exact (ndA5FlatBandPMF_eventMass_le_exp_mul_harmonic
    hB hcount (ndA5NoHitEvent B)).trans
      (mul_le_mul_of_nonneg_left
        (ndA5HarmonicBandNoHitMass_le_error
          descent hB hcount hj)
        (Real.exp_pos _).le)

/-- Exact natural whole-source uniform no-hit probability as the mapped A5
flat-source event mass. -/
theorem uniformNoHitProbability_natCast_taoSection5SourceY_eq_flatSourceNoHitMass
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (hcount : 0 < ndA5BandCount B branch) :
    uniformNoHitProbability (B : ℝ) (Tao.taoSection5SourceY B branch)
        (ndA5OddBlock_sourceY_nonempty hB branch hcount) =
      ((ndA5FlatSourcePMF B branch hB hcount).toOuterMeasure
        (ndA5NoHitEvent B)).toReal := by
  unfold uniformNoHitProbability ndA5FlatSourcePMF
  rw [Tao.pmfProb_eq_toOuterMeasure_toReal,
    PMF.toOuterMeasure_map_apply]
  apply congrArg ENNReal.toReal
  apply congrArg
    (uniformOddBlockPMF (Tao.taoSection5SourceY B branch)
      (ndA5OddBlock_sourceY_nonempty hB branch hcount)).toOuterMeasure
  ext N
  simp only [Set.mem_setOf_eq, Set.mem_preimage, ndA5NoHitEvent]
  rw [Tao.syracuseHitsAtMostReal_iff_floor (by positivity),
    Nat.floor_natCast]
  rfl

/-- Both whole uniform source branches have a genuine polynomial no-hit rate.
Exact convex mixing introduces no band-count factor, and the possible top is
charged once. -/
theorem eventually_ndA5FlatSourceNoHitMass_le_forty_four :
    ∀ᶠ B : ℕ in atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch)
        (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch),
        ((ndA5FlatSourcePMF B branch hB hcount).toOuterMeasure
          (ndA5NoHitEvent B)).toReal ≤
            44 * (B : ℝ) ^ (-(1 / 32000 : ℝ)) := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [Tao.eventually_taoSection5DescentScaleFacts,
        hlog.eventually_ge_atTop (300000 : ℝ)]
      with B descent hlogB
  intro branch hB hcount
  let R := (B : ℝ) ^ (-(1 / 32000 : ℝ))
  have hR : 0 ≤ R := Real.rpow_nonneg (Nat.cast_nonneg B) _
  have hfortyR : 0 ≤ (40 : ℝ) * R :=
    mul_nonneg (by norm_num) hR
  have hexp : Real.exp (ndA5BandBeta B branch) ≤ 4 := by
    calc
      Real.exp (ndA5BandBeta B branch) ≤
          Real.exp (2 * Real.log 2) :=
        (Real.exp_lt_exp.mpr
          (ndA5BandBeta_lt_two_mul_logTwo
            (branch := branch) hB hlogB)).le
      _ = 4 := by
        rw [two_mul, Real.exp_add,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have hband (j : ℕ) (hj : j < ndA5BandCount B branch) :
      ((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure
          (ndA5NoHitEvent B)).toReal ≤ 40 * R := by
    calc
      ((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure
          (ndA5NoHitEvent B)).toReal ≤
          Real.exp (ndA5BandBeta B branch) *
            Tao.taoSection5NoHitError B :=
        ndA5FlatBandNoHitMass_le_exp_mul_error
          descent hB hcount hj
      _ ≤ Real.exp (ndA5BandBeta B branch) * (10 * R) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [R] using
            Tao.taoSection5NoHitError_le_ten_mul_threshold_rpow hB)
          (Real.exp_pos _).le
      _ ≤ 4 * (10 * R) :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = 40 * R := by ring
  have hbands :
      (∑ j ∈ Finset.range (ndA5BandCount B branch),
          ndA5FlatBandWeight B branch j *
            ((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure
              (ndA5NoHitEvent B)).toReal) ≤
        ∑ j ∈ Finset.range (ndA5BandCount B branch),
          ndA5FlatBandWeight B branch j * (40 * R) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (hband j (Finset.mem_range.mp hj))
      (ndA5FlatBandWeight_nonneg B branch j)
  have hsumWeight :
      (∑ j ∈ Finset.range (ndA5BandCount B branch),
        ndA5FlatBandWeight B branch j) ≤ 1 := by
    have hnormalize :=
      sum_ndA5FlatBandWeight_add_topWeight_eq_one hB branch hcount
    have htopNonneg := ndA5FlatTopWeight_nonneg B branch
    linarith
  have hpow : (B : ℝ) ^ (-1 : ℝ) ≤ R := by
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hB : (1 : ℝ) ≤ B) (by norm_num)
  have htop :
      ndA5FlatTopRestrictedMass B branch (ndA5NoHitEvent B) ≤ 4 * R := by
    calc
      ndA5FlatTopRestrictedMass B branch (ndA5NoHitEvent B) ≤
          ndA5FlatTopWeight B branch :=
        ndA5FlatTopRestrictedMass_le_weight hB hcount _
      _ ≤ 4 / (B : ℝ) :=
        ndA5FlatTopWeight_le_four_div hB branch hcount
      _ = 4 * (B : ℝ) ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]
        ring
      _ ≤ 4 * R := mul_le_mul_of_nonneg_left hpow (by norm_num)
  calc
    ((ndA5FlatSourcePMF B branch hB hcount).toOuterMeasure
        (ndA5NoHitEvent B)).toReal =
        (∑ j ∈ Finset.range (ndA5BandCount B branch),
          ndA5FlatBandWeight B branch j *
            ((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure
              (ndA5NoHitEvent B)).toReal) +
          ndA5FlatTopRestrictedMass B branch (ndA5NoHitEvent B) :=
      ndA5FlatSourcePMF_eventMass_eq_band_mixture_add_top
        hB hcount (ndA5NoHitEvent B)
    _ ≤ (∑ j ∈ Finset.range (ndA5BandCount B branch),
          ndA5FlatBandWeight B branch j * (40 * R)) + 4 * R :=
      add_le_add hbands htop
    _ = (∑ j ∈ Finset.range (ndA5BandCount B branch),
          ndA5FlatBandWeight B branch j) * (40 * R) + 4 * R := by
      rw [Finset.sum_mul]
    _ ≤ 1 * (40 * R) + 4 * R := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_right hsumWeight
          hfortyR) (4 * R)
    _ = 44 * R := by ring
    _ = 44 * (B : ℝ) ^ (-(1 / 32000 : ℝ)) := by rfl

/-- Consumer-shaped natural specialization of ND-M2(i). -/
theorem eventually_uniformNoHitProbability_natCast_taoSection5SourceY_le_forty_four :
    ∀ᶠ B : ℕ in atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch)
        (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch),
        uniformNoHitProbability (B : ℝ)
            (Tao.taoSection5SourceY B branch)
            (ndA5OddBlock_sourceY_nonempty hB branch hcount) ≤
          44 * (B : ℝ) ^ (-(1 / 32000 : ℝ)) := by
  filter_upwards [eventually_ndA5FlatSourceNoHitMass_le_forty_four]
      with B hnoHit
  intro branch hB hcount
  rw [uniformNoHitProbability_natCast_taoSection5SourceY_eq_flatSourceNoHitMass
    hB branch hcount]
  exact hnoHit branch hB hcount

end

end ND
end Erdos1135
