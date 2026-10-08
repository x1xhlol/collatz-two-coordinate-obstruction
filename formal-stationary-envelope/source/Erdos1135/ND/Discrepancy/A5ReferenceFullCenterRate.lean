import Erdos1135.ND.Band.A5ReferenceExteriorCoefficientRate
import Erdos1135.ND.Band.A5ReferenceExteriorEnvelope
import Erdos1135.ND.Discrepancy.A5ReferenceInteriorRate

/-!
# A5 full reference center rate

This leaf consumes the strict exterior CommonZ rate together with the global
physical profile envelope.  It charges both the exterior profile and the
omitted exterior center, then splices that one-rate exterior row with the
checked factor-five interior row at the same scheduled reference level.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped Topology

noncomputable section

/-- The branch-, band-, and law-independent common reference profile. -/
noncomputable def ndA5ReferenceCommonProfile
    (B : ℕ) (E : Set ℕ) : ℝ :=
  (2 / ndA5LogFourThirds) *
    Tao.taoSection5PayloadFreeCommonZ (ndA5ReferenceLevel B)
      (Tao.taoSection5EPrime B E)

private theorem two_div_ndA5LogFourThirds_le_eight :
    (2 / ndA5LogFourThirds : ℝ) ≤ 8 := by
  have hquarter : (1 / 4 : ℝ) ≤ ndA5LogFourThirds := by
    unfold ndA5LogFourThirds
    have h := Real.one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < 4 / 3 by norm_num)
    norm_num at h ⊢
    exact h
  apply (div_le_iff₀ ndA5LogFourThirds_pos).2
  nlinarith

/-- The common profile is eventually a nonnegative absolute quantity bounded
by forty, uniformly in the endpoint event. -/
theorem eventually_ndA5ReferenceCommonProfile_mem_Icc_forty :
    ∀ᶠ B : ℕ in atTop,
      ∀ E : Set ℕ, ndA5ReferenceCommonProfile B E ∈ Set.Icc (0 : ℝ) 40 := by
  filter_upwards
      [Tao.eventually_taoSection5PassLostWindowFacts,
        Tao.eventually_taoSection5PassScheduleFacts,
        eventually_ndA5ReferenceLevel_integer_room]
      with B lost schedule hroom
  intro E
  have hindex :
      Tao.taoSection5M0 B + ndA5ReferenceLevel B ≤
        Tao.taoSection5N0 B := by
    obtain ⟨n, hn⟩ := schedule.nonempty Tao.TaoSection5SourceBranch.alpha
    have hrange := schedule.range Tao.TaoSection5SourceBranch.alpha n hn
    have htwo :
        2 * Tao.taoSection5M0 B ≤ Tao.taoSection5N0 B :=
      hrange.1.trans hrange.2
    omega
  have hZ :=
    Tao.taoSection5PayloadFreeCommonZ_ePrime_mem_Icc_five
      lost (E := E) hindex
  have ha0 : (0 : ℝ) ≤ 2 / ndA5LogFourThirds := by
    exact div_nonneg (by norm_num) ndA5LogFourThirds_pos.le
  unfold ndA5ReferenceCommonProfile
  constructor
  · exact mul_nonneg ha0 hZ.1
  · calc
      (2 / ndA5LogFourThirds) *
          Tao.taoSection5PayloadFreeCommonZ (ndA5ReferenceLevel B)
            (Tao.taoSection5EPrime B E) ≤
        8 * 5 :=
          mul_le_mul two_div_ndA5LogFourThirds_le_eight hZ.2 hZ.1
            (by norm_num)
      _ = 40 := by norm_num

private theorem eventually_ndA5ReferenceExteriorCharge_le_interiorScalarRate
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C)
    {d : ℝ} (hd2 : d < 2) :
    ∀ᶠ B : ℕ in atTop,
      (ndA5ReferenceExteriorProfileEnvelope B C +
          2 / ndA5LogFourThirds) *
          Real.rpow (Real.log B) (-3 : ℝ) ≤
        ndA5ReferenceInteriorScalarRate B d := by
  have hCpos : 0 < C := by linarith
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hN :
      Tendsto (fun B : ℕ => (Tao.taoSection5N0 B : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ndTendsto_taoSection5N0_atTop
  filter_upwards
      [eventually_three_mul_ndA5TubeWidth_le_log C hCpos,
        hN.eventually_ge_atTop (1 : ℝ),
        hlog.eventually_ge_atTop (1 : ℝ),
        hlog.eventually_ge_atTop (4 / ndA5LogFourThirds)]
      with B hpadding hNone hLOne hLcenter
  let L : ℝ := Real.log B
  let N : ℝ := Tao.taoSection5N0 B
  let W : ℝ := ndA5TubeWidth B C
  have hLpos : 0 < L := by
    dsimp only [L]
    exact zero_lt_one.trans_le hLOne
  have hNreal : (1 : ℝ) ≤ N := by simpa only [N] using hNone
  have hsqrtNone : (1 : ℝ) ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]
    exact hNreal
  have hsqrtNpos : 0 < Real.sqrt N := zero_lt_one.trans_le hsqrtNone
  have hW0 : 0 ≤ W := by
    dsimp only [W, ndA5TubeWidth]
    exact mul_nonneg hCpos.le (Real.sqrt_nonneg _)
  have hEnvLe :
      ndA5ReferenceExteriorProfileEnvelope B C ≤ 672 * W := by
    unfold ndA5ReferenceExteriorProfileEnvelope
    change 672 * W / Real.sqrt N ≤ 672 * W
    apply (div_le_iff₀ hsqrtNpos).2
    calc
      672 * W = (672 * W) * 1 := by ring
      _ ≤ (672 * W) * Real.sqrt N :=
        mul_le_mul_of_nonneg_left hsqrtNone
          (mul_nonneg (by norm_num) hW0)
  have hWLe : W ≤ (11 / 500000 : ℝ) * L := by
    simpa only [W, L] using (by nlinarith [hpadding] :
      ndA5TubeWidth B C ≤ (11 / 500000 : ℝ) * Real.log B)
  have hEnvHalf :
      ndA5ReferenceExteriorProfileEnvelope B C ≤ L / 2 := by
    calc
      ndA5ReferenceExteriorProfileEnvelope B C ≤ 672 * W := hEnvLe
      _ ≤ 672 * ((11 / 500000 : ℝ) * L) :=
        mul_le_mul_of_nonneg_left hWLe (by norm_num)
      _ ≤ L / 2 := by nlinarith [hLpos]
  have hcenterHalf : (2 / ndA5LogFourThirds : ℝ) ≤ L / 2 := by
    have hscaled : (4 : ℝ) ≤ L * ndA5LogFourThirds :=
      (div_le_iff₀ ndA5LogFourThirds_pos).mp
        (by simpa only [L] using hLcenter)
    apply (div_le_iff₀ ndA5LogFourThirds_pos).2
    nlinarith
  have hcharge :
      ndA5ReferenceExteriorProfileEnvelope B C +
          2 / ndA5LogFourThirds ≤ L := by
    linarith
  have hrpow0 : 0 ≤ Real.rpow L (-3 : ℝ) := by
    simpa only [Real.rpow_eq_pow] using
      Real.rpow_nonneg hLpos.le (-3 : ℝ)
  have hfactor :
      L * Real.rpow L (-3 : ℝ) = Real.rpow L (-2 : ℝ) := by
    calc
      L * Real.rpow L (-3 : ℝ) =
          Real.rpow L (1 : ℝ) * Real.rpow L (-3 : ℝ) := by
            congr 1
            simpa only [Real.rpow_eq_pow] using (Real.rpow_one L).symm
      _ = Real.rpow L ((1 : ℝ) + (-3 : ℝ)) :=
        (Real.rpow_add hLpos _ _).symm
      _ = Real.rpow L (-2 : ℝ) := by norm_num
  calc
    (ndA5ReferenceExteriorProfileEnvelope B C +
          2 / ndA5LogFourThirds) *
          Real.rpow (Real.log B) (-3 : ℝ) =
        (ndA5ReferenceExteriorProfileEnvelope B C +
          2 / ndA5LogFourThirds) * Real.rpow L (-3 : ℝ) := by rfl
    _ ≤ L * Real.rpow L (-3 : ℝ) :=
      mul_le_mul_of_nonneg_right hcharge hrpow0
    _ = Real.rpow L (-2 : ℝ) := hfactor
    _ ≤ Real.rpow L (-d) := by
      simpa only [Real.rpow_eq_pow] using
        Real.rpow_le_rpow_of_exponent_le hLOne (by linarith : (-2 : ℝ) ≤ -d)
    _ = ndA5ReferenceInteriorScalarRate B d := by
      rfl

private theorem abs_sub_mul_le_add_mul
    {P Z Env a : ℝ}
    (hP0 : 0 ≤ P) (hP : P ≤ Env * Z)
    (hZ0 : 0 ≤ Z) (ha0 : 0 ≤ a) :
    |P - a * Z| ≤ (Env + a) * Z := by
  calc
    |P - a * Z| = |P + -(a * Z)| := by ring
    _ ≤ |P| + |-(a * Z)| := abs_add_le _ _
    _ = P + a * Z := by
      rw [abs_of_nonneg hP0, abs_neg, abs_of_nonneg (mul_nonneg ha0 hZ0)]
    _ ≤ Env * Z + a * Z := add_le_add hP le_rfl
    _ = (Env + a) * Z := by ring

/-- The exterior physical profile and its omitted exterior center together
fit inside one copy of the interior scalar rate. -/
theorem eventually_ndA5ReferenceExteriorPhysicalDecay_referenceLevel_le_one
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C)
    {d : ℝ} (hd2 : d < 2) :
    ∀ᶠ B : ℕ in atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch) (j : ℕ) (E : Set ℕ),
        j < ndA5BandCount B branch →
          (|ndA5HarmonicReferenceExteriorPhysicalProfile B
                (ndA5ReferenceLevel B) branch C j E -
              (2 / ndA5LogFourThirds) *
                Tao.taoSection5PayloadFreeCommonZ (ndA5ReferenceLevel B)
                  (ndA5ReferenceExteriorEndpoints B C E)| ≤
            ndA5ReferenceInteriorScalarRate B d) ∧
          (|ndA5FlatReferenceExteriorPhysicalProfile B
                (ndA5ReferenceLevel B) branch C j E -
              (2 / ndA5LogFourThirds) *
                Tao.taoSection5PayloadFreeCommonZ (ndA5ReferenceLevel B)
                  (ndA5ReferenceExteriorEndpoints B C E)| ≤
            ndA5ReferenceInteriorScalarRate B d) := by
  have hCpos : 0 < C := by linarith
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [eventually_ndA5ReferenceExteriorCommonZ_mem_Icc_log_rpow_neg_three
          C hC,
        eventually_ndA5ReferenceExteriorCharge_le_interiorScalarRate C hC hd2,
        eventually_three_mul_ndA5TubeWidth_le_log C hCpos,
        hlog.eventually_ge_atTop (300000 : ℝ),
        eventually_ge_atTop (1 : ℕ)]
      with B hZ hscalar hpadding hlogB hB
  intro branch j E hj
  let Z : ℝ := Tao.taoSection5PayloadFreeCommonZ
    (ndA5ReferenceLevel B) (ndA5ReferenceExteriorEndpoints B C E)
  let Env : ℝ := ndA5ReferenceExteriorProfileEnvelope B C
  let a : ℝ := 2 / ndA5LogFourThirds
  have hZE : Z ∈ Set.Icc (0 : ℝ) (Real.rpow (Real.log B) (-3 : ℝ)) := by
    simpa only [Z] using hZ E
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    exact div_nonneg (by norm_num) ndA5LogFourThirds_pos.le
  have hEnv0 : 0 ≤ Env := by
    dsimp only [Env, ndA5ReferenceExteriorProfileEnvelope]
    exact div_nonneg
      (mul_nonneg (by norm_num) (by
        unfold ndA5TubeWidth
        exact mul_nonneg hCpos.le (Real.sqrt_nonneg _)))
      (Real.sqrt_nonneg _)
  have hcharge0 : 0 ≤ Env + a := add_nonneg hEnv0 ha0
  have hH0 :=
    ndA5HarmonicReferenceExteriorPhysicalProfile_nonneg B branch C j E
  have hF0 :=
    ndA5FlatReferenceExteriorPhysicalProfile_nonneg B branch C j E
  have hH :=
    ndA5HarmonicReferenceExteriorPhysicalProfile_le_envelope_mul_commonZ
      hB hlogB hC hpadding hj (E := E)
  have hF :=
    ndA5FlatReferenceExteriorPhysicalProfile_le_envelope_mul_commonZ
      hB hlogB hC hpadding hj (E := E)
  have hHcenter :
      |ndA5HarmonicReferenceExteriorPhysicalProfile B
            (ndA5ReferenceLevel B) branch C j E - a * Z| ≤
        (Env + a) * Z := by
    exact abs_sub_mul_le_add_mul hH0 (by simpa only [Env, Z] using hH)
      hZE.1 ha0
  have hFcenter :
      |ndA5FlatReferenceExteriorPhysicalProfile B
            (ndA5ReferenceLevel B) branch C j E - a * Z| ≤
        (Env + a) * Z := by
    exact abs_sub_mul_le_add_mul hF0 (by simpa only [Env, Z] using hF)
      hZE.1 ha0
  have hrate :
      (Env + a) * Z ≤ ndA5ReferenceInteriorScalarRate B d := by
    calc
      (Env + a) * Z ≤
          (Env + a) * Real.rpow (Real.log B) (-3 : ℝ) :=
        mul_le_mul_of_nonneg_left hZE.2 hcharge0
      _ ≤ ndA5ReferenceInteriorScalarRate B d := by
        simpa only [Env, a] using hscalar
  simpa only [a, Z] using ⟨hHcenter.trans hrate, hFcenter.trans hrate⟩

private theorem abs_full_center_le
    {PInt PExt ZInt ZExt a eInt eExt : ℝ}
    (hInt : |PInt - a * ZInt| ≤ eInt)
    (hExt : |PExt - a * ZExt| ≤ eExt) :
    |(PInt + PExt) - a * (ZInt + ZExt)| ≤ eInt + eExt := by
  calc
    |(PInt + PExt) - a * (ZInt + ZExt)| =
        |(PInt - a * ZInt) + (PExt - a * ZExt)| := by ring
    _ ≤ |PInt - a * ZInt| + |PExt - a * ZExt| := abs_add_le _ _
    _ ≤ eInt + eExt := add_le_add hInt hExt

/-- Both full scheduled reference profiles are centered at the same
branch-, band-, and law-independent CommonZ profile with factor six. -/
theorem eventually_ndA5ReferenceFullPhysicalDecay_referenceLevel_le_six
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C)
    {c kappa d : ℝ}
    (hPhase : PhaseGap c kappa)
    (hd : 0 < d) (hdk : d < 1 / (2 * kappa)) :
    ∀ᶠ B : ℕ in atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch) (j : ℕ) (E : Set ℕ),
        j < ndA5BandCount B branch →
          (|ndA5HarmonicReferencePhysicalProfile B
                (ndA5ReferenceLevel B) branch C j E -
              ndA5ReferenceCommonProfile B E| ≤
            6 * ndA5ReferenceInteriorScalarRate B d) ∧
          (|ndA5FlatReferencePhysicalProfile B
                (ndA5ReferenceLevel B) branch C j E -
              ndA5ReferenceCommonProfile B E| ≤
            6 * ndA5ReferenceInteriorScalarRate B d) := by
  have hkappa : 0 < kappa := by linarith [hPhase.two_lt_kappa]
  have hfrac : 1 / (2 * kappa) < 2 := by
    apply (div_lt_iff₀ (mul_pos (by norm_num) hkappa)).2
    nlinarith [hPhase.two_lt_kappa]
  have hd2 : d < 2 := hdk.trans hfrac
  filter_upwards
      [eventually_ndA5ReferenceInteriorDecay_referenceLevel_le_five
          C hC hPhase hd hdk,
        eventually_ndA5ReferenceExteriorPhysicalDecay_referenceLevel_le_one
          C hC hd2]
      with B hInt hExt
  intro branch j E hj
  have hIntPair := hInt branch j E hj
  have hExtPair := hExt branch j E hj
  have hIntPair' :
      (|ndA5HarmonicReferenceInteriorPhysicalProfile B
            (ndA5ReferenceLevel B) branch C j E -
          (2 / ndA5LogFourThirds) *
            Tao.taoSection5PayloadFreeCommonZ (ndA5ReferenceLevel B)
              (ndA5ReferenceInteriorEndpoints B C E)| ≤
        5 * ndA5ReferenceInteriorScalarRate B d) ∧
      (|ndA5FlatReferenceInteriorPhysicalProfile B
            (ndA5ReferenceLevel B) branch C j E -
          (2 / ndA5LogFourThirds) *
            Tao.taoSection5PayloadFreeCommonZ (ndA5ReferenceLevel B)
              (ndA5ReferenceInteriorEndpoints B C E)| ≤
        5 * ndA5ReferenceInteriorScalarRate B d) := by
    simpa only [ndA5HarmonicReferenceInteriorPhysicalProfile,
      ndA5FlatReferenceInteriorPhysicalProfile] using hIntPair
  constructor
  · calc
      |ndA5HarmonicReferencePhysicalProfile B
            (ndA5ReferenceLevel B) branch C j E -
          ndA5ReferenceCommonProfile B E| =
        |(ndA5HarmonicReferenceInteriorPhysicalProfile B
              (ndA5ReferenceLevel B) branch C j E +
            ndA5HarmonicReferenceExteriorPhysicalProfile B
              (ndA5ReferenceLevel B) branch C j E) -
          (2 / ndA5LogFourThirds) *
            (Tao.taoSection5PayloadFreeCommonZ (ndA5ReferenceLevel B)
                (ndA5ReferenceInteriorEndpoints B C E) +
              Tao.taoSection5PayloadFreeCommonZ (ndA5ReferenceLevel B)
                (ndA5ReferenceExteriorEndpoints B C E))| := by
          rw [ndA5HarmonicReferencePhysicalProfile_eq_interior_add_exterior,
            ndA5ReferenceCommonProfile,
            ndA5ReferenceCommonZ_ePrime_eq_interior_add_exterior]
      _ ≤ 5 * ndA5ReferenceInteriorScalarRate B d +
          ndA5ReferenceInteriorScalarRate B d :=
        abs_full_center_le hIntPair'.1 hExtPair.1
      _ = 6 * ndA5ReferenceInteriorScalarRate B d := by ring
  · calc
      |ndA5FlatReferencePhysicalProfile B
            (ndA5ReferenceLevel B) branch C j E -
          ndA5ReferenceCommonProfile B E| =
        |(ndA5FlatReferenceInteriorPhysicalProfile B
              (ndA5ReferenceLevel B) branch C j E +
            ndA5FlatReferenceExteriorPhysicalProfile B
              (ndA5ReferenceLevel B) branch C j E) -
          (2 / ndA5LogFourThirds) *
            (Tao.taoSection5PayloadFreeCommonZ (ndA5ReferenceLevel B)
                (ndA5ReferenceInteriorEndpoints B C E) +
              Tao.taoSection5PayloadFreeCommonZ (ndA5ReferenceLevel B)
                (ndA5ReferenceExteriorEndpoints B C E))| := by
          rw [ndA5FlatReferencePhysicalProfile_eq_interior_add_exterior,
            ndA5ReferenceCommonProfile,
            ndA5ReferenceCommonZ_ePrime_eq_interior_add_exterior]
      _ ≤ 5 * ndA5ReferenceInteriorScalarRate B d +
          ndA5ReferenceInteriorScalarRate B d :=
        abs_full_center_le hIntPair'.2 hExtPair.2
      _ = 6 * ndA5ReferenceInteriorScalarRate B d := by ring

end
end ND
end Erdos1135
