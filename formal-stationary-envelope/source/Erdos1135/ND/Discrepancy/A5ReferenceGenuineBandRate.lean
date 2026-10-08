/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
import Erdos1135.ND.Discrepancy.A5ReferenceTerminalAggregateRate
import Erdos1135.ND.Discrepancy.A5ReferenceFullCenterRate
import Erdos1135.ND.Discrepancy.A5BandCoverageRate
import Erdos1135.ND.Band.A5NominalTotalCap
import Erdos1135.ND.Band.A5PaddedBandDiameter

/-!
# Genuine A5 band passage rate at the common center

This leaf composes terminal coverage, weighted nominalization, scheduled
reference aggregation, and the full interior/exterior common-center estimate.
The public endpoint is one positive-width half-open band at the fixed
conservative tube constant `C = 40`.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped BigOperators Topology

noncomputable section

private theorem ndPMFEventMass_toReal_le_one_genuine
    {Omega : Type*} (mu : PMF Omega) (S : Set Omega) :
    (mu.toOuterMeasure S).toReal ≤ 1 := by
  have huniv : mu.toOuterMeasure Set.univ = 1 :=
    (mu.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
  have hmono :
      (mu.toOuterMeasure S).toReal ≤
        (mu.toOuterMeasure Set.univ).toReal :=
    ENNReal.toReal_mono (by simp [huniv])
      (mu.toOuterMeasure.mono (Set.subset_univ S))
  simpa [huniv] using hmono

private theorem eventually_const_mul_nat_rpow_neg_le_log_rate
    {K a d epsilon : ℝ}
    (_hK : 0 < K) (ha : 0 < a) (hepsilon : 0 < epsilon) :
    ∀ᶠ B : ℕ in atTop,
      K * Real.rpow (B : ℝ) (-a) ≤
        epsilon * Real.rpow (Real.log B) (-d) := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdecay :
      Tendsto
        (fun L : ℝ =>
          K * (Real.rpow L d * Real.exp (-a * L)))
        atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero d a ha).const_mul K
  have hsmall :
      ∀ᶠ B : ℕ in atTop,
        K * (Real.rpow (Real.log B) d *
          Real.exp (-a * Real.log B)) ≤ epsilon :=
    (hdecay.comp hlog).eventually_le_const hepsilon
  filter_upwards
      [hlog.eventually_ge_atTop (1 : ℝ), hsmall,
        Filter.eventually_ge_atTop (1 : ℕ)]
      with B hlogOne hsmallB hBOne
  let L : ℝ := Real.log B
  have hLpos : 0 < L := zero_lt_one.trans_le hlogOne
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hBOne
  have hpowPos : 0 < Real.rpow L d := Real.rpow_pos_of_pos hLpos _
  have hscaled :
      (K * Real.exp (-a * L)) * Real.rpow L d ≤ epsilon := by
    calc
      (K * Real.exp (-a * L)) * Real.rpow L d =
          K * (Real.rpow L d * Real.exp (-a * L)) := by ring
      _ ≤ epsilon := by simpa only [L] using hsmallB
  have hdiv :
      K * Real.exp (-a * L) ≤ epsilon / Real.rpow L d :=
    (le_div_iff₀ hpowPos).2 hscaled
  have hneg :
      Real.rpow L (-d) = (Real.rpow L d)⁻¹ := by
    simpa only using Real.rpow_neg hLpos.le d
  calc
    K * (B : ℝ) ^ (-a) =
        K * Real.exp (-a * L) := by
      rw [Real.rpow_def_of_pos hBpos]
      congr 1
      dsimp only [L]
      ring
    _ ≤ epsilon / Real.rpow L d := hdiv
    _ = epsilon * Real.rpow L (-d) := by
      rw [hneg]
      simp only [div_eq_mul_inv]
    _ = epsilon * Real.rpow (Real.log B) (-d) := by rfl

private theorem eventually_const_mul_log_rpow_neg_le_genuine
    {K e d epsilon : ℝ}
    (_hK : 0 < K) (hde : d < e) (hepsilon : 0 < epsilon) :
    ∀ᶠ B : ℕ in atTop,
      K * Real.rpow (Real.log B) (-e) ≤
        epsilon * Real.rpow (Real.log B) (-d) := by
  let delta : ℝ := e - d
  have hdelta : 0 < delta := by
    dsimp only [delta]
    linarith
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdecay :
      Tendsto
        (fun B : ℕ => K * Real.rpow (Real.log B) (-delta))
        atTop (nhds 0) := by
    simpa only [mul_zero] using
      ((tendsto_rpow_neg_atTop hdelta).comp hlog).const_mul K
  filter_upwards
      [hlog.eventually_ge_atTop (1 : ℝ),
        hdecay.eventually_le_const hepsilon]
      with B hlogOne hsmall
  let L : ℝ := Real.log B
  have hLpos : 0 < L := zero_lt_one.trans_le hlogOne
  have hfactor :
      Real.rpow L (-e) =
        Real.rpow L (-delta) * Real.rpow L (-d) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hLpos]
    congr 1
    dsimp only [delta]
    ring
  rw [hfactor]
  calc
    K * (Real.rpow L (-delta) * Real.rpow L (-d)) =
        (K * Real.rpow L (-delta)) * Real.rpow L (-d) := by ring
    _ ≤ epsilon * Real.rpow L (-d) :=
      mul_le_mul_of_nonneg_right (by simpa only [L] using hsmall)
        (Real.rpow_nonneg hLpos.le _)

private theorem eventually_log_rpow_neg_ten_le_rate_quarter
    {d : ℝ} (hd20 : d < 1 / 20) :
    ∀ᶠ B : ℕ in atTop,
      Real.rpow (Real.log B) (-10 : ℝ) ≤
        (1 / 4 : ℝ) * ndA5ReferenceInteriorScalarRate B d := by
  simpa only [ndA5ReferenceInteriorScalarRate, one_mul] using
    (eventually_const_mul_log_rpow_neg_le_genuine
      (K := (1 : ℝ)) (e := (10 : ℝ)) (d := d)
      (epsilon := (1 / 4 : ℝ)) (by norm_num)
      (hd20.trans (by norm_num)) (by norm_num))

private theorem eventually_eleven_mul_nat_rpow_neg_le_rate_half
    {d : ℝ} :
    ∀ᶠ B : ℕ in atTop,
      11 * Real.rpow (B : ℝ) (-(9 / 10 : ℝ)) ≤
        (1 / 2 : ℝ) * ndA5ReferenceInteriorScalarRate B d := by
  simpa only [ndA5ReferenceInteriorScalarRate] using
    (eventually_const_mul_nat_rpow_neg_le_log_rate
      (K := (11 : ℝ)) (a := (9 / 10 : ℝ)) (d := d)
      (epsilon := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num))

private theorem ten_mul_ndA5TubeWidth_le_n0_of_guards
    {B : ℕ} {C : ℝ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B) :
    10 * ndA5TubeWidth B C ≤ (Tao.taoSection5N0 B : ℝ) := by
  let L : ℝ := Real.log B
  let N : ℝ := Tao.taoSection5N0 B
  have hL0 : 0 ≤ L := by dsimp only [L]; linarith
  have hell : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hellOne : Real.log (2 : ℝ) < 1 := by
    have h := Real.log_lt_sub_one_of_pos
      (show (0 : ℝ) < 2 by norm_num) (show (2 : ℝ) ≠ 1 by norm_num)
    norm_num at h ⊢
    exact h
  have hdiv : L / 10 ≤ L / (10 * Real.log 2) := by
    apply (div_le_div_iff₀ (by norm_num) (mul_pos (by norm_num) hell)).2
    nlinarith
  have hNraw := Tao.log_div_ten_log_two_sub_one_lt_taoSection5N0 B
  have hLN : L / 20 ≤ N := by
    dsimp only [L, N] at hNraw ⊢
    nlinarith
  have hwidth : 10 * ndA5TubeWidth B C ≤ (11 / 50000 : ℝ) * L := by
    dsimp only [L] at hpadding ⊢
    nlinarith
  calc
    10 * ndA5TubeWidth B C ≤ (11 / 50000 : ℝ) * L := hwidth
    _ ≤ L / 20 := by nlinarith
    _ ≤ N := hLN

/-- At the fixed conservative width, the genuine harmonic and flat passage
masses of every valid positive-width half-open A5 band share the same CommonZ
center with factor seven.  The eta loss and PhaseGap loss remain separate
strict exponent hypotheses. -/
theorem eventually_ndA5GenuineBandPassDecay_referenceLevel_le_seven
    {c kappa d : ℝ}
    (hPhase : PhaseGap c kappa)
    (hd : 0 < d) (hd20 : d < 1 / 20)
    (hdk : d < 1 / (2 * kappa)) :
    ∀ᶠ B : ℕ in atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch) (j : ℕ) (E : Set ℕ)
        (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch),
        j < ndA5BandCount B branch →
          (|((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure
                (Tao.taoSection5PassEvent B E)).toReal -
              ndA5ReferenceCommonProfile B E| ≤
            7 * ndA5ReferenceInteriorScalarRate B d) ∧
          (|((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure
                (Tao.taoSection5PassEvent B E)).toReal -
              ndA5ReferenceCommonProfile B E| ≤
            7 * ndA5ReferenceInteriorScalarRate B d) := by
  let C : ℝ := 40
  have hC40 : (40 : ℝ) ≤ C := by rfl
  have hChalf : (1 / 2 : ℝ) ≤ C := by dsimp only [C]; norm_num
  have hCpos : 0 < C := by positivity
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [Tao.eventually_taoSection5AffineSourceScaleFacts,
        Tao.eventually_taoSection5DescentScaleFacts,
        Tao.eventually_taoSection5PassTimeLocalizationFacts,
        Tao.eventually_taoSection5PassLostWindowFacts,
        Tao.eventually_taoSection5ReversePrefixScalarBudget,
        hlog.eventually_ge_atTop (300000 : ℝ),
        eventually_three_mul_ndA5TubeWidth_le_log C hCpos,
        eventually_ndA5TubeWidth_le_taoSection5TypicalSlack C hCpos,
        eventually_ndA5M0_lt_of_mem_paddedBandWindow C hChalf,
        eventually_ndA5PaddedBandWindow_diameter_le_m0 C hChalf,
        eventually_abs_ndA5HarmonicBandPassMass_sub_terminalAtomUnionMass_le_quarter_log_rpow_neg_ten
          C hC40,
        eventually_abs_ndA5FlatBandPassMass_sub_terminalAtomUnionMass_lt_log_rpow_neg_ten
          C hC40,
        eventually_abs_ndA5ReferenceTerminalNominalSums_sub_physicalProfiles_le_rate
          C hChalf hd hd20 (by norm_num : (0 : ℝ) < 1 / 4),
        eventually_ndA5ReferenceFullPhysicalDecay_referenceLevel_le_six
          C hChalf hPhase hd hdk,
        eventually_log_rpow_neg_ten_le_rate_quarter hd20,
        eventually_eleven_mul_nat_rpow_neg_le_rate_half (d := d)]
      with B facts descent time lost budget hlogB hpadding hwidth htime hdiam
        hcoverageH hcoverageF haggregate hcenter hlogRate hpolyRate
  intro branch j E hB hcount hj
  let muH := ndA5HarmonicBandPMF B branch j hB hcount
  let muF := ndA5FlatBandPMF B branch j hB hcount
  let G_H := (muH.toOuterMeasure (Tao.taoSection5PassEvent B E)).toReal
  let G_F := (muF.toOuterMeasure (Tao.taoSection5PassEvent B E)).toReal
  let U_H := (muH.toOuterMeasure
    (ndA5TerminalAtomUnion B branch C j E)).toReal
  let U_F := (muF.toOuterMeasure
    (ndA5TerminalAtomUnion B branch C j E)).toReal
  let I_H := ∑ i : NDA5TerminalAtomIndex B branch C j E,
    ndA5HarmonicTerminalAtomNominalIdealMass i
  let I_F := ∑ i : NDA5TerminalAtomIndex B branch C j E,
    ndA5FlatTerminalAtomNominalIdealMass i
  let P_H := ndA5HarmonicReferencePhysicalProfile B
    (ndA5ReferenceLevel B) branch C j E
  let P_F := ndA5FlatReferencePhysicalProfile B
    (ndA5ReferenceLevel B) branch C j E
  let Z := ndA5ReferenceCommonProfile B E
  let R := ndA5ReferenceInteriorScalarRate B d
  have hWn0 : 10 * ndA5TubeWidth B C ≤ (Tao.taoSection5N0 B : ℝ) :=
    ten_mul_ndA5TubeWidth_le_n0_of_guards hlogB hpadding
  have hWlarge : 6 ≤ ndA5TubeWidth B C := by
    linarith [ndA5TubeWidth_ge_one_hundred_forty_two hChalf hlogB]
  have hcoverH : |G_H - U_H| ≤ (1 / 4 : ℝ) *
      Real.rpow (Real.log B) (-10 : ℝ) := by
    simpa only [G_H, U_H, muH] using
      hcoverageH branch j E hB hcount descent time lost budget hlogB
        hpadding hWn0 hWlarge hwidth hj
  have hcoverF : |G_F - U_F| ≤
      Real.rpow (Real.log B) (-10 : ℝ) := by
    exact (by
      simpa only [G_F, U_F, muF] using
        (hcoverageF branch j E hB hcount descent time lost budget hlogB
          hpadding hWn0 hWlarge hwidth hj).le)
  have ht2 : ∀ i : NDA5TerminalAtomIndex B branch C j E,
      NDA5T2ScaleFacts B i.1.1 C := by
    intro i
    exact ndA5PaddedBandWindow_t2_of_guards
      hB hlogB hpadding hj i.1.2
  have htime' : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      Tao.taoSection5M0 B < n := htime branch j hj
  have hdiam' : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      ∀ n' ∈ ndA5PaddedBandWindow B branch C j,
        n ≤ n' → n' - n ≤ Tao.taoSection5M0 B := hdiam branch j hj
  have hnomHraw :=
    ndA5HarmonicTerminalAtomUnionMass_sub_nominalIdealSum_abs_le
      (E := E) facts hlogB hcount ht2 htime' hdiam'
  have hnomFraw :=
    abs_ndA5FlatTerminalAtomUnionMass_sub_nominalIdealSum_lt
      (E := E) facts hlogB hcount ht2 htime' hdiam'
  have hUH : U_H ≤ 1 := ndPMFEventMass_toReal_le_one_genuine muH _
  have hbase : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hstrong : Real.rpow (B : ℝ) (-(19749 / 20000 : ℝ)) ≤
      Real.rpow (B : ℝ) (-(9 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
  have heps0 : 0 ≤ Real.rpow (B : ℝ) (-(9 / 10 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hnomH : |U_H - I_H| ≤
      11 * Real.rpow (B : ℝ) (-(9 / 10 : ℝ)) := by
    have hmass :
        Real.rpow (B : ℝ) (-(19749 / 20000 : ℝ)) * U_H ≤
          Real.rpow (B : ℝ) (-(9 / 10 : ℝ)) := by
      calc
        Real.rpow (B : ℝ) (-(19749 / 20000 : ℝ)) * U_H ≤
            Real.rpow (B : ℝ) (-(19749 / 20000 : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hUH (Real.rpow_nonneg (by positivity) _)
        _ ≤ Real.rpow (B : ℝ) (-(9 / 10 : ℝ)) := by simpa using hstrong
    have hraw : |U_H - I_H| ≤
        Real.rpow (B : ℝ) (-(19749 / 20000 : ℝ)) * U_H +
          5 * Real.rpow (B : ℝ) (-(9 / 10 : ℝ)) := by
      simpa only [U_H, I_H, muH] using hnomHraw
    linarith
  have hnomF : |U_F - I_F| ≤
      11 * Real.rpow (B : ℝ) (-(9 / 10 : ℝ)) := by
    simpa only [U_F, I_F, muF] using hnomFraw.le
  have hagg := haggregate branch j E hj
  have haggH : |I_H - P_H| ≤ (1 / 4 : ℝ) * R := by
    simpa only [I_H, P_H, R] using hagg.1
  have haggF : |I_F - P_F| ≤ (1 / 4 : ℝ) * R := by
    simpa only [I_F, P_F, R] using hagg.2
  have hcenterPair := hcenter branch j E hj
  have hcenterH : |P_H - Z| ≤ 6 * R := by
    simpa only [P_H, Z, R] using hcenterPair.1
  have hcenterF : |P_F - Z| ≤ 6 * R := by
    simpa only [P_F, Z, R] using hcenterPair.2
  have hlogRate' : Real.rpow (Real.log B) (-10 : ℝ) ≤
      (1 / 4 : ℝ) * R := by simpa only [R] using hlogRate
  have hpolyRate' : 11 * Real.rpow (B : ℝ) (-(9 / 10 : ℝ)) ≤
      (1 / 2 : ℝ) * R := by simpa only [R] using hpolyRate
  constructor
  · calc
      |G_H - Z| = |(G_H - U_H) + (U_H - I_H) +
          (I_H - P_H) + (P_H - Z)| := by ring
      _ ≤ |G_H - U_H| + |U_H - I_H| +
          |I_H - P_H| + |P_H - Z| := by
        calc
          |(G_H - U_H) + (U_H - I_H) + (I_H - P_H) + (P_H - Z)| ≤
              |(G_H - U_H) + (U_H - I_H) + (I_H - P_H)| +
                |P_H - Z| := abs_add_le _ _
          _ ≤ (|(G_H - U_H) + (U_H - I_H)| + |I_H - P_H|) +
                |P_H - Z| := add_le_add (abs_add_le _ _) le_rfl
          _ ≤ (|G_H - U_H| + |U_H - I_H| + |I_H - P_H|) +
                |P_H - Z| :=
            add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
      _ ≤ ((1 / 4 : ℝ) * R + (1 / 2 : ℝ) * R +
          (1 / 4 : ℝ) * R) + 6 * R := by
        gcongr
        · exact hcoverH.trans (by nlinarith [hlogRate'])
        · exact hnomH.trans hpolyRate'
      _ = 7 * R := by ring
  · calc
      |G_F - Z| = |(G_F - U_F) + (U_F - I_F) +
          (I_F - P_F) + (P_F - Z)| := by ring
      _ ≤ |G_F - U_F| + |U_F - I_F| +
          |I_F - P_F| + |P_F - Z| := by
        calc
          |(G_F - U_F) + (U_F - I_F) + (I_F - P_F) + (P_F - Z)| ≤
              |(G_F - U_F) + (U_F - I_F) + (I_F - P_F)| +
                |P_F - Z| := abs_add_le _ _
          _ ≤ (|(G_F - U_F) + (U_F - I_F)| + |I_F - P_F|) +
                |P_F - Z| := add_le_add (abs_add_le _ _) le_rfl
          _ ≤ (|G_F - U_F| + |U_F - I_F| + |I_F - P_F|) +
                |P_F - Z| :=
            add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
      _ ≤ ((1 / 4 : ℝ) * R + (1 / 2 : ℝ) * R +
          (1 / 4 : ℝ) * R) + 6 * R := by
        gcongr
        · exact hcoverF.trans hlogRate'
        · exact hnomF.trans hpolyRate'
      _ = 7 * R := by ring

theorem eventually_one_hundred_sixty_div_natCast_le_ndA5ReferenceInteriorScalarRate
    (d : ℝ) :
    ∀ᶠ B : ℕ in atTop,
      160 * Real.rpow (B : ℝ) (-1) ≤
        ndA5ReferenceInteriorScalarRate B d := by
  simpa only [ndA5ReferenceInteriorScalarRate, one_mul] using
    (eventually_const_mul_nat_rpow_neg_le_log_rate
      (K := (160 : ℝ)) (a := (1 : ℝ)) (d := d)
      (epsilon := (1 : ℝ)) (by norm_num) (by norm_num) (by norm_num))

end
end ND
end Erdos1135
