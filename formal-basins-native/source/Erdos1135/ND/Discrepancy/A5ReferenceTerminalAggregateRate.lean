import Erdos1135.ND.Discrepancy.A5ReferenceInteriorRate
import Erdos1135.ND.Band.A5ReferenceEtaRate

/-!
# Scalar rate for the A5 terminal aggregate

This leaf absorbs the common reference-cell eta error and both conditioned-FM1
nonproportional rows into an arbitrary fraction of the interior logarithmic
rate.  The strict exponent loss `d < 1 / 20` is visible: it comes from the
slowest term in the checked eta envelope.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped Topology

noncomputable section

private theorem rpow_nat_pow_eq_rpow_mul
    {x : ℝ} (hx : 0 ≤ x) (a : ℝ) (n : ℕ) :
    Real.rpow x a ^ n = Real.rpow x (a * (n : ℝ)) := by
  calc
    Real.rpow x a ^ n =
        Real.rpow (Real.rpow x a) (n : ℝ) :=
      (Real.rpow_natCast (Real.rpow x a) n).symm
    _ = Real.rpow x (a * (n : ℝ)) :=
      (Real.rpow_mul hx a (n : ℝ)).symm

private theorem eventually_const_mul_log_rpow_neg_le
    {K e d epsilon : ℝ}
    (hK : 0 < K) (hde : d < e) (hepsilon : 0 < epsilon) :
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

private theorem ndA5ReferenceEtaEnvelope_le_slowest
    {B : ℕ} (hlogOne : (1 : ℝ) ≤ Real.log B) :
    ndA5ReferenceEtaEnvelope B ≤
      ((57 * 100000 / 340 : ℝ) +
          (1021 * 100000 / 340 : ℝ) +
          (8 / (1 / 200000 : ℝ) ^ 3)) *
        Real.rpow (Real.log B) (-(1 / 20 : ℝ)) := by
  have hsecond :
      Real.rpow (Real.log B) (-(3 / 10 : ℝ)) ≤
        Real.rpow (Real.log B) (-(1 / 20 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hlogOne (by norm_num)
  have hthird :
      Real.rpow (Real.log B) (-(9 / 5 : ℝ)) ≤
        Real.rpow (Real.log B) (-(1 / 20 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hlogOne (by norm_num)
  unfold ndA5ReferenceEtaEnvelope
  calc
    (57 * 100000 / 340 : ℝ) *
          Real.rpow (Real.log B) (-(1 / 20 : ℝ)) +
        (1021 * 100000 / 340 : ℝ) *
          Real.rpow (Real.log B) (-(3 / 10 : ℝ)) +
        (8 / (1 / 200000 : ℝ) ^ 3) *
          Real.rpow (Real.log B) (-(9 / 5 : ℝ)) ≤
      (57 * 100000 / 340 : ℝ) *
          Real.rpow (Real.log B) (-(1 / 20 : ℝ)) +
        (1021 * 100000 / 340 : ℝ) *
          Real.rpow (Real.log B) (-(1 / 20 : ℝ)) +
        (8 / (1 / 200000 : ℝ) ^ 3) *
          Real.rpow (Real.log B) (-(1 / 20 : ℝ)) := by
        gcongr <;> norm_num
    _ = ((57 * 100000 / 340 : ℝ) +
          (1021 * 100000 / 340 : ℝ) +
          (8 / (1 / 200000 : ℝ) ^ 3)) *
        Real.rpow (Real.log B) (-(1 / 20 : ℝ)) := by ring

private theorem ndA5Reference_width_div_level_pow_three_le
    {B : ℕ} {C : ℝ}
    (hlogOne : (1 : ℝ) ≤ Real.log B)
    (hwidth : ndA5TubeWidth B C ≤
      Real.rpow (Real.log B) (3 / 5 : ℝ))
    (hlower : (1 / 200000 : ℝ) *
        Real.rpow (Real.log B) (3 / 5 : ℝ) ≤
      (ndA5ReferenceLevel B : ℝ)) :
    ndA5TubeWidth B C / (ndA5ReferenceLevel B : ℝ) ^ 3 ≤
      (1 / (1 / 200000 : ℝ) ^ 3) *
        Real.rpow (Real.log B) (-(6 / 5 : ℝ)) := by
  let L : ℝ := Real.log B
  let R : ℝ := Real.rpow L (3 / 5 : ℝ)
  let A : ℝ := 1 / 200000
  let M : ℝ := ndA5ReferenceLevel B
  have hLpos : 0 < L := zero_lt_one.trans_le hlogOne
  have hRpos : 0 < R := Real.rpow_pos_of_pos hLpos _
  have hApos : 0 < A := by dsimp only [A]; norm_num
  have hbasePos : 0 < A * R := mul_pos hApos hRpos
  have hMpos : 0 < M := hbasePos.trans_le (by
    simpa only [A, R, M, L] using hlower)
  have hpowLe : (A * R) ^ 3 ≤ M ^ 3 :=
    pow_le_pow_left₀ hbasePos.le
      (by simpa only [A, R, M, L] using hlower) 3
  have hpre :
      ndA5TubeWidth B C / M ^ 3 ≤ R / (A * R) ^ 3 := by
    calc
      ndA5TubeWidth B C / M ^ 3 ≤ R / M ^ 3 :=
        div_le_div_of_nonneg_right
          (by simpa only [R, L] using hwidth) (pow_nonneg hMpos.le 3)
      _ ≤ R / (A * R) ^ 3 :=
        div_le_div_of_nonneg_left hRpos.le (pow_pos hbasePos 3) hpowLe
  have hRcube : R ^ 3 = Real.rpow L (9 / 5 : ℝ) := by
    dsimp only [R]
    convert rpow_nat_pow_eq_rpow_mul hLpos.le (3 / 5 : ℝ) 3 using 1
    norm_num
  have hcancel :
      R ^ 3 * Real.rpow L (-(6 / 5 : ℝ)) = R := by
    rw [hRcube]
    calc
      Real.rpow L (9 / 5 : ℝ) * Real.rpow L (-(6 / 5 : ℝ)) =
          Real.rpow L (9 / 5 - 6 / 5 : ℝ) :=
        (Real.rpow_add hLpos (9 / 5 : ℝ) (-(6 / 5 : ℝ))).symm
      _ = R := by
        dsimp only [R]
        congr 1
        norm_num
  have hid :
      R / (A * R) ^ 3 =
        (1 / A ^ 3) * Real.rpow L (-(6 / 5 : ℝ)) := by
    rw [mul_pow]
    field_simp [hApos.ne', hRpos.ne']
    nlinarith [hcancel]
  simpa only [M, A, L] using hpre.trans_eq hid

private theorem ndA5Reference_width_div_level_pow_eleven_le
    {B : ℕ} {C : ℝ}
    (hlogOne : (1 : ℝ) ≤ Real.log B)
    (hwidth : ndA5TubeWidth B C ≤
      Real.rpow (Real.log B) (3 / 5 : ℝ))
    (hlower : (1 / 200000 : ℝ) *
        Real.rpow (Real.log B) (3 / 5 : ℝ) ≤
      (ndA5ReferenceLevel B : ℝ)) :
    ndA5TubeWidth B C / (ndA5ReferenceLevel B : ℝ) ^ 11 ≤
      (1 / (1 / 200000 : ℝ) ^ 11) *
        Real.rpow (Real.log B) (-6 : ℝ) := by
  let L : ℝ := Real.log B
  let R : ℝ := Real.rpow L (3 / 5 : ℝ)
  let A : ℝ := 1 / 200000
  let M : ℝ := ndA5ReferenceLevel B
  have hLpos : 0 < L := zero_lt_one.trans_le hlogOne
  have hRpos : 0 < R := Real.rpow_pos_of_pos hLpos _
  have hApos : 0 < A := by dsimp only [A]; norm_num
  have hbasePos : 0 < A * R := mul_pos hApos hRpos
  have hMpos : 0 < M := hbasePos.trans_le (by
    simpa only [A, R, M, L] using hlower)
  have hpowLe : (A * R) ^ 11 ≤ M ^ 11 :=
    pow_le_pow_left₀ hbasePos.le
      (by simpa only [A, R, M, L] using hlower) 11
  have hpre :
      ndA5TubeWidth B C / M ^ 11 ≤ R / (A * R) ^ 11 := by
    calc
      ndA5TubeWidth B C / M ^ 11 ≤ R / M ^ 11 :=
        div_le_div_of_nonneg_right
          (by simpa only [R, L] using hwidth) (pow_nonneg hMpos.le 11)
      _ ≤ R / (A * R) ^ 11 :=
        div_le_div_of_nonneg_left hRpos.le (pow_pos hbasePos 11) hpowLe
  have hRpow : R ^ 11 = Real.rpow L (33 / 5 : ℝ) := by
    dsimp only [R]
    convert rpow_nat_pow_eq_rpow_mul hLpos.le (3 / 5 : ℝ) 11 using 1
    norm_num
  have hcancel :
      R ^ 11 * Real.rpow L (-6 : ℝ) = R := by
    rw [hRpow]
    calc
      Real.rpow L (33 / 5 : ℝ) * Real.rpow L (-6 : ℝ) =
          Real.rpow L (33 / 5 - 6 : ℝ) :=
        (Real.rpow_add hLpos (33 / 5 : ℝ) (-6 : ℝ)).symm
      _ = R := by
        dsimp only [R]
        congr 1
        norm_num
  have hid :
      R / (A * R) ^ 11 =
        (1 / A ^ 11) * Real.rpow L (-6 : ℝ) := by
    rw [mul_pow]
    field_simp [hApos.ne', hRpos.ne']
    nlinarith [hcancel]
  simpa only [M, A, L] using hpre.trans_eq hid

private theorem eventually_ndA5ReferenceTerminalFlatRHS_le_slowest
    (Cband Cfm1 : ℝ) (hCband : 0 < Cband) (hCfm1 : 0 ≤ Cfm1) :
    ∀ᶠ B : ℕ in atTop,
      let m := ndA5ReferenceLevel B
      let W := ndA5TubeWidth B Cband
      let cap := 1 + 11 * (B : ℝ) ^ (-(9 / 10 : ℝ))
      2 * ndA5ReferenceAbsorbBar B Cband * cap +
          14 * W * ndA5FlatReferenceNonproportionalError m Cfm1 ≤
        (((1032 / 25 : ℝ) *
              ((57 * 100000 / 340 : ℝ) +
                (1021 * 100000 / 340 : ℝ) +
                (8 / (1 / 200000 : ℝ) ^ 3))) +
            ((1120 * Cfm1 / (1 / 200000 : ℝ) ^ 11) +
              (4480 / (1 / 200000 : ℝ) ^ 3))) *
          Real.rpow (Real.log B) (-(1 / 20 : ℝ)) := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [hlog.eventually_ge_atTop (1 : ℝ),
        eventually_ndA5ReferenceEtaBar_le_envelope Cband hCband,
        eventually_ndA5ReferenceLevel_cast_sandwich,
        eventually_ndA5TubeWidth_le_taoSection5TypicalSlack Cband hCband,
        Filter.eventually_ge_atTop (1 : ℕ)]
      with B hlogOne heta hsandwich hwidth hBOne
  let L : ℝ := Real.log B
  let m : ℕ := ndA5ReferenceLevel B
  let W : ℝ := ndA5TubeWidth B Cband
  let cap : ℝ := 1 + 11 * (B : ℝ) ^ (-(9 / 10 : ℝ))
  let Aeta : ℝ :=
    (57 * 100000 / 340 : ℝ) +
      (1021 * 100000 / 340 : ℝ) +
      (8 / (1 / 200000 : ℝ) ^ 3)
  let Knp : ℝ :=
    (1120 * Cfm1 / (1 / 200000 : ℝ) ^ 11) +
      (4480 / (1 / 200000 : ℝ) ^ 3)
  have hLpos : 0 < L := zero_lt_one.trans_le hlogOne
  have hslow0 : 0 ≤ Real.rpow L (-(1 / 20 : ℝ)) :=
    Real.rpow_nonneg hLpos.le _
  have hcap : cap ≤ 12 := by
    have hpow : (B : ℝ) ^ (-(9 / 10 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast hBOne) (by norm_num)
    dsimp only [cap]
    nlinarith
  have hcap0 : 0 ≤ cap := by
    dsimp only [cap]
    positivity
  have hetaSlow : ndA5ReferenceEtaBar B Cband ≤
      Aeta * Real.rpow L (-(1 / 20 : ℝ)) :=
    heta.trans (by
      simpa only [Aeta, L] using
        ndA5ReferenceEtaEnvelope_le_slowest hlogOne)
  have hAbsorb :
      2 * ndA5ReferenceAbsorbBar B Cband * cap ≤
        (1032 / 25 : ℝ) * Aeta *
          Real.rpow L (-(1 / 20 : ℝ)) := by
    unfold ndA5ReferenceAbsorbBar
    calc
      2 * ((43 / 25 : ℝ) * ndA5ReferenceEtaBar B Cband) * cap ≤
          2 * ((43 / 25 : ℝ) *
            (Aeta * Real.rpow L (-(1 / 20 : ℝ)))) * cap := by
        gcongr <;> positivity
      _ ≤ 2 * ((43 / 25 : ℝ) *
            (Aeta * Real.rpow L (-(1 / 20 : ℝ)))) * 12 := by
        apply mul_le_mul_of_nonneg_left hcap
        positivity
      _ = (1032 / 25 : ℝ) * Aeta *
          Real.rpow L (-(1 / 20 : ℝ)) := by ring
  have hdiv3 := ndA5Reference_width_div_level_pow_three_le
    hlogOne (by simpa only [W, Tao.taoSection5TypicalSlack, L] using hwidth)
      hsandwich.1
  have hdiv11 := ndA5Reference_width_div_level_pow_eleven_le
    hlogOne (by simpa only [W, Tao.taoSection5TypicalSlack, L] using hwidth)
      hsandwich.1
  have hpowSix : Real.rpow L (-6 : ℝ) ≤
      Real.rpow L (-(6 / 5 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hlogOne (by norm_num)
  have hpowNp : Real.rpow L (-(6 / 5 : ℝ)) ≤
      Real.rpow L (-(1 / 20 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hlogOne (by norm_num)
  have hnp :
      14 * W * ndA5FlatReferenceNonproportionalError m Cfm1 ≤
        Knp * Real.rpow L (-(1 / 20 : ℝ)) := by
    have hfirst :
        1120 * Cfm1 * (W / (m : ℝ) ^ 11) ≤
          (1120 * Cfm1 / (1 / 200000 : ℝ) ^ 11) *
            Real.rpow L (-6 : ℝ) := by
      calc
        1120 * Cfm1 * (W / (m : ℝ) ^ 11) ≤
            1120 * Cfm1 *
              ((1 / (1 / 200000 : ℝ) ^ 11) *
                Real.rpow L (-6 : ℝ)) :=
          mul_le_mul_of_nonneg_left (by simpa only [W, m, L] using hdiv11)
            (mul_nonneg (by norm_num) hCfm1)
        _ = (1120 * Cfm1 / (1 / 200000 : ℝ) ^ 11) *
            Real.rpow L (-6 : ℝ) := by ring
    have hsecond :
        4480 * (W / (m : ℝ) ^ 3) ≤
          (4480 / (1 / 200000 : ℝ) ^ 3) *
            Real.rpow L (-(6 / 5 : ℝ)) := by
      calc
        4480 * (W / (m : ℝ) ^ 3) ≤
            4480 * ((1 / (1 / 200000 : ℝ) ^ 3) *
              Real.rpow L (-(6 / 5 : ℝ))) :=
          mul_le_mul_of_nonneg_left (by simpa only [W, m, L] using hdiv3)
            (by norm_num)
        _ = (4480 / (1 / 200000 : ℝ) ^ 3) *
            Real.rpow L (-(6 / 5 : ℝ)) := by ring
    unfold ndA5FlatReferenceNonproportionalError
    change 14 * W *
        (80 * (Cfm1 / (m : ℝ) ^ 11) +
          4 / (m : ℝ) ^ 3 * 80) ≤ _
    calc
      14 * W *
          (80 * (Cfm1 / (m : ℝ) ^ 11) +
            4 / (m : ℝ) ^ 3 * 80) =
          1120 * Cfm1 * (W / (m : ℝ) ^ 11) +
            4480 * (W / (m : ℝ) ^ 3) := by ring
      _ ≤ (1120 * Cfm1 / (1 / 200000 : ℝ) ^ 11) *
            Real.rpow L (-6 : ℝ) +
          (4480 / (1 / 200000 : ℝ) ^ 3) *
            Real.rpow L (-(6 / 5 : ℝ)) := add_le_add hfirst hsecond
      _ ≤ Knp * Real.rpow L (-(6 / 5 : ℝ)) := by
        calc
          (1120 * Cfm1 / (1 / 200000 : ℝ) ^ 11) *
                Real.rpow L (-6 : ℝ) +
              (4480 / (1 / 200000 : ℝ) ^ 3) *
                Real.rpow L (-(6 / 5 : ℝ)) ≤
            (1120 * Cfm1 / (1 / 200000 : ℝ) ^ 11) *
                Real.rpow L (-(6 / 5 : ℝ)) +
              (4480 / (1 / 200000 : ℝ) ^ 3) *
                Real.rpow L (-(6 / 5 : ℝ)) := by
              apply add_le_add _ le_rfl
              apply mul_le_mul_of_nonneg_left hpowSix
              positivity
          _ = Knp * Real.rpow L (-(6 / 5 : ℝ)) := by
            dsimp only [Knp]
            ring
      _ ≤ Knp * Real.rpow L (-(1 / 20 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hpowNp
        dsimp only [Knp]
        positivity
  dsimp only
  calc
    2 * ndA5ReferenceAbsorbBar B Cband * cap +
        14 * W * ndA5FlatReferenceNonproportionalError m Cfm1 ≤
      (1032 / 25 : ℝ) * Aeta * Real.rpow L (-(1 / 20 : ℝ)) +
        Knp * Real.rpow L (-(1 / 20 : ℝ)) := add_le_add hAbsorb hnp
    _ = (((1032 / 25 : ℝ) * Aeta) + Knp) *
        Real.rpow L (-(1 / 20 : ℝ)) := by ring
    _ = (((1032 / 25 : ℝ) *
              ((57 * 100000 / 340 : ℝ) +
                (1021 * 100000 / 340 : ℝ) +
                (8 / (1 / 200000 : ℝ) ^ 3))) +
            ((1120 * Cfm1 / (1 / 200000 : ℝ) ^ 11) +
              (4480 / (1 / 200000 : ℝ) ^ 3))) *
          Real.rpow (Real.log B) (-(1 / 20 : ℝ)) := by rfl

/-- For every fixed tube and conditioned-FM1 constant, both terminal
aggregate scalar errors are eventually smaller than any prescribed positive
fraction of the strict logarithmic rate. -/
theorem eventually_ndA5ReferenceTerminalAggregateRHS_le_rate
    (Cband Cfm1 : ℝ) (hCband : 0 < Cband) (hCfm1 : 0 ≤ Cfm1)
    {d epsilon : ℝ} (hd : 0 < d) (hd20 : d < 1 / 20)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ B : ℕ in atTop,
      let m := ndA5ReferenceLevel B
      let W := ndA5TubeWidth B Cband
      let cap := 1 + 11 * (B : ℝ) ^ (-(9 / 10 : ℝ))
      (2 * ndA5ReferenceAbsorbBar B Cband * cap +
          14 * W * ndA5HarmonicReferenceNonproportionalError m Cfm1 ≤
        epsilon * ndA5ReferenceInteriorScalarRate B d) ∧
      (2 * ndA5ReferenceAbsorbBar B Cband * cap +
          14 * W * ndA5FlatReferenceNonproportionalError m Cfm1 ≤
        epsilon * ndA5ReferenceInteriorScalarRate B d) := by
  let K : ℝ :=
    ((1032 / 25 : ℝ) *
        ((57 * 100000 / 340 : ℝ) +
          (1021 * 100000 / 340 : ℝ) +
          (8 / (1 / 200000 : ℝ) ^ 3))) +
      ((1120 * Cfm1 / (1 / 200000 : ℝ) ^ 11) +
        (4480 / (1 / 200000 : ℝ) ^ 3))
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hrate := eventually_const_mul_log_rpow_neg_le
    hK hd20 hepsilon
  filter_upwards
      [eventually_ndA5ReferenceTerminalFlatRHS_le_slowest
        Cband Cfm1 hCband hCfm1,
        hrate,
        eventually_ndA5ReferenceLevel_integer_room]
      with B hflat hrateB hroom
  let m := ndA5ReferenceLevel B
  let W := ndA5TubeWidth B Cband
  let cap := 1 + 11 * (B : ℝ) ^ (-(9 / 10 : ℝ))
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (by omega : 0 < m)
  have hH0 : 0 ≤ ndA5HarmonicReferenceNonproportionalError m Cfm1 := by
    unfold ndA5HarmonicReferenceNonproportionalError
    positivity
  have hHF :
      ndA5HarmonicReferenceNonproportionalError m Cfm1 ≤
        ndA5FlatReferenceNonproportionalError m Cfm1 := by
    unfold ndA5HarmonicReferenceNonproportionalError
      ndA5FlatReferenceNonproportionalError
    have hCdiv : 0 ≤ Cfm1 / (m : ℝ) ^ 11 := by positivity
    have htail : 0 ≤ 4 / (m : ℝ) ^ 3 := by positivity
    nlinarith
  have hW0 : 0 ≤ W := by
    dsimp only [W, ndA5TubeWidth]
    positivity
  have hharmonic :
      2 * ndA5ReferenceAbsorbBar B Cband * cap +
          14 * W * ndA5HarmonicReferenceNonproportionalError m Cfm1 ≤
        2 * ndA5ReferenceAbsorbBar B Cband * cap +
          14 * W * ndA5FlatReferenceNonproportionalError m Cfm1 := by
    gcongr
  constructor
  · exact hharmonic.trans (hflat.trans (by
      simpa only [K, ndA5ReferenceInteriorScalarRate] using hrateB))
  · exact hflat.trans (by
      simpa only [K, ndA5ReferenceInteriorScalarRate] using hrateB)

/-- The one conditioned-FM1 constant can be chosen before the base and then
hidden again: uniformly in every branch, valid band, and event, both literal
nominal terminal sums approach their scheduled physical reference profiles at
an arbitrary positive fraction of the strict logarithmic rate. -/
theorem eventually_abs_ndA5ReferenceTerminalNominalSums_sub_physicalProfiles_le_rate
    (Cband : ℝ) (hCband : (1 / 2 : ℝ) ≤ Cband)
    {d epsilon : ℝ} (hd : 0 < d) (hd20 : d < 1 / 20)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ B : ℕ in atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch) (j : ℕ) (E : Set ℕ),
        j < ndA5BandCount B branch →
          (|(∑ i : NDA5TerminalAtomIndex B branch Cband j E,
                ndA5HarmonicTerminalAtomNominalIdealMass i) -
              ndA5HarmonicReferencePhysicalProfile B
                (ndA5ReferenceLevel B) branch Cband j E| ≤
            epsilon * ndA5ReferenceInteriorScalarRate B d) ∧
          (|(∑ i : NDA5TerminalAtomIndex B branch Cband j E,
                ndA5FlatTerminalAtomNominalIdealMass i) -
              ndA5FlatReferencePhysicalProfile B
                (ndA5ReferenceLevel B) branch Cband j E| ≤
            epsilon * ndA5ReferenceInteriorScalarRate B d) := by
  have hCpos : 0 < Cband := by positivity
  obtain ⟨Cfm1, hCfm1, haggregate⟩ :=
    exists_eventually_ndA5ReferenceTerminalAggregateBoundAt Cband hCband
  have hrate := eventually_ndA5ReferenceTerminalAggregateRHS_le_rate
    Cband Cfm1 hCpos hCfm1 hd hd20 hepsilon
  filter_upwards [haggregate, hrate] with B haggregateB hrateB
  intro branch j E hj
  have hpair := haggregateB branch j E hj
  exact ⟨hpair.1.trans hrateB.1, hpair.2.trans hrateB.2⟩

end
end ND
end Erdos1135
