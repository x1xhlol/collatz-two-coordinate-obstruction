/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalFreshEStar
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEStarUniform

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao

open Tao.TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

noncomputable section

def explicitRenewalConstants : TaoSection7Lemma710Constants :=
  { C710 := 2 ^ 116
    c710 := 1 / 256
    C710_nonneg := by positivity
    c710_pos := by norm_num }

private theorem sharpTail_half_of_bounds
    (constants : TaoSection7Lemma710Constants) {A : ℕ} (hA : 1 ≤ A)
    (hq : 256 * Real.exp (-(constants.c710 * (A : ℝ))) ≤ 1 / 2)
    (hgeom : 2 * constants.C710 * (1 / 2 : ℝ) ^ A ≤ 1 / 2) :
    constants.C710 * taoSection7Case3BaseKcutSharpExpTail constants A *
      ((4 : ℝ) ^ (4 * A)) ≤ (1 / 2 : ℝ) * (A : ℝ) ^ 2 := by
  have hAreal : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hAsq : (A : ℝ) ≤ (A : ℝ) ^ 2 := by nlinarith
  have hexpSqLe : Real.exp (-(constants.c710 * (A : ℝ) ^ 2)) ≤
      Real.exp (-(constants.c710 * (A : ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hAsq constants.c710_pos.le]
  have hexpHalf : Real.exp (-(constants.c710 * (A : ℝ) ^ 2)) ≤ 1 / 2 := by
    have hsmall : Real.exp (-(constants.c710 * (A : ℝ))) ≤ 1 / 2 := by
      nlinarith [Real.exp_pos (-(constants.c710 * (A : ℝ)))]
    exact hexpSqLe.trans hsmall
  have hdenPos : 0 < 1 - Real.exp (-(constants.c710 * (A : ℝ) ^ 2)) := by
    linarith
  have hinv : (1 - Real.exp (-(constants.c710 * (A : ℝ) ^ 2)))⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ hdenPos]
    linarith
  have hpow4 : (4 : ℝ) ^ (4 * A) = (256 : ℝ) ^ A := by
    rw [pow_mul]
    norm_num
  have hexpPow : Real.exp (-(constants.c710 * (A : ℝ))) ^ A =
      Real.exp (-(constants.c710 * (A : ℝ) ^ 2)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hfactor : Real.exp (-(constants.c710 * (A : ℝ) ^ 2)) *
      (4 : ℝ) ^ (4 * A) =
        (256 * Real.exp (-(constants.c710 * (A : ℝ)))) ^ A := by
    rw [hpow4, mul_pow, hexpPow]
    ring
  have hqPow : (256 * Real.exp (-(constants.c710 * (A : ℝ)))) ^ A ≤
      (1 / 2 : ℝ) ^ A := pow_le_pow_left₀ (by positivity) hq A
  unfold taoSection7Case3BaseKcutSharpExpTail
  calc
    _ = constants.C710 * (1 - Real.exp (-(constants.c710 * (A : ℝ) ^ 2)))⁻¹ *
        (Real.exp (-(constants.c710 * (A : ℝ) ^ 2)) * (4 : ℝ) ^ (4 * A)) := by ring
    _ ≤ constants.C710 * 2 *
        (Real.exp (-(constants.c710 * (A : ℝ) ^ 2)) * (4 : ℝ) ^ (4 * A)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinv constants.C710_nonneg) (by positivity)
    _ = constants.C710 * 2 *
        (256 * Real.exp (-(constants.c710 * (A : ℝ)))) ^ A := by rw [hfactor]
    _ ≤ constants.C710 * 2 * (1 / 2 : ℝ) ^ A :=
      mul_le_mul_of_nonneg_left hqPow
        (mul_nonneg constants.C710_nonneg (by norm_num))
    _ ≤ (1 / 2 : ℝ) := by simpa [mul_comm] using hgeom
    _ ≤ (1 / 2 : ℝ) * (A : ℝ) ^ 2 := by nlinarith

private theorem halfPow8192_le :
    (1 / 2 : ℝ) ^ 8192 ≤ (1 / 2 : ℝ) ^ 118 :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)

def explicitRenewal_case3Slack :
    TaoSection7Case3BaseKcutFactorizedSlackSchedule
      8192 8 32768 explicitRenewalConstants := by
  have hgeom : 2 * explicitRenewalConstants.C710 * (1 / 2 : ℝ) ^ 8192 ≤ 1 / 2 := by
    calc
      _ ≤ 2 * explicitRenewalConstants.C710 * (1 / 2 : ℝ) ^ 118 :=
        mul_le_mul_of_nonneg_left halfPow8192_le
          (mul_nonneg (by norm_num) explicitRenewalConstants.C710_nonneg)
      _ ≤ 1 / 2 := by norm_num [explicitRenewalConstants]
  have hq : 256 * Real.exp (-(explicitRenewalConstants.c710 * (8192 : ℝ))) ≤ 1 / 2 := by
    have hlog : Real.log (2 : ℝ) ≤ 1 := by
      convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num
    have he : Real.exp (-32 : ℝ) ≤ (1 / 512 : ℝ) := by
      calc
        _ ≤ Real.exp (-(9 * Real.log (2 : ℝ))) := Real.exp_le_exp.mpr (by linarith)
        _ = 1 / 512 := by
          rw [Real.exp_neg, show (9 : ℝ) * Real.log 2 = (9 : ℕ) * Real.log 2 by norm_num,
            Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          norm_num
    norm_num only [explicitRenewalConstants] at ⊢
    linarith
  refine
    { base_ge_four := by norm_num
      polySlack := 1 / 2
      expSlack := 1 / 2
      polySlack_nonneg := by norm_num
      expSlack_nonneg := by norm_num
      slack_sum := by norm_num
      polynomial_base_slack := ?_
      exponential_kcut_slack := sharpTail_half_of_bounds explicitRenewalConstants (by norm_num) hq hgeom }
  have hp : (1 / 16 : ℝ) ^ 8192 ≤ (1 / 2 : ℝ) ^ 8192 :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  calc
    _ = 2 * explicitRenewalConstants.C710 * (1 / 16 : ℝ) ^ 8192 := by
      rw [show 32768 = 4 * 8192 by norm_num, pow_mul, pow_mul, ← div_pow]
      norm_num only [Nat.cast_ofNat]
      rw [mul_comm explicitRenewalConstants.C710 2]
    _ ≤ 2 * explicitRenewalConstants.C710 * (1 / 2 : ℝ) ^ 8192 :=
      mul_le_mul_of_nonneg_left hp
        (mul_nonneg (by norm_num) explicitRenewalConstants.C710_nonneg)
    _ ≤ 1 / 2 := hgeom

def explicitRenewalEpsilon (E : ℕ) : ℝ := ((2 : ℝ) ^ E)⁻¹

def explicitRenewalPriority (E : ℕ) : ℕ := 10 * 6409 * 2 ^ (3 * E)

def explicitRenewalWhiteStops (E : ℕ) : ℕ :=
  2 ^ E * (explicitRenewalPriority E + 3 * (8192 + 3) + 1) + 1

theorem explicitRenewal_epsilon_exp (E : ℕ) :
    explicitRenewalEpsilon E = Real.exp (-(E : ℝ) * Real.log 2) := by
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rfl

def explicitRenewal_scalar {E : ℕ} (hE : 20 ≤ E) :
    TaoSection7ClaimStarScalarPacket (explicitRenewalEpsilon E) := by
  apply TaoSection7ClaimStarScalarPacket.of_le_exp_neg_ten
  · unfold explicitRenewalEpsilon
    positivity
  · rw [explicitRenewal_epsilon_exp]
    apply Real.exp_le_exp.mpr
    have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
      convert Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num
    have hEreal : (20 : ℝ) ≤ E := by exact_mod_cast hE
    nlinarith

theorem explicitRenewal_priority_exact (E : ℕ) :
    (explicitRenewalEpsilon E) ^ 3 * (explicitRenewalPriority E : ℝ) = 10 * 6409 := by
  unfold explicitRenewalEpsilon explicitRenewalPriority
  push_cast
  rw [show 3 * E = E * 3 by omega, pow_mul]
  field_simp
  norm_num

theorem explicitRenewal_white_room (E : ℕ) :
    (explicitRenewalPriority E : ℝ) + (8195 : ℝ) * Real.log 10 +
        explicitRenewalEpsilon E <
      explicitRenewalEpsilon E * (explicitRenewalWhiteStops E : ℝ) := by
  have hlog : Real.log (10 : ℝ) < 3 := by
    have hexp := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 4
    norm_num [Finset.sum_range_succ] at hexp
    exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr (by linarith)
  have hD : (2 : ℝ) ^ E ≠ 0 := ne_of_gt (by positivity)
  have hid : explicitRenewalEpsilon E * (explicitRenewalWhiteStops E : ℝ) =
      (explicitRenewalPriority E : ℝ) + 3 * 8195 + 1 + explicitRenewalEpsilon E := by
    unfold explicitRenewalWhiteStops explicitRenewalEpsilon
    push_cast
    field_simp
    <;> ring
  rw [hid]
  linarith

def explicitRenewal_fixed {E : ℕ} (hE : 20 ≤ E) :
    TaoSection7Case3FixedParameters explicitRenewalConstants 6409
      (explicitRenewalEpsilon E) := by
  let T := explicitRenewalPriority E
  let R := explicitRenewalWhiteStops E
  let Pmax := lemma79CanonicalSurvivalMaxTime 8 32768 T R
  let P := Pmax + 1
  have hpriority : (10 : ℝ) * (6409 : ℝ) ≤
      (explicitRenewalEpsilon E) ^ 3 * ((T + 1 : ℕ) : ℝ) := by
    have h := explicitRenewal_priority_exact E
    change (explicitRenewalEpsilon E) ^ 3 * (T : ℝ) = _ at h
    push_cast
    nlinarith [pow_nonneg (show 0 ≤ explicitRenewalEpsilon E by
      unfold explicitRenewalEpsilon; positivity) 3]
  have hiterate : taoSection7Case3BaseKcutNextBoundIterateRoom
      8 32768 T (R - 1) T P := by
    simp [taoSection7Case3BaseKcutNextBoundIterateRoom,
      taoSection7Case3IterateRoom, P, Pmax, lemma79CanonicalSurvivalMaxTime]
  exact
    { scalar := explicitRenewal_scalar hE
      A_pos := by norm_num
      Aweight := 8192
      A_le_Aweight := by norm_num
      Aweight_ge_eight := by norm_num
      factorizedSlack := explicitRenewal_case3Slack
      T := T
      priority_threshold := hpriority
      Amarkov := 8193
      Amarkov_eq := rfl
      R := R
      R_pos := by dsimp [R, explicitRenewalWhiteStops]; omega
      white_room := by simpa only [Nat.cast_ofNat] using explicitRenewal_white_room E
      Pmax := Pmax
      Pmax_eq := rfl
      P := P
      P_eq := rfl
      iterate_room := hiterate }

theorem explicitRenewal_canonicalEStar {E : ℕ} (hE : 20 ≤ E) :
    TaoSection7Case3CanonicalEStarData (explicitRenewal_fixed hE)
      (2 ^ 34 * ((explicitRenewal_fixed hE).Pmax + 1)) := by
  refine ⟨?_⟩
  intro n m J fpGap entry family old M
    hS0 hPmaxJ hgap hbase hpair hold hscale hm hM hcap
  let fixed := explicitRenewal_fixed hE
  let allowed := Finset.range (fixed.Pmax + 1)
  let mu := lemma79CanonicalEndpointFreshPMF J entry fpGap
  let constants := explicitRenewalConstants
  have hpoly0 (p : ℕ) :
      0 ≤ taoSection7Case3BaseKcutPolynomialBudgetTerm constants 8192 8 32768 p := by
    unfold taoSection7Case3BaseKcutPolynomialBudgetTerm
      taoSection7Case3LargeTriangleBoundWithBase
    exact mul_nonneg constants.C710_nonneg (by positivity)
  have hexp0 (p : ℕ) :
      0 ≤ taoSection7Case3BaseKcutExponentialBudgetTerm constants 8192 p := by
    unfold taoSection7Case3BaseKcutExponentialBudgetTerm
    exact mul_nonneg constants.C710_nonneg (Real.exp_pos _).le
  have hrow : ∀ p, p ∈ allowed →
      (mu.toOuterMeasure (lemma79CanonicalEndpointFreshEStarAt
        entry family 8 32768 p)).toReal ≤
      taoSection7Case3BaseKcutPolynomialBudgetTerm constants 8192 8 32768 p +
        taoSection7Case3BaseKcutExponentialBudgetTerm constants 8192 p := by
    intro p hp
    have hpPmax : p ≤ fixed.Pmax := Nat.le_of_lt_succ (Finset.mem_range.mp hp)
    have hbound := explicitRenewal_freshEStar_fixedOffset fixed.Pmax allowed
      n m J fpGap 8 32768 p entry family old M hS0
      (hpPmax.trans hPmaxJ) hgap hbase hpair hold hscale hm hM hcap hp
    have hbudget := lemma79FixedOffsetBudget_eq_baseKcutTerms constants 8192 8 32768 p
    norm_num only [Nat.cast_ofNat] at hbudget
    have hfixedBudget0 : 0 ≤ constants.C710 * lemma79OutsideEprimeScale 8192 p /
        taoSection7Case3LargeTriangleBoundWithBase (8 : ℝ) 32768 p +
      constants.C710 * Real.exp (-(constants.c710 * lemma79OutsideEprimeScale 8192 p)) := by
      rw [hbudget]
      exact add_nonneg (hpoly0 p) (hexp0 p)
    change mu.toOuterMeasure _ ≤ ENNReal.ofReal
      (constants.C710 * lemma79OutsideEprimeScale 8192 p /
        taoSection7Case3LargeTriangleBoundWithBase (8 : ℝ) 32768 p +
      constants.C710 * Real.exp (-(constants.c710 * lemma79OutsideEprimeScale 8192 p))) at hbound
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    rw [ENNReal.toReal_ofReal hfixedBudget0] at hreal
    rw [hbudget] at hreal
    exact hreal
  calc
    _ ≤ ∑ p ∈ allowed,
        (mu.toOuterMeasure (lemma79CanonicalEndpointFreshEStarAt
          entry family 8 32768 p)).toReal := by
      exact lemma79CanonicalEndpointFreshEStarEvent_toReal_le_sum
        mu entry family 8 32768 fixed.T fixed.R
    _ ≤ ∑ p ∈ allowed,
        (taoSection7Case3BaseKcutPolynomialBudgetTerm constants 8192 8 32768 p +
          taoSection7Case3BaseKcutExponentialBudgetTerm constants 8192 p) :=
      Finset.sum_le_sum hrow
    _ ≤ (fixed.Aweight : ℝ) ^ 2 / (4 : ℝ) ^ (4 * fixed.Aweight) :=
      fixed.to_absorptionInputs.sum_canonicalTerms_le

end

end Erdos1135Predecessor.ND.PositiveDensity
