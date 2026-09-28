/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Prop78Case3FixedParameters

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

theorem taoSection7Case3_requestedA_weighted_inner_le_one_hundredth
    {A Aweight : ℕ}
    (hAAweight : A ≤ Aweight)
    (hAweight : 8 ≤ Aweight) :
    (10 : ℝ) ^ A *
        ((Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ (4 * Aweight)) +
          1 / ((10 : ℝ) ^ (Aweight + 3))) ≤
      1 / 100 := by
  have hinner :=
    taoSection7Case3_inner756_AweightPrefactor_Kcut_FSlack_budget
      (Aweight := Aweight) (Kcut := 4 * Aweight)
      (by omega : 3 ≤ Aweight) (le_refl (4 * Aweight))
  calc
    (10 : ℝ) ^ A *
          ((Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ (4 * Aweight)) +
            1 / ((10 : ℝ) ^ (Aweight + 3))) ≤
        (10 : ℝ) ^ A *
          (1 / ((10 : ℝ) ^ (Aweight + 2))) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ ≤ (10 : ℝ) ^ Aweight *
          (1 / ((10 : ℝ) ^ (Aweight + 2))) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) hAAweight) (by positivity)
    _ = 1 / 100 := by
      rw [pow_add]
      field_simp [pow_ne_zero]
      norm_num

theorem taoSection7Case3_requestedA_good_weight_le_one_tenth
    {A : ℕ} (hA : 1 ≤ A) :
    (10 : ℝ) ^ A * Real.exp (-((10 : ℝ) * (A : ℝ))) ≤
      1 / 10 := by
  have hexpTen : Real.exp (-10) ≤ (1 / 100 : ℝ) :=
    (Real.exp_le_exp.mpr (by norm_num : (-10 : ℝ) ≤ -6)).trans
      taoSection7_exp_neg_six_lt_one_hundredth.le
  have hbase :
      (10 : ℝ) * Real.exp (-10) ≤ 1 / 10 := by
    nlinarith
  calc
    (10 : ℝ) ^ A * Real.exp (-((10 : ℝ) * (A : ℝ))) =
        ((10 : ℝ) * Real.exp (-10)) ^ A := by
      rw [show -((10 : ℝ) * (A : ℝ)) = (A : ℝ) * (-10) by ring,
        Real.exp_nat_mul, ← mul_pow]
    _ ≤ (1 / 10 : ℝ) ^ A :=
      pow_le_pow_left₀ (by positivity) hbase A
    _ ≤ 1 / 10 :=
      pow_le_of_le_one (by norm_num) (by norm_num)
        (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hA))

theorem
    taoSection7Case3_requestedA_weighted_priority_budget_le_sixtyOneHundredths
    {A Aweight : ℕ}
    (hA : 1 ≤ A)
    (hAAweight : A ≤ Aweight)
    (hAweight : 8 ≤ Aweight) :
    (1 / 2 : ℝ) +
        (10 : ℝ) ^ A *
          ((Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ (4 * Aweight)) +
            1 / ((10 : ℝ) ^ (Aweight + 3))) +
        (10 : ℝ) ^ A * Real.exp (-((10 : ℝ) * (A : ℝ))) ≤
      61 / 100 := by
  have hinner :=
    taoSection7Case3_requestedA_weighted_inner_le_one_hundredth
      hAAweight hAweight
  have hgood := taoSection7Case3_requestedA_good_weight_le_one_tenth hA
  calc
    (1 / 2 : ℝ) +
          (10 : ℝ) ^ A *
            ((Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ (4 * Aweight)) +
              1 / ((10 : ℝ) ^ (Aweight + 3))) +
          (10 : ℝ) ^ A * Real.exp (-((10 : ℝ) * (A : ℝ))) ≤
        1 / 2 + 1 / 100 + 1 / 10 :=
      add_le_add (add_le_add le_rfl hinner) hgood
    _ = 61 / 100 := by norm_num

theorem TaoSection7Case3FixedParameters.weighted_priority_budget_le_sixtyOneHundredths
    {constants : TaoSection7Lemma710Constants}
    {A : ℕ} {epsilon : ℝ}
    (fixed : TaoSection7Case3FixedParameters constants A epsilon) :
    (1 / 2 : ℝ) +
        (10 : ℝ) ^ A *
          ((fixed.Aweight : ℝ) ^ 2 /
              ((4 : ℝ) ^ (4 * fixed.Aweight)) +
            1 / ((10 : ℝ) ^ (fixed.Aweight + 3))) +
        (10 : ℝ) ^ A * Real.exp (-((10 : ℝ) * (A : ℝ))) ≤
      61 / 100 :=
  taoSection7Case3_requestedA_weighted_priority_budget_le_sixtyOneHundredths
    fixed.A_pos fixed.A_le_Aweight fixed.Aweight_ge_eight

end

end Tao

end Erdos1135Predecessor
