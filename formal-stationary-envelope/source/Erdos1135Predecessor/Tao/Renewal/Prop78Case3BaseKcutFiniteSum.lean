/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Prop78Case3EStarSupportProducer
import Erdos1135Predecessor.Tao.Section6.Corollary63
import Mathlib.Analysis.PSeries

namespace Erdos1135Predecessor

namespace Tao

open scoped BigOperators

noncomputable section

def taoSection7Case3BaseKcutPolynomialBudgetTerm
    (constants : TaoSection7Lemma710Constants)
    (Aweight base Kcut p : ℕ) : ℝ :=
  constants.C710 *
    (((Aweight : ℝ) ^ 2 * (1 + (p : ℝ))) /
      taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut p)

def taoSection7Case3BaseKcutExponentialBudgetTerm
    (constants : TaoSection7Lemma710Constants)
    (Aweight p : ℕ) : ℝ :=
  constants.C710 *
    Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2 * (1 + (p : ℝ))))

noncomputable def taoSection7Case3BaseKcutPolynomialScale
    (constants : TaoSection7Lemma710Constants)
    (Aweight base Kcut : ℕ) : ℝ :=
  constants.C710 * (Aweight : ℝ) ^ 2 / ((base : ℝ) ^ Kcut)

theorem taoSection7Case3BaseKcutPolynomialBudgetTerm_eq_scale_invSq
    {constants : TaoSection7Lemma710Constants}
    {Aweight base Kcut p : ℕ}
    (hbase : 0 < base) :
    taoSection7Case3BaseKcutPolynomialBudgetTerm constants Aweight base Kcut p =
      taoSection7Case3BaseKcutPolynomialScale constants Aweight base Kcut *
        (((1 : ℝ) + (p : ℝ)) ^ 2)⁻¹ := by
  have hbase_ne : (base : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hbase)
  have hbase_pow_ne : (base : ℝ) ^ Kcut ≠ 0 := pow_ne_zero Kcut hbase_ne
  have hp_ne : (1 + (p : ℝ)) ≠ 0 := by positivity
  have hp2_ne : ((1 : ℝ) + (p : ℝ)) ^ 2 ≠ 0 := pow_ne_zero 2 hp_ne
  unfold taoSection7Case3BaseKcutPolynomialBudgetTerm
  unfold taoSection7Case3BaseKcutPolynomialScale
  unfold taoSection7Case3LargeTriangleBoundWithBase
  field_simp [hbase_pow_ne, hp_ne, hp2_ne]

theorem taoSection7Case3BaseKcut_polynomial_pointwise_le_canonical
    {allowed : Finset ℕ}
    {Aweight base Kcut : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (hbase : 0 < base) :
    ∀ p, p ∈ allowed →
      taoSection7Case3BaseKcutPolynomialBudgetTerm constants Aweight base Kcut p ≤
        taoSection7Case3BaseKcutPolynomialScale constants Aweight base Kcut *
          (((1 : ℝ) + (p : ℝ)) ^ 2)⁻¹ := by
  intro p _hp
  rw [taoSection7Case3BaseKcutPolynomialBudgetTerm_eq_scale_invSq
    (constants := constants) (Aweight := Aweight) (base := base)
    (Kcut := Kcut) (p := p) hbase]

theorem taoSection7Case3BaseKcutPolynomialScale_nonneg
    {constants : TaoSection7Lemma710Constants}
    {Aweight base Kcut : ℕ}
    (hbase : 0 < base) :
    0 ≤ taoSection7Case3BaseKcutPolynomialScale constants Aweight base Kcut := by
  have hbase_real : 0 < (base : ℝ) := by
    exact_mod_cast hbase
  have hden_nonneg : 0 ≤ (base : ℝ) ^ Kcut :=
    le_of_lt (pow_pos hbase_real Kcut)
  unfold taoSection7Case3BaseKcutPolynomialScale
  exact div_nonneg (mul_nonneg constants.C710_nonneg (sq_nonneg _)) hden_nonneg

theorem taoSection7Case3_invSq_range_sum_eq_Ioo (m : ℕ) :
    (Finset.range m).sum (fun p => (((1 : ℝ) + (p : ℝ)) ^ 2)⁻¹) =
      (Finset.Ioo 0 (m + 1)).sum (fun i => (((i : ℝ) ^ 2)⁻¹)) := by
  have himage :
      (Finset.range m).image (fun p => p + 1) = Finset.Ioo 0 (m + 1) := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_image.1 hi with ⟨p, hp, rfl⟩
      simp only [Finset.mem_Ioo]
      constructor
      · omega
      · exact Nat.succ_lt_succ (Finset.mem_range.1 hp)
    · intro hi
      have hi_pos : 0 < i := (Finset.mem_Ioo.1 hi).1
      have hi_lt : i < m + 1 := (Finset.mem_Ioo.1 hi).2
      refine Finset.mem_image.2 ⟨i - 1, ?_, ?_⟩
      · exact Finset.mem_range.2
          (Nat.sub_lt_left_of_lt_add hi_pos (by
            simpa [Nat.add_comm] using hi_lt))
      · omega
  rw [← himage]
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl ?_
    intro p _hp
    congr 1
    norm_num [Nat.cast_add]
    ring
  · intro a _ha b _hb hab
    exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hab)

theorem taoSection7Case3_invSq_range_sum_le_two (m : ℕ) :
    (Finset.range m).sum (fun p => (((1 : ℝ) + (p : ℝ)) ^ 2)⁻¹) ≤ 2 := by
  rw [taoSection7Case3_invSq_range_sum_eq_Ioo]
  simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (m + 1))

theorem taoSection7Case3_invSq_sum_le_two_of_subset_range
    {allowed : Finset ℕ} {m : ℕ}
    (hsub : ∀ p, p ∈ allowed → p < m) :
    allowed.sum (fun p => (((1 : ℝ) + (p : ℝ)) ^ 2)⁻¹) ≤ 2 := by
  have hsubset : allowed ⊆ Finset.range m := by
    intro p hp
    exact Finset.mem_range.2 (hsub p hp)
  calc
    allowed.sum (fun p => (((1 : ℝ) + (p : ℝ)) ^ 2)⁻¹)
        ≤ (Finset.range m).sum
            (fun p => (((1 : ℝ) + (p : ℝ)) ^ 2)⁻¹) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
            intro p _hp _hnot
            positivity)
    _ ≤ 2 := taoSection7Case3_invSq_range_sum_le_two m

structure TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs
    (allowed : Finset ℕ)
    (Aweight base Kcut : ℕ)
    (constants : TaoSection7Lemma710Constants) where
  base_ge_four : 4 ≤ base
  polynomialBudget : ℝ
  exponentialBudget : ℝ
  polynomial_nonneg : 0 ≤ polynomialBudget
  exponential_nonneg : 0 ≤ exponentialBudget
  polynomial_sum_le :
    allowed.sum
        (fun p =>
          taoSection7Case3BaseKcutPolynomialBudgetTerm
            constants Aweight base Kcut p) ≤
      polynomialBudget
  exponential_sum_le :
    allowed.sum
        (fun p =>
          taoSection7Case3BaseKcutExponentialBudgetTerm
            constants Aweight p) ≤
      exponentialBudget
  scalar_tail_budget :
    polynomialBudget + exponentialBudget ≤
      (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut)

structure TaoSection7Case3BaseKcutScalarRowInputs
    (allowed : Finset ℕ)
    (Aweight base Kcut : ℕ)
    (constants : TaoSection7Lemma710Constants) where
  base_ge_four : 4 ≤ base
  polynomialScale : ℝ
  invSqBound : ℝ
  expTail : ℝ
  polynomialBudget : ℝ
  exponentialBudget : ℝ
  polynomial_scale_nonneg : 0 ≤ polynomialScale
  polynomial_nonneg : 0 ≤ polynomialBudget
  exponential_nonneg : 0 ≤ exponentialBudget
  polynomial_pointwise_le :
    ∀ p, p ∈ allowed →
      taoSection7Case3BaseKcutPolynomialBudgetTerm constants Aweight base Kcut p ≤
        polynomialScale * (((1 : ℝ) + (p : ℝ)) ^ 2)⁻¹
  invSq_sum :
    allowed.sum (fun p => (((1 : ℝ) + (p : ℝ)) ^ 2)⁻¹) ≤ invSqBound
  polynomial_absorb :
    polynomialScale * invSqBound ≤ polynomialBudget
  exp_sum :
    allowed.sum
        (fun p =>
          Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2 * (1 + (p : ℝ))))) ≤
      expTail
  exponential_absorb :
    constants.C710 * expTail ≤ exponentialBudget
  scalar_tail_budget :
    polynomialBudget + exponentialBudget ≤
      (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut)

theorem TaoSection7Case3BaseKcutScalarRowInputs.polynomial_sum_le
    {allowed : Finset ℕ}
    {Aweight base Kcut : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (h :
      TaoSection7Case3BaseKcutScalarRowInputs
        allowed Aweight base Kcut constants) :
    allowed.sum
        (fun p =>
          taoSection7Case3BaseKcutPolynomialBudgetTerm
            constants Aweight base Kcut p) ≤
      h.polynomialBudget := by
  calc
    allowed.sum
        (fun p =>
          taoSection7Case3BaseKcutPolynomialBudgetTerm
            constants Aweight base Kcut p)
        ≤ allowed.sum
            (fun p => h.polynomialScale * (((1 : ℝ) + (p : ℝ)) ^ 2)⁻¹) :=
          Finset.sum_le_sum fun p hp => h.polynomial_pointwise_le p hp
    _ = h.polynomialScale *
          allowed.sum (fun p => (((1 : ℝ) + (p : ℝ)) ^ 2)⁻¹) := by
          rw [Finset.mul_sum]
    _ ≤ h.polynomialScale * h.invSqBound :=
          mul_le_mul_of_nonneg_left h.invSq_sum h.polynomial_scale_nonneg
    _ ≤ h.polynomialBudget := h.polynomial_absorb

theorem TaoSection7Case3BaseKcutScalarRowInputs.exponential_sum_le
    {allowed : Finset ℕ}
    {Aweight base Kcut : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (h :
      TaoSection7Case3BaseKcutScalarRowInputs
        allowed Aweight base Kcut constants) :
    allowed.sum
        (fun p =>
          taoSection7Case3BaseKcutExponentialBudgetTerm
            constants Aweight p) ≤
      h.exponentialBudget := by
  calc
    allowed.sum
        (fun p =>
          taoSection7Case3BaseKcutExponentialBudgetTerm
            constants Aweight p)
        = constants.C710 *
            allowed.sum
              (fun p =>
                Real.exp
                  (-(constants.c710 * (Aweight : ℝ) ^ 2 * (1 + (p : ℝ))))) := by
          rw [Finset.mul_sum]
          rfl
    _ ≤ constants.C710 * h.expTail :=
          mul_le_mul_of_nonneg_left h.exp_sum constants.C710_nonneg
    _ ≤ h.exponentialBudget := h.exponential_absorb

structure TaoSection7Case3BaseKcutScalarTailSchedule
    (Aweight Kcut : ℕ)
    (constants : TaoSection7Lemma710Constants) where
  expTail : ℝ
  polynomialBudget : ℝ
  exponentialBudget : ℝ
  polynomial_nonneg : 0 ≤ polynomialBudget
  exponential_nonneg : 0 ≤ exponentialBudget
  exponential_tail_le :
    constants.C710 * expTail ≤ exponentialBudget
  final_tail :
    polynomialBudget + exponentialBudget ≤
      (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut)

noncomputable def taoSection7Case3BaseKcutUnitTailBudget
    (Aweight Kcut : ℕ) : ℝ :=
  (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut)

theorem taoSection7Case3BaseKcutUnitTailBudget_nonneg
    (Aweight Kcut : ℕ) :
    0 ≤ taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut := by
  unfold taoSection7Case3BaseKcutUnitTailBudget
  exact div_nonneg (sq_nonneg _)
    (le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 4) Kcut))

noncomputable def taoSection7Case3BaseKcutSharpExpTail
    (constants : TaoSection7Lemma710Constants)
    (Aweight : ℕ) : ℝ :=
  Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2)) *
    (1 - Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2)))⁻¹

structure TaoSection7Case3BaseKcutFactorizedSlackSchedule
    (Aweight base Kcut : ℕ)
    (constants : TaoSection7Lemma710Constants) where
  base_ge_four : 4 ≤ base
  polySlack : ℝ
  expSlack : ℝ
  polySlack_nonneg : 0 ≤ polySlack
  expSlack_nonneg : 0 ≤ expSlack
  slack_sum : polySlack + expSlack ≤ 1
  polynomial_base_slack :
    constants.C710 * 2 *
        (((4 : ℝ) ^ Kcut) / ((base : ℝ) ^ Kcut)) ≤
      polySlack
  exponential_kcut_slack :
    constants.C710 *
        taoSection7Case3BaseKcutSharpExpTail constants Aweight *
        ((4 : ℝ) ^ Kcut) ≤
      expSlack * ((Aweight : ℝ) ^ 2)

theorem TaoSection7Case3BaseKcutFactorizedSlackSchedule.base_pos
    {Aweight base Kcut : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (h :
      TaoSection7Case3BaseKcutFactorizedSlackSchedule
        Aweight base Kcut constants) :
    0 < base :=
  lt_of_lt_of_le (by norm_num : 0 < 4) h.base_ge_four

theorem TaoSection7Case3BaseKcutFactorizedSlackSchedule.polynomial_absorb
    {Aweight base Kcut : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (h :
      TaoSection7Case3BaseKcutFactorizedSlackSchedule
        Aweight base Kcut constants) :
    taoSection7Case3BaseKcutPolynomialScale constants Aweight base Kcut * 2 ≤
      h.polySlack *
        taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut := by
  have hbase_pos_real : 0 < (base : ℝ) := by
    exact_mod_cast h.base_pos
  have hbase_pow_ne : (base : ℝ) ^ Kcut ≠ 0 :=
    pow_ne_zero Kcut (ne_of_gt hbase_pos_real)
  have h4_pow_pos : 0 < (4 : ℝ) ^ Kcut :=
    pow_pos (by norm_num : (0 : ℝ) < 4) Kcut
  have h4_pow_ne : (4 : ℝ) ^ Kcut ≠ 0 := ne_of_gt h4_pow_pos
  have hunit_nonneg :
      0 ≤ taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut :=
    taoSection7Case3BaseKcutUnitTailBudget_nonneg Aweight Kcut
  have hmul := mul_le_mul_of_nonneg_right h.polynomial_base_slack hunit_nonneg
  calc
    taoSection7Case3BaseKcutPolynomialScale constants Aweight base Kcut * 2 =
        (constants.C710 * 2 *
            (((4 : ℝ) ^ Kcut) / ((base : ℝ) ^ Kcut))) *
          taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut := by
          unfold taoSection7Case3BaseKcutPolynomialScale
          unfold taoSection7Case3BaseKcutUnitTailBudget
          field_simp [hbase_pow_ne, h4_pow_ne]
    _ ≤ h.polySlack *
          taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut := hmul

theorem TaoSection7Case3BaseKcutFactorizedSlackSchedule.exponential_absorb
    {Aweight base Kcut : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (h :
      TaoSection7Case3BaseKcutFactorizedSlackSchedule
        Aweight base Kcut constants) :
    constants.C710 *
        taoSection7Case3BaseKcutSharpExpTail constants Aweight ≤
      h.expSlack *
        taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut := by
  have h4_pow_pos : 0 < (4 : ℝ) ^ Kcut :=
    pow_pos (by norm_num : (0 : ℝ) < 4) Kcut
  have hle' :
      constants.C710 *
          taoSection7Case3BaseKcutSharpExpTail constants Aweight ≤
        h.expSlack * ((Aweight : ℝ) ^ 2) / ((4 : ℝ) ^ Kcut) :=
    (le_div_iff₀ h4_pow_pos).2 h.exponential_kcut_slack
  simpa [taoSection7Case3BaseKcutUnitTailBudget, mul_div_assoc] using hle'

theorem TaoSection7Case3BaseKcutFactorizedSlackSchedule.final_tail
    {Aweight base Kcut : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (h :
      TaoSection7Case3BaseKcutFactorizedSlackSchedule
        Aweight base Kcut constants) :
    h.polySlack * taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut +
        h.expSlack * taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut ≤
      taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut := by
  have hunit_nonneg :
      0 ≤ taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut :=
    taoSection7Case3BaseKcutUnitTailBudget_nonneg Aweight Kcut
  calc
    h.polySlack * taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut +
        h.expSlack * taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut =
        (h.polySlack + h.expSlack) *
          taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut := by
          ring
    _ ≤ 1 * taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut :=
          mul_le_mul_of_nonneg_right h.slack_sum hunit_nonneg
    _ = taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut := by
          ring

def TaoSection7Case3BaseKcutFactorizedSlackSchedule.to_tailSchedule
    {Aweight base Kcut : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (h :
      TaoSection7Case3BaseKcutFactorizedSlackSchedule
        Aweight base Kcut constants) :
    TaoSection7Case3BaseKcutScalarTailSchedule Aweight Kcut constants where
  expTail := taoSection7Case3BaseKcutSharpExpTail constants Aweight
  polynomialBudget :=
    h.polySlack * taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut
  exponentialBudget :=
    h.expSlack * taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut
  polynomial_nonneg :=
    mul_nonneg h.polySlack_nonneg
      (taoSection7Case3BaseKcutUnitTailBudget_nonneg Aweight Kcut)
  exponential_nonneg :=
    mul_nonneg h.expSlack_nonneg
      (taoSection7Case3BaseKcutUnitTailBudget_nonneg Aweight Kcut)
  exponential_tail_le := h.exponential_absorb
  final_tail := by
    simpa [taoSection7Case3BaseKcutUnitTailBudget] using h.final_tail

def TaoSection7Case3BaseKcutScalarRowInputs.of_tailSchedule
    {allowed : Finset ℕ}
    {Aweight base Kcut : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (schedule :
      TaoSection7Case3BaseKcutScalarTailSchedule
        Aweight Kcut constants)
    (base_ge_four : 4 ≤ base)
    {polynomialScale invSqBound : ℝ}
    (polynomial_scale_nonneg : 0 ≤ polynomialScale)
    (polynomial_pointwise_le :
      ∀ p, p ∈ allowed →
        taoSection7Case3BaseKcutPolynomialBudgetTerm constants Aweight base Kcut p ≤
          polynomialScale * (((1 : ℝ) + (p : ℝ)) ^ 2)⁻¹)
    (invSq_sum :
      allowed.sum (fun p => (((1 : ℝ) + (p : ℝ)) ^ 2)⁻¹) ≤ invSqBound)
    (polynomial_absorb :
      polynomialScale * invSqBound ≤ schedule.polynomialBudget)
    (exp_sum :
      allowed.sum
          (fun p =>
            Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2 * (1 + (p : ℝ))))) ≤
        schedule.expTail) :
    TaoSection7Case3BaseKcutScalarRowInputs
      allowed Aweight base Kcut constants where
  base_ge_four := base_ge_four
  polynomialScale := polynomialScale
  invSqBound := invSqBound
  expTail := schedule.expTail
  polynomialBudget := schedule.polynomialBudget
  exponentialBudget := schedule.exponentialBudget
  polynomial_scale_nonneg := polynomial_scale_nonneg
  polynomial_nonneg := schedule.polynomial_nonneg
  exponential_nonneg := schedule.exponential_nonneg
  polynomial_pointwise_le := polynomial_pointwise_le
  invSq_sum := invSq_sum
  polynomial_absorb := polynomial_absorb
  exp_sum := exp_sum
  exponential_absorb := schedule.exponential_tail_le
  scalar_tail_budget := schedule.final_tail

theorem taoSection7Case3_exp_shifted_sum_le_exp_mul_inv_one_sub_of_subset_range
    {allowed : Finset ℕ} {m : ℕ} {c : ℝ}
    (hc : 0 < c)
    (hsub : ∀ p, p ∈ allowed → p < m) :
    allowed.sum (fun p => Real.exp (-(c * (1 + (p : ℝ))))) ≤
      Real.exp (-c) * (1 - Real.exp (-c))⁻¹ := by
  have hsubset : allowed ⊆ Finset.range m := by
    intro p hp
    exact Finset.mem_range.2 (hsub p hp)
  have hsum_range :
      allowed.sum (fun p => Real.exp (-c * (p : ℝ))) ≤
        (Finset.range m).sum (fun p => Real.exp (-c * (p : ℝ))) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro p _hp _hnot
      exact le_of_lt (Real.exp_pos _))
  have hshift :
      allowed.sum (fun p => Real.exp (-(c * (1 + (p : ℝ))))) =
        Real.exp (-c) *
          allowed.sum (fun p => Real.exp (-c * (p : ℝ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro p _hp
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    allowed.sum (fun p => Real.exp (-(c * (1 + (p : ℝ)))))
        = Real.exp (-c) *
            allowed.sum (fun p => Real.exp (-c * (p : ℝ))) := hshift
    _ ≤ Real.exp (-c) *
          (Finset.range m).sum (fun p => Real.exp (-c * (p : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hsum_range
            (le_of_lt (Real.exp_pos (-c)))
    _ ≤ Real.exp (-c) * (1 - Real.exp (-c))⁻¹ := by
          exact mul_le_mul_of_nonneg_left
            (finite_exp_neg_mul_sum_le_inv_one_sub (c := c) hc m)
            (le_of_lt (Real.exp_pos (-c)))

theorem taoSection7Case3BaseKcut_exponential_sum_le_exp_mul_inv_one_sub_of_subset_range
    {allowed : Finset ℕ} {Aweight m : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (hA : 0 < Aweight)
    (hsub : ∀ p, p ∈ allowed → p < m) :
    allowed.sum
        (fun p =>
          Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2 * (1 + (p : ℝ))))) ≤
      Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2)) *
        (1 - Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2)))⁻¹ := by
  have hAreal : 0 < (Aweight : ℝ) := by
    exact_mod_cast hA
  have hc : 0 < constants.c710 * (Aweight : ℝ) ^ 2 :=
    mul_pos constants.c710_pos (pow_pos hAreal 2)
  simpa [mul_assoc] using
    (taoSection7Case3_exp_shifted_sum_le_exp_mul_inv_one_sub_of_subset_range
      (allowed := allowed) (m := m)
      (c := constants.c710 * (Aweight : ℝ) ^ 2) hc hsub)

def TaoSection7Case3BaseKcutScalarRowInputs.of_canonicalRangeTailSchedule
    {allowed : Finset ℕ}
    {Aweight base Kcut m : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (schedule :
      TaoSection7Case3BaseKcutScalarTailSchedule
        Aweight Kcut constants)
    (base_ge_four : 4 ≤ base)
    (hA : 0 < Aweight)
    (hsub : ∀ p, p ∈ allowed → p < m)
    (polynomial_absorb :
      taoSection7Case3BaseKcutPolynomialScale constants Aweight base Kcut * 2 ≤
        schedule.polynomialBudget)
    (exp_tail_le :
      Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2)) *
          (1 - Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2)))⁻¹ ≤
        schedule.expTail) :
    TaoSection7Case3BaseKcutScalarRowInputs
      allowed Aweight base Kcut constants := by
  have hbase : 0 < base := lt_of_lt_of_le (by norm_num : 0 < 4) base_ge_four
  exact
    TaoSection7Case3BaseKcutScalarRowInputs.of_tailSchedule
      (allowed := allowed) (Aweight := Aweight) (base := base)
      (Kcut := Kcut) (constants := constants)
      schedule base_ge_four
      (polynomialScale :=
        taoSection7Case3BaseKcutPolynomialScale constants Aweight base Kcut)
      (invSqBound := 2)
      (taoSection7Case3BaseKcutPolynomialScale_nonneg
        (constants := constants) (Aweight := Aweight) (base := base)
        (Kcut := Kcut) hbase)
      (taoSection7Case3BaseKcut_polynomial_pointwise_le_canonical
        (allowed := allowed) (Aweight := Aweight) (base := base)
        (Kcut := Kcut) (constants := constants) hbase)
      (taoSection7Case3_invSq_sum_le_two_of_subset_range
        (allowed := allowed) (m := m) hsub)
      polynomial_absorb
      ((taoSection7Case3BaseKcut_exponential_sum_le_exp_mul_inv_one_sub_of_subset_range
        (allowed := allowed) (Aweight := Aweight) (m := m)
        (constants := constants) hA hsub).trans exp_tail_le)

def TaoSection7Case3BaseKcutScalarRowInputs.of_factorizedSlackSchedule
    {allowed : Finset ℕ}
    {Aweight base Kcut m : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (schedule :
      TaoSection7Case3BaseKcutFactorizedSlackSchedule
        Aweight base Kcut constants)
    (hA : 0 < Aweight)
    (hsub : ∀ p, p ∈ allowed → p < m) :
    TaoSection7Case3BaseKcutScalarRowInputs
      allowed Aweight base Kcut constants :=
  TaoSection7Case3BaseKcutScalarRowInputs.of_canonicalRangeTailSchedule
    (allowed := allowed) (Aweight := Aweight) (base := base)
    (Kcut := Kcut) (m := m) (constants := constants)
    schedule.to_tailSchedule schedule.base_ge_four hA hsub
    (by
      simpa [TaoSection7Case3BaseKcutFactorizedSlackSchedule.to_tailSchedule]
        using schedule.polynomial_absorb)
    (by
      simp [TaoSection7Case3BaseKcutFactorizedSlackSchedule.to_tailSchedule,
        taoSection7Case3BaseKcutSharpExpTail])

def TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs.of_scalarRows
    {allowed : Finset ℕ}
    {Aweight base Kcut : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (h :
      TaoSection7Case3BaseKcutScalarRowInputs
        allowed Aweight base Kcut constants) :
    TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs
      allowed Aweight base Kcut constants where
  base_ge_four := h.base_ge_four
  polynomialBudget := h.polynomialBudget
  exponentialBudget := h.exponentialBudget
  polynomial_nonneg := h.polynomial_nonneg
  exponential_nonneg := h.exponential_nonneg
  polynomial_sum_le := h.polynomial_sum_le
  exponential_sum_le := h.exponential_sum_le
  scalar_tail_budget := h.scalar_tail_budget

end

end Tao

end Erdos1135Predecessor
