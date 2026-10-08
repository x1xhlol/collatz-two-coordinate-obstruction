/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section6.Corollary63
import Erdos1135SecondScale.Tao.Renewal.Prop78Case3EStarSupportProducer
import Mathlib.Analysis.PSeries

/-!
# Proposition 7.8 Case 3 Base-Kcut Finite-Sum Absorption

This module splits the base-repaired `E*_used` finite-sum budget into the two
scalar rows visible in Tao's Case 3 argument: the polynomial large-triangle
tail and the exponential Lemma 7.10 tail.  It also proves the first scalar row
microfacts: canonical polynomial normalization, finite-range inverse-square
control, and finite-range exponential-tail control.

The final polynomial/exponential absorption and scalar tail comparison are
still explicit source-facing obligations, since they require a real
`Kcut`/`Aweight` slack schedule.
-/

namespace Erdos1135SecondScale
namespace Tao

open scoped BigOperators

noncomputable section

/-- Polynomial part of the base-repaired Lemma 7.10 per-offset budget. -/
def taoSection7Case3BaseKcutPolynomialBudgetTerm
    (constants : TaoSection7Lemma710Constants)
    (Aweight base Kcut p : ℕ) : ℝ :=
  constants.C710 *
    (((Aweight : ℝ) ^ 2 * (1 + (p : ℝ))) /
      taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut p)

/-- Exponential part of the base-repaired Lemma 7.10 per-offset budget. -/
def taoSection7Case3BaseKcutExponentialBudgetTerm
    (constants : TaoSection7Lemma710Constants)
    (Aweight p : ℕ) : ℝ :=
  constants.C710 *
    Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2 * (1 + (p : ℝ))))

/--
Canonical scalar multiplier for the polynomial row after expanding the
base-`Kcut` large-triangle threshold.
-/
noncomputable def taoSection7Case3BaseKcutPolynomialScale
    (constants : TaoSection7Lemma710Constants)
    (Aweight base Kcut : ℕ) : ℝ :=
  constants.C710 * (Aweight : ℝ) ^ 2 / ((base : ℝ) ^ Kcut)

/--
Exact normalization of the polynomial row into the canonical scale times the
inverse-square offset summand.
-/
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

theorem taoSection7Case3BaseKcut_polynomial_sum_le_scale_mul_two_of_subset_range
    {allowed : Finset ℕ} {Aweight base Kcut m : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (hbase : 0 < base)
    (hsub : ∀ p, p ∈ allowed → p < m) :
    allowed.sum
        (fun p =>
          taoSection7Case3BaseKcutPolynomialBudgetTerm
            constants Aweight base Kcut p) ≤
      taoSection7Case3BaseKcutPolynomialScale constants Aweight base Kcut * 2 := by
  calc
    allowed.sum
        (fun p =>
          taoSection7Case3BaseKcutPolynomialBudgetTerm
            constants Aweight base Kcut p)
        ≤ allowed.sum
            (fun p =>
              taoSection7Case3BaseKcutPolynomialScale constants Aweight base Kcut *
                (((1 : ℝ) + (p : ℝ)) ^ 2)⁻¹) :=
          Finset.sum_le_sum
            (taoSection7Case3BaseKcut_polynomial_pointwise_le_canonical
              (allowed := allowed) (Aweight := Aweight) (base := base)
              (Kcut := Kcut) (constants := constants) hbase)
    _ = taoSection7Case3BaseKcutPolynomialScale constants Aweight base Kcut *
          allowed.sum (fun p => (((1 : ℝ) + (p : ℝ)) ^ 2)⁻¹) := by
          rw [Finset.mul_sum]
    _ ≤ taoSection7Case3BaseKcutPolynomialScale constants Aweight base Kcut * 2 :=
          mul_le_mul_of_nonneg_left
            (taoSection7Case3_invSq_sum_le_two_of_subset_range
              (allowed := allowed) (m := m) hsub)
            (taoSection7Case3BaseKcutPolynomialScale_nonneg
              (constants := constants) (Aweight := Aweight) (base := base)
              (Kcut := Kcut) hbase)

/--
Generic two-row split inputs for the base-repaired finite-sum packet.

This is the pure finite-sum algebra socket: source-facing producers may choose
their own row terms, as long as the per-offset budget is split pointwise and
the two row sums are absorbed by the named scalar budgets.
-/
structure TaoSection7Case3BaseKcutBudgetSplitInputs
    (allowed : Finset ℕ) (perBudget : ℕ → ℝ)
    (Aweight base Kcut : ℕ) where
  base_ge_four : 4 ≤ base
  polynomialTerm : ℕ → ℝ
  exponentialTerm : ℕ → ℝ
  polynomialBudget : ℝ
  exponentialBudget : ℝ
  polynomial_nonneg : 0 ≤ polynomialBudget
  exponential_nonneg : 0 ≤ exponentialBudget
  perBudget_split :
    ∀ p, p ∈ allowed →
      perBudget p = polynomialTerm p + exponentialTerm p
  polynomial_sum_le : allowed.sum polynomialTerm ≤ polynomialBudget
  exponential_sum_le : allowed.sum exponentialTerm ≤ exponentialBudget
  scalar_tail_budget :
    polynomialBudget + exponentialBudget ≤
      (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut)

def TaoSection7Case3BaseKcutFiniteSumBudgetPacket.of_splitInputs
    {allowed : Finset ℕ} {perBudget : ℕ → ℝ}
    {Aweight base Kcut : ℕ}
    (h :
      TaoSection7Case3BaseKcutBudgetSplitInputs
        allowed perBudget Aweight base Kcut) :
    TaoSection7Case3BaseKcutFiniteSumBudgetPacket
      allowed perBudget Aweight base Kcut where
  base_ge_four := h.base_ge_four
  polynomialBudget := h.polynomialBudget
  exponentialBudget := h.exponentialBudget
  polynomial_nonneg := h.polynomial_nonneg
  exponential_nonneg := h.exponential_nonneg
  sum_perBudget_le := by
    calc
      allowed.sum perBudget =
          allowed.sum (fun p => h.polynomialTerm p + h.exponentialTerm p) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            exact h.perBudget_split p hp
      _ = allowed.sum h.polynomialTerm + allowed.sum h.exponentialTerm := by
            rw [Finset.sum_add_distrib]
      _ ≤ h.polynomialBudget + h.exponentialBudget :=
            add_le_add h.polynomial_sum_le h.exponential_sum_le
  scalar_tail_budget := h.scalar_tail_budget

/--
Two-row scalar absorption inputs for the base-repaired finite-sum packet.

The row estimates are still future analytic/scalar work; this record merely
keeps them separated so downstream support cannot hide the source split inside
a raw finite-sum inequality.
-/
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

/--
Source-facing scalar-row inputs for the base-repaired finite-sum absorption.

This record is one step closer to the analytic source proof than
`TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs`: it derives the two row
sums from an inverse-square summation input, an exponential-tail summation
input, and two scalar absorption inequalities.
-/
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

/--
Scalar-tail schedule package for the base-`Kcut` Case 3 row.

This keeps the exponential absorption and final tail comparison separate from
the row-summation facts.  A source producer for this record must include the
missing upper/slack comparison between `Kcut` and `Aweight^2`; the existing
lower bound `4 * Aweight <= Kcut` is not enough by itself.
-/
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

/-- The unit final scalar budget used by the exact base-`Kcut` row socket. -/
noncomputable def taoSection7Case3BaseKcutUnitTailBudget
    (Aweight Kcut : ℕ) : ℝ :=
  (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut)

theorem taoSection7Case3BaseKcutUnitTailBudget_nonneg
    (Aweight Kcut : ℕ) :
    0 ≤ taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut := by
  unfold taoSection7Case3BaseKcutUnitTailBudget
  exact div_nonneg (sq_nonneg _)
    (le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 4) Kcut))

/-- Source-sized shifted exponential tail for the base-`Kcut` Case 3 row. -/
noncomputable def taoSection7Case3BaseKcutSharpExpTail
    (constants : TaoSection7Lemma710Constants)
    (Aweight : ℕ) : ℝ :=
  Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2)) *
    (1 - Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2)))⁻¹

/--
Factorized slack schedule for the base-`Kcut` scalar tail.

This is still a schedule interface: the polynomial base slack and exponential
`Kcut` slack are explicit fields.  It deliberately separates the two scalar
absorption issues so `4 * Aweight <= Kcut` cannot be mistaken for final budget
evidence.
-/
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

def TaoSection7Case3BaseKcutScalarTailSchedule.of_factorizedSlack
    {Aweight base Kcut : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (h :
      TaoSection7Case3BaseKcutFactorizedSlackSchedule
        Aweight base Kcut constants) :
    TaoSection7Case3BaseKcutScalarTailSchedule Aweight Kcut constants :=
  h.to_tailSchedule

theorem taoSection7Case3BaseKcut_polynomial_absorb_of_factorizedSlack
    {Aweight base Kcut : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (h :
      TaoSection7Case3BaseKcutFactorizedSlackSchedule
        Aweight base Kcut constants) :
    taoSection7Case3BaseKcutPolynomialScale constants Aweight base Kcut * 2 ≤
      h.polySlack *
        taoSection7Case3BaseKcutUnitTailBudget Aweight Kcut :=
  h.polynomial_absorb

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

/--
Finite shifted exponential-tail bound for an allowed set contained in
`range m`.
-/
theorem taoSection7Case3_exp_shifted_sum_le_inv_one_sub_of_subset_range
    {allowed : Finset ℕ} {m : ℕ} {c : ℝ}
    (hc : 0 < c)
    (hsub : ∀ p, p ∈ allowed → p < m) :
    allowed.sum (fun p => Real.exp (-(c * (1 + (p : ℝ))))) ≤
      (1 - Real.exp (-c))⁻¹ := by
  have hsubset : allowed ⊆ Finset.range m := by
    intro p hp
    exact Finset.mem_range.2 (hsub p hp)
  calc
    allowed.sum (fun p => Real.exp (-(c * (1 + (p : ℝ)))))
        ≤ allowed.sum (fun p => Real.exp (-c * (p : ℝ))) := by
          refine Finset.sum_le_sum ?_
          intro p _hp
          have hp_le : (p : ℝ) ≤ 1 + (p : ℝ) := by norm_num
          have hmul : c * (p : ℝ) ≤ c * (1 + (p : ℝ)) :=
            mul_le_mul_of_nonneg_left hp_le (le_of_lt hc)
          exact Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ (Finset.range m).sum (fun p => Real.exp (-c * (p : ℝ))) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
            intro p _hp _hnot
            exact le_of_lt (Real.exp_pos _))
    _ ≤ (1 - Real.exp (-c))⁻¹ :=
          finite_exp_neg_mul_sum_le_inv_one_sub (c := c) hc m

/--
Coarse Case 3 exponential-tail row bound from a finite allowed-offset range.

This denominator-only bound is useful as a general auxiliary; the
source-sized scalar row should use the sharper shifted theorem below, which
retains the leading `exp (-(c710 * Aweight^2))` factor.
-/
theorem taoSection7Case3BaseKcut_exponential_sum_le_inv_one_sub_of_subset_range
    {allowed : Finset ℕ} {Aweight m : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (hA : 0 < Aweight)
    (hsub : ∀ p, p ∈ allowed → p < m) :
    allowed.sum
        (fun p =>
          Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2 * (1 + (p : ℝ))))) ≤
      (1 - Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2)))⁻¹ := by
  have hAreal : 0 < (Aweight : ℝ) := by
    exact_mod_cast hA
  have hc : 0 < constants.c710 * (Aweight : ℝ) ^ 2 :=
    mul_pos constants.c710_pos (pow_pos hAreal 2)
  simpa [mul_assoc] using
    (taoSection7Case3_exp_shifted_sum_le_inv_one_sub_of_subset_range
      (allowed := allowed) (m := m)
      (c := constants.c710 * (Aweight : ℝ) ^ 2) hc hsub)

/--
Sharp finite shifted exponential-tail bound for an allowed set contained in
`range m`, retaining the leading shifted factor `exp (-c)`.
-/
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

/--
Case 3 source-sized exponential-tail row bound from a finite allowed-offset
range, retaining the leading shifted factor.
-/
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

def TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs.to_splitInputs
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {allowed : Finset ℕ}
    {Aweight base Kcut : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (h :
      TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs
        allowed Aweight base Kcut constants)
    (perOffset :
      TaoSection7Case3BaseKcutPerOffsetProbabilityPacket
        μ pointAt family allowed Aweight base Kcut constants) :
    TaoSection7Case3BaseKcutBudgetSplitInputs
      allowed perOffset.perBudget Aweight base Kcut where
  base_ge_four := h.base_ge_four
  polynomialTerm :=
    fun p =>
      taoSection7Case3BaseKcutPolynomialBudgetTerm
        constants Aweight base Kcut p
  exponentialTerm :=
    fun p =>
      taoSection7Case3BaseKcutExponentialBudgetTerm
        constants Aweight p
  polynomialBudget := h.polynomialBudget
  exponentialBudget := h.exponentialBudget
  polynomial_nonneg := h.polynomial_nonneg
  exponential_nonneg := h.exponential_nonneg
  perBudget_split := by
    intro p hp
    rw [perOffset.perBudget_eq p hp]
    rfl
  polynomial_sum_le := h.polynomial_sum_le
  exponential_sum_le := h.exponential_sum_le
  scalar_tail_budget := h.scalar_tail_budget

theorem TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs.sum_perBudget_le
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {allowed : Finset ℕ}
    {Aweight base Kcut : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (h :
      TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs
        allowed Aweight base Kcut constants)
    (perOffset :
      TaoSection7Case3BaseKcutPerOffsetProbabilityPacket
        μ pointAt family allowed Aweight base Kcut constants) :
    allowed.sum perOffset.perBudget ≤ h.polynomialBudget + h.exponentialBudget :=
  by
    simpa [TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs.to_splitInputs] using
      (TaoSection7Case3BaseKcutFiniteSumBudgetPacket.of_splitInputs
        (h.to_splitInputs perOffset)).sum_perBudget_le

/--
Build the existing base-repaired finite-sum packet from separated scalar rows.
-/
def TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs.to_budgetPacket
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {allowed : Finset ℕ}
    {Aweight base Kcut : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (h :
      TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs
        allowed Aweight base Kcut constants)
    (perOffset :
      TaoSection7Case3BaseKcutPerOffsetProbabilityPacket
        μ pointAt family allowed Aweight base Kcut constants) :
    TaoSection7Case3BaseKcutFiniteSumBudgetPacket
      allowed perOffset.perBudget Aweight base Kcut :=
  TaoSection7Case3BaseKcutFiniteSumBudgetPacket.of_splitInputs
    (h.to_splitInputs perOffset)

/--
Probability-bound consumer using separated base-Kcut scalar absorption inputs.

This is still conditional on the deterministic cover, admissibility schedule,
per-offset Lemma 7.10 packet, and the two scalar row estimates.
-/
theorem taoSection7Case3_prob_EStarUsed_le_of_baseKcutAbsorptionInputs
    {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {EStarUsed : Set Ω}
    {Aweight base Kcut m : ℕ}
    {inspected : Set ℕ}
    {constants : TaoSection7Lemma710Constants}
    (cover :
      TaoSection7Case3EStarUsedBaseKcutCover
        pointAt family EStarUsed base Kcut inspected)
    (admissible :
      TaoSection7Case3BaseKcutAdmissibilitySchedule
        cover.allowed base m Kcut)
    (perOffset :
      TaoSection7Case3BaseKcutPerOffsetProbabilityPacket
        μ pointAt family cover.allowed Aweight base Kcut constants)
    (absorption :
      TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs
        cover.allowed Aweight base Kcut constants) :
    pmfProb μ EStarUsed ≤ (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut) :=
  taoSection7Case3_prob_EStarUsed_le_of_baseKcutPackets
    (μ := μ) cover admissible perOffset
    (absorption.to_budgetPacket perOffset)

/--
Same-parameter scalar schedule for the base-`Kcut` finite-sum packet.

This ties the factorized scalar slack to the same admissibility schedule,
`Aweight`, `Kcut`, allowed offsets, and `m` used by the per-offset Lemma 7.10
packet.  It is not a source proof of the slack inequalities; those remain
fields of `factorizedSlack`.
-/
structure TaoSection7Case3BaseKcutSourcePinnedScalarSchedule
    (allowed : Finset ℕ)
    (Aweight base Kcut m : ℕ)
    (constants : TaoSection7Lemma710Constants) where
  factorizedSlack :
    TaoSection7Case3BaseKcutFactorizedSlackSchedule
      Aweight base Kcut constants
  admissible :
    TaoSection7Case3BaseKcutAdmissibilitySchedule allowed base m Kcut
  Aweight_large : 3 ≤ Aweight
  kcut_large : 4 * Aweight ≤ Kcut
  allowed_subset_range : ∀ p, p ∈ allowed → p < m

theorem TaoSection7Case3BaseKcutSourcePinnedScalarSchedule.Aweight_pos
    {allowed : Finset ℕ}
    {Aweight base Kcut m : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (h :
      TaoSection7Case3BaseKcutSourcePinnedScalarSchedule
        allowed Aweight base Kcut m constants) :
    0 < Aweight :=
  lt_of_lt_of_le (by norm_num : 0 < 3) h.Aweight_large

def TaoSection7Case3BaseKcutSourcePinnedScalarSchedule.to_scalarRows
    {allowed : Finset ℕ}
    {Aweight base Kcut m : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (h :
      TaoSection7Case3BaseKcutSourcePinnedScalarSchedule
        allowed Aweight base Kcut m constants) :
    TaoSection7Case3BaseKcutScalarRowInputs
      allowed Aweight base Kcut constants :=
  TaoSection7Case3BaseKcutScalarRowInputs.of_factorizedSlackSchedule
    (allowed := allowed) (Aweight := Aweight) (base := base)
    (Kcut := Kcut) (m := m) (constants := constants)
    h.factorizedSlack h.Aweight_pos h.allowed_subset_range

def TaoSection7Case3BaseKcutSourcePinnedScalarSchedule.to_absorptionInputs
    {allowed : Finset ℕ}
    {Aweight base Kcut m : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (h :
      TaoSection7Case3BaseKcutSourcePinnedScalarSchedule
        allowed Aweight base Kcut m constants) :
    TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs
      allowed Aweight base Kcut constants :=
  TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs.of_scalarRows
    h.to_scalarRows

def TaoSection7Case3BaseKcutSourcePinnedScalarSchedule.to_budgetPacket
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {allowed : Finset ℕ}
    {Aweight base Kcut m : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (h :
      TaoSection7Case3BaseKcutSourcePinnedScalarSchedule
        allowed Aweight base Kcut m constants)
    (perOffset :
      TaoSection7Case3BaseKcutPerOffsetProbabilityPacket
        μ pointAt family allowed Aweight base Kcut constants) :
    TaoSection7Case3BaseKcutFiniteSumBudgetPacket
      allowed perOffset.perBudget Aweight base Kcut :=
  h.to_absorptionInputs.to_budgetPacket perOffset

theorem taoSection7Case3_prob_EStarUsed_le_of_factorizedSourceSchedule
    {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {EStarUsed : Set Ω}
    {Aweight base Kcut m : ℕ}
    {inspected : Set ℕ}
    {constants : TaoSection7Lemma710Constants}
    (cover :
      TaoSection7Case3EStarUsedBaseKcutCover
        pointAt family EStarUsed base Kcut inspected)
    (schedule :
      TaoSection7Case3BaseKcutSourcePinnedScalarSchedule
        cover.allowed Aweight base Kcut m constants)
    (perOffset :
      TaoSection7Case3BaseKcutPerOffsetProbabilityPacket
        μ pointAt family cover.allowed Aweight base Kcut constants) :
    pmfProb μ EStarUsed ≤ (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut) :=
  taoSection7Case3_prob_EStarUsed_le_of_baseKcutPackets
    (μ := μ) cover schedule.admissible perOffset
    (schedule.to_budgetPacket perOffset)

end

end Tao
end Erdos1135SecondScale
