/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section6.FixedAmbientSlice
import Erdos1135SecondScale.Tao.Section6.Geom2IntervalConcentration

/-!
# Section 6 High-Regime Mixing

This leaf performs the numerical Section 6 closeout in the high regime.  It
sums the fixed-ambient slice estimates, charges the global exceptional event
once, and preserves one spare power for the later adjacent-scale telescope.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Exact cardinality of the bounded stopping-index/weight box. -/
theorem taoSection6LocalGateIndex_card (n : ℕ) :
    Fintype.card (taoSection6LocalGateIndex n) = n * (2 * n) := by
  simp [taoSection6LocalGateIndex]

/-- The smallest nontrivial local-gate box has eight entries. -/
theorem taoSection6LocalGateIndex_card_two :
    Fintype.card (taoSection6LocalGateIndex 2) = 8 := by
  norm_num [taoSection6LocalGateIndex_card]

/-- Multiplying the per-slice `n^(-(A+3))` rate by the exact box cardinality
spends precisely two powers of `n`. -/
theorem taoSection6_box_mul_div_pow_eq
    (A n : ℕ) (D : ℝ) (hn : 1 ≤ n) :
    (((n * (2 * n) : ℕ) : ℝ) *
        (D / (n : ℝ) ^ (A + 3))) =
      (2 * D) / (n : ℝ) ^ (A + 1) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [show A + 3 = (A + 1) + 2 by omega, pow_add]
  push_cast
  field_simp [hnR]

/-- Uniform fixed-slice bounds sum to the expected high-regime rate. -/
theorem taoSection6FixedAmbientOscillation_sum_le
    {CA D : ℝ} {A n m : ℕ} (hn : 1 ≤ n)
    (hslice : ∀ k : Fin n, ∀ l : Fin (2 * n),
      taoZModPowOscillation m n
          (taoSection6FixedAmbientSubmass CA n k l) ≤
        D / (n : ℝ) ^ (A + 3)) :
    (∑ k : Fin n, ∑ l : Fin (2 * n),
      taoZModPowOscillation m n
        (taoSection6FixedAmbientSubmass CA n k l)) ≤
      (2 * D) / (n : ℝ) ^ (A + 1) := by
  let B : ℝ := D / (n : ℝ) ^ (A + 3)
  calc
    (∑ k : Fin n, ∑ l : Fin (2 * n),
        taoZModPowOscillation m n
          (taoSection6FixedAmbientSubmass CA n k l)) ≤
        ∑ _k : Fin n, ∑ _l : Fin (2 * n), B := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      exact hslice k l
    _ = (((n * (2 * n) : ℕ) : ℝ) * B) := by
      simp [Nat.cast_mul]
      ring
    _ = (2 * D) / (n : ℝ) ^ (A + 1) := by
      exact taoSection6_box_mul_div_pow_eq A n D hn

/-- Proposition 1.17 implies the stronger Section 6 estimate in the
high regime `0.9n ≤ m ≤ n`.  The output retains one extra ambient power for
the later adjacent-scale summation. -/
theorem TaoProp117PrimitivePolynomialDecayStatement.exists_syracFineScaleOscillation_le_highRegime
    (h117 : TaoProp117PrimitivePolynomialDecayStatement)
    (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ n m : ℕ, N0 ≤ n →
        m ≤ n →
        9 * n ≤ 10 * m →
        syracFineScaleOscillation m n ≤
          C / (n : ℝ) ^ (A + 1) := by
  let CA : ℝ := 8 * ((A : ℝ) + 4)
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hCA : (17 : ℝ) ≤ CA := by
    dsimp [CA]
    nlinarith
  obtain ⟨D, hD, Nslice, hslice⟩ :=
    h117.exists_taoSection6FixedAmbientOscillation_le CA hCA A
  obtain ⟨Nevent, hNevent, hevent⟩ :=
    exists_syracFineScaleOscillation_le_fixedAmbient_sum_add_globalFailure
      CA hCA
  refine ⟨2 * D + 2, by nlinarith, max Nslice Nevent,
    hNevent.trans (le_max_right _ _), ?_⟩
  intro n m hn hmn hhigh
  have hnSlice : Nslice ≤ n := (le_max_left _ _).trans hn
  have hnEvent : Nevent ≤ n := (le_max_right _ _).trans hn
  have hnTwo : 2 ≤ n := hNevent.trans hnEvent
  have hnOne : 1 ≤ n := by omega
  have hslices :
      (∑ k : Fin n, ∑ l : Fin (2 * n),
        taoZModPowOscillation m n
          (taoSection6FixedAmbientSubmass CA n k l)) ≤
        (2 * D) / (n : ℝ) ^ (A + 1) := by
    apply taoSection6FixedAmbientOscillation_sum_le hnOne
    intro k l
    exact hslice n k l m hnSlice (by omega) hmn hhigh
  have hfailure :
      2 * taoSection6GlobalFailureMass CA n ≤
        2 / (n : ℝ) ^ (A + 1) := by
    have h := taoSection6GlobalFailureMass_le_inv_pow A hnTwo
    dsimp [CA]
    calc
      2 * taoSection6GlobalFailureMass (8 * ((A : ℝ) + 4)) n ≤
          2 * (1 / (n : ℝ) ^ (A + 1)) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
      _ = 2 / (n : ℝ) ^ (A + 1) := by ring
  calc
    syracFineScaleOscillation m n ≤
        (∑ k : Fin n, ∑ l : Fin (2 * n),
          taoZModPowOscillation m n
            (taoSection6FixedAmbientSubmass CA n k l)) +
          2 * taoSection6GlobalFailureMass CA n :=
      hevent n hnEvent m hmn
    _ ≤ (2 * D) / (n : ℝ) ^ (A + 1) +
        2 / (n : ℝ) ^ (A + 1) := add_le_add hslices hfailure
    _ = (2 * D + 2) / (n : ℝ) ^ (A + 1) := by ring

/-- Exponent-zero canary for the stronger high-regime endpoint. -/
theorem TaoProp117PrimitivePolynomialDecayStatement.exists_syracFineScaleOscillation_le_highRegime_zero
    (h117 : TaoProp117PrimitivePolynomialDecayStatement) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ n m : ℕ, N0 ≤ n →
        m ≤ n →
        9 * n ≤ 10 * m →
        syracFineScaleOscillation m n ≤ C / (n : ℝ) := by
  simpa using h117.exists_syracFineScaleOscillation_le_highRegime 0

/-- The diagonal `m=n` always lies in the high regime. -/
theorem taoSection6_diagonal_highRegime (n : ℕ) :
    9 * n ≤ 10 * n := by omega

end

end Tao
end Erdos1135SecondScale
