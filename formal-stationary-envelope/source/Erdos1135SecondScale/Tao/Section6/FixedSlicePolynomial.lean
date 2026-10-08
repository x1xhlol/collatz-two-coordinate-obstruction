/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section6.FixedSliceSource
import Erdos1135SecondScale.Tao.Section6.HeadEntropyScalar

/-!
# Section 6 Polynomial Fixed-Slice Bound

This leaf absorbs the head entropy factor into a deliberately coarse natural
exponent and applies primitive Proposition 1.17 at that exponent.  The cutoff
branch is internal: below the strict crossing threshold the gated slice is
empty.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- The source-facing squared slice estimate after absorbing the head entropy
factor.  No cutoff or head witness remains in the statement. -/
theorem exists_taoSection6FixedSliceOscillation_sq_le_headEntropy
    {B : ℕ} {C : ℝ}
    (hdecay : syracPMFPrimitivePolynomialDecayAt B C)
    (hC : 0 ≤ C)
    (CA : ℝ) (hCA : 17 ≤ CA) :
    ∃ N0 : ℕ, ∀ T k l m : ℕ,
      N0 ≤ T + (k + 1) →
      m ≤ T + (k + 1) →
      9 * (T + (k + 1)) ≤ 10 * m →
      taoZModPowOscillation m (T + (k + 1))
          (taoSection6GatedSourceSubmass CA T k l) ^ 2 ≤
        taoSection6TailDecayDelta C B (T + (k + 1)) ^ 2 *
          ((T + (k + 1) : ℕ) : ℝ) ^ taoSection6HeadEntropyExponent CA := by
  obtain ⟨N0, hsource⟩ :=
    exists_taoSection6FixedSliceOscillation_sq_le hdecay hC CA hCA
  refine ⟨N0, ?_⟩
  intro T k l m hn hmn hm
  let n := T + (k + 1)
  have hn_pos : 1 ≤ n := by omega
  by_cases hl : taoCor63StarQ CA n < (l : ℝ)
  · have hraw := hsource T k l m hn hmn hm
    have hent := taoSection6HeadEntropyFactor_lt_pow hn_pos hl
    calc
      taoZModPowOscillation m n (taoSection6GatedSourceSubmass CA T k l) ^ 2 ≤
          taoSection6TailDecayDelta C B n ^ 2 *
            (((3 ^ n : ℕ) : ℝ)) * (1 / 2 : ℝ) ^ l := by
        simpa [n] using hraw
      _ = taoSection6TailDecayDelta C B n ^ 2 *
            taoSection6HeadEntropyFactor n l := by
        simp only [taoSection6HeadEntropyFactor]
        ring
      _ ≤ taoSection6TailDecayDelta C B n ^ 2 *
            (n : ℝ) ^ taoSection6HeadEntropyExponent CA :=
        mul_le_mul_of_nonneg_left (le_of_lt hent) (sq_nonneg _)
  · have hgate : ¬ ∃ head : List ℕ+,
        taoSection6HeadGate CA n k l head := by
      rintro ⟨head, hhead⟩
      apply hl
      simpa [taoSection6HeadGate_weight hhead] using
        (taoSection6HeadGate_crossing hhead).2
    have hzero :=
      taoSection6FixedSliceOscillation_eq_zero_of_headGate_empty
        (CA := CA) (T := T) (k := k) (l := l) (m := m) hgate
    have hrhs :
        0 ≤ taoSection6TailDecayDelta C B n ^ 2 *
          (n : ℝ) ^ taoSection6HeadEntropyExponent CA :=
      mul_nonneg (sq_nonneg _) (pow_nonneg (by positivity) _)
    simpa [n, hzero] using hrhs

/-- Primitive Proposition 1.17 supplies a polynomial fixed-slice rate uniform
in both stopping and weight indices. -/
theorem TaoProp117PrimitivePolynomialDecayStatement.exists_taoSection6FixedSliceOscillation_le
    (h117 : TaoProp117PrimitivePolynomialDecayStatement)
    (CA : ℝ) (hCA : 17 ≤ CA) (A : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ N0 : ℕ, ∀ T k l m : ℕ,
      N0 ≤ T + (k + 1) →
      m ≤ T + (k + 1) →
      9 * (T + (k + 1)) ≤ 10 * m →
      taoZModPowOscillation m (T + (k + 1))
          (taoSection6GatedSourceSubmass CA T k l) ≤
        D / ((T + (k + 1) : ℕ) : ℝ) ^ (A + 3) := by
  let P := taoSection6HeadEntropyExponent CA
  let B := A + P + 3
  have hB : 0 < B := by omega
  obtain ⟨C, hC, hdecay⟩ := h117.bound hB
  let D := C * (20 : ℝ) ^ B
  have hD : 0 ≤ D := mul_nonneg hC (pow_nonneg (by norm_num) _)
  obtain ⟨N0, hsq⟩ :=
    exists_taoSection6FixedSliceOscillation_sq_le_headEntropy
      hdecay hC CA hCA
  refine ⟨D, hD, N0, ?_⟩
  intro T k l m hn hmn hm
  let n := T + (k + 1)
  have hn_nat : 1 ≤ n := by omega
  have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_nat
  have hn_pos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn_real
  have hsq' := hsq T k l m hn hmn hm
  have hpowB : (n : ℝ) ^ B = (n : ℝ) ^ (A + 3) * (n : ℝ) ^ P := by
    rw [show B = (A + 3) + P by omega, pow_add]
  have hdelta :
      taoSection6TailDecayDelta C B n =
        (D / (n : ℝ) ^ (A + 3)) / (n : ℝ) ^ P := by
    rw [taoSection6TailDecayDelta, hpowB]
    dsimp [D]
    field_simp
  have hP_one : (1 : ℝ) ≤ (n : ℝ) ^ P := one_le_pow₀ hn_real
  have hP_pos : (0 : ℝ) < (n : ℝ) ^ P := by positivity
  let R := D / (n : ℝ) ^ (A + 3)
  have hscalar :
      (taoSection6TailDecayDelta C B n) ^ 2 * (n : ℝ) ^ P ≤ R ^ 2 := by
    rw [hdelta]
    change (R / (n : ℝ) ^ P) ^ 2 * (n : ℝ) ^ P ≤ R ^ 2
    rw [div_pow]
    field_simp
    nlinarith [sq_nonneg R]
  have hosc_sq :
      taoZModPowOscillation m n (taoSection6GatedSourceSubmass CA T k l) ^ 2 ≤
        R ^ 2 := by
    have hsq'' :
        taoZModPowOscillation m n (taoSection6GatedSourceSubmass CA T k l) ^ 2 ≤
          taoSection6TailDecayDelta C B n ^ 2 * (n : ℝ) ^ P := by
      simpa [n, P] using hsq'
    exact hsq''.trans hscalar
  have hosc_nonneg :
      0 ≤ taoZModPowOscillation m n (taoSection6GatedSourceSubmass CA T k l) := by
    simp only [taoZModPowOscillation]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hR_nonneg : 0 ≤ R := by
    exact div_nonneg hD (pow_nonneg (by positivity) _)
  have hosc :
      taoZModPowOscillation m n (taoSection6GatedSourceSubmass CA T k l) ≤ R := by
    nlinarith [sq_nonneg
      (taoZModPowOscillation m n (taoSection6GatedSourceSubmass CA T k l) - R)]
  simpa [n, R] using hosc

end

end Tao
end Erdos1135SecondScale
