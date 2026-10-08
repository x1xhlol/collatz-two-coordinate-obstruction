/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.AntitoneResidueSums
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Reciprocal Sums In Natural Residue Classes

This neutral arithmetic leaf bounds an inclusive reciprocal progression by averaging the sharp
interlacing estimate for antitone weights.  It is independent of Syracuse dynamics, PMFs, and the
real endpoint rounding used later in Tao's Lemma 5.3.
-/

namespace Erdos1135SecondScale
namespace Tao

open scoped BigOperators

/-- Naturals in `[A, U]` congruent to the arbitrary representative `R` modulo `Q`. -/
def reciprocalModEqClass (A U Q R : ℕ) : Finset ℕ :=
  (Finset.Icc A U).filter fun N => N ≡ R [MOD Q]

/-- Sharp inclusive harmonic-interval estimate with the first endpoint retained. -/
theorem sum_Icc_reciprocal_le_one_div_add_log_div
    {A U : ℕ} (hA : 1 ≤ A) (hAU : A ≤ U) :
    (∑ N ∈ Finset.Icc A U, 1 / (N : ℝ)) ≤
      1 / (A : ℝ) + Real.log ((U : ℝ) / (A : ℝ)) := by
  have hApos : 0 < (A : ℝ) := by exact_mod_cast hA
  have hUpos : 0 < (U : ℝ) := by
    exact hApos.trans_le (by exact_mod_cast hAU)
  have htail :
      (∑ N ∈ Finset.Ioc A U, 1 / (N : ℝ)) ≤
        Real.log ((U : ℝ) / (A : ℝ)) := by
    calc
      (∑ N ∈ Finset.Ioc A U, 1 / (N : ℝ)) =
          ∑ N ∈ Finset.Ico A U, 1 / ((N + 1 : ℕ) : ℝ) := by
        rw [← Finset.Ico_add_one_add_one_eq_Ioc A U]
        exact (Finset.sum_Ico_add'
          (fun N : ℕ => 1 / (N : ℝ)) A U 1).symm
      _ ≤ ∫ x : ℝ in (A : ℝ)..(U : ℝ), 1 / x := by
        simpa only [one_div] using
          (@AntitoneOn.sum_le_integral_Ico A U (fun x : ℝ => x⁻¹)
            hAU (inv_antitoneOn_Icc_right hApos))
      _ = Real.log ((U : ℝ) / (A : ℝ)) :=
        integral_one_div_of_pos hApos hUpos
  rw [← Finset.Ioc_insert_left hAU,
    Finset.sum_insert (by simp : A ∉ Finset.Ioc A U)]
  simpa [add_comm] using add_le_add_right htail (1 / (A : ℝ))

private noncomputable def clampedReciprocal (A N : ℕ) : ℝ :=
  1 / ((max A N : ℕ) : ℝ)

private theorem clampedReciprocal_antitone
    {A : ℕ} (hA : 1 ≤ A) : Antitone (clampedReciprocal A) := by
  intro M N hMN
  apply one_div_le_one_div_of_le
  · exact_mod_cast hA.trans (le_max_left A M)
  · exact_mod_cast max_le_max_left A hMN

private theorem clampedReciprocal_nonneg (A N : ℕ) :
    0 ≤ clampedReciprocal A N := by
  exact one_div_nonneg.mpr (Nat.cast_nonneg _)

private theorem clampedReciprocal_eq_reciprocal
    {A N : ℕ} (hAN : A ≤ N) :
    clampedReciprocal A N = 1 / (N : ℝ) := by
  simp [clampedReciprocal, max_eq_right hAN]

/-- A reciprocal progression has one interlacing endpoint term plus the uniform average of the
sharp full-interval estimate.  Both occurrences of `1/A` are intentional. -/
theorem sum_Icc_reciprocal_modEq_le
    {A U Q R : ℕ} (hA : 1 ≤ A) (hAU : A ≤ U) (hQ : 0 < Q) :
    (∑ N ∈ reciprocalModEqClass A U Q R, 1 / (N : ℝ)) ≤
      1 / (A : ℝ) +
        (1 / (Q : ℝ)) *
          (1 / (A : ℝ) + Real.log ((U : ℝ) / (A : ℝ))) := by
  classical
  let r : Fin Q := ⟨R % Q, Nat.mod_lt R hQ⟩
  let w : ℕ → ℝ := clampedReciprocal A
  let H : Fin Q → ℝ := antitoneResidueClassSum A U Q w
  have hw : Antitone w := by
    simpa only [w] using clampedReciprocal_antitone hA
  have hw_nonneg : ∀ N, 0 ≤ w N := by
    intro N
    simpa only [w] using clampedReciprocal_nonneg A N
  have hclass :
      reciprocalModEqClass A U Q R = antitoneResidueClass A U Q r := by
    ext N
    simp [reciprocalModEqClass, antitoneResidueClass, Nat.ModEq, r]
  have hleft :
      (∑ N ∈ reciprocalModEqClass A U Q R, 1 / (N : ℝ)) = H r := by
    rw [hclass]
    change (∑ N ∈ antitoneResidueClass A U Q r, 1 / (N : ℝ)) =
      ∑ N ∈ antitoneResidueClass A U Q r, w N
    apply Finset.sum_congr rfl
    intro N hN
    exact (by
      simpa only [w] using
        (clampedReciprocal_eq_reciprocal
          (mem_antitoneResidueClass.mp hN).1).symm)
  have hsum :
      (Q : ℝ) * H r ≤ (Q : ℝ) * w A + ∑ s : Fin Q, H s := by
    calc
      (Q : ℝ) * H r = ∑ _s : Fin Q, H r := by simp
      _ ≤ ∑ s : Fin Q, (w A + H s) := by
        exact Finset.sum_le_sum fun s _hs =>
          antitoneResidueClassSum_le_add hQ w
            hw hw_nonneg r s
      _ = (Q : ℝ) * w A + ∑ s : Fin Q, H s := by
        simp only [Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hQreal : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have havg :
      H r ≤ w A + (1 / (Q : ℝ)) * ∑ s : Fin Q, H s := by
    calc
      H r ≤ ((Q : ℝ) * w A + ∑ s : Fin Q, H s) / (Q : ℝ) := by
        apply (le_div_iff₀ hQreal).2
        simpa [mul_comm] using hsum
      _ = w A + (1 / (Q : ℝ)) * ∑ s : Fin Q, H s := by
        field_simp [ne_of_gt hQreal]
  have htotal :
      (∑ s : Fin Q, H s) =
        ∑ N ∈ Finset.Icc A U, 1 / (N : ℝ) := by
    rw [show (∑ s : Fin Q, H s) =
        ∑ N ∈ Finset.Icc A U, w N by
      simpa only [H] using sum_antitoneResidueClassSum hQ w]
    apply Finset.sum_congr rfl
    intro N hN
    exact clampedReciprocal_eq_reciprocal (Finset.mem_Icc.mp hN).1
  rw [hleft]
  calc
    H r ≤ w A + (1 / (Q : ℝ)) * ∑ s : Fin Q, H s := havg
    _ = 1 / (A : ℝ) +
        (1 / (Q : ℝ)) *
          (∑ N ∈ Finset.Icc A U, 1 / (N : ℝ)) := by
      rw [htotal]
      simp [w, clampedReciprocal]
    _ ≤ 1 / (A : ℝ) +
        (1 / (Q : ℝ)) *
          (1 / (A : ℝ) + Real.log ((U : ℝ) / (A : ℝ))) := by
      gcongr
      exact sum_Icc_reciprocal_le_one_div_add_log_div hA hAU

end Tao
end Erdos1135SecondScale
