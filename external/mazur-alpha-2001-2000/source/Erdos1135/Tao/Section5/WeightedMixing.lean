import Erdos1135.Tao.Fourier.MixingStatement

/-!
# Section 5 Weighted Mixing Algebra

This leaf owns the coefficient norm and the generic weighted consequence of
Tao's full-L1 Syracuse oscillation.  It has no source window, passage event,
typicality, or Common-Z dependency.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

/-- Coefficient/test functions appearing in the Section 5 fine-scale mixing step. -/
abbrev TaoSection5CoefficientFunction (k : ℕ) : Type :=
  ZMod (3 ^ k) → ℝ

/-- Full-L1 size of a finite coefficient/test function. -/
def taoSection5CoefficientL1
    (k : ℕ) (c : TaoSection5CoefficientFunction k) : ℝ := by
  classical
  exact ∑ x : ZMod (3 ^ k), |c x|

/-- Pointwise coefficient bound matching the source role of Lemma 5.3. -/
def TaoSection5CoefficientSupBound
    (k : ℕ) (c : TaoSection5CoefficientFunction k) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ X : ZMod (3 ^ k), |c X| ≤ C

/-- Weighted fine-scale Syracuse term before fiber averaging. -/
def taoSection5FineSyracWeightedTerm
    (k : ℕ) (c : TaoSection5CoefficientFunction k) : ℝ := by
  classical
  exact ∑ X : ZMod (3 ^ k), c X * syracPMFMassVector k X

/-- Weighted coarse/fiber-averaged Syracuse term from Proposition 1.14. -/
def taoSection5CoarseSyracWeightedTerm
    (m k : ℕ) (c : TaoSection5CoefficientFunction k) : ℝ := by
  classical
  exact ∑ X : ZMod (3 ^ k),
    c X *
      (zmodPowFiberAverageScale m k *
        zmodPowFiberSum m k (syracPMFMassVector k) X)

/-- Absolute weighted fine/coarse error consumed in the Section 5 main-term step. -/
def taoSection5WeightedMixingError
    (m k : ℕ) (c : TaoSection5CoefficientFunction k) : ℝ :=
  |taoSection5FineSyracWeightedTerm k c -
    taoSection5CoarseSyracWeightedTerm m k c|

/-- A coefficient bounded by `C` costs at most `C` times the full-L1
Syracuse oscillation. -/
theorem taoSection5WeightedMixingError_le_sup_mul_oscillation
    {m k : ℕ} {c : TaoSection5CoefficientFunction k} {C : ℝ}
    (hC : TaoSection5CoefficientSupBound k c C) :
    taoSection5WeightedMixingError m k c ≤ C * syracFineScaleOscillation m k := by
  classical
  let delta : ZMod (3 ^ k) → ℝ := fun X =>
    syracPMFMassVector k X -
      zmodPowFiberAverageScale m k * zmodPowFiberSum m k (syracPMFMassVector k) X
  have hdiff :
      taoSection5FineSyracWeightedTerm k c -
          taoSection5CoarseSyracWeightedTerm m k c =
        ∑ X : ZMod (3 ^ k), c X * delta X := by
    rw [taoSection5FineSyracWeightedTerm, taoSection5CoarseSyracWeightedTerm,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro X _hX
    simp [delta]
    ring
  have habsSum :
      |∑ X : ZMod (3 ^ k), c X * delta X| ≤
        ∑ X : ZMod (3 ^ k), |c X * delta X| :=
    Finset.abs_sum_le_sum_abs _ _
  have hterm :
      (∑ X : ZMod (3 ^ k), |c X * delta X|) ≤
        ∑ X : ZMod (3 ^ k), C * |delta X| := by
    refine Finset.sum_le_sum ?_
    intro X _hX
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hC.2 X) (abs_nonneg _)
  have hsumC :
      (∑ X : ZMod (3 ^ k), C * |delta X|) =
        C * ∑ X : ZMod (3 ^ k), |delta X| := by
    rw [Finset.mul_sum]
  have hosc :
      syracFineScaleOscillation m k =
        ∑ X : ZMod (3 ^ k), |delta X| := by
    simp [syracFineScaleOscillation, taoZModPowOscillation, delta]
  calc
    taoSection5WeightedMixingError m k c =
        |∑ X : ZMod (3 ^ k), c X * delta X| := by
          simp [taoSection5WeightedMixingError, hdiff]
    _ ≤ ∑ X : ZMod (3 ^ k), |c X * delta X| := habsSum
    _ ≤ ∑ X : ZMod (3 ^ k), C * |delta X| := hterm
    _ = C * syracFineScaleOscillation m k := by rw [hsumC, hosc]

end

end Tao
end Erdos1135
