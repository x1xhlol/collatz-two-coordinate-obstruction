/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Section 5 Payload-Free Coefficient

This neutral owner contains Tao's elementary residue-fiber coefficient and its
generic finite partition identity.  It has no Section 6, PMF, or schedule
dependency.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Payload-free form of Tao's coefficient `c_n` from `(5.23)`. -/
def taoSection5PayloadFreeCoefficient
    (k : ℕ) (S : Finset ℕ) (X : ZMod (3 ^ k)) : ℝ := by
  classical
  exact ((3 ^ k : ℕ) : ℝ) *
    ((S.filter (fun M : ℕ => (M : ZMod (3 ^ k)) = X)).sum
      (fun M => 1 / (M : ℝ)))

/-- Evaluating the source coefficient against any test function removes the
residue-class partition exactly. -/
theorem sum_taoSection5PayloadFreeCoefficient_mul
    (k : ℕ) (S : Finset ℕ) (f : ZMod (3 ^ k) → ℝ) :
    (∑ X : ZMod (3 ^ k),
        taoSection5PayloadFreeCoefficient k S X * f X) =
      ((3 ^ k : ℕ) : ℝ) *
        ∑ M ∈ S, (1 / (M : ℝ)) * f (M : ZMod (3 ^ k)) := by
  classical
  let g : ℕ → ZMod (3 ^ k) := fun M => (M : ZMod (3 ^ k))
  have hfiber := Finset.sum_fiberwise_eq_sum_filter
    S (Finset.univ : Finset (ZMod (3 ^ k))) g
      (fun M => (1 / (M : ℝ)) * f (g M))
  have hpartition :
      (∑ X : ZMod (3 ^ k),
          ∑ M ∈ S with g M = X, (1 / (M : ℝ)) * f X) =
        ∑ M ∈ S, (1 / (M : ℝ)) * f (g M) := by
    calc
      (∑ X : ZMod (3 ^ k),
          ∑ M ∈ S with g M = X, (1 / (M : ℝ)) * f X) =
          ∑ X : ZMod (3 ^ k),
            ∑ M ∈ S with g M = X, (1 / (M : ℝ)) * f (g M) := by
              apply Finset.sum_congr rfl
              intro X _hX
              apply Finset.sum_congr rfl
              intro M hM
              rw [(Finset.mem_filter.mp hM).2]
      _ = ∑ M ∈ S, (1 / (M : ℝ)) * f (g M) := by
            simpa using hfiber
  unfold taoSection5PayloadFreeCoefficient
  calc
    (∑ X : ZMod (3 ^ k),
        (((3 ^ k : ℕ) : ℝ) *
          (S.filter (fun M : ℕ => (M : ZMod (3 ^ k)) = X)).sum
            (fun M => 1 / (M : ℝ))) * f X) =
        ((3 ^ k : ℕ) : ℝ) *
          ∑ X : ZMod (3 ^ k),
            ((S.filter (fun M : ℕ => (M : ZMod (3 ^ k)) = X)).sum
              (fun M => 1 / (M : ℝ))) * f X := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro X _hX
                ring
    _ = ((3 ^ k : ℕ) : ℝ) *
        ∑ X : ZMod (3 ^ k),
          ∑ M ∈ S with g M = X, (1 / (M : ℝ)) * f X := by
            congr 1
            apply Finset.sum_congr rfl
            intro X _hX
            rw [Finset.sum_mul]
    _ = ((3 ^ k : ℕ) : ℝ) *
        ∑ M ∈ S, (1 / (M : ℝ)) * f (g M) := by
          rw [hpartition]
    _ = ((3 ^ k : ℕ) : ℝ) *
        ∑ M ∈ S, (1 / (M : ℝ)) * f (M : ZMod (3 ^ k)) := by
          rfl

end

end Tao
end Erdos1135SecondScale
