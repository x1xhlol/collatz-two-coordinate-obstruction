import GenericSeedPredecessorCount
import SeedDensityFloor

set_option autoImplicit false

namespace CollatzCanonical.BoundedInverseSeed
open Erdos1135Predecessor
open Erdos1135Predecessor.ND.PositiveDensity

theorem frozenSeedHeightMultiplier_pos (b k n : ℕ) :
    0 < frozenSeedHeightMultiplier b k n := by
  unfold frozenSeedHeightMultiplier
  positivity

def predecessorSeedBase : ℕ := 2 ^ 80

noncomputable def predecessorSeedGeneration : ℕ :=
  explicitLogarithmicSeedGeneration predecessorSeedBase explicitSyracuseMixingCoefficient

noncomputable def predecessorSeedMultiplier : ℕ :=
  frozenSeedHeightMultiplier predecessorSeedBase
    (explicitSeedFloor predecessorSeedBase predecessorSeedGeneration / 4)
    predecessorSeedGeneration

noncomputable def predecessorDensityFloor (a : ℕ) : ℝ :=
  sixthRootDensityFloor explicitSyracuseMixingCoefficient (predecessorSeedMultiplier * a)

theorem predecessorSeedMultiplier_pos : 0 < predecessorSeedMultiplier := by
  exact frozenSeedHeightMultiplier_pos _ _ _

theorem predecessorDensityFloor_pos {a : ℕ} (ha : 0 < a) :
    0 < predecessorDensityFloor a :=
  sixthRootDensityFloor_pos _ (Nat.mul_pos predecessorSeedMultiplier_pos ha)

theorem predecessorDensityFloor_ge_exp {a : ℕ} (ha : 0 < a) :
    Real.exp (-Real.log 3 *
      (88 * (explicitSyracuseMixingCoefficient : ℝ) *
        ((predecessorSeedMultiplier * a : ℕ) : ℝ)) ^ (1 / 6 : ℝ)) /
      (256 * ((predecessorSeedMultiplier * a : ℕ) : ℝ)) ≤ predecessorDensityFloor a :=
  sixthRootDensityFloor_ge_exp _ (Nat.mul_pos predecessorSeedMultiplier_pos ha)

theorem generalTarget_predecessors_explicit_lower_density
    {a : ℕ} (ha : 0 < a) (hthree : ¬ 3 ∣ a) :
    ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      predecessorDensityFloor a * (X : ℝ) ≤
        (Terras.natCount (ordinaryPredecessorSet a) X : ℝ) := by
  obtain ⟨r, hr, hbound, X0, hcount⟩ :=
    generalTarget_predecessors_seed_lower_density_at_depth ha hthree
      (b := predecessorSeedBase) (C := explicitSyracuseMixingCoefficient)
      (N := predecessorSeedGeneration) le_rfl explicitSyracuseMixing_six le_rfl
      (seedMixingDepth explicitSyracuseMixingCoefficient)
      (fun r => seedMixingDepth_one_le _ _)
      (fun r => seedMixingDepth_budget _ _)
  refine ⟨X0, fun X hX => ?_⟩
  have hfloor : predecessorDensityFloor a ≤
      sixthRootDensityFloor explicitSyracuseMixingCoefficient r :=
    sixthRootDensityFloor_antitone _ hr hbound
  have hc := hcount X hX
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hc
  rw [← sixthRootDensityFloor_eq_depth _ hr] at hc
  exact (mul_le_mul_of_nonneg_right hfloor (Nat.cast_nonneg X)).trans hc

#print axioms frozenSeedHeightMultiplier_pos
#print axioms predecessorSeedMultiplier_pos
#print axioms predecessorDensityFloor_pos
#print axioms predecessorDensityFloor_ge_exp
#print axioms generalTarget_predecessors_explicit_lower_density

end CollatzCanonical.BoundedInverseSeed
