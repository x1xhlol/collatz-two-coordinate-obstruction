import GenericPowerPredecessorCount
import PowerDensityFloor

set_option autoImplicit false

namespace CollatzCanonical.BoundedInverseSeed
open Erdos1135Predecessor Erdos1135Predecessor.ND.PositiveDensity

theorem generalTarget_predecessors_power_floor
    {a b C N p : ℕ} {Cp : ℝ}
    (ha : 0 < a) (hthree : ¬ 3 ∣ a) (hb : 2 ^ 80 ≤ b)
    (hmix : Tao.syracFineScaleMixingAt 6 (C : ℝ))
    (hN : explicitLogarithmicSeedGeneration b C ≤ N)
    (hp : 0 < p) (hCp : 0 ≤ Cp) (hmixp : Tao.syracFineScaleMixingAt p Cp) :
    ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      powerDensityFloor p Cp
        (frozenSeedHeightMultiplier b (explicitSeedFloor b N / 4) N * a) * (X : ℝ) ≤
          (Terras.natCount (ordinaryPredecessorSet a) X : ℝ) := by
  obtain ⟨r, hr, hbound, X0, hcount⟩ :=
    generalTarget_predecessors_seed_lower_density_at_power ha hthree hb hmix hN
      hCp hmixp (powerMixingDepth p Cp)
      (fun r => powerMixingDepth_one_le _ _ _)
      (fun r => powerMixingDepth_budget p hp Cp hCp r)
  refine ⟨X0, fun X hX => ?_⟩
  have hfloor := powerDensityFloor_antitone p Cp hCp hr hbound
  have hc := hcount X hX
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hc
  rw [← powerDensityFloor_eq_depth p Cp hr] at hc
  exact (mul_le_mul_of_nonneg_right hfloor (Nat.cast_nonneg X)).trans hc

#print axioms generalTarget_predecessors_power_floor

end CollatzCanonical.BoundedInverseSeed
