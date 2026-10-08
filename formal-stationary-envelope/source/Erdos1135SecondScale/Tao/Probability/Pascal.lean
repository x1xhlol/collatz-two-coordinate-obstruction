/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.Geom

/-!
# Section 7 Pascal Pair Mass

This module records the finite arithmetic behind Tao's Section 7 pairing step:
the sum of two independent positive `Geom(2)` variables has Pascal mass, and
conditioning on sum `3` leaves the two ordered pairs with equal weight.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

/-- Real mass of an ordered pair of positive `Geom(2)` values. -/
noncomputable def geom2PNatPairMass (a b : ℕ+) : ℝ :=
  (geom2PNat a).toReal * (geom2PNat b).toReal

theorem geom2PNatPairMass_eq_pow (a b : ℕ+) :
    geom2PNatPairMass a b = (1 / 2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) := by
  simp [geom2PNatPairMass, geom2PNat_apply_toReal, pow_add]

/-- Source-style finite mass of all ordered positive pairs with sum `b`. -/
noncomputable def pascalGeom2PairMass (b : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (b - 1), (1 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ (b - a)

theorem pascalGeom2PairMass_eq (b : ℕ) (hb : 2 ≤ b) :
    pascalGeom2PairMass b = ((b - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ b := by
  have hterm :
      ∀ a ∈ Finset.Icc 1 (b - 1),
        (1 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ (b - a) = (1 / 2 : ℝ) ^ b := by
    intro a ha
    have ha_le : a ≤ b := by
      have ha_upper : a ≤ b - 1 := (Finset.mem_Icc.mp ha).2
      exact ha_upper.trans (Nat.sub_le b 1)
    rw [← pow_add]
    congr 1
    omega
  calc
    pascalGeom2PairMass b
        = ∑ _a ∈ Finset.Icc 1 (b - 1), (1 / 2 : ℝ) ^ b := by
          unfold pascalGeom2PairMass
          exact Finset.sum_congr rfl hterm
    _ = ((Finset.Icc 1 (b - 1)).card : ℝ) * (1 / 2 : ℝ) ^ b := by
          simp [nsmul_eq_mul]
    _ = ((b - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ b := by
          have hcard : (Finset.Icc 1 (b - 1)).card = b - 1 := by
            rw [Nat.card_Icc]
            omega
          rw [hcard]

theorem pascalGeom2PairMass_three :
    pascalGeom2PairMass 3 = (1 / 4 : ℝ) := by
  calc
    pascalGeom2PairMass 3 = ((3 - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ 3 := by
      exact pascalGeom2PairMass_eq 3 (by norm_num)
    _ = (1 / 4 : ℝ) := by norm_num

theorem geom2PNatPairMass_one_two :
    geom2PNatPairMass (1 : ℕ+) (2 : ℕ+) = (1 / 8 : ℝ) := by
  norm_num [geom2PNatPairMass_eq_pow]

theorem geom2PNatPairMass_two_one :
    geom2PNatPairMass (2 : ℕ+) (1 : ℕ+) = (1 / 8 : ℝ) := by
  norm_num [geom2PNatPairMass_eq_pow]

theorem geom2PNatPairMass_one_two_eq_two_one :
    geom2PNatPairMass (1 : ℕ+) (2 : ℕ+) =
      geom2PNatPairMass (2 : ℕ+) (1 : ℕ+) := by
  rw [geom2PNatPairMass_one_two, geom2PNatPairMass_two_one]

theorem geom2PNatPairMass_one_two_div_pascal_three :
    geom2PNatPairMass (1 : ℕ+) (2 : ℕ+) / pascalGeom2PairMass 3 = (1 / 2 : ℝ) := by
  rw [geom2PNatPairMass_one_two, pascalGeom2PairMass_three]
  norm_num

theorem geom2PNatPairMass_two_one_div_pascal_three :
    geom2PNatPairMass (2 : ℕ+) (1 : ℕ+) / pascalGeom2PairMass 3 = (1 / 2 : ℝ) := by
  rw [geom2PNatPairMass_two_one, pascalGeom2PairMass_three]
  norm_num

end Tao
end Erdos1135SecondScale
