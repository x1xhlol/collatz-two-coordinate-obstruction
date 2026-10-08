/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Probability.Finite
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Probability.Distributions.Geometric

namespace Erdos1135Predecessor

namespace Tao

noncomputable def geom2Nat : PMF ℕ :=
  ProbabilityTheory.geometricPMF (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num)

noncomputable def geom2PNat : PMF ℕ+ :=
  geom2Nat.map fun n => ⟨n + 1, Nat.succ_pos n⟩

theorem geom2Nat_apply_toReal (n : ℕ) :
    (geom2Nat n).toReal = (1 / 2 : ℝ) ^ (n + 1) := by
  change (ENNReal.ofReal (ProbabilityTheory.geometricPMFReal (1 / 2 : ℝ) n)).toReal =
    (1 / 2 : ℝ) ^ (n + 1)
  rw [ENNReal.toReal_ofReal]
  · unfold ProbabilityTheory.geometricPMFReal
    ring
  · unfold ProbabilityTheory.geometricPMFReal
    positivity

theorem geom2PNat_apply_eq_geom2Nat_pred (a : ℕ+) :
    geom2PNat a = geom2Nat ((a : ℕ) - 1) := by
  rw [geom2PNat, PMF.map_apply]
  rw [tsum_eq_single ((a : ℕ) - 1)]
  · have heq : a = (⟨(a : ℕ) - 1 + 1, Nat.succ_pos ((a : ℕ) - 1)⟩ : ℕ+) := by
      apply Subtype.ext
      exact (Nat.succ_pred_eq_of_pos a.2).symm
    rw [if_pos heq]
  · intro n hn
    by_cases h : a = (⟨n + 1, Nat.succ_pos n⟩ : ℕ+)
    · have hn' : n = (a : ℕ) - 1 := by
        have hnat : (a : ℕ) = n + 1 := by
          exact congrArg Subtype.val h
        omega
      exact (hn hn').elim
    · simp [h]

theorem geom2PNat_apply_toReal (a : ℕ+) :
    (geom2PNat a).toReal = (1 / 2 : ℝ) ^ (a : ℕ) := by
  rw [geom2PNat_apply_eq_geom2Nat_pred]
  rw [geom2Nat_apply_toReal]
  have h : (a : ℕ) - 1 + 1 = (a : ℕ) := Nat.succ_pred_eq_of_pos a.2
  rw [h]

noncomputable def geom4Nat : PMF ℕ :=
  ProbabilityTheory.geometricPMF (p := (1 / 4 : ℝ)) (by norm_num) (by norm_num)

noncomputable def geom4PNat : PMF ℕ+ :=
  geom4Nat.map fun n => ⟨n + 1, Nat.succ_pos n⟩

theorem geom4Nat_apply_toReal (n : ℕ) :
    (geom4Nat n).toReal = (1 / 4 : ℝ) * (3 / 4 : ℝ) ^ n := by
  change (ENNReal.ofReal (ProbabilityTheory.geometricPMFReal (1 / 4 : ℝ) n)).toReal =
    (1 / 4 : ℝ) * (3 / 4 : ℝ) ^ n
  rw [ENNReal.toReal_ofReal]
  · unfold ProbabilityTheory.geometricPMFReal
    ring
  · unfold ProbabilityTheory.geometricPMFReal
    positivity

theorem geom4PNat_apply_eq_geom4Nat_pred (j : ℕ+) :
    geom4PNat j = geom4Nat ((j : ℕ) - 1) := by
  rw [geom4PNat, PMF.map_apply]
  rw [tsum_eq_single ((j : ℕ) - 1)]
  · have heq : j = (⟨(j : ℕ) - 1 + 1, Nat.succ_pos ((j : ℕ) - 1)⟩ : ℕ+) := by
      apply Subtype.ext
      exact (Nat.succ_pred_eq_of_pos j.2).symm
    rw [if_pos heq]
  · intro n hn
    by_cases h : j = (⟨n + 1, Nat.succ_pos n⟩ : ℕ+)
    · have hn' : n = (j : ℕ) - 1 := by
        have hnat : (j : ℕ) = n + 1 := by
          exact congrArg Subtype.val h
        omega
      exact (hn hn').elim
    · simp [h]

theorem geom4PNat_apply_toReal (j : ℕ+) :
    (geom4PNat j).toReal =
      (1 / 4 : ℝ) * (3 / 4 : ℝ) ^ ((j : ℕ) - 1) := by
  rw [geom4PNat_apply_eq_geom4Nat_pred]
  rw [geom4Nat_apply_toReal]

theorem geom4PNat_apply_nat_succ_toReal (n : ℕ) :
    (geom4PNat ⟨n + 1, Nat.succ_pos n⟩).toReal =
      (1 / 4 : ℝ) * (3 / 4 : ℝ) ^ n := by
  simp [geom4PNat_apply_toReal]

noncomputable def taoSection7Geom4FirstHitMass (j : ℕ+) : ℝ :=
  (1 / 4 : ℝ) * (3 / 4 : ℝ) ^ ((j : ℕ) - 1)

noncomputable def taoSection7Geom4MissMass (n : ℕ) : ℝ :=
  (1 / 4 : ℝ) * (3 / 4 : ℝ) ^ n

theorem tsum_geom2_positive_even_real :
    (∑' k : ℕ, (1 / 2 : ℝ) ^ (2 * k + 2)) = 1 / 3 := by
  calc
    (∑' k : ℕ, (1 / 2 : ℝ) ^ (2 * k + 2))
        = ∑' k : ℕ, (1 / 4 : ℝ) * (1 / 4 : ℝ) ^ k := by
          apply tsum_congr
          intro k
          ring_nf
          rw [show (1 / 2 : ℝ) ^ (k * 2) = (1 / 4 : ℝ) ^ k by
            rw [Nat.mul_comm k 2, pow_mul]
            norm_num]
    _ = (1 / 4 : ℝ) * (∑' k : ℕ, (1 / 4 : ℝ) ^ k) := by
          rw [tsum_mul_left]
    _ = 1 / 3 := by
          rw [tsum_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 4 : ℝ))
            (by norm_num : (1 / 4 : ℝ) < 1)]
          norm_num

theorem tsum_geom2_positive_odd_real :
    (∑' k : ℕ, (1 / 2 : ℝ) ^ (2 * k + 1)) = 2 / 3 := by
  calc
    (∑' k : ℕ, (1 / 2 : ℝ) ^ (2 * k + 1))
        = ∑' k : ℕ, (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ k := by
          apply tsum_congr
          intro k
          ring_nf
          rw [show (1 / 2 : ℝ) ^ (k * 2) = (1 / 4 : ℝ) ^ k by
            rw [Nat.mul_comm k 2, pow_mul]
            norm_num]
    _ = (1 / 2 : ℝ) * (∑' k : ℕ, (1 / 4 : ℝ) ^ k) := by
          rw [tsum_mul_left]
    _ = 2 / 3 := by
          rw [tsum_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 4 : ℝ))
            (by norm_num : (1 / 4 : ℝ) < 1)]
          norm_num

theorem tsum_geom2PNat_even_param_toReal :
    (∑' k : ℕ,
        (geom2PNat ⟨2 * k + 2, by omega⟩).toReal) = 1 / 3 := by
  simpa [geom2PNat_apply_toReal] using tsum_geom2_positive_even_real

theorem tsum_geom2PNat_odd_param_toReal :
    (∑' k : ℕ,
        (geom2PNat ⟨2 * k + 1, by omega⟩).toReal) = 2 / 3 := by
  simpa [geom2PNat_apply_toReal] using tsum_geom2_positive_odd_real

end Tao

end Erdos1135Predecessor
