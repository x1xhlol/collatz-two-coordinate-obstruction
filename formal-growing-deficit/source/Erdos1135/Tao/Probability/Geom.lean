import Erdos1135.Tao.Probability.Finite
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Probability.Distributions.Geometric

set_option backward.isDefEq.respectTransparency false

/-!
# Positive-Support Geometric Distribution

This module fixes the `Geom(2)` convention used for Tao's positive valuation exponents.  The
underlying mathlib geometric distribution is zero-based on `ℕ`; `geom2PNat` shifts it to `ℕ+`.
-/

namespace Erdos1135
namespace Tao

set_option linter.deprecated false in
/-- Zero-based `Geom(2)` on natural numbers, with mass `2^-(n+1)`. -/
noncomputable def geom2Nat : PMF ℕ :=
  ProbabilityTheory.geometricPMF (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num)

/-- Positive-support `Geom(2)` on `ℕ+`, with mass `2^-a`. -/
noncomputable def geom2PNat : PMF ℕ+ :=
  geom2Nat.map fun n => ⟨n + 1, Nat.succ_pos n⟩

theorem geom2Nat_apply_toReal (n : ℕ) :
    (geom2Nat n).toReal = (1 / 2 : ℝ) ^ (n + 1) := by
  change (ENNReal.ofReal (((1 - (1 / 2 : ℝ)) ^ n * (1 / 2 : ℝ)))).toReal =
    (1 / 2 : ℝ) ^ (n + 1)
  rw [ENNReal.toReal_ofReal]
  · ring
  · positivity

theorem geom2PNat_apply_eq_geom2Nat_pred (a : ℕ+) :
    geom2PNat a = geom2Nat ((a : ℕ) - 1) := by
  rw [geom2PNat, PMF.map_apply]
  rw [tsum_eq_single ((a : ℕ) - 1)]
  · have heq : a = (⟨(a : ℕ) - 1 + 1, Nat.succ_pos ((a : ℕ) - 1)⟩ : ℕ+) := by
      apply Subtype.ext
      exact (Nat.succ_pred_eq_of_pos a.2).symm
    rw [ite_eq_left heq]
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

/-- The real first-moment series of the positive-support Geom(2) law is summable. -/
theorem summable_geom2PNat_mul_natCast :
    Summable fun a : ℕ+ =>
      (geom2PNat a).toReal * (((a : ℕ) : ℝ)) := by
  apply (Equiv.pnatEquivNat.symm.summable_iff).mp
  have hbase :
      Summable fun n : ℕ =>
        ((n : ℝ) ^ 1) * (1 / 2 : ℝ) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
  have hshift :
      Summable fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) ^ 1) * (1 / 2 : ℝ) ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr hbase
  refine hshift.congr ?_
  intro n
  rw [Function.comp_apply, Equiv.pnatEquivNat_symm_apply]
  have hmass :
      (geom2PNat n.succPNat).toReal =
        (1 / 2 : ℝ) ^ (n + 1) := by
    simpa using geom2PNat_apply_toReal n.succPNat
  have hcoe : ((n.succPNat : ℕ+) : ℕ) = n + 1 := by rfl
  rw [hmass, hcoe]
  ring

/-- A positive-support Geom(2) variable has mean `2`. -/
theorem tsum_geom2PNat_mul_natCast :
    (∑' a : ℕ+,
      (geom2PNat a).toReal * (((a : ℕ) : ℝ))) = 2 := by
  calc
    (∑' a : ℕ+, (geom2PNat a).toReal * (((a : ℕ) : ℝ))) =
        ∑' n : ℕ,
          (geom2PNat (Equiv.pnatEquivNat.symm n)).toReal *
            ((((Equiv.pnatEquivNat.symm n : ℕ+) : ℕ) : ℝ)) := by
      exact (Equiv.pnatEquivNat.symm.tsum_eq _).symm
    _ = ∑' n : ℕ,
        (1 / 2 : ℝ) *
          ((((n + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n)) := by
      apply tsum_congr
      intro n
      rw [Equiv.pnatEquivNat_symm_apply]
      have hmass :
          (geom2PNat n.succPNat).toReal =
            (1 / 2 : ℝ) ^ (n + 1) := by
        simpa using geom2PNat_apply_toReal n.succPNat
      have hcoe : ((n.succPNat : ℕ+) : ℕ) = n + 1 := by rfl
      rw [hmass, hcoe, pow_succ]
      ring
    _ = (1 / 2 : ℝ) *
        ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n) := by
      rw [tsum_mul_left]
    _ = 2 := by
      have h :=
        tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1
          (r := (1 / 2 : ℝ)) (by norm_num)
      have h' :
          (∑' n : ℕ,
            (((n + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n)) = 4 := by
        convert h using 1
        · apply tsum_congr
          intro n
          simp
        · norm_num
      rw [h']
      norm_num

set_option linter.deprecated false in
/-- Zero-based `Geom(4)` on natural numbers, with success probability `1/4`. -/
noncomputable def geom4Nat : PMF ℕ :=
  ProbabilityTheory.geometricPMF (p := (1 / 4 : ℝ)) (by norm_num) (by norm_num)

/-- Positive-support `Geom(4)` on `ℕ+`, with mass `(1/4) * (3/4)^(j-1)`. -/
noncomputable def geom4PNat : PMF ℕ+ :=
  geom4Nat.map fun n => ⟨n + 1, Nat.succ_pos n⟩

theorem geom4Nat_apply_toReal (n : ℕ) :
    (geom4Nat n).toReal = (1 / 4 : ℝ) * (3 / 4 : ℝ) ^ n := by
  change (ENNReal.ofReal (((1 - (1 / 4 : ℝ)) ^ n * (1 / 4 : ℝ)))).toReal =
    (1 / 4 : ℝ) * (3 / 4 : ℝ) ^ n
  rw [ENNReal.toReal_ofReal]
  · ring
  · positivity

theorem geom4PNat_apply_eq_geom4Nat_pred (j : ℕ+) :
    geom4PNat j = geom4Nat ((j : ℕ) - 1) := by
  rw [geom4PNat, PMF.map_apply]
  rw [tsum_eq_single ((j : ℕ) - 1)]
  · have heq : j = (⟨(j : ℕ) - 1 + 1, Nat.succ_pos ((j : ℕ) - 1)⟩ : ℕ+) := by
      apply Subtype.ext
      exact (Nat.succ_pred_eq_of_pos j.2).symm
    rw [ite_eq_left heq]
  · intro n hn
    by_cases h : j = (⟨n + 1, Nat.succ_pos n⟩ : ℕ+)
    · have hn' : n = (j : ℕ) - 1 := by
        have hnat : (j : ℕ) = n + 1 := by
          exact congrArg Subtype.val h
        omega
      exact (hn hn').elim
    · simp [h]

/-- Real mass formula for positive-support `Geom(4)`. -/
theorem geom4PNat_apply_toReal (j : ℕ+) :
    (geom4PNat j).toReal =
      (1 / 4 : ℝ) * (3 / 4 : ℝ) ^ ((j : ℕ) - 1) := by
  rw [geom4PNat_apply_eq_geom4Nat_pred]
  rw [geom4Nat_apply_toReal]

theorem geom4PNat_apply_one_toReal :
    (geom4PNat 1).toReal = (1 / 4 : ℝ) := by
  norm_num [geom4PNat_apply_toReal]

theorem geom4PNat_apply_nat_succ_toReal (n : ℕ) :
    (geom4PNat ⟨n + 1, Nat.succ_pos n⟩).toReal =
      (1 / 4 : ℝ) * (3 / 4 : ℝ) ^ n := by
  simp [geom4PNat_apply_toReal]

/-- Source-facing first-hit mass notation for Section 7.3. -/
noncomputable def taoSection7Geom4FirstHitMass (j : ℕ+) : ℝ :=
  (1 / 4 : ℝ) * (3 / 4 : ℝ) ^ ((j : ℕ) - 1)

theorem geom4PNat_apply_toReal_eq_firstHitMass (j : ℕ+) :
    (geom4PNat j).toReal = taoSection7Geom4FirstHitMass j := by
  rw [geom4PNat_apply_toReal]
  rfl

theorem taoSection7Geom4FirstHitMass_one :
    taoSection7Geom4FirstHitMass 1 = (1 / 4 : ℝ) := by
  norm_num [taoSection7Geom4FirstHitMass]

theorem taoSection7Geom4FirstHitMass_nat_succ (n : ℕ) :
    taoSection7Geom4FirstHitMass ⟨n + 1, Nat.succ_pos n⟩ =
      (1 / 4 : ℝ) * (3 / 4 : ℝ) ^ n := by
  simp [taoSection7Geom4FirstHitMass]

theorem taoSection7Geom4FirstHitMass_succ (j : ℕ+) :
    taoSection7Geom4FirstHitMass (j + 1) =
      (3 / 4 : ℝ) * taoSection7Geom4FirstHitMass j := by
  obtain ⟨n, hn⟩ := j
  cases n with
  | zero =>
      cases hn
  | succ n =>
      simp [taoSection7Geom4FirstHitMass]
      ring

/-- Zero-based mass for the number of misses before the first `b_j = 3` hit. -/
noncomputable def taoSection7Geom4MissMass (n : ℕ) : ℝ :=
  (1 / 4 : ℝ) * (3 / 4 : ℝ) ^ n

theorem tsum_taoSection7Geom4MissMass :
    (∑' n : ℕ, taoSection7Geom4MissMass n) = 1 := by
  calc
    (∑' n : ℕ, taoSection7Geom4MissMass n)
        = (1 / 4 : ℝ) * ∑' n : ℕ, (3 / 4 : ℝ) ^ n := by
          unfold taoSection7Geom4MissMass
          rw [tsum_mul_left]
    _ = 1 := by
          rw [tsum_geometric_of_lt_one (by norm_num : 0 ≤ (3 / 4 : ℝ))
            (by norm_num : (3 / 4 : ℝ) < 1)]
          norm_num

theorem tsum_taoSection7Geom4MissMass_mul_missCount :
    (∑' n : ℕ, taoSection7Geom4MissMass n * (n : ℝ)) = 3 := by
  calc
    (∑' n : ℕ, taoSection7Geom4MissMass n * (n : ℝ))
        = ∑' n : ℕ, (1 / 4 : ℝ) * ((n : ℝ) * (3 / 4 : ℝ) ^ n) := by
          apply tsum_congr
          intro n
          unfold taoSection7Geom4MissMass
          ring
    _ = (1 / 4 : ℝ) * ∑' n : ℕ, (n : ℝ) * (3 / 4 : ℝ) ^ n := by
          rw [tsum_mul_left]
    _ = 3 := by
          rw [tsum_coe_mul_geometric_of_norm_lt_one
            (r := (3 / 4 : ℝ)) (by norm_num)]
          norm_num

theorem tsum_taoSection7Geom4MissMass_mul_hitIndex :
    (∑' n : ℕ, taoSection7Geom4MissMass n * (((n + 1 : ℕ) : ℝ))) = 4 := by
  calc
    (∑' n : ℕ, taoSection7Geom4MissMass n * (((n + 1 : ℕ) : ℝ)))
        = ∑' n : ℕ,
            (1 / 4 : ℝ) * ((((n + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ n)) := by
          apply tsum_congr
          intro n
          unfold taoSection7Geom4MissMass
          ring
    _ = (1 / 4 : ℝ) *
            ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ n) := by
          rw [tsum_mul_left]
    _ = 4 := by
          have h :=
            tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1
              (r := (3 / 4 : ℝ)) (by norm_num)
          have h' :
              (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ n)) = 16 := by
            convert h using 1
            · apply tsum_congr
              intro n
              simp
            · norm_num
          rw [h']
          norm_num

theorem taoSection7Geom4FirstHitMass_eq_missMass (n : ℕ) :
    taoSection7Geom4FirstHitMass ⟨n + 1, Nat.succ_pos n⟩ =
      taoSection7Geom4MissMass n := by
  rw [taoSection7Geom4FirstHitMass_nat_succ]
  rfl

theorem geom4PNat_apply_nat_succ_toReal_eq_missMass (n : ℕ) :
    (geom4PNat ⟨n + 1, Nat.succ_pos n⟩).toReal =
      taoSection7Geom4MissMass n := by
  rw [geom4PNat_apply_nat_succ_toReal]
  rfl

theorem tsum_taoSection7Geom4FirstHitMass_nat_succ :
    (∑' n : ℕ,
      taoSection7Geom4FirstHitMass ⟨n + 1, Nat.succ_pos n⟩) = 1 := by
  simpa [taoSection7Geom4FirstHitMass_eq_missMass] using
    tsum_taoSection7Geom4MissMass

theorem tsum_taoSection7Geom4FirstHitMass_nat_succ_mul_missCount :
    (∑' n : ℕ,
      taoSection7Geom4FirstHitMass ⟨n + 1, Nat.succ_pos n⟩ * (n : ℝ)) = 3 := by
  simpa [taoSection7Geom4FirstHitMass_eq_missMass] using
    tsum_taoSection7Geom4MissMass_mul_missCount

theorem tsum_taoSection7Geom4FirstHitMass_nat_succ_mul_hitIndex :
    (∑' n : ℕ,
      taoSection7Geom4FirstHitMass ⟨n + 1, Nat.succ_pos n⟩ *
        (((n + 1 : ℕ) : ℝ))) = 4 := by
  simpa [taoSection7Geom4FirstHitMass_eq_missMass] using
    tsum_taoSection7Geom4MissMass_mul_hitIndex

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

theorem tsum_geom2_positive_mod6_real (r : ℕ) :
    (∑' k : ℕ, (1 / 2 : ℝ) ^ (6 * k + r)) =
      (1 / 2 : ℝ) ^ r * (64 / 63) := by
  calc
    (∑' k : ℕ, (1 / 2 : ℝ) ^ (6 * k + r))
        = ∑' k : ℕ, (1 / 2 : ℝ) ^ r * (1 / 64 : ℝ) ^ k := by
          apply tsum_congr
          intro k
          rw [show 6 * k + r = r + k * 6 by omega, pow_add]
          congr 1
          rw [show k * 6 = 6 * k by omega, pow_mul]
          norm_num
    _ = (1 / 2 : ℝ) ^ r * (∑' k : ℕ, (1 / 64 : ℝ) ^ k) := by
          rw [tsum_mul_left]
    _ = (1 / 2 : ℝ) ^ r * (64 / 63) := by
          rw [tsum_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 64 : ℝ))
            (by norm_num : (1 / 64 : ℝ) < 1)]
          norm_num

theorem tsum_geom2PNat_mod6_one_toReal :
    (∑' k : ℕ,
        (geom2PNat ⟨6 * k + 1, by omega⟩).toReal) = 32 / 63 := by
  calc
    (∑' k : ℕ, (geom2PNat ⟨6 * k + 1, by omega⟩).toReal)
        = (1 / 2 : ℝ) ^ 1 * (64 / 63) := by
          simpa [geom2PNat_apply_toReal] using tsum_geom2_positive_mod6_real 1
    _ = 32 / 63 := by norm_num

theorem tsum_geom2PNat_mod6_two_toReal :
    (∑' k : ℕ,
        (geom2PNat ⟨6 * k + 2, by omega⟩).toReal) = 16 / 63 := by
  calc
    (∑' k : ℕ, (geom2PNat ⟨6 * k + 2, by omega⟩).toReal)
        = (1 / 2 : ℝ) ^ 2 * (64 / 63) := by
          simpa [geom2PNat_apply_toReal] using tsum_geom2_positive_mod6_real 2
    _ = 16 / 63 := by norm_num

theorem tsum_geom2PNat_mod6_three_toReal :
    (∑' k : ℕ,
        (geom2PNat ⟨6 * k + 3, by omega⟩).toReal) = 8 / 63 := by
  calc
    (∑' k : ℕ, (geom2PNat ⟨6 * k + 3, by omega⟩).toReal)
        = (1 / 2 : ℝ) ^ 3 * (64 / 63) := by
          simpa [geom2PNat_apply_toReal] using tsum_geom2_positive_mod6_real 3
    _ = 8 / 63 := by norm_num

theorem tsum_geom2PNat_mod6_four_toReal :
    (∑' k : ℕ,
        (geom2PNat ⟨6 * k + 4, by omega⟩).toReal) = 4 / 63 := by
  calc
    (∑' k : ℕ, (geom2PNat ⟨6 * k + 4, by omega⟩).toReal)
        = (1 / 2 : ℝ) ^ 4 * (64 / 63) := by
          simpa [geom2PNat_apply_toReal] using tsum_geom2_positive_mod6_real 4
    _ = 4 / 63 := by norm_num

theorem tsum_geom2PNat_mod6_five_toReal :
    (∑' k : ℕ,
        (geom2PNat ⟨6 * k + 5, by omega⟩).toReal) = 2 / 63 := by
  calc
    (∑' k : ℕ, (geom2PNat ⟨6 * k + 5, by omega⟩).toReal)
        = (1 / 2 : ℝ) ^ 5 * (64 / 63) := by
          simpa [geom2PNat_apply_toReal] using tsum_geom2_positive_mod6_real 5
    _ = 2 / 63 := by norm_num

theorem tsum_geom2PNat_mod6_six_toReal :
    (∑' k : ℕ,
        (geom2PNat ⟨6 * k + 6, by omega⟩).toReal) = 1 / 63 := by
  calc
    (∑' k : ℕ, (geom2PNat ⟨6 * k + 6, by omega⟩).toReal)
        = (1 / 2 : ℝ) ^ 6 * (64 / 63) := by
          simpa [geom2PNat_apply_toReal] using tsum_geom2_positive_mod6_real 6
    _ = 1 / 63 := by norm_num

end Tao
end Erdos1135
