/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitPolynomialGeometricTail
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricCoreSummedVariation
import Erdos1135Predecessor.ND.PositiveDensity.SuccessfulRootTernaryResidueCoverage

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

theorem rootCoreStripConstant_le_explicit : ndRootCoreStripConstant ≤ (2 : ℝ) ^ (457 : ℕ) := by
  rw [show (457 : ℕ) = 200 * 2 + 57 by decide, pow_add, pow_mul]
  norm_num [ndRootCoreStripConstant, Nat.factorial]

theorem rootCore_cap_ratio_le_199_div_200 : (1 / 2 : ℝ) ^ (1 / 100 : ℝ) ≤ 199 / 200 := by
  have he : ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ 100 = (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  by_contra hn
  have hh := pow_lt_pow_left₀ (lt_of_not_ge hn) (by norm_num : (0 : ℝ) ≤ 199 / 200)
    (by decide : 100 ≠ 0)
  rw [he] at hh
  norm_num at hh

theorem rootCoreStripConstant_div_floor_le_explicit {b : ℕ} (hb : 2 ^ 80 ≤ b) :
    ndRootCoreStripConstant / (b : ℝ) ^ 6 ≤ 1 / (2 : ℝ) ^ 23 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 2 ^ 80) hb)
  have hbpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 ^ 80)
    (show (2 : ℝ) ^ 80 ≤ b by exact_mod_cast hb) 6
  have hs := rootCoreStripConstant_le_explicit
  apply (div_le_iff₀ (pow_pos hb0 _)).mpr
  norm_num only [← pow_mul, Nat.reduceMul] at hbpow
  rw [show (457 : ℕ) = 200 * 2 + 57 by decide, pow_add, pow_mul] at hs
  norm_num at hs
  norm_num at hbpow ⊢
  linarith

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem core_probability_deficit_le_explicit
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (hb : 2 ^ 80 ≤ U.floor)
    (cap : ℕ → ℕ) (hcap : ∀ n, 16 + n / 100 ≤ cap n) (n : ℕ) :
    1 - ndRootCoreStripBoundedCrossingProbability (U.forwardIterate cap n).floor
      (ndRootCoreWidth (U.forwardIterate cap n).floor) (cap n) ≤
      (1 / (2 : ℝ) ^ 23 + 1 / (2 : ℝ) ^ 16) * (199 / 200 : ℝ) ^ n := by
  have hb32 : 32 ^ 5 ≤ U.floor := (by norm_num : (32 : ℕ) ^ 5 ≤ 2 ^ 80).trans hb
  let b := (U.forwardIterate cap n).floor
  have hm := U.forward_core_width_guard hb32 cap n
  have he := one_sub_exp_sub_tail_le_rootCoreStripBoundedCrossingProbability
    (K := cap n) (U.forwardIterate cap n).floor_twoHundred hm.1 hm.2
  have hs := rootCore_strip_failure_le_inverse_sixth (b := b)
    (by have h := (U.forwardIterate cap n).floor_twoHundred; omega)
  have hi : 1 / (b : ℝ) ^ 6 ≤ (1 / (U.floor : ℝ) ^ 6) * ((200 / 201 : ℝ) ^ 6) ^ n := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / (b : ℝ))
      (U.core_inverse_floor_le_geometric cap n) 6
    simpa only [div_pow, one_pow, mul_pow, ← pow_mul, Nat.mul_comm] using hh
  have hstrip := mul_le_mul_of_nonneg_left hi
    (by unfold ndRootCoreStripConstant; positivity : 0 ≤ ndRootCoreStripConstant)
  change _ ≤ ndRootCoreStripConstant / (b : ℝ) ^ 6 at hs
  simp only [← mul_assoc, mul_one_div] at hstrip
  have hcoef := rootCoreStripConstant_div_floor_le_explicit hb
  have hratio := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (200 / 201 : ℝ) ^ 6)
    (by norm_num : (200 / 201 : ℝ) ^ 6 ≤ 199 / 200) n
  have hstripFinal := mul_le_mul hcoef hratio (by positivity)
    (by positivity : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ 23)
  have hct := rootCore_cap_failure_le_geometric cap 16 hcap n
  have hcr := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (1 / 100 : ℝ))
    rootCore_cap_ratio_le_199_div_200 n
  have hcapFinal := mul_le_mul_of_nonneg_left hcr (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ 16)
  have h16 : (1 / 2 : ℝ) ^ (16 : ℕ) = 1 / (2 : ℝ) ^ (16 : ℕ) := by norm_num
  rw [h16] at hct hcapFinal
  dsimp only [b] at hs hstrip
  nlinarith only [he, hs, hstrip, hstripFinal, hct, hcapFinal]

private theorem finite_product_ge_one_sub_deficit (f : ℕ → ℝ)
    (h0 : ∀ n, 0 ≤ f n) (h1 : ∀ n, f n ≤ 1) (n : ℕ) :
    1 - (∑ j ∈ Finset.range n, (1 - f j)) ≤ ∏ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : (∏ j ∈ Finset.range n, f j) ≤ 1 :=
      Finset.prod_le_one (fun j _ => h0 j) (fun j _ => h1 j)
    have hh := mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr (h1 n))
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    nlinarith

theorem coreProbabilityProduct_ge_255_div_256
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (hb : 2 ^ 80 ≤ U.floor)
    (cap : ℕ → ℕ) (hcap : ∀ n, 16 + n / 100 ≤ cap n) (n : ℕ) :
    (255 / 256 : ℝ) ≤ ndRootCoreProbabilityProduct U.floor cap ndRootCoreWidth n := by
  let f (j : ℕ) := ndRootCoreStripBoundedCrossingProbability
    (U.forwardIterate cap j).floor (ndRootCoreWidth (U.forwardIterate cap j).floor) (cap j)
  have hb32 : 32 ^ 5 ≤ U.floor := (by norm_num : (32 : ℕ) ^ 5 ≤ 2 ^ 80).trans hb
  have h0 (j : ℕ) : 0 ≤ f j := (rootCoreStripBoundedCrossingProbability_pos
    (by have h := (U.forwardIterate cap j).floor_twoHundred; omega)
    (by have h := (U.forward_core_width_guard hb32 cap j).1; omega)).le
  have h1 (j : ℕ) : f j ≤ 1 := by
    have hh := Tao.taoGatedRejectedMass_nonneg (Tao.geom2PNatListPMF
      (ndGeom2ShiftedWideSymmetricHorizon (U.forwardIterate cap j).floor))
      (fun full => ∃ i : ndRootCoreSelectedWords (U.forwardIterate cap j).floor
        (ndRootCoreWidth (U.forwardIterate cap j).floor) (cap j), full.take i.val.length = i.val)
      (Tao.taoSection7OffsetZMod (ndGeom2ShiftedWideSymmetricHorizon (U.forwardIterate cap j).floor))
    rw [rootCore_rejectedMass_eq_one_sub_probability _ _ _ _ le_rfl] at hh
    dsimp [f]
    linarith
  obtain ⟨hgeo, hgeob⟩ := polynomialGeometric_moment_le 0
    (r := (199 / 200 : ℝ)) (by norm_num) (by norm_num)
  simp only [pow_zero, one_mul] at hgeo hgeob
  norm_num at hgeob
  have hgeofin : (∑ j ∈ Finset.range n, (199 / 200 : ℝ) ^ j) ≤ 200 :=
    (hgeo.sum_le_tsum (Finset.range n) (fun j _ => by positivity)).trans hgeob
  have hsum : (∑ j ∈ Finset.range n, (1 - f j)) ≤ (1 / 256 : ℝ) := by
    calc
      _ ≤ (1 / (2 : ℝ) ^ 23 + 1 / (2 : ℝ) ^ 16) *
          (∑ j ∈ Finset.range n, (199 / 200 : ℝ) ^ j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun j _ => U.core_probability_deficit_le_explicit hb cap hcap j)
      _ ≤ (1 / (2 : ℝ) ^ 23 + 1 / (2 : ℝ) ^ 16) * 200 :=
        mul_le_mul_of_nonneg_left hgeofin (by positivity)
      _ ≤ _ := by norm_num
  have hp := finite_product_ge_one_sub_deficit f h0 h1 n
  rw [U.rootCoreProbabilityProduct_eq_prod_forward]
  change (255 / 256 : ℝ) ≤ ∏ j ∈ Finset.range n, f j
  linarith

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
