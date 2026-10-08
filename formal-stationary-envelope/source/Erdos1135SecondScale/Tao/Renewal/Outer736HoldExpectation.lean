/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.HoldExpectation
import Erdos1135SecondScale.Tao.Renewal.Outer736SourceAlgebra
import Erdos1135SecondScale.Tao.Renewal.Prop78Case1Scalar
import Erdos1135SecondScale.Tao.Renewal.QmStatement

/-!
# Outer (7.36) Hold Expectation

This leaf proves finiteness of every positive-support Geom(4) polynomial
moment and transports a capped polynomial observable through the checked
first-coordinate Hold law.  The cap keeps the PMF-map step inside the existing
bounded expectation API.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open scoped BigOperators

/-- Every natural polynomial moment of the positive-support Geom(4) law is
summable. -/
theorem taoSection7Geom4PNat_polynomial_moment_summable (A : ℕ) :
    Summable fun j : ℕ+ =>
      (geom4PNat j).toReal * (((j : ℕ) : ℝ) ^ A) := by
  apply (Equiv.pnatEquivNat.symm.summable_iff).mp
  have hbase :
      Summable fun n : ℕ =>
        ((n : ℝ) ^ A) * (3 / 4 : ℝ) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one A (by norm_num)
  have hshift :
      Summable fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) ^ A) *
          (3 / 4 : ℝ) ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr hbase
  refine (hshift.mul_left (1 / 3 : ℝ)).congr ?_
  intro n
  rw [Function.comp_apply, Equiv.pnatEquivNat_symm_apply]
  have hcoe : ((n.succPNat : ℕ+) : ℕ) = n + 1 := by rfl
  have hmass :
      (geom4PNat n.succPNat).toReal =
        (1 / 4 : ℝ) * (3 / 4 : ℝ) ^ n := by
    simpa using geom4PNat_apply_nat_succ_toReal n
  rw [hmass, hcoe, pow_succ]
  ring

/-- The finite positive-support Geom(4) polynomial moment. -/
noncomputable def taoSection7Geom4PolynomialMoment (A : ℕ) : ℝ :=
  ∑' j : ℕ+,
    (geom4PNat j).toReal * (((j : ℕ) : ℝ) ^ A)

theorem taoSection7Geom4PolynomialMoment_nonneg (A : ℕ) :
    0 ≤ taoSection7Geom4PolynomialMoment A := by
  unfold taoSection7Geom4PolynomialMoment
  exact tsum_nonneg (fun _ =>
    mul_nonneg ENNReal.toReal_nonneg (pow_nonneg (Nat.cast_nonneg _) A))

/-- Transport a bounded observable dominated by `scale * j^A` through the
Hold first-coordinate law, using `min 1` as the bounded transport weight. -/
theorem taoSection7HoldExpectationFull_le_scale_mul_geom4PolynomialMoment
    (A : ℕ) {F : TaoSection7RenewalPoint → ℝ}
    (hF : TaoSection7QBounded01 F)
    {scale : ℝ} (hscale : 0 ≤ scale)
    (hpoint : ∀ h : TaoSection7RenewalPoint,
      F h ≤ scale * (((h.j : ℕ) : ℝ) ^ A)) :
    taoSection7HoldExpectationFull F ≤
      scale * taoSection7Geom4PolynomialMoment A := by
  let W : ℕ+ → ℝ :=
    fun j => min 1 (scale * (((j : ℕ) : ℝ) ^ A))
  have hW0 : ∀ j, 0 ≤ W j := by
    intro j
    dsimp [W]
    exact le_min (by norm_num)
      (mul_nonneg hscale (pow_nonneg (Nat.cast_nonneg _) A))
  have hW1 : ∀ j, W j ≤ 1 := by
    intro j
    exact min_le_left _ _
  have hFW : ∀ h : TaoSection7RenewalPoint, F h ≤ W h.j := by
    intro h
    exact le_min (hF h).2 (hpoint h)
  have hmono :
      taoSection7HoldExpectationFull F ≤
        taoSection7HoldExpectationFull (fun h => W h.j) :=
    taoSection7HoldExpectationFull_mono_of_bounded01
      (fun h => (hF h).1) (fun h => (hF h).2)
      (fun h => hW0 h.j) (fun h => hW1 h.j) hFW
  have htransport :=
    pmf_map_weighted_tsum_toReal_eq_of_bounded01
      taoSection7HoldPMF
      (fun h : TaoSection7RenewalPoint => h.j)
      W hW0 hW1
  have hmap := taoSection7HoldPMF_map_j_eq_geom4PNat_checked
  unfold taoSection7HoldPMF_map_j_eq_geom4PNat at hmap
  rw [hmap] at htransport
  have hupper : Summable fun j : ℕ+ =>
      (geom4PNat j).toReal *
        (scale * (((j : ℕ) : ℝ) ^ A)) := by
    exact
      ((taoSection7Geom4PNat_polynomial_moment_summable A).mul_left scale).congr
        (fun j => by ring)
  have hterm : ∀ j : ℕ+,
      (geom4PNat j).toReal * W j ≤
        (geom4PNat j).toReal *
          (scale * (((j : ℕ) : ℝ) ^ A)) := by
    intro j
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) ENNReal.toReal_nonneg
  calc
    taoSection7HoldExpectationFull F ≤
        taoSection7HoldExpectationFull (fun h => W h.j) := hmono
    _ = ∑' j : ℕ+, (geom4PNat j).toReal * W j := by
      unfold taoSection7HoldExpectationFull
      exact htransport.2.2.symm
    _ ≤ ∑' j : ℕ+, (geom4PNat j).toReal *
          (scale * (((j : ℕ) : ℝ) ^ A)) :=
      htransport.1.tsum_le_tsum hterm hupper
    _ = scale * taoSection7Geom4PolynomialMoment A := by
      unfold taoSection7Geom4PolynomialMoment
      rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      ring

/-- Pointwise inverse-gap decay implies the outer `(7.36)` Hold expectation
bound with exactly one `8^A` source-algebra loss. -/
theorem taoSection7SourceActualQ_outer736_of_pointwise_decay
    {n A : ℕ} {xi : ZMod (3 ^ n)} {epsilon D : ℝ}
    (hn : 0 < n) (hepsilon : 0 ≤ epsilon) (hD : 0 ≤ D)
    (hpoint : ∀ h : TaoSection7RenewalPoint,
      taoSection7SourceActualQ n xi epsilon h ≤
        D *
          ((((taoSection7QDistanceToCutoff (n / 2) h : ℝ) ^ A)⁻¹))) :
    taoSection7HoldExpectationFull
        (taoSection7SourceActualQ n xi epsilon) ≤
      (D * (8 : ℝ) ^ A * taoSection7Geom4PolynomialMoment A) /
        (n : ℝ) ^ A := by
  let scale : ℝ := D * (8 : ℝ) ^ A * (((n : ℝ) ^ A)⁻¹)
  have hscale : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hpoly : ∀ h : TaoSection7RenewalPoint,
      taoSection7SourceActualQ n xi epsilon h ≤
        scale * (((h.j : ℕ) : ℝ) ^ A) := by
    simpa [scale] using
      (TaoSection7Outer736.sourceAlgebra_to_jPolynomial
        hn hD hpoint)
  have hbound :=
    taoSection7HoldExpectationFull_le_scale_mul_geom4PolynomialMoment
      A
      (taoSection7SourceActualQ_bounded01
        (n := n) (xi := xi) hepsilon)
      hscale hpoly
  calc
    taoSection7HoldExpectationFull
        (taoSection7SourceActualQ n xi epsilon) ≤
      scale * taoSection7Geom4PolynomialMoment A := hbound
    _ = (D * (8 : ℝ) ^ A * taoSection7Geom4PolynomialMoment A) /
        (n : ℝ) ^ A := by
      dsimp [scale]
      rw [div_eq_mul_inv]
      ring

end

end Tao
end Erdos1135SecondScale
