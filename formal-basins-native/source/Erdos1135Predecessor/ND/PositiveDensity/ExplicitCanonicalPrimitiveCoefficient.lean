/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalGeom4Moment
import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalMonotonicity
import Erdos1135Predecessor.Tao.Fourier.Section7SChiActualQ
import Erdos1135Predecessor.Tao.Fourier.Section7SourceLaw
import Erdos1135Predecessor.Tao.Renewal.Outer736HoldExpectation
import Erdos1135Predecessor.Tao.Renewal.Prop78Pointwise737

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao

noncomputable section

theorem explicitRenewal_pointwise_of_monotonicity
    {n A C : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hC : TaoSection7Prop78Threshold A epsilon C)
    (hmono : ∀ m : ℕ, C ≤ m → m ≤ n / 2 →
      taoSection7SourceActualQmAtCutoff n A m xi epsilon ≤
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon)
    (p : TaoSection7RenewalPoint) :
    taoSection7SourceActualQ n xi epsilon p ≤
      (C : ℝ) ^ A * ((taoSection7QDistanceToCutoff (n / 2) p : ℝ) ^ A)⁻¹ := by
  have hQm := taoSection7SourceActualQmAtCutoff_le_threshold_pow_of_monotonicity
    hepsilon hC hmono (n / 2) le_rfl
  have htail : taoSection7QmTail (n / 2) (n / 2) p := by
    unfold taoSection7QmTail
    omega
  have hprod := (taoSection7SourceActualQ_weighted_le_QmAtCutoff
    (n := n) (A := A) (m := n / 2) (xi := xi) hepsilon htail).trans hQm
  have hd : (0 : ℝ) < taoSection7QDistanceToCutoff (n / 2) p := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
      (le_max_right (n / 2 - (p.j : ℕ)) 1))
  have hp : 0 < (taoSection7QDistanceToCutoff (n / 2) p : ℝ) ^ A := pow_pos hd _
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hprod)

theorem explicitRenewal_primitive_of_monotonicity
    {A C : ℕ} {epsilon : ℝ}
    (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1)
    (hC : TaoSection7Prop78Threshold A epsilon C)
    (hmono : ∀ (n : ℕ) (xi : ZMod (3 ^ n)), zmodThreePrimitive n xi →
      ∀ m : ℕ, C ≤ m → m ≤ n / 2 →
        taoSection7SourceActualQmAtCutoff n A m xi epsilon ≤
          taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon) :
    syracPMFPrimitivePolynomialDecayAt A ((32 * (A : ℝ) * C) ^ A) := by
  intro n hn xi hxi
  have hpoint := explicitRenewal_pointwise_of_monotonicity he0 hC (hmono n xi hxi)
  have hH := taoSection7SourceActualQ_outer736_of_pointwise_decay
    (A := A) (D := (C : ℝ) ^ A) (by omega : 0 < n) he0 (by positivity) hpoint
  have hK : (C : ℝ) ^ A * (8 : ℝ) ^ A * taoSection7Geom4PolynomialMoment A ≤
      (32 * (A : ℝ) * C) ^ A := by
    calc
      _ ≤ (C : ℝ) ^ A * (8 : ℝ) ^ A * (4 * (A : ℝ)) ^ A :=
        mul_le_mul_of_nonneg_left (explicitRenewal_geom4_moment_pow A) (by positivity)
      _ = _ := by
        rw [← mul_pow, ← mul_pow]
        congr 1
        ring
  rw [TaoSection7CharacterBridgeStatement.source_law n hn xi hxi]
  exact (norm_taoSection7SChi_le_holdExpectation_sourceActualQ n xi he0 he1).trans
    (hH.trans (div_le_div_of_nonneg_right hK (by positivity)))

end

end Erdos1135Predecessor.ND.PositiveDensity
