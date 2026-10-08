/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Syracuse.Basic
import Mathlib.Algebra.BigOperators.Field

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

open scoped BigOperators

noncomputable section

structure NDCommonZReverseEdge where
  source : ℕ
  target : ℕ
  exponent : ℕ
  source_pos : 0 < source
  target_pos : 0 < target
  affine : 2 ^ exponent * target = 3 * source + 1

def ndCommonZEdgeSourceWeight (q : ℕ) (e : NDCommonZReverseEdge) : ℝ :=
  (3 : ℝ) ^ q / (e.source : ℝ)

def ndCommonZEdgeTransportedWeight (q : ℕ)
    (e : NDCommonZReverseEdge) : ℝ :=
  (3 : ℝ) ^ (q + 1) /
    ((2 : ℝ) ^ e.exponent * (e.target : ℝ))

def ndCommonZEdgeDefect (q : ℕ) (e : NDCommonZReverseEdge) : ℝ :=
  (3 : ℝ) ^ q /
    ((e.source : ℝ) * (3 * (e.source : ℝ) + 1))

theorem ndCommonZEdgeDefect_nonneg
    (q : ℕ) (e : NDCommonZReverseEdge) :
    0 ≤ ndCommonZEdgeDefect q e := by
  unfold ndCommonZEdgeDefect
  positivity

theorem ndCommonZEdge_source_eq_transport_add_defect
    (q : ℕ) (e : NDCommonZReverseEdge) :
    ndCommonZEdgeSourceWeight q e =
      ndCommonZEdgeTransportedWeight q e +
        ndCommonZEdgeDefect q e := by
  have haffine :
      (2 : ℝ) ^ e.exponent * (e.target : ℝ) =
        3 * (e.source : ℝ) + 1 := by
    exact_mod_cast e.affine
  unfold ndCommonZEdgeSourceWeight ndCommonZEdgeTransportedWeight
    ndCommonZEdgeDefect
  rw [haffine]
  have hsv : (e.source : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt e.source_pos)
  have hden : 3 * (e.source : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hsv, hden]
  ring

def ndCommonZActualReverseEdge (v : ℕ) (hv : 0 < v) :
    NDCommonZReverseEdge where
  source := v
  target := Tao.syracuse v
  exponent := Tao.syracuseExponent v
  source_pos := hv
  target_pos := Tao.syracuse_pos v
  affine := Tao.two_pow_syracuseExponent_mul_syracuse v

end

end PositiveDensity

end ND

end Erdos1135Predecessor
