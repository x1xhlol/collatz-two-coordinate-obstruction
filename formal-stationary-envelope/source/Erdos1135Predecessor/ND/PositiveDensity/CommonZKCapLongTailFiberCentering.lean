/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.CollatzStep
import Erdos1135Predecessor.ND.PositiveDensity.BoundedPMFDisintegration
import Erdos1135Predecessor.ND.PositiveDensity.CommonZEndpointPrefixFactorization
import Erdos1135Predecessor.ND.PositiveDensity.CommonZFullReverseKernel
import Erdos1135Predecessor.ND.PositiveDensity.GatedFiberCovariance
import Erdos1135Predecessor.Tao.Probability.Finite
import Erdos1135Predecessor.Tao.Probability.FullL1
import Erdos1135Predecessor.Tao.Probability.Geom2CenteredMoment
import Erdos1135Predecessor.Tao.Probability.Geom2ListProjectivity
import Erdos1135Predecessor.Tao.Probability.Geom2ListReverse
import Erdos1135Predecessor.Tao.Probability.Geom2TerminalMoment
import Erdos1135Predecessor.Tao.Section5.AffineSourceLaw
import Erdos1135Predecessor.Tao.Section5.EndpointRatio
import Erdos1135Predecessor.Tao.Section5.FiveStepCompression
import Erdos1135Predecessor.Tao.Section6.AmbientOffsetAppend
import Erdos1135Predecessor.Tao.Section6.UniformLift
import Erdos1135Predecessor.Tao.Syracuse.AffineOdd
import Erdos1135Predecessor.Tao.Syracuse.AffineTrajectory
import Erdos1135Predecessor.Tao.Syracuse.Defs
import Erdos1135Predecessor.Tao.Syracuse.FirstPassageInterval
import Erdos1135Predecessor.Tao.Syracuse.ParityBridge
import Erdos1135Predecessor.Tao.Syracuse.TruncatedValuationPacking
import Erdos1135Predecessor.Terras.Core.Defs
import Erdos1135Predecessor.Terras.Density.NaturalDensity
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

open scoped BigOperators

noncomputable section

noncomputable def ndCommonZAmbientTailFiberPoint
    (d q l : ℕ) (base : ZMod (3 ^ (q + d)))
    (z : ZMod (3 ^ q)) : ZMod (3 ^ (q + d)) :=
  base + Tao.taoSection6AmbientTailEmbed d q l z

theorem ndCommonZAmbientTailEmbed_projection_eq_zero
    (d q l : ℕ) (z : ZMod (3 ^ q)) :
    Tao.taoZModThreeProjection (show d ≤ q + d by omega)
        (Tao.taoSection6AmbientTailEmbed d q l z) = 0 := by
  unfold Tao.taoSection6AmbientTailEmbed
  rw [map_mul, map_mul, Tao.taoZModThreeProjection_three_pow]
  have hpow : (3 : ZMod (3 ^ d)) ^ d = 0 := by
    simpa only [Nat.cast_pow] using
      (ZMod.natCast_pow_eq_zero_of_le 3 (Nat.le_refl d))
  rw [hpow]
  simp

theorem ndCommonZAmbientTailEmbed_injective (d q l : ℕ) :
    Function.Injective (Tao.taoSection6AmbientTailEmbed d q l) := by
  intro z w hzw
  let u : (ZMod (3 ^ (q + d)))ˣ := Tao.taoCor63TwoPowUnit (q + d) l
  have hscaled :
      (3 : ZMod (3 ^ (q + d))) ^ d *
          (z.val : ZMod (3 ^ (q + d))) =
        (3 : ZMod (3 ^ (q + d))) ^ d *
          (w.val : ZMod (3 ^ (q + d))) := by
    change
      (3 : ZMod (3 ^ (q + d))) ^ d *
          ((u⁻¹ : (ZMod (3 ^ (q + d)))ˣ) : ZMod (3 ^ (q + d))) *
            (z.val : ZMod (3 ^ (q + d))) =
        (3 : ZMod (3 ^ (q + d))) ^ d *
          ((u⁻¹ : (ZMod (3 ^ (q + d)))ˣ) : ZMod (3 ^ (q + d))) *
            (w.val : ZMod (3 ^ (q + d))) at hzw
    have hunit :
        (u : ZMod (3 ^ (q + d))) *
          ((u⁻¹ : (ZMod (3 ^ (q + d)))ˣ) : ZMod (3 ^ (q + d))) =
            1 := by simp
    calc
      (3 : ZMod (3 ^ (q + d))) ^ d *
          (z.val : ZMod (3 ^ (q + d))) =
          1 * ((3 : ZMod (3 ^ (q + d))) ^ d *
            (z.val : ZMod (3 ^ (q + d)))) := by ring
      _ = ((u : ZMod (3 ^ (q + d))) *
            ((u⁻¹ : (ZMod (3 ^ (q + d)))ˣ) : ZMod (3 ^ (q + d)))) *
          ((3 : ZMod (3 ^ (q + d))) ^ d *
            (z.val : ZMod (3 ^ (q + d)))) := by rw [hunit]
      _ = (u : ZMod (3 ^ (q + d))) *
          ((3 : ZMod (3 ^ (q + d))) ^ d *
            ((u⁻¹ : (ZMod (3 ^ (q + d)))ˣ) : ZMod (3 ^ (q + d))) *
              (z.val : ZMod (3 ^ (q + d)))) := by ring
      _ = (u : ZMod (3 ^ (q + d))) *
          ((3 : ZMod (3 ^ (q + d))) ^ d *
            ((u⁻¹ : (ZMod (3 ^ (q + d)))ˣ) : ZMod (3 ^ (q + d))) *
              (w.val : ZMod (3 ^ (q + d)))) := by rw [hzw]
      _ = ((u : ZMod (3 ^ (q + d))) *
            ((u⁻¹ : (ZMod (3 ^ (q + d)))ˣ) : ZMod (3 ^ (q + d)))) *
          ((3 : ZMod (3 ^ (q + d))) ^ d *
            (w.val : ZMod (3 ^ (q + d)))) := by ring
      _ = (3 : ZMod (3 ^ (q + d))) ^ d *
          (w.val : ZMod (3 ^ (q + d))) := by rw [hunit]; ring
  have hmod :
      3 ^ d * z.val ≡ 3 ^ d * w.val [MOD 3 ^ (q + d)] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hscaled
  have hpow : 3 ^ (q + d) = 3 ^ d * 3 ^ q := by
    rw [pow_add, Nat.mul_comm]
  have hmod' :
      3 ^ d * z.val ≡ 3 ^ d * w.val [MOD 3 ^ d * 3 ^ q] := by
    rw [← hpow]
    exact hmod
  have hval : z.val ≡ w.val [MOD 3 ^ q] :=
    Nat.ModEq.mul_left_cancel' (pow_ne_zero d (by decide : 3 ≠ 0)) hmod'
  have hcast : (z.val : ZMod (3 ^ q)) = (w.val : ZMod (3 ^ q)) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact hval
  calc
    z = (z.val : ZMod (3 ^ q)) := (ZMod.natCast_zmod_val z).symm
    _ = (w.val : ZMod (3 ^ q)) := hcast
    _ = w := ZMod.natCast_zmod_val w

theorem ndCommonZAmbientTailFiberPoint_projection
    (d q l : ℕ) (base : ZMod (3 ^ (q + d))) (z : ZMod (3 ^ q)) :
    Tao.taoZModThreeProjection (show d ≤ q + d by omega)
        (ndCommonZAmbientTailFiberPoint d q l base z) =
      Tao.taoZModThreeProjection (show d ≤ q + d by omega) base := by
  unfold ndCommonZAmbientTailFiberPoint
  rw [map_add, ndCommonZAmbientTailEmbed_projection_eq_zero, add_zero]

theorem ndCommonZAmbientTailFiberPoint_injective
    (d q l : ℕ) (base : ZMod (3 ^ (q + d))) :
    Function.Injective (ndCommonZAmbientTailFiberPoint d q l base) := by
  intro z w hzw
  unfold ndCommonZAmbientTailFiberPoint at hzw
  apply ndCommonZAmbientTailEmbed_injective d q l
  exact add_left_cancel hzw

theorem ndCommonZHeadPrefix_projection_eq_offset
    (d q : ℕ) (head : List ℕ+) :
    Tao.taoZModThreeProjection (show d ≤ q + d by omega)
        (Tao.taoSection7OffsetPrefix (q + d) d head) =
      Tao.taoSection7OffsetZMod d head := by
  rw [Tao.taoSection7OffsetZMod_eq_offsetPrefix]
  unfold Tao.taoSection7OffsetPrefix
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  unfold Tao.taoSection7OffsetSummand
  rw [map_mul, Tao.taoZModThreeProjection_three_pow,
    Tao.taoZModThreeProjection_inv_two_pow]

end

end PositiveDensity

end ND

end Erdos1135Predecessor
