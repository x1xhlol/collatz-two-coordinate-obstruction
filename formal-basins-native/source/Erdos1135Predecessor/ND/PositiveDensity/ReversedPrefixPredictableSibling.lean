/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Basic
import Erdos1135Predecessor.CollatzStep
import Erdos1135Predecessor.ND.Fourier.FixedTotalReferenceRatio
import Erdos1135Predecessor.ND.PositiveDensity.BoundedPMFDisintegration
import Erdos1135Predecessor.ND.PositiveDensity.CommonZEndpointPrefixFactorization
import Erdos1135Predecessor.ND.PositiveDensity.CommonZFullReverseKernel
import Erdos1135Predecessor.ND.PositiveDensity.CommonZPathTelescoping
import Erdos1135Predecessor.ND.PositiveDensity.CommonZProjectionEnergyBound
import Erdos1135Predecessor.ND.PositiveDensity.GatedFiberCovariance
import Erdos1135Predecessor.Tao.Fourier.MixingStatement
import Erdos1135Predecessor.Tao.Fourier.OscillationAlgebra
import Erdos1135Predecessor.Tao.Fourier.Section7SChiActualQ
import Erdos1135Predecessor.Tao.Fourier.Section7SourceLaw
import Erdos1135Predecessor.Tao.Probability.Finite
import Erdos1135Predecessor.Tao.Probability.FullL1
import Erdos1135Predecessor.Tao.Probability.GatedSubmassComplement
import Erdos1135Predecessor.Tao.Probability.GatedSubmassPartition
import Erdos1135Predecessor.Tao.Probability.Geom2CenteredMoment
import Erdos1135Predecessor.Tao.Probability.Geom2ListProjectivity
import Erdos1135Predecessor.Tao.Probability.Geom2ListReverse
import Erdos1135Predecessor.Tao.Probability.Geom2TerminalMoment
import Erdos1135Predecessor.Tao.Renewal.Lemma77PascalGaussian
import Erdos1135Predecessor.Tao.Renewal.Outer736HoldExpectation
import Erdos1135Predecessor.Tao.Renewal.Prop78Pointwise737
import Erdos1135Predecessor.Tao.Section5.AffineSourceLaw
import Erdos1135Predecessor.Tao.Section5.EndpointRatio
import Erdos1135Predecessor.Tao.Section5.FiveStepCompression
import Erdos1135Predecessor.Tao.Section6.AdjacentOneStep
import Erdos1135Predecessor.Tao.Section6.AmbientOffsetAppend
import Erdos1135Predecessor.Tao.Section6.AmbientTailDecay
import Erdos1135Predecessor.Tao.Section6.EventAggregation
import Erdos1135Predecessor.Tao.Section6.FiniteFourierCollision
import Erdos1135Predecessor.Tao.Section6.FixedAmbientSlice
import Erdos1135Predecessor.Tao.Section6.GatePartition
import Erdos1135Predecessor.Tao.Section6.GatedSourceConvolution
import Erdos1135Predecessor.Tao.Section6.Geom2IntervalConcentration
import Erdos1135Predecessor.Tao.Section6.HeadEntropyScalar
import Erdos1135Predecessor.Tao.Section6.HighRegimeMixing
import Erdos1135Predecessor.Tao.Section6.InversePowerTail
import Erdos1135Predecessor.Tao.Section6.ModulusProjection
import Erdos1135Predecessor.Tao.Section6.UniformLift
import Erdos1135Predecessor.Tao.Syracuse.AffineEnvelope
import Erdos1135Predecessor.Tao.Syracuse.AffineOdd
import Erdos1135Predecessor.Tao.Syracuse.AffineResidue
import Erdos1135Predecessor.Tao.Syracuse.AffineReverse
import Erdos1135Predecessor.Tao.Syracuse.AffineTrajectory
import Erdos1135Predecessor.Tao.Syracuse.Defs
import Erdos1135Predecessor.Tao.Syracuse.FirstPassageInterval
import Erdos1135Predecessor.Tao.Syracuse.OddSource
import Erdos1135Predecessor.Tao.Syracuse.ParityBridge
import Erdos1135Predecessor.Tao.Syracuse.TruncatedValuationPacking
import Erdos1135Predecessor.Tao.Syracuse.TruncatedValuationTV
import Erdos1135Predecessor.Tao.Syracuse.ValuationDistribution
import Erdos1135Predecessor.Terras.Core.Defs
import Erdos1135Predecessor.Terras.Density.NaturalDensity
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.PowersetCard
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

open scoped BigOperators

noncomputable section

noncomputable def ndReversedPrefixAmbientChild
    (q : ℕ) (pre : List ℕ+) (z : ZMod (3 ^ 1)) :
    ZMod (3 ^ (1 + q)) :=
  Tao.taoSection7OffsetPrefix (1 + q) q pre +
    Tao.taoSection6AmbientTailEmbed q 1 (Tao.taoTupleWeight pre) z

theorem ndReversedPrefixAmbientHead_projection
    (q : ℕ) (pre : List ℕ+) :
    Tao.taoZModThreeProjection (show q ≤ 1 + q by omega)
        (Tao.taoSection7OffsetPrefix (1 + q) q pre) =
      Tao.taoSection7OffsetZMod q pre := by
  rw [Tao.taoSection7OffsetZMod_eq_offsetPrefix]
  unfold Tao.taoSection7OffsetPrefix
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  unfold Tao.taoSection7OffsetSummand
  rw [map_mul, Tao.taoZModThreeProjection_three_pow,
    Tao.taoZModThreeProjection_inv_two_pow]

theorem ndAmbientTailEmbed_one_projection_eq_zero
    (q l : ℕ) (z : ZMod (3 ^ 1)) :
    Tao.taoZModThreeProjection (show q ≤ 1 + q by omega)
        (Tao.taoSection6AmbientTailEmbed q 1 l z) = 0 := by
  unfold Tao.taoSection6AmbientTailEmbed
  rw [map_mul, map_mul, Tao.taoZModThreeProjection_three_pow]
  have hpow : (3 : ZMod (3 ^ q)) ^ q = 0 := by
    simpa only [Nat.cast_pow] using
      (ZMod.natCast_pow_eq_zero_of_le 3 (Nat.le_refl q))
  rw [hpow]
  simp

theorem ndReversedPrefixAmbientChild_projection
    (q : ℕ) (pre : List ℕ+) (z : ZMod (3 ^ 1)) :
    Tao.taoZModThreeProjection (show q ≤ 1 + q by omega)
        (ndReversedPrefixAmbientChild q pre z) =
      Tao.taoSection7OffsetZMod q pre := by
  unfold ndReversedPrefixAmbientChild
  rw [map_add, ndReversedPrefixAmbientHead_projection,
    ndAmbientTailEmbed_one_projection_eq_zero, add_zero]

theorem ndAmbientTailEmbed_one_injective (q l : ℕ) :
    Function.Injective (Tao.taoSection6AmbientTailEmbed q 1 l) := by
  intro z w hzw
  let u : (ZMod (3 ^ (1 + q)))ˣ := Tao.taoCor63TwoPowUnit (1 + q) l
  have hscaled :
      (3 : ZMod (3 ^ (1 + q))) ^ q *
          (z.val : ZMod (3 ^ (1 + q))) =
        (3 : ZMod (3 ^ (1 + q))) ^ q *
          (w.val : ZMod (3 ^ (1 + q))) := by
    change
      (3 : ZMod (3 ^ (1 + q))) ^ q *
          ((u⁻¹ : (ZMod (3 ^ (1 + q)))ˣ) : ZMod (3 ^ (1 + q))) *
            (z.val : ZMod (3 ^ (1 + q))) =
        (3 : ZMod (3 ^ (1 + q))) ^ q *
          ((u⁻¹ : (ZMod (3 ^ (1 + q)))ˣ) : ZMod (3 ^ (1 + q))) *
            (w.val : ZMod (3 ^ (1 + q))) at hzw
    have hunit :
        (u : ZMod (3 ^ (1 + q))) *
          ((u⁻¹ : (ZMod (3 ^ (1 + q)))ˣ) : ZMod (3 ^ (1 + q))) = 1 := by
      simp
    calc
      (3 : ZMod (3 ^ (1 + q))) ^ q *
          (z.val : ZMod (3 ^ (1 + q))) =
          1 * ((3 : ZMod (3 ^ (1 + q))) ^ q *
            (z.val : ZMod (3 ^ (1 + q)))) := by ring
      _ = ((u : ZMod (3 ^ (1 + q))) *
            ((u⁻¹ : (ZMod (3 ^ (1 + q)))ˣ) : ZMod (3 ^ (1 + q)))) *
          ((3 : ZMod (3 ^ (1 + q))) ^ q *
            (z.val : ZMod (3 ^ (1 + q)))) := by rw [hunit]
      _ = (u : ZMod (3 ^ (1 + q))) *
          ((3 : ZMod (3 ^ (1 + q))) ^ q *
            ((u⁻¹ : (ZMod (3 ^ (1 + q)))ˣ) : ZMod (3 ^ (1 + q))) *
              (z.val : ZMod (3 ^ (1 + q)))) := by ring
      _ = (u : ZMod (3 ^ (1 + q))) *
          ((3 : ZMod (3 ^ (1 + q))) ^ q *
            ((u⁻¹ : (ZMod (3 ^ (1 + q)))ˣ) : ZMod (3 ^ (1 + q))) *
              (w.val : ZMod (3 ^ (1 + q)))) := by rw [hzw]
      _ = ((u : ZMod (3 ^ (1 + q))) *
            ((u⁻¹ : (ZMod (3 ^ (1 + q)))ˣ) : ZMod (3 ^ (1 + q)))) *
          ((3 : ZMod (3 ^ (1 + q))) ^ q *
            (w.val : ZMod (3 ^ (1 + q)))) := by ring
      _ = (3 : ZMod (3 ^ (1 + q))) ^ q *
          (w.val : ZMod (3 ^ (1 + q))) := by rw [hunit]; ring
  have hmod :
      3 ^ q * z.val ≡ 3 ^ q * w.val [MOD 3 ^ (1 + q)] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hscaled
  have hpow : 3 ^ (1 + q) = 3 ^ q * 3 := by
    rw [Nat.add_comm]
    exact pow_succ 3 q
  have hmod' :
      3 ^ q * z.val ≡ 3 ^ q * w.val [MOD 3 ^ q * 3] := by
    rw [← hpow]
    exact hmod
  have hval : z.val ≡ w.val [MOD 3] :=
    Nat.ModEq.mul_left_cancel' (pow_ne_zero q (by decide : 3 ≠ 0)) hmod'
  have hcast : (z.val : ZMod (3 ^ 1)) = (w.val : ZMod (3 ^ 1)) := by
    rw [ZMod.natCast_eq_natCast_iff]
    simpa using hval
  calc
    z = (z.val : ZMod (3 ^ 1)) := (ZMod.natCast_zmod_val z).symm
    _ = (w.val : ZMod (3 ^ 1)) := hcast
    _ = w := ZMod.natCast_zmod_val w

theorem ndReversedPrefixAmbientChild_injective
    (q : ℕ) (pre : List ℕ+) :
    Function.Injective (ndReversedPrefixAmbientChild q pre) := by
  intro z w hzw
  unfold ndReversedPrefixAmbientChild at hzw
  have htail :
      Tao.taoSection6AmbientTailEmbed q 1 (Tao.taoTupleWeight pre) z =
        Tao.taoSection6AmbientTailEmbed q 1 (Tao.taoTupleWeight pre) w := by
    exact add_left_cancel hzw
  exact ndAmbientTailEmbed_one_injective q (Tao.taoTupleWeight pre) htail

end

end PositiveDensity

end ND

end Erdos1135Predecessor
