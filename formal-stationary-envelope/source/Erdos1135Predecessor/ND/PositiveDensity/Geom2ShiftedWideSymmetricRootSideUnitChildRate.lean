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
import Erdos1135Predecessor.ND.PositiveDensity.A5HistoricalAdjacentCylinderQOneRootDyadicPhysicalCensus
import Erdos1135Predecessor.ND.PositiveDensity.A5SupportedTargetCounting
import Erdos1135Predecessor.ND.PositiveDensity.BoundedPMFDisintegration
import Erdos1135Predecessor.ND.PositiveDensity.CommonZEndpointAdaptiveCanonicalTotal
import Erdos1135Predecessor.ND.PositiveDensity.CommonZEndpointPrefixFactorization
import Erdos1135Predecessor.ND.PositiveDensity.CommonZFullReverseKernel
import Erdos1135Predecessor.ND.PositiveDensity.CommonZKCapLongTailFiberCentering
import Erdos1135Predecessor.ND.PositiveDensity.CommonZLongRangeCoordinateCapFirstBad
import Erdos1135Predecessor.ND.PositiveDensity.CommonZPathTelescoping
import Erdos1135Predecessor.ND.PositiveDensity.CommonZProjectionEnergyBound
import Erdos1135Predecessor.ND.PositiveDensity.CommonZReverseGenerator
import Erdos1135Predecessor.ND.PositiveDensity.GatedFiberCovariance
import Erdos1135Predecessor.ND.PositiveDensity.Geom2MarkedFirstHitUnitSupportEnergyFloor
import Erdos1135Predecessor.ND.PositiveDensity.Geom2OneLawGaussianBaseAdaptiveFirstHitRate
import Erdos1135Predecessor.ND.PositiveDensity.Geom2OneLawGaussianFirstHitRate
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideBoundedOvershootPhysicalIncidence
import Erdos1135Predecessor.ND.PositiveDensity.ReversedPrefixPredictableSibling
import Erdos1135Predecessor.ND.PositiveDensity.Statement
import Erdos1135Predecessor.ND.PositiveDensity.TerminalTotalCancellation
import Erdos1135Predecessor.ND.Probability.Geom2FiniteTwoEventTail
import Erdos1135Predecessor.Tao.Fourier.MixingStatement
import Erdos1135Predecessor.Tao.Fourier.OscillationAlgebra
import Erdos1135Predecessor.Tao.Fourier.Section7Character
import Erdos1135Predecessor.Tao.Fourier.Section7SChiActualQ
import Erdos1135Predecessor.Tao.Fourier.Section7SourceLaw
import Erdos1135Predecessor.Tao.Probability.Finite
import Erdos1135Predecessor.Tao.Probability.FullL1
import Erdos1135Predecessor.Tao.Probability.GatedSubmassComplement
import Erdos1135Predecessor.Tao.Probability.GatedSubmassPartition
import Erdos1135Predecessor.Tao.Probability.Geom
import Erdos1135Predecessor.Tao.Probability.Geom2CenteredMoment
import Erdos1135Predecessor.Tao.Probability.Geom2ListProjectivity
import Erdos1135Predecessor.Tao.Probability.Geom2ListReverse
import Erdos1135Predecessor.Tao.Probability.Geom2TerminalMoment
import Erdos1135Predecessor.Tao.Renewal.Lemma77PascalGaussian
import Erdos1135Predecessor.Tao.Renewal.Outer736HoldExpectation
import Erdos1135Predecessor.Tao.Renewal.Prop78Pointwise737
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshOutsideEprimeWidth
import Erdos1135Predecessor.Tao.Section5.AffineSourceLaw
import Erdos1135Predecessor.Tao.Section5.EndpointRatio
import Erdos1135Predecessor.Tao.Section5.FiveStepCompression
import Erdos1135Predecessor.Tao.Section6.AdjacentOneStep
import Erdos1135Predecessor.Tao.Section6.AmbientOffsetAppend
import Erdos1135Predecessor.Tao.Section6.AmbientTailDecay
import Erdos1135Predecessor.Tao.Section6.EventAggregation
import Erdos1135Predecessor.Tao.Section6.FiberAverageDFT
import Erdos1135Predecessor.Tao.Section6.FiniteFourierCollision
import Erdos1135Predecessor.Tao.Section6.FiniteFourierParseval
import Erdos1135Predecessor.Tao.Section6.FixedAmbientSlice
import Erdos1135Predecessor.Tao.Section6.GatePartition
import Erdos1135Predecessor.Tao.Section6.GatedSourceConvolution
import Erdos1135Predecessor.Tao.Section6.Geom2IntervalConcentration
import Erdos1135Predecessor.Tao.Section6.GlobalOscillationBound
import Erdos1135Predecessor.Tao.Section6.HeadEntropyScalar
import Erdos1135Predecessor.Tao.Section6.HighRegimeMixing
import Erdos1135Predecessor.Tao.Section6.InversePowerTail
import Erdos1135Predecessor.Tao.Section6.ModulusProjection
import Erdos1135Predecessor.Tao.Section6.Prop114Assembly
import Erdos1135Predecessor.Tao.Section6.UniformLift
import Erdos1135Predecessor.Tao.Syracuse.AffineEnvelope
import Erdos1135Predecessor.Tao.Syracuse.AffineOdd
import Erdos1135Predecessor.Tao.Syracuse.AffineResidue
import Erdos1135Predecessor.Tao.Syracuse.AffineReverse
import Erdos1135Predecessor.Tao.Syracuse.AffineTrajectory
import Erdos1135Predecessor.Tao.Syracuse.Basic
import Erdos1135Predecessor.Tao.Syracuse.CollatzBridge
import Erdos1135Predecessor.Tao.Syracuse.Defs
import Erdos1135Predecessor.Tao.Syracuse.FirstPassageInterval
import Erdos1135Predecessor.Tao.Syracuse.OddSource
import Erdos1135Predecessor.Tao.Syracuse.OffsetInjectivity
import Erdos1135Predecessor.Tao.Syracuse.ParityBridge
import Erdos1135Predecessor.Tao.Syracuse.TruncatedValuationPacking
import Erdos1135Predecessor.Tao.Syracuse.TruncatedValuationTV
import Erdos1135Predecessor.Tao.Syracuse.ValuationDistribution
import Erdos1135Predecessor.Terras.Core.Defs
import Erdos1135Predecessor.Terras.Density.NaturalDensity
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
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
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.PowersetCard
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Basic
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

theorem ndNatCast_eq_reversedPrefixAmbientChild_sourceDigit_of_affine
    {s N M : ℕ} {rootSide : List ℕ+}
    (hlen : rootSide.length = s)
    (hAff : Tao.taoAffList rootSide.reverse (N : ℚ) = (M : ℚ)) :
    (M : ZMod (3 ^ (1 + s))) =
      ndReversedPrefixAmbientChild s rootSide (N : ZMod (3 ^ 1)) := by
  let R := ZMod (3 ^ (1 + s))
  have hhead :
      Tao.taoSection7OffsetPrefix (1 + s) s rootSide =
        Tao.taoAffineOffsetZModAt (1 + s) rootSide.reverse := by
    rw [Tao.taoAffineOffsetZModAt_reverse_eq_offsetPrefix]
    rw [hlen]
  have hprojection :
      Tao.taoZModThreeProjection (show 1 ≤ 1 + s by omega)
          (N : ZMod (3 ^ (1 + s))) =
        (N : ZMod (3 ^ 1)) := by
    exact Tao.taoZModThreeProjection_natCast
      (show 1 ≤ 1 + s by omega) N
  have hscaled :=
    Tao.taoSection6_three_pow_mul_val_eq_three_pow_mul_of_projection_eq
      1 s (N : ZMod (3 ^ (1 + s))) (N : ZMod (3 ^ 1)) hprojection
  have htail :
      Tao.taoSection6AmbientTailEmbed s 1 (Tao.taoTupleWeight rootSide)
          (N : ZMod (3 ^ 1)) =
        (3 : R) ^ s *
          (((2 : R) ^ Tao.taoTupleWeight rootSide)⁻¹) * (N : R) := by
    unfold Tao.taoSection6AmbientTailEmbed
    rw [← ZMod.inv_coe_unit, Tao.taoCor63TwoPowUnit_coe]
    calc
      (3 : R) ^ s * (((2 : R) ^ Tao.taoTupleWeight rootSide)⁻¹) *
          (((N : ZMod (3 ^ 1)).val : ℕ) : R) =
        (((2 : R) ^ Tao.taoTupleWeight rootSide)⁻¹) *
          ((3 : R) ^ s * (((N : ZMod (3 ^ 1)).val : ℕ) : R)) := by ring
      _ = (((2 : R) ^ Tao.taoTupleWeight rootSide)⁻¹) *
          ((3 : R) ^ s * (N : R)) := by rw [hscaled]
      _ = (3 : R) ^ s *
          (((2 : R) ^ Tao.taoTupleWeight rootSide)⁻¹) * (N : R) := by ring
  have hclear :=
    (Tao.taoAffList_eq_nat_iff_cleared rootSide.reverse N M).mp hAff
  have hcast := congrArg (fun x : ℕ => (x : R)) hclear
  have hcast' :
      (3 : R) ^ s * (N : R) + (Tao.taoOffsetNum rootSide.reverse : R) =
        (2 : R) ^ Tao.taoTupleWeight rootSide * (M : R) := by
    dsimp only [R] at hcast ⊢
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hcast ⊢
    simpa only [List.length_reverse, hlen, Tao.taoTupleWeight_reverse] using hcast
  have hinv := Tao.taoZModThreePow_inv_two_pow_mul
    (1 + s) (Tao.taoTupleWeight rootSide)
  rw [ndReversedPrefixAmbientChild, hhead, htail]
  unfold Tao.taoAffineOffsetZModAt
  calc
    (M : R) = 1 * (M : R) := by ring
    _ = ((((2 : R) ^ Tao.taoTupleWeight rootSide)⁻¹) *
          ((2 : R) ^ Tao.taoTupleWeight rootSide)) * (M : R) := by
      rw [hinv]
    _ = (((2 : R) ^ Tao.taoTupleWeight rootSide)⁻¹) *
          (((2 : R) ^ Tao.taoTupleWeight rootSide) * (M : R)) := by ring
    _ = (((2 : R) ^ Tao.taoTupleWeight rootSide)⁻¹) *
          ((3 : R) ^ s * (N : R) + (Tao.taoOffsetNum rootSide.reverse : R)) := by
      rw [hcast']
    _ = (Tao.taoOffsetNum rootSide.reverse : R) *
          (((2 : R) ^ Tao.taoTupleWeight rootSide)⁻¹) +
        (3 : R) ^ s *
          (((2 : R) ^ Tao.taoTupleWeight rootSide)⁻¹) * (N : R) := by ring
    _ = (Tao.taoOffsetNum rootSide.reverse : R) *
          (((2 : R) ^ Tao.taoTupleWeight rootSide.reverse)⁻¹) +
        (3 : R) ^ s *
          (((2 : R) ^ Tao.taoTupleWeight rootSide)⁻¹) * (N : R) := by
      rw [Tao.taoTupleWeight_reverse]

theorem
    ndGeom2PredictableRootSideBoundedOvershootIncidence_root_eq_ambientChild_sourceDigit
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hbaseNine : ∀ i, 9 ≤ base i)
    (hrootLower : ∀ i, 16 ^ base i ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    (root (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) :
        ZMod (3 ^
          (1 + ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z))) =
      ndReversedPrefixAmbientChild
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z)
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z)
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z :
          ZMod (3 ^ 1)) := by
  apply ndNatCast_eq_reversedPrefixAmbientChild_sourceDigit_of_affine
    (ndGeom2PredictableRootSideBoundedOvershootIncidence_word_length z)
  simpa only [
    ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord] using
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd_and_affine
      hrootOdd hbaseNine hrootLower z).2

end

end PositiveDensity

end ND

end Erdos1135Predecessor
