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
import Erdos1135Predecessor.ND.PositiveDensity.A5SupportedTargetCounting
import Erdos1135Predecessor.ND.PositiveDensity.BoundedPMFDisintegration
import Erdos1135Predecessor.ND.PositiveDensity.CommonZEndpointPrefixFactorization
import Erdos1135Predecessor.ND.PositiveDensity.CommonZFullReverseKernel
import Erdos1135Predecessor.ND.PositiveDensity.CommonZKCapLongTailFiberCentering
import Erdos1135Predecessor.ND.PositiveDensity.CommonZPathTelescoping
import Erdos1135Predecessor.ND.PositiveDensity.CommonZProjectionEnergyBound
import Erdos1135Predecessor.ND.PositiveDensity.CommonZReverseGenerator
import Erdos1135Predecessor.ND.PositiveDensity.GatedFiberCovariance
import Erdos1135Predecessor.ND.PositiveDensity.Geom2OneLawGaussianBaseAdaptiveFirstHitRate
import Erdos1135Predecessor.ND.PositiveDensity.Geom2OneLawGaussianFirstHitRate
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricOutwardBaseGrowth
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideGeometricFullTerminalCount
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideUniformFloorIntervalStoppedFlux
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideUnitChildRate
import Erdos1135Predecessor.ND.PositiveDensity.ReversedPrefixPredictableSibling
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
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.PowersetCard
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
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

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

private theorem histogramPacketRootLower
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) :
    ∀ i, 16 ^ U.floor ≤ U.state.root i := fun i =>
  (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans (U.state.rootLower i)

def forwardRootPath (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) : (n : ℕ) → (z : (U.forwardIterate cap n).state.Label) →
    NDGeom2RootSideSyracusePath ((U.forwardIterate cap n).state.root z)
      (U.state.root (U.forwardAncestor cap n z))
  | 0, z => NDGeom2RootSideSyracusePath.nil _ (U.state.root_odd z)
  | n + 1, z =>
      ((U.next (cap 0)).forwardRootPath (ndGeom2RootSideCapTail cap) n z).appendRootSideIncidence
        U.state.root_odd (fun _ => by have h := U.floor_twoHundred; omega)
        U.histogramPacketRootLower
        (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical
          (U.forwardFirstIncidence cap n z))

theorem forwardRootPath_word_eq_reverse
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (z : (U.forwardIterate cap n).state.Label) :
    (U.forwardRootPath cap n z).word = (U.forwardWord cap n z).reverse := by
  induction n generalizing U cap with
  | zero => rfl
  | succ n ih =>
      change ((U.next (cap 0)).forwardRootPath (ndGeom2RootSideCapTail cap) n z).word ++
          ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord
            (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical
              (U.forwardFirstIncidence cap n z)) = _
      rw [ih]
      simp only [forwardWord, List.reverse_append,
        ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord,
        ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_word]

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
