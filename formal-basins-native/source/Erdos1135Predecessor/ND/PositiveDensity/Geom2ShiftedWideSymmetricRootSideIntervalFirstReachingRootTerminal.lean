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
import Erdos1135Predecessor.ND.PositiveDensity.CommonZEndpointPrefixFactorization
import Erdos1135Predecessor.ND.PositiveDensity.CommonZFullReverseKernel
import Erdos1135Predecessor.ND.PositiveDensity.CommonZKCapLongTailFiberCentering
import Erdos1135Predecessor.ND.PositiveDensity.CommonZLongRangeCoordinateCapFirstBad
import Erdos1135Predecessor.ND.PositiveDensity.CommonZPathTelescoping
import Erdos1135Predecessor.ND.PositiveDensity.CommonZProjectionEnergyBound
import Erdos1135Predecessor.ND.PositiveDensity.CommonZReverseGenerator
import Erdos1135Predecessor.ND.PositiveDensity.GatedFiberCovariance
import Erdos1135Predecessor.ND.PositiveDensity.Geom2OneLawGaussianBaseAdaptiveFirstHitRate
import Erdos1135Predecessor.ND.PositiveDensity.Geom2OneLawGaussianFirstHitRate
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricBalancedCrossingAffineDensity
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricBoundedOvershootPhysicalIncidence
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricPhysicalScaleIntervalAdvance
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRegenerativeState
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideBoundedOvershootPhysicalIncidence
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideHistoryPhysicalCollision
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

private theorem rootTerminal_prefixLikelihood_le_terminal_div_source
    (source : ℕ) (hsource : Odd source) (depth : ℕ) :
    ndCommonZOrbitPrefixLikelihood source hsource depth ≤
      (((Tao.syracuse^[depth]) source : ℕ) : ℝ) / (source : ℝ) := by
  let terminal := (Tao.syracuse^[depth]) source
  have hsourcePos : (0 : ℝ) < source := by
    exact_mod_cast Odd.pos hsource
  have hterminalPos : (0 : ℝ) < terminal := by
    exact_mod_cast Odd.pos
      (Tao.syracuse_iterate_odd_trajectory depth source hsource)
  have hfactor :
      ndCommonZOrbitPrefixMass source hsource depth =
        ndCommonZOrbitPrefixLikelihood source hsource depth *
          (1 / (terminal : ℝ)) := by
    have hadd := ndCommonZOrbitPrefixMass_add source hsource depth 0
    simpa only [Nat.add_zero, ndCommonZOrbitPrefixMass_zero, terminal] using
      hadd
  have hmass := ndCommonZOrbitPrefixMass_le_zero source hsource depth
  rw [hfactor, ndCommonZOrbitPrefixMass_zero] at hmass
  apply (le_div_iff₀ hsourcePos).2
  have hscaled := mul_le_mul_of_nonneg_right hmass hterminalPos.le
  calc
    ndCommonZOrbitPrefixLikelihood source hsource depth * (source : ℝ) =
        (ndCommonZOrbitPrefixLikelihood source hsource depth *
            (1 / (terminal : ℝ))) *
          (terminal : ℝ) * (source : ℝ) := by
      field_simp
    _ ≤ (1 / (source : ℝ)) * (terminal : ℝ) * (source : ℝ) := by
      exact mul_le_mul_of_nonneg_right hscaled hsourcePos.le
    _ = (terminal : ℝ) := by field_simp

theorem
    ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom_eq_prefixLikelihood
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hbaseNine : ∀ i, 9 ≤ base i)
    (hrootLower : ∀ i, 16 ^ base i ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom z =
      ndCommonZOrbitPrefixLikelihood
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd
          hrootOdd hbaseNine hrootLower z)
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z) := by
  have hpmf := Tao.geom2PNatListPMF_apply_length_toReal
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord z)
  rw [ndGeom2PredictableRootSideBoundedOvershootIncidence_chronologicalWord_length
    z] at hpmf
  unfold ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom
    ndCommonZOrbitPrefixLikelihood ndCommonZOrbitPrefixGeomMass
  rw [ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_valuation
    hrootOdd hbaseNine hrootLower z]
  rw [← hpmf]
  unfold
    ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord
  rw [Tao.geom2PNatListPMF_apply_reverse]
  ring

theorem
    ndGeom2PredictableRootSideBoundedOvershootIncidence_source_mul_atom_le_root
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hbaseNine : ∀ i, 9 ≤ base i)
    (hrootLower : ∀ i, 16 ^ base i ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) *
        ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom z ≤
      (root (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) : ℝ) := by
  let source := ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z
  let depth := ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z
  let terminal :=
    root (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)
  have hsourceOdd : Odd source := by
    simpa only [source] using
      ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd
        hrootOdd hbaseNine hrootLower z
  have hsourcePos : (0 : ℝ) < source := by
    exact_mod_cast Odd.pos hsourceOdd
  have hlike :=
    rootTerminal_prefixLikelihood_le_terminal_div_source
      source hsourceOdd depth
  have hiterate : (Tao.syracuse^[depth]) source = terminal := by
    simpa only [source, depth, terminal] using
      ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_iterate
        hrootOdd hbaseNine hrootLower z
  rw [hiterate] at hlike
  rw [ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom_eq_prefixLikelihood
    hrootOdd hbaseNine hrootLower z]
  calc
    (source : ℝ) * ndCommonZOrbitPrefixLikelihood source hsourceOdd depth =
        ndCommonZOrbitPrefixLikelihood source hsourceOdd depth *
          (source : ℝ) := by ring
    _ ≤ ((terminal : ℝ) / (source : ℝ)) * (source : ℝ) :=
      mul_le_mul_of_nonneg_right hlike hsourcePos.le
    _ = (terminal : ℝ) := by field_simp

end

end PositiveDensity

end ND

end Erdos1135Predecessor
