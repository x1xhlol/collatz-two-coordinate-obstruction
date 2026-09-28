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
import Erdos1135Predecessor.ND.PositiveDensity.CommonZEndpointAdaptiveCanonicalTotal
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
import Erdos1135Predecessor.Tao.Syracuse.AffineTrajectory
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
import Mathlib.RingTheory.ZMod.UnitsCyclic
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

def ndBalancedTotal (j : ℕ) : ℕ := Nat.clog 2 (3 ^ j)

@[simp] theorem ndBalancedTotal_zero : ndBalancedTotal 0 = 0 := by
  simp [ndBalancedTotal]

theorem three_pow_le_two_pow_ndBalancedTotal (j : ℕ) :
    3 ^ j ≤ 2 ^ ndBalancedTotal j := by
  exact Nat.le_pow_clog (by norm_num) _

theorem two_pow_ndBalancedTotal_le_two_mul_three_pow (j : ℕ) :
    2 ^ ndBalancedTotal j ≤ 2 * 3 ^ j := by
  apply two_pow_clog_two_le_two_mul
  positivity

theorem ndBalancedTotal_le_two_mul (j : ℕ) :
    ndBalancedTotal j ≤ 2 * j := by
  apply Nat.clog_le_of_le_pow
  calc
    3 ^ j ≤ 4 ^ j := by
      gcongr
      norm_num
    _ = (2 ^ 2) ^ j := by norm_num
    _ = 2 ^ (2 * j) := by rw [pow_mul]

end

end PositiveDensity

end ND

end Erdos1135Predecessor
