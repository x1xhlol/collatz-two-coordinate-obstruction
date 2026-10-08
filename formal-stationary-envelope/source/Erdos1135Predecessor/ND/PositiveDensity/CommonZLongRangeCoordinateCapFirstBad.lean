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

def ndPNatAddNat (cap : ℕ) (a : ℕ+) : ℕ+ :=
  ⟨cap + (a : ℕ), by
    have ha : 0 < (a : ℕ) := a.2
    omega⟩

@[simp] theorem ndPNatAddNat_coe (cap : ℕ) (a : ℕ+) :
    (ndPNatAddNat cap a : ℕ) = cap + (a : ℕ) :=
  rfl

def ndGeom2PNatTailShiftEquiv (cap : ℕ) :
    ℕ+ ≃ {a : ℕ+ // cap < (a : ℕ)} :=
  { toFun := fun a =>
      ⟨ndPNatAddNat cap a, by
        change cap < cap + (a : ℕ)
        have ha : 0 < (a : ℕ) := a.2
        omega⟩
    invFun := fun a =>
      ⟨(a.1 : ℕ) - cap, Nat.sub_pos_of_lt a.2⟩
    left_inv := by
      intro a
      apply Subtype.ext
      change cap + (a : ℕ) - cap = (a : ℕ)
      omega
    right_inv := by
      intro a
      apply Subtype.ext
      apply Subtype.ext
      change cap + ((a.1 : ℕ) - cap) = (a.1 : ℕ)
      omega }

theorem geom2PNat_tailShift_apply_toReal
    (cap : ℕ) (a : ℕ+) :
    (Tao.geom2PNat (ndPNatAddNat cap a)).toReal =
      (1 / 2 : ℝ) ^ cap * (Tao.geom2PNat a).toReal := by
  rw [Tao.geom2PNat_apply_toReal, Tao.geom2PNat_apply_toReal]
  simp only [ndPNatAddNat_coe, pow_add]

theorem ndPMFWeightedExpectation_geom2_tail_indicator_eq_shift
    (cap : ℕ) (F : ℕ+ → ℝ) :
    ndPMFWeightedExpectation Tao.geom2PNat (fun a =>
        {b : ℕ+ | cap < (b : ℕ)}.indicator F a) =
      (1 / 2 : ℝ) ^ cap *
        ndPMFWeightedExpectation Tao.geom2PNat (fun a =>
          F (ndPNatAddNat cap a)) := by
  classical
  let Tail : Set ℕ+ := {a | cap < (a : ℕ)}
  let f : ℕ+ → ℝ := fun a =>
    (Tao.geom2PNat a).toReal * Tail.indicator F a
  have hsupp : Function.support f ⊆ Tail := by
    intro a ha
    by_contra htail
    have hfzero : f a = 0 := by
      unfold f
      rw [Set.indicator_of_notMem htail]
      simp
    exact ha hfzero
  let e := ndGeom2PNatTailShiftEquiv cap
  calc
    ndPMFWeightedExpectation Tao.geom2PNat (fun a =>
        {b : ℕ+ | cap < (b : ℕ)}.indicator F a) =
        ∑' a : ℕ+, f a := by
      rfl
    _ = ∑' a : {a : ℕ+ // a ∈ Tail}, f a.1 :=
      (tsum_subtype_eq_of_support_subset
        (f := f) (s := Tail) hsupp).symm
    _ = ∑' a : {a : ℕ+ // a ∈ Tail},
        (Tao.geom2PNat a.1).toReal * F a.1 := by
      apply tsum_congr
      intro a
      have ha : a.1 ∈ Tail := a.2
      simp only [f]
      rw [Set.indicator_of_mem ha]
    _ = ∑' a : ℕ+,
        (Tao.geom2PNat (e a).1).toReal * F (e a).1 := by
      exact
        (e.tsum_eq (fun a : {a : ℕ+ // a ∈ Tail} =>
          (Tao.geom2PNat a.1).toReal * F a.1)).symm
    _ = ∑' a : ℕ+,
        (1 / 2 : ℝ) ^ cap *
          ((Tao.geom2PNat a).toReal * F (ndPNatAddNat cap a)) := by
      apply tsum_congr
      intro a
      change
        (Tao.geom2PNat (ndPNatAddNat cap a)).toReal *
            F (ndPNatAddNat cap a) =
          (1 / 2 : ℝ) ^ cap *
            ((Tao.geom2PNat a).toReal * F (ndPNatAddNat cap a))
      rw [geom2PNat_tailShift_apply_toReal]
      ring
    _ = (1 / 2 : ℝ) ^ cap *
        ndPMFWeightedExpectation Tao.geom2PNat (fun a =>
          F (ndPNatAddNat cap a)) := by
      rw [tsum_mul_left]
      rfl

end

end PositiveDensity

end ND

end Erdos1135Predecessor
