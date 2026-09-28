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
import Erdos1135Predecessor.ND.PositiveDensity.CommonZEndpointPrefixFactorization
import Erdos1135Predecessor.ND.PositiveDensity.CommonZFullReverseKernel
import Erdos1135Predecessor.Tao.Probability.Finite
import Erdos1135Predecessor.Tao.Probability.GatedSubmassComplement
import Erdos1135Predecessor.Tao.Probability.Geom2CenteredMoment
import Erdos1135Predecessor.Tao.Probability.Geom2ListReverse
import Erdos1135Predecessor.Tao.Probability.Geom2TerminalMoment
import Erdos1135Predecessor.Tao.Section5.EndpointRatio
import Erdos1135Predecessor.Tao.Section5.FiveStepCompression
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

theorem sum_taoGatedSubmass_eq_sourceEventProbability
    {alpha beta : Type*} [Fintype beta]
    (p : PMF alpha) (G : alpha → Prop) (f : alpha → beta) :
    (∑ y, Tao.taoGatedSubmass p G f y) =
      (p.toOuterMeasure {a | G a}).toReal := by
  have huniv : p.toOuterMeasure Set.univ = 1 :=
    (p.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
  have hfinite (S : Set alpha) : p.toOuterMeasure S ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      p.toOuterMeasure S ≤ p.toOuterMeasure Set.univ :=
        p.toOuterMeasure.mono (Set.subset_univ S)
      _ = 1 := huniv
  have hpartitionEnn :
      p.toOuterMeasure {a | G a} +
          p.toOuterMeasure {a | ¬ G a} = 1 := by
    rw [p.toOuterMeasure_apply, p.toOuterMeasure_apply]
    calc
      (∑' a, {a | G a}.indicator p a) +
          ∑' a, {a | ¬ G a}.indicator p a =
          ∑' a, ({a | G a}.indicator p a +
            {a | ¬ G a}.indicator p a) := ENNReal.tsum_add.symm
      _ = ∑' a, p a := by
        apply tsum_congr
        intro a
        by_cases ha : G a <;> simp [ha]
      _ = 1 := p.tsum_coe
  have hpartitionReal := congrArg ENNReal.toReal hpartitionEnn
  rw [ENNReal.toReal_add (hfinite {a | G a})
      (hfinite {a | ¬ G a}), ENNReal.toReal_one] at hpartitionReal
  have htotal := Tao.taoGatedSubmass_sum_add_rejected_eq_one p G f
  rw [Tao.taoGatedRejectedMass_eq_toOuterMeasure] at htotal
  linarith

end

end PositiveDensity

end ND

end Erdos1135Predecessor
