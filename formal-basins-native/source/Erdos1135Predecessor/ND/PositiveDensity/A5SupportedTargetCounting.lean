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
import Erdos1135Predecessor.ND.PositiveDensity.CommonZPathTelescoping
import Erdos1135Predecessor.ND.PositiveDensity.CommonZReverseGenerator
import Erdos1135Predecessor.ND.PositiveDensity.TargetCounting
import Erdos1135Predecessor.Tao.Fourier.Section7SChiActualQ
import Erdos1135Predecessor.Tao.Probability.Finite
import Erdos1135Predecessor.Tao.Probability.FullL1
import Erdos1135Predecessor.Tao.Probability.GatedSubmassPartition
import Erdos1135Predecessor.Tao.Section5.FiveStepCompression
import Erdos1135Predecessor.Tao.Syracuse.AffineEnvelope
import Erdos1135Predecessor.Tao.Syracuse.AffineOdd
import Erdos1135Predecessor.Tao.Syracuse.AffineResidue
import Erdos1135Predecessor.Tao.Syracuse.AffineTrajectory
import Erdos1135Predecessor.Tao.Syracuse.Defs
import Erdos1135Predecessor.Tao.Syracuse.OddSource
import Erdos1135Predecessor.Tao.Syracuse.TruncatedValuationPacking
import Erdos1135Predecessor.Tao.Syracuse.ValuationDistribution
import Erdos1135Predecessor.Terras.Density.NaturalDensity
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

noncomputable section

theorem finset_card_le_natCount_of_subset_range
    {S : Finset ℕ} {A : Set ℕ} {X : ℕ}
    (hX : S ⊆ Finset.range X) (hA : ↑S ⊆ A) :
    S.card ≤ Terras.natCount A X := by
  classical
  rw [Terras.natCount_eq_count, Nat.count_eq_card_filter_range]
  apply Finset.card_le_card
  intro N hN
  exact Finset.mem_filter.mpr ⟨hX hN, hA hN⟩

end

end PositiveDensity

end ND

end Erdos1135Predecessor
