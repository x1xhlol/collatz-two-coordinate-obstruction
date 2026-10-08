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
import Erdos1135Predecessor.ND.Fourier.FixedTotalReferenceRatio
import Erdos1135Predecessor.ND.PositiveDensity.SyracuseBoundedRealizer
import Erdos1135Predecessor.ND.PositiveDensity.TerminalTotalCancellation
import Erdos1135Predecessor.Tao.Fourier.Section7SChiActualQ
import Erdos1135Predecessor.Tao.Probability.Finite
import Erdos1135Predecessor.Tao.Probability.FullL1
import Erdos1135Predecessor.Tao.Probability.Geom2CenteredMoment
import Erdos1135Predecessor.Tao.Renewal.Lemma77PascalGaussian
import Erdos1135Predecessor.Tao.Section6.ConductorFrequency
import Erdos1135Predecessor.Tao.Section6.ModulusProjection
import Erdos1135Predecessor.Tao.Syracuse.AffineTrajectory
import Erdos1135Predecessor.Tao.Syracuse.Defs
import Erdos1135Predecessor.Tao.Syracuse.TruncatedValuationPacking
import Erdos1135Predecessor.Terras.Density.NaturalDensity
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.PowersetCard
import Mathlib.Data.Sym.Card
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

noncomputable section

theorem ndThreeUnitResidue_of_projection_ne_zero
    {m : ℕ} (hm : 0 < m) (x : ZMod (3 ^ m))
    (hproj : Tao.taoZModThreeProjection (Nat.one_le_iff_ne_zero.mpr hm.ne') x ≠ 0) :
    ndThreeUnitResidue x := by
  unfold ndThreeUnitResidue
  intro hmod
  apply hproj
  rw [Tao.taoZModThreeProjection_eq_natCast_val]
  exact (ZMod.natCast_eq_zero_iff x.val 3).2
    ((Nat.dvd_iff_mod_eq_zero).2 hmod)

theorem taoSection7OffsetZMod_one_ne_zero (as : List ℕ+) :
    Tao.taoSection7OffsetZMod 1 as ≠ 0 := by
  simp [Tao.taoSection7OffsetZMod]
  intro h
  exfalso
  have hdvd : 3 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 3).1 h
  norm_num at hdvd

theorem ndThreeUnitResidue_taoSection7OffsetZMod
    {m : ℕ} (hm : 0 < m) (as : List ℕ+) :
    ndThreeUnitResidue (Tao.taoSection7OffsetZMod m as) := by
  apply ndThreeUnitResidue_of_projection_ne_zero hm
  rw [Tao.taoSection7OffsetZMod_projection_eq_take_of_le]
  exact taoSection7OffsetZMod_one_ne_zero (as.take 1)

theorem syracPMF_toReal_eq_zero_of_not_unit
    {m : ℕ} (hm : 0 < m) (x : ZMod (3 ^ m))
    (hx : ¬ ndThreeUnitResidue x) :
    (Tao.syracPMF m x).toReal = 0 := by
  classical
  rw [Tao.syracPMF_eq_geom2PNatListPMF_map_taoSection7OffsetZMod,
    Tao.pmf_map_apply_toReal_tsum]
  calc
    (∑' as : List ℕ+,
        if x = Tao.taoSection7OffsetZMod m as then
          (Tao.geom2PNatListPMF m as).toReal else 0) =
        ∑' _as : List ℕ+, (0 : ℝ) := by
      apply tsum_congr
      intro as
      have hne : x ≠ Tao.taoSection7OffsetZMod m as := by
        intro h
        apply hx
        rw [h]
        exact ndThreeUnitResidue_taoSection7OffsetZMod hm as
      simp [hne]
    _ = 0 := tsum_zero

end

end PositiveDensity

end ND

end Erdos1135Predecessor
