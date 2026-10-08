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
import Erdos1135Predecessor.ND.PositiveDensity.CommonZPathTelescoping
import Erdos1135Predecessor.Tao.Probability.Finite
import Erdos1135Predecessor.Tao.Probability.Geom2TerminalMoment
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
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

open scoped BigOperators

noncomputable section

theorem ndGeom2PNatListMass_append (as bs : List ℕ+) :
    Tao.geom2PNatListMass (as ++ bs) =
      Tao.geom2PNatListMass as * Tao.geom2PNatListMass bs := by
  unfold Tao.geom2PNatListMass
  simp

theorem ndCommonZOrbitPrefixGeomMass_add
    (N : ℕ) (hN : Odd N) (d m : ℕ) :
    ndCommonZOrbitPrefixGeomMass N hN (d + m) =
      ndCommonZOrbitPrefixGeomMass N hN d *
        ndCommonZOrbitPrefixGeomMass ((Tao.syracuse^[d]) N)
          (Tao.syracuse_iterate_odd_trajectory d N hN) m := by
  unfold ndCommonZOrbitPrefixGeomMass
  rw [Tao.syracuseValuationPNatList_add]
  exact ndGeom2PNatListMass_append _ _

noncomputable def ndCommonZOrbitPrefixLikelihood
    (N : ℕ) (hN : Odd N) (d : ℕ) : ℝ :=
  ndCommonZOrbitPrefixGeomMass N hN d * (3 : ℝ) ^ d

theorem ndCommonZOrbitPrefixMass_add
    (N : ℕ) (hN : Odd N) (d m : ℕ) :
    ndCommonZOrbitPrefixMass N hN (d + m) =
      ndCommonZOrbitPrefixLikelihood N hN d *
        ndCommonZOrbitPrefixMass ((Tao.syracuse^[d]) N)
          (Tao.syracuse_iterate_odd_trajectory d N hN) m := by
  unfold ndCommonZOrbitPrefixMass ndCommonZOrbitPrefixLikelihood
    ndCommonZEdgeSourceWeight
  simp only [ndCommonZOrbitEdge_source]
  rw [ndCommonZOrbitPrefixGeomMass_add, pow_add]
  rw [Function.iterate_add_apply]
  have hiter :
      (Tao.syracuse^[d]) ((Tao.syracuse^[m]) N) =
        (Tao.syracuse^[m]) ((Tao.syracuse^[d]) N) := by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
      Nat.add_comm]
  rw [hiter]
  ring

end

end PositiveDensity

end ND

end Erdos1135Predecessor
