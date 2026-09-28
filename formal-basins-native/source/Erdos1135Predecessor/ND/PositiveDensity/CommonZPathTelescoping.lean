/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.CommonZReverseGenerator
import Erdos1135Predecessor.Tao.Syracuse.FirstPassageInterval
import Erdos1135Predecessor.Tao.Syracuse.LogTimeCollatzBridge
import Erdos1135Predecessor.Tao.Syracuse.ValuationDistribution

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

open scoped BigOperators

noncomputable section

def ndCommonZOrbitEdge (N : ℕ) (hN : Odd N) (k : ℕ) :
    NDCommonZReverseEdge :=
  ndCommonZActualReverseEdge ((Tao.syracuse^[k]) N)
    (Odd.pos (Tao.syracuse_iterate_odd_trajectory k N hN))

@[simp] theorem ndCommonZOrbitEdge_source
    (N : ℕ) (hN : Odd N) (k : ℕ) :
    (ndCommonZOrbitEdge N hN k).source = (Tao.syracuse^[k]) N :=
  rfl

@[simp] theorem ndCommonZOrbitEdge_target
    (N : ℕ) (hN : Odd N) (k : ℕ) :
    (ndCommonZOrbitEdge N hN k).target =
      (Tao.syracuse^[k + 1]) N := by
  unfold ndCommonZOrbitEdge ndCommonZActualReverseEdge
  simp only
  rw [Function.iterate_succ_apply']

@[simp] theorem ndCommonZOrbitEdge_exponent
    (N : ℕ) (hN : Odd N) (k : ℕ) :
    (ndCommonZOrbitEdge N hN k).exponent =
      Tao.syracuseExponent ((Tao.syracuse^[k]) N) :=
  rfl

noncomputable def ndCommonZOrbitPrefixGeomMass
    (N : ℕ) (hN : Odd N) (k : ℕ) : ℝ :=
  Tao.geom2PNatListMass (Tao.syracuseValuationPNatList k N hN)

noncomputable def ndCommonZOrbitPrefixMass
    (N : ℕ) (hN : Odd N) (k : ℕ) : ℝ :=
  ndCommonZOrbitPrefixGeomMass N hN k *
    ndCommonZEdgeSourceWeight k (ndCommonZOrbitEdge N hN k)

noncomputable def ndCommonZOrbitStepDefect
    (N : ℕ) (hN : Odd N) (k : ℕ) : ℝ :=
  ndCommonZOrbitPrefixGeomMass N hN k *
    ndCommonZEdgeDefect k (ndCommonZOrbitEdge N hN k)

theorem ndCommonZOrbitPrefixGeomMass_nonneg
    (N : ℕ) (hN : Odd N) (k : ℕ) :
    0 ≤ ndCommonZOrbitPrefixGeomMass N hN k := by
  unfold ndCommonZOrbitPrefixGeomMass
  rw [Tao.geom2PNatListMass_eq_inv_pow]
  positivity

theorem ndCommonZOrbitStepDefect_nonneg
    (N : ℕ) (hN : Odd N) (k : ℕ) :
    0 ≤ ndCommonZOrbitStepDefect N hN k := by
  exact mul_nonneg (ndCommonZOrbitPrefixGeomMass_nonneg N hN k)
    (ndCommonZEdgeDefect_nonneg k (ndCommonZOrbitEdge N hN k))

theorem ndCommonZOrbitPrefixGeomMass_succ
    (N : ℕ) (hN : Odd N) (k : ℕ) :
    ndCommonZOrbitPrefixGeomMass N hN (k + 1) =
      ndCommonZOrbitPrefixGeomMass N hN k /
        (2 : ℝ) ^ Tao.syracuseExponent ((Tao.syracuse^[k]) N) := by
  unfold ndCommonZOrbitPrefixGeomMass
  rw [Tao.geom2PNatListMass_eq_inv_pow,
    Tao.geom2PNatListMass_eq_inv_pow,
    Tao.taoTupleWeight_syracuseValuationPNatList_succ]
  rw [pow_add]
  simp [Tao.syracuseTerminalExponentPNat]
  rw [div_eq_mul_inv]
  ring

theorem ndCommonZOrbit_transport_eq_nextMass
    (N : ℕ) (hN : Odd N) (k : ℕ) :
    ndCommonZOrbitPrefixGeomMass N hN k *
        ndCommonZEdgeTransportedWeight k (ndCommonZOrbitEdge N hN k) =
      ndCommonZOrbitPrefixMass N hN (k + 1) := by
  unfold ndCommonZOrbitPrefixMass
  rw [ndCommonZOrbitPrefixGeomMass_succ]
  unfold ndCommonZEdgeTransportedWeight
    ndCommonZEdgeSourceWeight
  simp only [ndCommonZOrbitEdge_exponent, ndCommonZOrbitEdge_target,
    ndCommonZOrbitEdge_source]
  rw [pow_succ]
  ring

theorem ndCommonZOrbitPrefixMass_eq_next_add_defect
    (N : ℕ) (hN : Odd N) (k : ℕ) :
    ndCommonZOrbitPrefixMass N hN k =
      ndCommonZOrbitPrefixMass N hN (k + 1) +
        ndCommonZOrbitStepDefect N hN k := by
  change
    ndCommonZOrbitPrefixGeomMass N hN k *
        ndCommonZEdgeSourceWeight k (ndCommonZOrbitEdge N hN k) =
      ndCommonZOrbitPrefixMass N hN (k + 1) +
        ndCommonZOrbitPrefixGeomMass N hN k *
          ndCommonZEdgeDefect k (ndCommonZOrbitEdge N hN k)
  rw [ndCommonZEdge_source_eq_transport_add_defect]
  rw [mul_add, ndCommonZOrbit_transport_eq_nextMass]

@[simp] theorem ndCommonZOrbitPrefixMass_zero
    (N : ℕ) (hN : Odd N) :
    ndCommonZOrbitPrefixMass N hN 0 = 1 / (N : ℝ) := by
  change
    Tao.geom2PNatListMass [] * ((3 : ℝ) ^ 0 / (N : ℝ)) =
      1 / (N : ℝ)
  simp [Tao.geom2PNatListMass]

theorem ndCommonZOrbitPrefixMass_antitone_step
    (N : ℕ) (hN : Odd N) (k : ℕ) :
    ndCommonZOrbitPrefixMass N hN (k + 1) ≤
      ndCommonZOrbitPrefixMass N hN k := by
  rw [ndCommonZOrbitPrefixMass_eq_next_add_defect N hN k]
  exact le_add_of_nonneg_right (ndCommonZOrbitStepDefect_nonneg N hN k)

theorem ndCommonZOrbitPrefixMass_le_zero
    (N : ℕ) (hN : Odd N) (k : ℕ) :
    ndCommonZOrbitPrefixMass N hN k ≤
      ndCommonZOrbitPrefixMass N hN 0 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      exact (ndCommonZOrbitPrefixMass_antitone_step N hN k).trans ih

end

end PositiveDensity

end ND

end Erdos1135Predecessor
