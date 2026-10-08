/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalWeightedCensus

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

open Filter

noncomputable section

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem fullTerminal_subweight_fan_two_conductor_bound_of_height
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K J : ℕ)
    (hseedNeOne : ∀ i, U.state.root i ≠ 1)
    (hseedHitsOne : ∀ i, ∃ t : ℕ, (Tao.syracuse^[t]) (U.state.root i) = 1)
    (v : U.FullTerminalAt cap n shift K → ℝ)
    (hv : ∀ z, 0 ≤ v z)
    (hvw : ∀ z, v z ≤ ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
      (U.forwardIterate cap n).state.outerWeight z)
    (m k : ℕ) (hmk : m ≤ k) (X : ℝ) (hX : 0 < X)
    (hQ : ((3 ^ k : ℕ) : ℝ) ≤ X)
    (hsource : ∀ z : U.FullTerminalAt cap n shift K,
      X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) ∧
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) < 32 * X)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hL1 : ndTernaryUniformMean k (fun y => |ndSyracuseUnitReferenceDensity k y -
      ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)|) ≤ epsilon)
    (H : ℝ) (hH : 0 ≤ H)
    (hheight : ∀ y, ndSyracuseUnitReferenceDensity m y ≤ H) :
    letI := (U.forwardIterate cap n).state.labelFintype
    (∑ z : U.FullTerminalAt cap n shift K, v z *
        ∑ j : Fin J, (1 / 4 : ℝ) ^ j.val * ndSyracuseUnitReferenceDensity k
          (ndTerminalSourceFan j.val
            (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) : ZMod (3 ^ k))) ≤
      (4 / 3 : ℝ) * H * (∑ z, v z) +
        44 * U.parentSourcePotential * epsilon := by
  classical
  letI := (U.forwardIterate cap n).state.labelFintype
  let W := fun z : U.FullTerminalAt cap n shift K =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
      (U.forwardIterate cap n).state.outerWeight z
  let source := fun z : U.FullTerminalAt cap n shift K =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z
  let delta := fun y : ZMod (3 ^ k) => |ndSyracuseUnitReferenceDensity k y -
    ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)|
  have hmass : 0 ≤ ∑ z, v z := Finset.sum_nonneg fun z _ => hv z
  have hstep (j : ℕ) :
      (∑ z, v z * ndSyracuseUnitReferenceDensity k
        (ndTerminalSourceFan j (source z) : ZMod (3 ^ k))) ≤
      H * (∑ z, v z) + 33 * U.parentSourcePotential * epsilon := by
    let psi := fun y : ZMod (3 ^ k) => delta (ndTerminalResidueFan k j y)
    have hp : ∀ y, 0 ≤ psi y := fun _ => abs_nonneg _
    have hmean : ndTernaryUniformMean k psi ≤ epsilon := by
      rw [show psi = (fun y => delta (ndTerminalResidueFan k j y)) from rfl,
        terminalResidueFan_fullMean]
      exact hL1
    have hc := U.fullTerminal_weighted_residue_census cap n shift K hseedNeOne hseedHitsOne
      k X hX hQ hsource psi hp
    have hc' : (∑ z, v z * psi (source z : ZMod (3 ^ k))) ≤
        33 * U.parentSourcePotential * epsilon := by
      apply le_trans (Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_right (hvw z) (hp _)))
      exact hc.trans (mul_le_mul_of_nonneg_left hmean
        (mul_nonneg (by norm_num) U.frozenSourcePotential_nonneg))
    have hpoint (x : ℕ) : ndSyracuseUnitReferenceDensity k
        (ndTerminalSourceFan j x : ZMod (3 ^ k)) ≤ H + psi (x : ZMod (3 ^ k)) := by
      dsimp [psi, delta]
      rw [terminalResidueFan_natCast]
      have hb := hheight
        (Tao.taoZModThreeProjection hmk (ndTerminalSourceFan j x : ZMod (3 ^ k)))
      have ha := le_abs_self (ndSyracuseUnitReferenceDensity k
          (ndTerminalSourceFan j x : ZMod (3 ^ k)) -
        ndSyracuseUnitReferenceDensity m
          (Tao.taoZModThreeProjection hmk (ndTerminalSourceFan j x : ZMod (3 ^ k))))
      linarith
    calc
      _ ≤ ∑ z, v z * (H + psi (source z : ZMod (3 ^ k))) :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpoint _) (hv z)
      _ = H * (∑ z, v z) + ∑ z, v z * psi (source z : ZMod (3 ^ k)) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, mul_comm]
      _ ≤ _ := add_le_add_right hc' _
  let B := H * (∑ z, v z) + 33 * U.parentSourcePotential * epsilon
  have hB : 0 ≤ B := add_nonneg (mul_nonneg hH hmass)
    (mul_nonneg (mul_nonneg (by norm_num) U.frozenSourcePotential_nonneg) he)
  calc
    _ = ∑ j : Fin J, (1 / 4 : ℝ) ^ j.val *
        ∑ z, v z * ndSyracuseUnitReferenceDensity k
          (ndTerminalSourceFan j.val (source z) : ZMod (3 ^ k)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro z _
      dsimp [source]
      ring
    _ ≤ ∑ j : Fin J, (1 / 4 : ℝ) ^ j.val * B :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hstep _) (by positivity)
    _ = (∑ j : Fin J, (1 / 4 : ℝ) ^ j.val) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ (4 / 3 : ℝ) * B := mul_le_mul_of_nonneg_right (terminal_fan_coeff_sum_le J) hB
    _ = _ := by dsimp [B]; ring

theorem fullCoreTerminalWeight_eq_ite
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (z : U.FullTerminalAt cap n shift K) :
    letI := Classical.propDecidable;
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
        (U.forwardCoreOuterWeight cap width n) z =
      if U.forwardCore cap width n (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)
      then ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
        (U.forwardIterate cap n).state.outerWeight z else 0 := by
  classical
  unfold ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight forwardCoreOuterWeight
  split_ifs <;> simp

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
