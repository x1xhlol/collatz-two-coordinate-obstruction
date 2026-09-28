/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.GeneralTargetFrozenSeed
import Erdos1135Predecessor.ND.PositiveDensity.ExplicitReferenceHeightCensus

namespace Erdos1135Predecessor.ND.PositiveDensity
open scoped BigOperators
noncomputable section
namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem fullTerminal_source_window
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : U.state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin U.floor (U.state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax U.floor (U.state.root i))
    (z : U.FullTerminalIncidence X hX hi) :
    X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) ∧
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) < 32 * X := by
  have hpacket : ∀ i, 16 ^ U.floor ≤ U.state.root i := fun i =>
    (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans (U.state.rootLower i)
  have hs := U.fullTerminalShift_spec X hX hi
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)
  have hb := ndGeom2RootSideCommonFloor_capOne_source_bounds U.state.root_odd
    (by have h := U.floor_twoHundred; omega) hpacket z
  refine ⟨hs.2.1.trans hb.1, ?_⟩
  nlinarith only [hb.2, hs.2.2]

theorem fullTerminal_weighted_residue_census_of_nonreturningSeed
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (hseed : ∀ i k, 0 < k → (Tao.syracuse^[k]) (U.state.root i) ≠ U.state.root i)
    (q : ℕ) (X : ℝ) (hX : 0 < X) (hQ : ((3 ^ q : ℕ) : ℝ) ≤ X)
    (hsource : ∀ z : U.FullTerminalAt cap n shift K,
      X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) ∧
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) < 32 * X)
    (psi : ZMod (3 ^ q) → ℝ) (hp : ∀ y, 0 ≤ psi y) :
    letI := (U.forwardIterate cap n).state.labelFintype
    (∑ z : U.FullTerminalAt cap n shift K,
      ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
        (U.forwardIterate cap n).state.outerWeight z *
        psi (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ZMod (3 ^ q))) ≤
      33 * U.parentSourcePotential * ndTernaryUniformMean q psi := by
  classical
  letI := (U.forwardIterate cap n).state.labelFintype
  have hc := U.fullTerminal_weighted_source_charge_of_nonreturningSeed cap n shift K hseed
    X hX (fun z => (hsource z).1) (fun x => psi (x : ZMod (3 ^ q))) (fun x => hp _)
  have hs := terminal_source_residue_sum_le (U.fullTerminalSources cap n shift K) q X hX hQ
    (fun x hx => by obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx; exact (hsource z).2) psi hp
  calc
    _ ≤ _ := hc
    _ ≤ (U.parentSourcePotential / X) * (33 * X * ndTernaryUniformMean q psi) :=
      mul_le_mul_of_nonneg_left hs (div_nonneg U.frozenSourcePotential_nonneg hX.le)
    _ = _ := by field_simp

theorem fullTerminal_subweight_fan_two_conductor_bound_of_height_of_nonreturningSeed
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K J : ℕ)
    (hseed : ∀ i k, 0 < k → (Tao.syracuse^[k]) (U.state.root i) ≠ U.state.root i)
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
    have hc := U.fullTerminal_weighted_residue_census_of_nonreturningSeed cap n shift K hseed
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

theorem forwardGoodDepthShiftUnitMass_le_two_conductor_of_height_of_nonreturningSeed
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K m k : ℕ) (hmk : m ≤ k)
    (hseed : ∀ i k, 0 < k → (Tao.syracuse^[k]) (U.state.root i) ≠ U.state.root i)
    (X : ℝ) (hX : 0 < X) (hQ : ((3 ^ k : ℕ) : ℝ) ≤ X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i))
    (hsource : ∀ z : (U.forwardIterate cap n).FullTerminalIncidence X hX hi,
      X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) ∧
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) < 32 * X)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hL1 : ndTernaryUniformMean k (fun y => |ndSyracuseUnitReferenceDensity k y -
      ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)|) ≤ epsilon)
    (p : ℕ) (hp : 0 < p)
    (hheight : ∀ y, ndSyracuseUnitReferenceDensity m y ≤ (2/3:ℝ)*(p:ℝ)) :
    U.forwardCoreTerminalGoodDepthShiftUnitMass cap width n K k X hX hi ≤
      (8 / 9 : ℝ) * (p : ℝ) * U.fullGoodCoreTerminalMass cap width n
        ((U.forwardIterate cap n).fullTerminalShift X hX hi) 1 +
        44 * U.parentSourcePotential * epsilon := by
  classical
  let V := U.forwardIterate cap n
  letI := V.state.labelFintype
  apply (U.forwardGoodDepthShiftUnitMass_le_full_cap_one_fan cap width n K k X hX hi).trans
  have h := U.fullTerminal_subweight_fan_two_conductor_bound_of_height_of_nonreturningSeed cap n (V.fullTerminalShift X hX hi)
    1 (K / 2 + 1) hseed
    (U.fullGoodCoreTerminalWeight cap width n (V.fullTerminalShift X hX hi) 1)
    (U.fullGoodCoreTerminalWeight_nonneg cap width n (V.fullTerminalShift X hX hi) 1)
    (U.fullGoodCoreTerminalWeight_le_original cap width n (V.fullTerminalShift X hX hi) 1)
    m k hmk X hX hQ hsource epsilon he hL1 ((2/3:ℝ)*(p:ℝ)) (by positivity) hheight
  convert h using 1 <;> unfold fullGoodCoreTerminalMass <;> ring

theorem fullGoodCoreTerminalMass_ge_of_square_budget_and_height_of_nonreturningSeed
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K m k : ℕ)
    (hm : 1 ≤ m) (hmk : m ≤ k) (hk : k ≤ (U.forwardIterate cap n).floor)
    (hseed : ∀ i k, 0 < k → (Tao.syracuse^[k]) (U.state.root i) ≠ U.state.root i)
    {Cmix a : ℝ}
    (hCmix : 0 ≤ Cmix) (hmix : ndExplicitQuadraticMixingAt Cmix m)
    (ha : 0 < a) (hsquare : 88 * U.parentSourcePotential * Cmix ≤ a * (m : ℝ) ^ 2)
    (p : ℕ) (hp : 0 < p)
    (hheight : ∀ y, ndSyracuseUnitReferenceDensity m y ≤ (2/3:ℝ)*(p:ℝ))
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i))
    (hmark : a ≤ U.forwardCoreTerminalGoodDepthShiftUnitMass cap width n K k X hX hi) :
    9 * a / (16 * (p : ℝ)) ≤ U.fullGoodCoreTerminalMass cap width n
      ((U.forwardIterate cap n).fullTerminalShift X hX hi) 1 := by
  let V := U.forwardIterate cap n
  have hOrig := (ha.trans_le hmark).trans_le
    (U.forwardGoodDepthShiftUnitMass_le_original cap width n K k X hX hi)
  have hQ := U.terminal_conductor_room_of_pos_mark cap width n K k hk X hX hi hOrig
  have hbound := U.forwardGoodDepthShiftUnitMass_le_two_conductor_of_height_of_nonreturningSeed cap width n K m k hmk
    hseed X hX hQ.le hi
    (fun z => V.fullTerminal_source_window X hX hi z)
    (Cmix / (m : ℝ) ^ 2) (div_nonneg hCmix (by positivity)) (hmix k hmk) p hp hheight
  have herror := explicitConductor_error_le_half hm hsquare
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (p : ℝ))).2
  nlinarith only [hmark, hbound, herror]

theorem fullGoodCoreTerminal_mass_mul_lower_le_frozenPotential_mul_card_of_nonreturningSeed
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (hseed : ∀ i k, 0 < k → (Tao.syracuse^[k]) (U.state.root i) ≠ U.state.root i)
    (X : ℝ) (hX : 0 < X)
    (hsource : ∀ z : U.FullTerminalAt cap n shift K,
      X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ)) :
    X * U.fullGoodCoreTerminalMass cap width n shift K ≤
      U.parentSourcePotential * (U.fullGoodCoreTerminalSources cap width n shift K).card := by
  classical
  letI := (U.forwardIterate cap n).state.labelFintype
  let S := U.fullGoodCoreTerminalSources cap width n shift K
  let psi := fun x : ℕ => if x ∈ S then (1 : ℝ) else 0
  let W := fun z : U.FullTerminalAt cap n shift K =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
      (U.forwardIterate cap n).state.outerWeight z
  have hW : ∀ z, 0 ≤ W z := fun z =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight_nonneg _
      (U.forwardIterate cap n).state.weight_nonneg z
  have hp : ∀ x, 0 ≤ psi x := by intro x; dsimp [psi]; split_ifs <;> norm_num
  have hm : U.fullGoodCoreTerminalMass cap width n shift K ≤
      ∑ z, W z * psi (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) := by
    apply Finset.sum_le_sum
    intro z _
    unfold fullGoodCoreTerminalWeight
    rw [U.fullCoreTerminalWeight_eq_ite]
    unfold ndTerminalDepthShiftIndicator
    split_ifs with hc hg hg
    · have hs : ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z ∈ S :=
        Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hg⟩, rfl⟩
      simp only [psi, if_pos hs, mul_one]
      exact le_rfl
    all_goals simpa only [mul_zero, zero_mul] using mul_nonneg (hW z) (hp _)
  have hsum : (∑ x ∈ U.fullTerminalSources cap n shift K, psi x) = (S.card : ℝ) := by
    calc
      _ = ∑ x ∈ S, psi x := by
        symm
        apply Finset.sum_subset (U.fullGoodCoreTerminalSources_subset_fullTerminalSources cap width n shift K)
        intro x _ hx
        simp only [psi, S, if_neg hx]
      _ = _ := by simp [psi]
  have hc := U.fullTerminal_weighted_source_charge_of_nonreturningSeed cap n shift K hseed
    X hX hsource psi hp
  rw [hsum] at hc
  have h := hm.trans hc
  rw [div_mul_eq_mul_div] at h
  exact (by simpa only [mul_comm X] using (le_div_iff₀ hX).mp h)

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState
end
end Erdos1135Predecessor.ND.PositiveDensity
