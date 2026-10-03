import TerminalFanEnvelope

set_option autoImplicit false

namespace CollatzCanonical.PeriodicCensusFloor
open Erdos1135Predecessor
open Erdos1135Predecessor.ND.PositiveDensity
open scoped BigOperators

noncomputable section

theorem fullTerminal_fan_le_envelope
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K J : ℕ)
    (hseed : ∀ i t, 0 < t → (Tao.syracuse^[t]) (U.state.root i) ≠ U.state.root i)
    (m k : ℕ) (hmk : m ≤ k) (X : ℝ) (hX : 0 < X)
    (hQ : ((3 ^ k : ℕ) : ℝ) ≤ X)
    (hsource : ∀ z : U.FullTerminalAt cap n shift K,
      X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) ∧
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) < 32 * X)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hL1 : ndTernaryUniformMean k (fun y => |ndSyracuseUnitReferenceDensity k y -
      ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)|) ≤ epsilon) :
    letI := (U.forwardIterate cap n).state.labelFintype
    (∑ z : U.FullTerminalAt cap n shift K,
      ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
        (U.forwardIterate cap n).state.outerWeight z *
        ∑ j : Fin J, (1 / 4 : ℝ) ^ j.val * ndSyracuseUnitReferenceDensity k
          (ndTerminalSourceFan j.val
            (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) : ZMod (3 ^ k))) ≤
      (∑ z : U.FullTerminalAt cap n shift K,
        ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
          (U.forwardIterate cap n).state.outerWeight z * terminalFanEnvelope m
            (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ZMod (3 ^ m))) +
        44 * U.parentSourcePotential * epsilon := by
  classical
  letI := (U.forwardIterate cap n).state.labelFintype
  let W := fun z : U.FullTerminalAt cap n shift K =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
      (U.forwardIterate cap n).state.outerWeight z
  let source := fun z : U.FullTerminalAt cap n shift K =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z
  have hW : ∀ z, 0 ≤ W z := fun z =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight_nonneg _
      (U.forwardIterate cap n).state.weight_nonneg z
  let delta := fun y : ZMod (3 ^ k) => |ndSyracuseUnitReferenceDensity k y -
    ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)|
  have hstep (j : ℕ) :
      (∑ z, W z * ndSyracuseUnitReferenceDensity k
        (ndTerminalSourceFan j (source z) : ZMod (3 ^ k))) ≤
      (∑ z, W z * ndSyracuseUnitReferenceDensity m
        (ndTerminalSourceFan j (source z) : ZMod (3 ^ m))) +
      33 * U.parentSourcePotential * epsilon := by
    let psi := fun y : ZMod (3 ^ k) => delta (ndTerminalResidueFan k j y)
    have hp : ∀ y, 0 ≤ psi y := fun _ => abs_nonneg _
    have hmean : ndTernaryUniformMean k psi ≤ epsilon := by
      rw [show psi = (fun y => delta (ndTerminalResidueFan k j y)) from rfl,
        terminalResidueFan_fullMean]
      exact hL1
    have hc := U.fullTerminal_weighted_residue_census_of_nonreturningSeed cap n shift K hseed
      k X hX hQ hsource psi hp
    have herr : (∑ z, W z * psi (source z : ZMod (3 ^ k))) ≤
        33 * U.parentSourcePotential * epsilon :=
      hc.trans (mul_le_mul_of_nonneg_left hmean
        (mul_nonneg (by norm_num) U.frozenSourcePotential_nonneg))
    have hpoint (x : ℕ) : ndSyracuseUnitReferenceDensity k
        (ndTerminalSourceFan j x : ZMod (3 ^ k)) ≤
      ndSyracuseUnitReferenceDensity m (ndTerminalSourceFan j x : ZMod (3 ^ m)) +
        psi (x : ZMod (3 ^ k)) := by
      dsimp [psi, delta]
      rw [terminalResidueFan_natCast, Tao.taoZModThreeProjection_natCast]
      exact sub_le_iff_le_add'.mp (le_abs_self _)
    calc
      _ ≤ ∑ z, W z * (ndSyracuseUnitReferenceDensity m
          (ndTerminalSourceFan j (source z) : ZMod (3 ^ m)) + psi (source z : ZMod (3 ^ k))) :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpoint _) (hW z)
      _ = (∑ z, W z * ndSyracuseUnitReferenceDensity m
          (ndTerminalSourceFan j (source z) : ZMod (3 ^ m))) +
          ∑ z, W z * psi (source z : ZMod (3 ^ k)) := by
        simp only [mul_add, Finset.sum_add_distrib]
      _ ≤ _ := add_le_add le_rfl herr
  have herror : 0 ≤ 33 * U.parentSourcePotential * epsilon :=
    mul_nonneg (mul_nonneg (by norm_num) U.frozenSourcePotential_nonneg) he
  calc
    _ = ∑ j : Fin J, (1 / 4 : ℝ) ^ j.val * ∑ z, W z *
        ndSyracuseUnitReferenceDensity k
          (ndTerminalSourceFan j.val (source z) : ZMod (3 ^ k)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro z _
      dsimp [W, source]
      ring
    _ ≤ ∑ j : Fin J, (1 / 4 : ℝ) ^ j.val *
        ((∑ z, W z * ndSyracuseUnitReferenceDensity m
          (ndTerminalSourceFan j.val (source z) : ZMod (3 ^ m))) +
          33 * U.parentSourcePotential * epsilon) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hstep j.val) (by positivity)
    _ = (∑ z, W z * ∑ j : Fin J, (1 / 4 : ℝ) ^ j.val *
          ndSyracuseUnitReferenceDensity m
            (ndTerminalSourceFan j.val (source z) : ZMod (3 ^ m))) +
        (∑ j : Fin J, (1 / 4 : ℝ) ^ j.val) * (33 * U.parentSourcePotential * epsilon) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_mul]
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ (∑ z, W z * terminalFanEnvelope m (source z : ZMod (3 ^ m))) +
        (4 / 3 : ℝ) * (33 * U.parentSourcePotential * epsilon) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro z _
        apply mul_le_mul_of_nonneg_left _ (hW z)
        simpa only [terminalResidueFan_natCast] using
          terminalFanEnvelope_dominates m J (source z : ZMod (3 ^ m))
      · exact mul_le_mul_of_nonneg_right (terminal_fan_coeff_sum_le J) herror
    _ = _ := by dsimp [W, source]; ring

theorem forwardGoodDepthShiftUnitMass_le_envelope_sources
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K m k : ℕ) (hmk : m ≤ k)
    (hseed : ∀ i t, 0 < t → (Tao.syracuse^[t]) (U.state.root i) ≠ U.state.root i)
    (X : ℝ) (hX : 0 < X) (hQ : ((3 ^ k : ℕ) : ℝ) ≤ X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i))
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hL1 : ndTernaryUniformMean k (fun y => |ndSyracuseUnitReferenceDensity k y -
      ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)|) ≤ epsilon) :
    U.forwardCoreTerminalGoodDepthShiftUnitMass cap width n K k X hX hi ≤
      (U.parentSourcePotential / X) *
        (∑ q ∈ U.fullTerminalSources cap n ((U.forwardIterate cap n).fullTerminalShift X hX hi) 1,
          terminalFanEnvelope m (q : ZMod (3 ^ m))) + 44 * U.parentSourcePotential * epsilon := by
  classical
  let V := U.forwardIterate cap n
  letI := V.state.labelFintype
  let shift := V.fullTerminalShift X hX hi
  have hwindow := fun z : U.FullTerminalAt cap n shift 1 =>
    V.fullTerminal_source_window X hX hi z
  have hfan := fullTerminal_fan_le_envelope U cap n shift 1 (K / 2 + 1) hseed
    m k hmk X hX hQ hwindow epsilon he hL1
  have hcompression := U.forwardGoodDepthShiftUnitMass_le_full_cap_one_fan cap width n K k X hX hi
  have hmono :
      (∑ z : U.FullTerminalAt cap n shift 1,
        U.fullGoodCoreTerminalWeight cap width n shift 1 z *
          ∑ j : Fin (K / 2 + 1), (1 / 4 : ℝ) ^ j.val * ndSyracuseUnitReferenceDensity k
            (ndTerminalSourceFan j.val
              (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) : ZMod (3 ^ k))) ≤
      (∑ z : U.FullTerminalAt cap n shift 1,
        ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight V.state.outerWeight z *
          ∑ j : Fin (K / 2 + 1), (1 / 4 : ℝ) ^ j.val * ndSyracuseUnitReferenceDensity k
            (ndTerminalSourceFan j.val
              (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) : ZMod (3 ^ k))) := by
    apply Finset.sum_le_sum
    intro z _
    apply mul_le_mul_of_nonneg_right
      (U.fullGoodCoreTerminalWeight_le_original cap width n shift 1 z)
    exact Finset.sum_nonneg fun j _ => mul_nonneg (by positivity)
      (ndSyracuseUnitReferenceDensity_nonneg _ _)
  have hcharge := U.fullTerminal_weighted_source_charge_of_nonreturningSeed cap n shift 1 hseed
    X hX (fun z => (hwindow z).1)
    (fun q => terminalFanEnvelope m (q : ZMod (3 ^ m))) (fun q => terminalFanEnvelope_nonneg _ _)
  exact (hcompression.trans (hmono.trans hfan)).trans (add_le_add hcharge le_rfl)

#print axioms fullTerminal_fan_le_envelope
#print axioms forwardGoodDepthShiftUnitMass_le_envelope_sources

end
end CollatzCanonical.PeriodicCensusFloor
