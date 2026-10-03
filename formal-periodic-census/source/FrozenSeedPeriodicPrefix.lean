import TerminalFanCensus
import BoundedPredecessorDensity
import NativePredecessorMapBridge

set_option autoImplicit false

namespace CollatzCanonical.PeriodicCensusFloor
open Erdos1135Predecessor
open Erdos1135Predecessor.ND.PositiveDensity
open CollatzCanonical.BoundedInverseSeed
open CollatzCylinderPacking.Arithmetic CollatzBasinMapBridges
open scoped BigOperators

noncomputable section

theorem terminalEnvelope_source_sum_le_basin_prefix
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K N X m : ℕ)
    (hreach : ∀ i, Erdos1135Predecessor.Reaches (U.state.root i) (2 * N))
    (hwindow : ∀ z : U.FullTerminalAt cap n shift K,
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) < 32 * (X : ℝ)) :
    (∑ q ∈ U.fullTerminalSources cap n shift K, terminalFanEnvelope m (q : ZMod (3 ^ m))) ≤
      ∑ q ∈ Finset.range (32 * X), basinIndicator N q *
        (if Odd q then terminalFanEnvelope m (q : ZMod (3 ^ m)) else 0) := by
  classical
  let S := U.fullTerminalSources cap n shift K
  have hmem (q : ℕ) (hq : q ∈ S) : Odd q ∧ basinIndicator N q = 1 ∧ q < 32 * X := by
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨(U.fullTerminalPath cap n shift K z).sourceOdd,
      native_predecessor_double_basin
        (U.fullTerminal_reaches_target_of_seed_reaches cap n shift K (2 * N) hreach z),
      by exact_mod_cast hwindow z⟩
  calc
    _ = ∑ q ∈ S, basinIndicator N q *
        (if Odd q then terminalFanEnvelope m (q : ZMod (3 ^ m)) else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [if_pos (hmem q hq).1, (hmem q hq).2.1, one_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        exact Finset.mem_range.mpr (hmem q hq).2.2
      · intro q _ _
        apply mul_nonneg (basinIndicator_bounds N q).1
        split_ifs
        · exact terminalFanEnvelope_nonneg _ _
        · exact le_rfl

theorem exists_frozen_seed_eventual_periodic_prefix
    {N : ℕ} (hN : 0 < N) (hunit : N % 3 ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ r ≤ predecessorSeedMultiplier * (2 * N) ∧
      ∀ m : ℕ, 1 ≤ m → ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
        (2 / 3 : ℝ) ≤ ((r : ℝ) / (X : ℝ)) *
          (∑ q ∈ Finset.range (32 * X), basinIndicator N q *
            (if Odd q then terminalFanEnvelope m (q : ZMod (3 ^ m)) else 0)) +
          44 * (r : ℝ) * (explicitSyracuseMixingCoefficient : ℝ) / (m : ℝ) ^ 2 := by
  let b := predecessorSeedBase
  let C := explicitSyracuseMixingCoefficient
  let G := predecessorSeedGeneration
  let Gmark := explicitLogarithmicGoodMarkedStart b C G
  have hthree : ¬ 3 ∣ 2 * N := by omega
  obtain ⟨r, hr, hl, ht, hbound, hnonreturn, _hunit, hgood⟩ :=
    exists_bounded_generalTarget_uniform_twoThirds_seed (a := 2 * N) (by omega) hthree
      (b := b) le_rfl C explicitSyracuseMixing_six (N := G) le_rfl
  have hb200 : 200 ≤ b := by dsimp [b, predecessorSeedBase]; norm_num
  let U := ndRootCoreSingletonState b r hb200 hr hl
  let cap := fun j : ℕ => 16 + j / 100
  have he : U.rootSpan 0 := by intro i j; change r ≤ 2 ^ 0 * r; simp
  have hcap : ∀ j, cap j ≤ 17 * (j + 1) := by
    intro j
    have hj := Nat.div_le_self j 100
    dsimp [cap]
    omega
  have hreach : ∀ i, Erdos1135Predecessor.Reaches (U.state.root i) (2 * N) := fun _ => ht
  have hseed : ∀ i t, 0 < t → (Tao.syracuse^[t]) (U.state.root i) ≠ U.state.root i :=
    fun _ => hnonreturn
  have hP : U.parentSourcePotential = (r : ℝ) := by
    change ndGeom2PredictableRootSideParentSourcePotential (Finset.univ : Finset Unit)
      (fun _ => (1 : ℝ)) (fun _ => r) = _
    simp [ndGeom2PredictableRootSideParentSourcePotential]
  refine ⟨r, hr.pos, hbound, ?_⟩
  intro m hm
  let J := Gmark + 2 * m + 20 * 10 ^ 9
  let H := ndExplicitRootIntervalHeight b 17 r J
  refine ⟨H + 1, ?_⟩
  intro X hlarge
  have hHX : (H : ℝ) < X := by exact_mod_cast (show H < X by omega)
  have hX : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hH : ∀ i : (U.iterate cap J).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.iterate cap J).floor
        ((U.iterate cap J).state.root i) ≤ H :=
    fun i => U.iterate_physicalIntervalMax_le_explicit cap 17 r hcap (fun _ => le_rfl) J i
  obtain ⟨n, hn, hi⟩ := U.exists_unstopped_generation_all_intervals_contain he cap hcap
    J (by dsimp [J]; omega) (X : ℝ) (fun i => (hH i).trans_lt hHX)
  have hif : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) := by
    rw [U.forwardIterate_eq_iterate cap n]
    exact hi
  let V := U.forwardIterate cap n
  let k := V.floor / 4
  have hroom := U.explicitConductor_quarter_room cap m n (by dsimp [J] at hn; omega)
  have hmark := hgood n (by dsimp [J] at hn; omega) (X : ℝ) hX hif
  have hOrig := (show (0 : ℝ) < 2 / 3 by norm_num).trans_le
    (hmark.trans (U.forwardGoodDepthShiftUnitMass_le_original cap ndRootCoreWidth n
      (cap n) k (X : ℝ) hX hif))
  have hQ := U.terminal_conductor_room_of_pos_mark cap ndRootCoreWidth n (cap n) k hroom.2
    (X : ℝ) hX hif hOrig
  have hmix := explicitMixing_quadratic (Nat.cast_nonneg C) explicitSyracuseMixing_six hm
  have hcen := forwardGoodDepthShiftUnitMass_le_envelope_sources U cap ndRootCoreWidth n
    (cap n) m k hroom.1 hseed (X : ℝ) hX hQ.le hif
    ((C : ℝ) / (m : ℝ) ^ 2) (div_nonneg (Nat.cast_nonneg C) (by positivity)) (hmix k hroom.1)
  let shift := V.fullTerminalShift (X : ℝ) hX hif
  have hprefix := terminalEnvelope_source_sum_le_basin_prefix U cap n shift 1 N X m hreach
    (fun z => (V.fullTerminal_source_window (X : ℝ) hX hif z).2)
  have hboundPrefix := mul_le_mul_of_nonneg_left hprefix
    (div_nonneg U.frozenSourcePotential_nonneg hX.le)
  have h := (hmark.trans hcen).trans (add_le_add hboundPrefix le_rfl)
  rw [hP] at h
  simpa only [C, div_mul_eq_mul_div, mul_div_assoc] using h

#print axioms terminalEnvelope_source_sum_le_basin_prefix
#print axioms exists_frozen_seed_eventual_periodic_prefix

end
end CollatzCanonical.PeriodicCensusFloor
