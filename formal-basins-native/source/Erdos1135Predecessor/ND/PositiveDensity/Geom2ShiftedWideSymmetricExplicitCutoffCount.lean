/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricOrdinaryTen46Clock
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalDepthShiftCensus
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalDepthShiftOrdinaryClock
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalWeightedCensus

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem publicCount_from_explicit_start_and_clock
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (hseed : ∀ i, Tao.syracuse (U.state.root i) = 1)
    (cap : ℕ → ℕ) {e L : ℕ} (he : U.rootSpan e)
    (hcap : ∀ n, cap n ≤ L * (n + 1))
    {Cclock eta : ℝ} (hCclock : 250 ≤ Cclock)
    (htarget : ∀ i, U.state.root i ∈ oddSyracuseLogTimeOneSet Cclock)
    (hP : 0 < U.parentSourcePotential)
    {Ctime : ℝ}
    (hclock : ∀ (n : ℕ)
      (shift : (U.forwardIterate cap n).state.Label → ℕ)
      (z : U.FullTerminalAt cap n shift 1),
      U.forwardCore cap ndRootCoreWidth n (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) →
      ndTerminalDepthShiftGood (U.forwardIterate cap n).floor
        (shift (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z) →
      ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z ∈ rawCollatzLogTimeOneSet Ctime)
    (N H : ℕ) (hN : 1000000000 * (e + L + 3) ≤ N)
    (hH : ∀ i : (U.iterate cap N).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.iterate cap N).floor
        ((U.iterate cap N).state.root i) ≤ H)
    (hmass : ∀ n, N ≤ n →
      let V := U.forwardIterate cap n;
      ∀ (X : ℝ) (hX : 0 < X)
        (hi : ∀ i : V.state.Label,
          ndGeom2ShiftedWideSymmetricPhysicalIntervalMin V.floor (V.state.root i) < X ∧
          X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax V.floor (V.state.root i)),
        eta ≤ U.fullGoodCoreTerminalMass cap ndRootCoreWidth n (V.fullTerminalShift X hX hi) 1) :
    ∀ Y : ℕ, 32 * (H + 1) ≤ Y →
      eta / (32 * U.parentSourcePotential) * Y ≤
        (Terras.natCount (rawCollatzLogTimeOneSet Ctime) Y : ℝ) := by
  classical
  intro Y hY
  have hYlarge : 32 * ((H : ℝ) + 1) ≤ Y := by exact_mod_cast hY
  let X := (Y : ℝ) / 32
  have hX : 0 < X := by dsimp [X]; have := Nat.cast_nonneg (α := ℝ) H; linarith
  have hHX : (H : ℝ) < X := by dsimp [X]; linarith
  obtain ⟨n, hn, hi⟩ := U.exists_unstopped_generation_all_intervals_contain he cap hcap
    N hN X (fun i => (hH i).trans_lt hHX)
  have hif : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) := by
    rw [U.forwardIterate_eq_iterate cap n]
    exact hi
  let shift := (U.forwardIterate cap n).fullTerminalShift X hX hif
  letI := (U.forwardIterate cap n).state.labelFintype
  let sources := U.fullGoodCoreTerminalSources cap ndRootCoreWidth n shift 1
  have hm : eta ≤ U.fullGoodCoreTerminalMass cap ndRootCoreWidth n shift 1 :=
    hmass n hn X hX hif
  have hc := U.fullTerminal_capOne_public_count cap n hCclock htarget X hX hif
  have hsub := U.fullGoodCoreTerminalSources_subset_fullTerminalSources cap ndRootCoreWidth n shift 1
  have hrange : sources ⊆ Finset.range Y := by
    intro source hs
    have h := (hc.1 source (hsub hs)).2.2
    have hlt : (source : ℝ) < Y := by dsimp [X] at h; linarith
    exact Finset.mem_range.mpr (by exact_mod_cast hlt)
  have htargetS : (↑sources : Set ℕ) ⊆ rawCollatzLogTimeOneSet Ctime := by
    intro source hs
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hs
    exact hclock n shift z (Finset.mem_filter.mp hz).2.1 (Finset.mem_filter.mp hz).2.2
  have hcard : sources.card ≤ Terras.natCount (rawCollatzLogTimeOneSet Ctime) Y :=
    finset_card_le_natCount_of_subset_range hrange htargetS
  have hseedNeOne : ∀ i, U.state.root i ≠ 1 := by
    intro i
    have hf := U.floor_twoHundred
    have hl := (Nat.pow_le_pow_right (by norm_num : 1 ≤ 16)
      (show 1 ≤ U.state.base i by have := U.floor_le_base i; omega)).trans (U.state.rootLower i)
    norm_num at hl
    omega
  have hseedHitsOne : ∀ i, ∃ t : ℕ, (Tao.syracuse^[t]) (U.state.root i) = 1 := by
    intro i
    exact ⟨1, by simpa using hseed i⟩
  have hcharge := U.fullGoodCoreTerminal_mass_mul_lower_le_frozenPotential_mul_card
    cap ndRootCoreWidth n shift 1 hseedNeOne hseedHitsOne X hX
    (fun z => (hc.1 _ (Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩)).2.1)
  have hcount : X * U.fullGoodCoreTerminalMass cap ndRootCoreWidth n shift 1 ≤
      U.parentSourcePotential * (Terras.natCount (rawCollatzLogTimeOneSet Ctime) Y : ℝ) :=
    hcharge.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hP.le)
  have htotal := (mul_le_mul_of_nonneg_left hm hX.le).trans hcount
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32 * U.parentSourcePotential)).2
  dsimp [X] at htotal
  nlinarith only [htotal]

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
