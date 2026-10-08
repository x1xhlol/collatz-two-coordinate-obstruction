/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.GeneralTargetTerminalCensus
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricExplicitCutoffCount

namespace Erdos1135Predecessor.ND.PositiveDensity
open scoped BigOperators
noncomputable section

def ordinaryPredecessorSet (a : ℕ) : Set ℕ :=
  {n | 0 < n ∧ Erdos1135Predecessor.Reaches n a}

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem generalTarget_publicCount_from_mass
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (a : ℕ)
    (hreach : ∀ i, Erdos1135Predecessor.Reaches (U.state.root i) a)
    (hseed : ∀ i k, 0 < k → (Tao.syracuse^[k]) (U.state.root i) ≠ U.state.root i)
    (cap : ℕ → ℕ) {e L : ℕ} (he : U.rootSpan e)
    (hcap : ∀ n, cap n ≤ L * (n + 1))
    {eta : ℝ} (hP : 0 < U.parentSourcePotential)
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
        (Terras.natCount (ordinaryPredecessorSet a) Y : ℝ) := by
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
  let V := U.forwardIterate cap n
  let shift := V.fullTerminalShift X hX hif
  letI := V.state.labelFintype
  let sources := U.fullGoodCoreTerminalSources cap ndRootCoreWidth n shift 1
  have hm : eta ≤ U.fullGoodCoreTerminalMass cap ndRootCoreWidth n shift 1 :=
    hmass n hn X hX hif
  have hwindow : ∀ z : U.FullTerminalAt cap n shift 1,
      X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) ∧
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) < 32 * X :=
    fun z => V.fullTerminal_source_window X hX hif z
  have hrange : sources ⊆ Finset.range Y := by
    intro source hs
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hs
    have h := (hwindow z).2
    have hlt : (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) < Y := by
      dsimp [X] at h
      linarith
    exact Finset.mem_range.mpr (by exact_mod_cast hlt)
  have htargetS : (↑sources : Set ℕ) ⊆ ordinaryPredecessorSet a := by
    intro source hs
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨(U.fullTerminalPath cap n shift 1 z).sourceOdd.pos,
      U.fullTerminal_reaches_target_of_seed_reaches cap n shift 1 a hreach z⟩
  have hcard : sources.card ≤ Terras.natCount (ordinaryPredecessorSet a) Y :=
    finset_card_le_natCount_of_subset_range hrange htargetS
  have hcharge := U.fullGoodCoreTerminal_mass_mul_lower_le_frozenPotential_mul_card_of_nonreturningSeed
    cap ndRootCoreWidth n shift 1 hseed X hX (fun z => (hwindow z).1)
  have hcount : X * U.fullGoodCoreTerminalMass cap ndRootCoreWidth n shift 1 ≤
      U.parentSourcePotential * (Terras.natCount (ordinaryPredecessorSet a) Y : ℝ) :=
    hcharge.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hP.le)
  have htotal := (mul_le_mul_of_nonneg_left hm hX.le).trans hcount
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32 * U.parentSourcePotential)).2
  dsimp [X] at htotal
  nlinarith only [htotal]

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState
end
end Erdos1135Predecessor.ND.PositiveDensity
