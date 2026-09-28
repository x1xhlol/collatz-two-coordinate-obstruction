/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitFrozenCoreSeed
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricExplicitCutoffCount

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem explicit_iterate_floor (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) : (U.iterate cap n).floor = explicitSeedFloor U.floor n := by
  rw [← U.forwardIterate_eq_iterate cap n, U.explicit_forward_floor]

theorem publicCount_ten46_from_potential_and_height
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (hb : 512 ^ 5 ≤ U.floor)
    (hseed : ∀ i, Tao.syracuse (U.state.root i) = 1)
    (cap : ℕ → ℕ) {e L : ℕ} (he : U.rootSpan e)
    (hcap : ∀ n, cap n ≤ L * (n + 1))
    {Cclock eta Pbar : ℝ} (hCclock : 250 ≤ Cclock)
    (htarget : ∀ i, U.state.root i ∈ oddSyracuseLogTimeOneSet Cclock)
    (hP : 0 < U.parentSourcePotential) (heta : 0 ≤ eta)
    (hPbar : U.parentSourcePotential ≤ Pbar)
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
      eta / (32 * Pbar) * Y ≤
        (Terras.natCount (rawCollatzLogTimeOneSet (523 / 50 : ℝ)) Y : ℝ) := by
  intro Y hY
  have hcount := U.publicCount_from_explicit_start_and_clock hseed cap he hcap
    hCclock htarget hP (fun n shift z hc hg =>
      U.fullGoodCoreTerminal_source_mem_rawCollatzLogTimeOneSet_ten46 hb hseed cap n shift 1 z hc hg)
    N H hN hH hmass Y hY
  apply le_trans _ hcount
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg Y)
  exact div_le_div_of_nonneg_left heta (by positivity : (0 : ℝ) < 32 * U.parentSourcePotential)
    (mul_le_mul_of_nonneg_left hPbar (by norm_num))

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
