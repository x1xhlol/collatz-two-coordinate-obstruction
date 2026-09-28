/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitAccumulatedFloorHeight
import Erdos1135Predecessor.ND.PositiveDensity.ExplicitFrozenCoreSeed
import Erdos1135Predecessor.ND.PositiveDensity.ExplicitReferenceHeightCensus
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricExplicitConductor
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricExplicitCutoffCount

namespace Erdos1135Predecessor.ND.PositiveDensity

noncomputable section

theorem explicit_count_ten46_from_supplied_margin_and_reference_height
    {b : ℕ} (hb : 2 ^ 80 ≤ b) (M Nmark : ℕ) (a : ℝ) (ha : 0 < a)
    (hsupplied : ∃ (r : ℕ) (hr : Odd r) (hl : 16 ^ b ≤ r),
      r < M ∧ r ∈ oddSyracuseLogTimeOneSet 250 ∧ Tao.syracuse r = 1 ∧
      IsUnit (r : ZMod (3 ^ 1)) ∧
      ∀ n ≥ Nmark,
        let U := ndRootCoreSingletonState b r
          ((by norm_num : (200 : ℕ) ≤ 2 ^ 80).trans hb) hr hl;
        let V := U.forwardIterate (fun j => 16 + j / 100) n;
        ∀ (X : ℝ) (hX : 0 < X)
          (hi : ∀ i : V.state.Label,
            ndGeom2ShiftedWideSymmetricPhysicalIntervalMin V.floor (V.state.root i) < X ∧
            X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax V.floor (V.state.root i)),
          a ≤ U.forwardCoreTerminalGoodDepthShiftUnitMass
            (fun j => 16 + j / 100) ndRootCoreWidth n (16 + n / 100) (V.floor / 4) X hX hi)
    {m : ℕ} (hm : 1 ≤ m)
    (Cbudget : ℝ) (hCbudget : 0 ≤ Cbudget)
    (hquadratic : ndExplicitQuadraticMixingAt Cbudget m)
    (hbudget : 88 * (M : ℝ) * Cbudget ≤ a * (m : ℝ) ^ 2)
    (p : ℕ) (hp : 0 < p)
    (href : ∀ y, ndSyracuseUnitReferenceDensity m y ≤ (2/3:ℝ)*(p:ℝ))
    (J : ℕ) (hJ : 20 * 10 ^ 9 ≤ J)
    (hstart : Nmark ≤ J)
    (hroom : ∀ U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState,
      U.floor = b → ∀ n, J ≤ n →
        m ≤ (U.forwardIterate (fun j => 16 + j / 100) n).floor / 4)
    (H : ℕ)
    (hheight : ∀ U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState,
      U.floor = b → (∀ i, U.state.root i ≤ M) →
      ∀ i : (U.iterate (fun j => 16 + j / 100) J).state.Label,
        ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
          (U.iterate (fun j => 16 + j / 100) J).floor
          ((U.iterate (fun j => 16 + j / 100) J).state.root i) ≤ H) :
    ∀ Y : ℕ,
      32 * (H + 1) ≤ Y →
      (9 * a / (512 * (M : ℝ) * (p : ℝ))) * Y ≤
        (Terras.natCount (rawCollatzLogTimeOneSet (523 / 50 : ℝ)) Y : ℝ) := by
  obtain ⟨r, hr, hl, hbound, ht, hhit, _hunit, hgood⟩ := hsupplied
  have hb200 : 200 ≤ b := (by norm_num : (200 : ℕ) ≤ 2 ^ 80).trans hb
  let U := ndRootCoreSingletonState b r hb200 hr hl
  let cap := fun j : ℕ => 16 + j / 100
  have he : U.rootSpan 0 := by intro i j; change r ≤ 2 ^ 0 * r; simp
  have hcap : ∀ j, cap j ≤ 17 * (j + 1) := by
    intro j
    have hj := Nat.div_le_self j 100
    dsimp [cap]
    omega
  have htarget : ∀ i, U.state.root i ∈ oddSyracuseLogTimeOneSet 250 := fun _ => ht
  have hseed : ∀ i, Tao.syracuse (U.state.root i) = 1 := fun _ => hhit
  have hP : U.parentSourcePotential = (r : ℝ) := by
    change ndGeom2PredictableRootSideParentSourcePotential (Finset.univ : Finset Unit)
      (fun _ => (1 : ℝ)) (fun _ => r) = _
    simp [ndGeom2PredictableRootSideParentSourcePotential]
  have hPpos : 0 < U.parentSourcePotential := by rw [hP]; exact_mod_cast hr.pos
  have hPbar : U.parentSourcePotential ≤ (M : ℝ) := by
    rw [hP]
    exact_mod_cast hbound.le
  have hsq : 88 * U.parentSourcePotential * Cbudget ≤ a * (m : ℝ) ^ 2 := by
    have hp := mul_le_mul_of_nonneg_right hPbar hCbudget
    linarith only [hbudget, hp]
  have hcount := U.publicCount_ten46_from_potential_and_height
    ((by norm_num : (512 : ℕ) ^ 5 ≤ 2 ^ 80).trans hb) hseed cap he hcap
    (by norm_num : (250 : ℝ) ≤ 250) htarget hPpos
    (show 0 ≤ 9 * a / (16 * (p : ℝ)) by positivity)
    hPbar J H (by norm_num at hJ ⊢; exact hJ) (hheight U rfl (fun _ => hbound.le))
    (fun n hn X hX hi =>
      U.fullGoodCoreTerminalMass_ge_of_square_budget_and_height cap ndRootCoreWidth n (cap n) m
        ((U.forwardIterate cap n).floor / 4) hm (hroom U rfl n hn)
        (Nat.div_le_self _ _) (by norm_num : (250 : ℝ) ≤ 250) htarget hCbudget
        hquadratic ha
        hsq p hp href X hX hi (hgood n (hstart.trans hn) X hX hi))
  intro Y hY
  have h := hcount Y hY
  convert h using 1 <;> ring

end

end Erdos1135Predecessor.ND.PositiveDensity
