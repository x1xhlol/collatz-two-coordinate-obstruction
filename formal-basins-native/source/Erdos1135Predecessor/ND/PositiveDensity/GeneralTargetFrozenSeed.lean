/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.GeneralTargetResidueCoverage
import Erdos1135Predecessor.ND.PositiveDensity.ExplicitUnitSupportedFrozenSeed

namespace Erdos1135Predecessor.ND.PositiveDensity
noncomputable section

theorem exists_generalTarget_full_core_mark
    {a b k : ℕ} (ha : 0 < a) (hthree : ¬ 3 ∣ a)
    (hb : 2 ^ 80 ≤ b) (hk : 1 ≤ k)
    (cap : ℕ → ℕ) (hcap : ∀ n, 16 + n / 100 ≤ cap n) (n : ℕ) :
    ∃ (r : ℕ) (hr : Odd r) (hl : 16 ^ b ≤ r),
      Erdos1135Predecessor.Reaches r a ∧
      (∀ t : ℕ, 0 < t → (Tao.syracuse^[t]) r ≠ r) ∧
      IsUnit (r : ZMod (3 ^ 1)) ∧
      (255 / 256 : ℝ) ≤
        (ndRootCoreSingletonState b r ((by norm_num : (200 : ℕ) ≤ 2 ^ 80).trans hb) hr hl).forwardCoreMarkedMass
          cap ndRootCoreWidth n k (fun _ => 1) := by
  have hb200 : 200 ≤ b := (by norm_num : (200 : ℕ) ≤ 2 ^ 80).trans hb
  obtain ⟨y, _, hy⟩ := exists_unit_rootCoreBackwardMark_ge_full_product
    (b := b) hk cap ndRootCoreWidth n
  let q := ndRootCoreBackwardConductor b k n
  let residue : Fin (3 ^ q) := ⟨y.val, ZMod.val_lt y⟩
  obtain ⟨r, hl, hr, htarget, hres, hnonreturn⟩ :=
    exists_large_nonreturning_predecessor_in_residue ha hthree q (16 ^ b) residue
  have heq : (r : ZMod (3 ^ q)) = y := by
    calc
      _ = ((r % 3 ^ q : ℕ) : ZMod (3 ^ q)) := by simp
      _ = ((y.val : ℕ) : ZMod (3 ^ q)) := congrArg (fun a : ℕ => (a : ZMod (3 ^ q))) hres
      _ = y := ZMod.natCast_zmod_val y
  have hg : ndRootCoreProbabilityProduct b cap ndRootCoreWidth n ≤
      ndRootCoreBackwardMark b cap ndRootCoreWidth k n (r : ZMod (3 ^ q)) := by rwa [heq]
  let U := ndRootCoreSingletonState b r hb200 hr hl.le
  have hp : (255 / 256 : ℝ) ≤ ndRootCoreProbabilityProduct b cap ndRootCoreWidth n :=
    U.coreProbabilityProduct_ge_255_div_256 hb cap hcap n
  have hu : IsUnit (r : ZMod (3 ^ 1)) := by
    by_contra hn
    have hz := rootCoreBackwardMark_natCast_eq_zero_of_not_unit b cap ndRootCoreWidth hk n r hn
    rw [hz] at hg
    nlinarith
  refine ⟨r, hr, hl.le, htarget, hnonreturn, hu, ?_⟩
  rw [rootCoreSingletonState_markedMass_eq_backwardMark _ _ _ _ _ _ _ _ _ hk]
  nlinarith

theorem exists_generalTarget_core_sequence_seed
    {a b : ℕ} (ha : 0 < a) (hthree : ¬ 3 ∣ a) (hb : 2 ^ 80 ≤ b) (N : ℕ) :
    ∃ (r : ℕ) (hr : Odd r) (hl : 16 ^ b ≤ r),
      Erdos1135Predecessor.Reaches r a ∧
      (∀ t : ℕ, 0 < t → (Tao.syracuse^[t]) r ≠ r) ∧
      IsUnit (r : ZMod (3 ^ 1)) ∧
      (255 / 256 : ℝ) ≤
        (ndRootCoreSingletonState b r ((by norm_num : (200 : ℕ) ≤ 2 ^ 80).trans hb) hr hl).coreMarkedSequence
          (fun n => 16 + n / 100) ndRootCoreWidth N := by
  let k := explicitSeedFloor b N / 4
  have hfloor := explicitSeedFloor_bounds b N
  have hk : 1 ≤ k := by dsimp [k]; omega
  obtain ⟨r, hr, hl, ht, hnonreturn, hunit, hmark⟩ :=
    exists_generalTarget_full_core_mark ha hthree hb hk
      (fun n => 16 + n / 100) (fun _ => le_rfl) N
  refine ⟨r, hr, hl, ht, hnonreturn, hunit, ?_⟩
  unfold NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.coreMarkedSequence
  rw [NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.explicit_forward_floor]
  exact hmark

theorem exists_generalTarget_uniform_twoThirds_seed
    {a b : ℕ} (ha : 0 < a) (hthree : ¬ 3 ∣ a) (hb : 2 ^ 80 ≤ b) (C : ℕ)
    (hmix : Tao.syracFineScaleMixingAt 6 (C : ℝ))
    {N : ℕ} (hN : explicitLogarithmicSeedGeneration b C ≤ N) :
    ∃ (r : ℕ) (hr : Odd r) (hl : 16 ^ b ≤ r),
      Erdos1135Predecessor.Reaches r a ∧
      (∀ t : ℕ, 0 < t → (Tao.syracuse^[t]) r ≠ r) ∧
      IsUnit (r : ZMod (3 ^ 1)) ∧
      ∀ n ≥ explicitLogarithmicGoodMarkedStart b C N,
        let U := ndRootCoreSingletonState b r
          ((by norm_num : (200 : ℕ) ≤ 2 ^ 80).trans hb) hr hl;
        let V := U.forwardIterate (fun j => 16 + j / 100) n;
        ∀ (X : ℝ) (hX : 0 < X)
          (hi : ∀ i : V.state.Label,
            ndGeom2ShiftedWideSymmetricPhysicalIntervalMin V.floor (V.state.root i) < X ∧
            X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax V.floor (V.state.root i)),
          (2 / 3 : ℝ) ≤ U.forwardCoreTerminalGoodDepthShiftUnitMass
            (fun j => 16 + j / 100) ndRootCoreWidth n (16 + n / 100) (V.floor / 4) X hX hi := by
  obtain ⟨r, hr, hl, ht, hnonreturn, hunit, hmark⟩ :=
    exists_generalTarget_core_sequence_seed ha hthree hb N
  refine ⟨r, hr, hl, ht, hnonreturn, hunit, ?_⟩
  intro n hn U V X hX hi
  let cap := fun j : ℕ => 16 + j / 100
  have hcap : ∀ j, cap j ≤ 17 * (j + 1) := by
    intro j
    have hj := Nat.div_le_self j 100
    dsimp [cap]
    omega
  have he : U.rootSpan 0 := by intro i j; change r ≤ 2 ^ 0 * r; simp
  have hD : U.denominator = 1 := rootCoreSingletonState_denominator_eq_one _ _ _ _ _
  have hseed : (255 / 256 : ℝ) * U.denominator ≤
      U.coreMarkedSequence cap ndRootCoreWidth N := by
    simpa only [hD, mul_one] using hmark
  have hNn : N ≤ n := by unfold explicitLogarithmicGoodMarkedStart at hn; omega
  have hnBudget : explicitLogarithmicTerminalStart U.floor C 0 ≤ n := by
    change explicitLogarithmicTerminalStart b C 0 ≤ n
    unfold explicitLogarithmicGoodMarkedStart at hn
    omega
  have h := NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.explicit_good_marked_margin_logarithmic_full
    C hmix U ((by norm_num : (32 : ℕ) ^ 5 ≤ 2 ^ 80).trans hb)
    cap 0 he hcap (fun _ => le_rfl) hN hNn hnBudget hseed X hX hi
  rw [hD, mul_one] at h
  exact (by norm_num : (2 / 3 : ℝ) ≤ 175 / 256).trans h

end
end Erdos1135Predecessor.ND.PositiveDensity
