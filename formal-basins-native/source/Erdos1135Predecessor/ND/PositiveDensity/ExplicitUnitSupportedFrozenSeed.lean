/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitUnitSupportedCoreSeed

namespace Erdos1135Predecessor.ND.PositiveDensity

noncomputable section

theorem exists_full_core_singleton_mark_of_bounded_residue_lift
    {b k : ℕ} (hb : 2 ^ 80 ≤ b) (hk : 1 ≤ k)
    (cap : ℕ → ℕ) (hcap : ∀ n, 16 + n / 100 ≤ cap n)
    (n : ℕ) {C : ℝ} (Mbound : ℕ)
    (hlift : ∀ r : Fin (3 ^ ndRootCoreBackwardConductor b k n),
      ∃ M : ℕ, 16 ^ b < M ∧ M < Mbound ∧
        M ∈ oddSyracuseLogTimeOneSet C ∧ Tao.syracuse M = 1 ∧
        M % 3 ^ ndRootCoreBackwardConductor b k n = r) :
    ∃ (M : ℕ) (hM : Odd M) (hl : 16 ^ b ≤ M),
      M < Mbound ∧
      M ∈ oddSyracuseLogTimeOneSet C ∧ Tao.syracuse M = 1 ∧
      IsUnit (M : ZMod (3 ^ 1)) ∧
      (255 / 256 : ℝ) ≤
        (ndRootCoreSingletonState b M ((by norm_num : (200 : ℕ) ≤ 2 ^ 80).trans hb) hM hl).forwardCoreMarkedMass
          cap ndRootCoreWidth n k (fun _ => 1) := by
  have hb200 : 200 ≤ b := (by norm_num : (200 : ℕ) ≤ 2 ^ 80).trans hb
  obtain ⟨y, _, hy⟩ := exists_unit_rootCoreBackwardMark_ge_full_product
    hk cap ndRootCoreWidth n
  let q := ndRootCoreBackwardConductor b k n
  let r : Fin (3 ^ q) := ⟨y.val, ZMod.val_lt y⟩
  obtain ⟨M, hM, hMb, ht, hhit, hres⟩ :=
    hlift r
  have heq : (M : ZMod (3 ^ q)) = y := by
    calc
      _ = ((M % 3 ^ q : ℕ) : ZMod (3 ^ q)) := by simp
      _ = ((y.val : ℕ) : ZMod (3 ^ q)) := congrArg (fun a : ℕ => (a : ZMod (3 ^ q))) hres
      _ = y := ZMod.natCast_zmod_val y
  have hg : ndRootCoreProbabilityProduct b cap ndRootCoreWidth n ≤
      ndRootCoreBackwardMark b cap ndRootCoreWidth k n (M : ZMod (3 ^ q)) := by rwa [heq]
  have hodd : Odd M := ht.2.1
  let U := ndRootCoreSingletonState b M hb200 hodd hM.le
  have hp : (255 / 256 : ℝ) ≤ ndRootCoreProbabilityProduct b cap ndRootCoreWidth n :=
    U.coreProbabilityProduct_ge_255_div_256 hb cap hcap n
  have hu : IsUnit (M : ZMod (3 ^ 1)) := by
    by_contra hn
    have hz := rootCoreBackwardMark_natCast_eq_zero_of_not_unit b cap ndRootCoreWidth hk n M hn
    rw [hz] at hg
    nlinarith
  refine ⟨M, hodd, hM.le, hMb, ht, hhit, hu, ?_⟩
  rw [rootCoreSingletonState_markedMass_eq_backwardMark _ _ _ _ _ _ _ _ _ hk]
  nlinarith

theorem exists_onePeriod_bounded_successful_full_core_mark
    {b : ℕ} (hb : 2 ^ 80 ≤ b) (N : ℕ) :
    ∃ (r : ℕ) (hr : Odd r) (hl : 16 ^ b ≤ r),
      r < explicitOnePeriodSeedRootBound b N ∧
      r ∈ oddSyracuseLogTimeOneSet 250 ∧ Tao.syracuse r = 1 ∧
      IsUnit (r : ZMod (3 ^ 1)) ∧
      (255 / 256 : ℝ) ≤
        (ndRootCoreSingletonState b r ((by norm_num : (200 : ℕ) ≤ 2 ^ 80).trans hb) hr hl).coreMarkedSequence
          (fun n => 16 + n / 100) ndRootCoreWidth N := by
  let k := explicitSeedFloor b N / 4
  have hfloor := explicitSeedFloor_bounds b N
  have hk : 1 ≤ k := by dsimp [k]; omega
  obtain ⟨r, hr, hl, hbound, ht, hhit, hunit, hmark⟩ :=
    exists_full_core_singleton_mark_of_bounded_residue_lift hb hk
      (fun n => 16 + n / 100) (fun _ => le_rfl) N
      (explicitOnePeriodSeedRootBound b N) (fun residue => by
        simpa only [explicitOnePeriodSeedRootBound, explicitExactSeedConductor] using
          exists_onePeriod_bounded_logTimeSuccessful_root_in_residue
            (ndRootCoreBackwardConductor b k N) b (by omega) residue (by norm_num : (1 : ℝ) ≤ 250))
  refine ⟨r, hr, hl, hbound, ht, hhit, hunit, ?_⟩
  unfold NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.coreMarkedSequence
  rw [NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.explicit_forward_floor]
  exact hmark

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem explicit_good_marked_margin_logarithmic_full
    (C : ℕ) (hmix : Tao.syracFineScaleMixingAt 6 (C : ℝ))
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (hb : 32 ^ 5 ≤ U.floor) (cap : ℕ → ℕ) (e : ℕ) (he : U.rootSpan e)
    (hcap : ∀ n, cap n ≤ 17 * (n + 1))
    (hcaplo : ∀ n, 16 + n / 100 ≤ cap n)
    {N n : ℕ} (hN : explicitLogarithmicSeedGeneration U.floor C ≤ N)
    (hNn : N ≤ n) (hn : explicitLogarithmicTerminalStart U.floor C e ≤ n)
    (hseed : (255 / 256 : ℝ) * U.denominator ≤
      U.coreMarkedSequence cap ndRootCoreWidth N)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i)) :
    (175 / 256 : ℝ) * U.denominator ≤
      U.forwardCoreTerminalGoodDepthShiftUnitMass cap ndRootCoreWidth n (cap n)
        ((U.forwardIterate cap n).floor / 4) X hX hi := by
  have hb1 : 1 ≤ U.floor := by omega
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hD : 0 ≤ U.denominator := by
    letI := U.state.labelFintype
    exact Finset.sum_nonneg fun i _ => U.state.weight_nonneg i
  have hcore := explicit_core_marked_difference hC hmix U hb cap 17 16 hcap hcaplo hNn
  have hcoreBudget := explicitCoreVariationTail_logarithmic_budget hb1 C 16 hC le_rfl hN
  have hcorePaid := hcore.trans (mul_le_mul_of_nonneg_left hcoreBudget hD)
  have hterminal := explicit_terminalUnitMass_le_majorant hC hmix
    U cap e 17 16 he hcap hcaplo n X hX hi
  have hterminalBudget := explicitTerminalVariation_logarithmic_budget hb1 C e 16 hC le_rfl hn
  have hterminalPaid := hterminal.trans (mul_le_mul_of_nonneg_left hterminalBudget hD)
  have hbad := U.forward_terminalBadDepthShiftUnitMass_le_summable_majorant
    cap e 17 he hcap n (cap n) X hX hi
  have hbadBudget := explicitTerminalVariation_logarithmic_budget hb1 C e 0 (by norm_num) hC hn
  have hbadPaid := hbad.trans (mul_le_mul_of_nonneg_left hbadBudget hD)
  have hc := (abs_le.mp hcorePaid).1
  have ht := (abs_le.mp hterminalPaid).1
  unfold forwardCoreTerminalGoodDepthShiftUnitMass
  linarith only [hseed, hc, ht, hbadPaid, hD]

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem exists_bounded_logarithmic_uniform_twoThirds_seed_of_mark
    {b : ℕ} (hb : 2 ^ 80 ≤ b) (C : ℕ)
    (hmix : Tao.syracFineScaleMixingAt 6 (C : ℝ))
    {N : ℕ} (hN : explicitLogarithmicSeedGeneration b C ≤ N)
    (M : ℕ)
    (hsupplied : ∃ (r : ℕ) (hr : Odd r) (hl : 16 ^ b ≤ r),
      r < M ∧ r ∈ oddSyracuseLogTimeOneSet 250 ∧ Tao.syracuse r = 1 ∧
      IsUnit (r : ZMod (3 ^ 1)) ∧
      (255 / 256 : ℝ) ≤
        (ndRootCoreSingletonState b r ((by norm_num : (200 : ℕ) ≤ 2 ^ 80).trans hb) hr hl).coreMarkedSequence
          (fun n => 16 + n / 100) ndRootCoreWidth N) :
    ∃ (r : ℕ) (hr : Odd r) (hl : 16 ^ b ≤ r),
      r < M ∧
      r ∈ oddSyracuseLogTimeOneSet 250 ∧ Tao.syracuse r = 1 ∧
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
  obtain ⟨r, hr, hl, hbound, ht, hhit, hunit, hmark⟩ :=
    hsupplied
  refine ⟨r, hr, hl, hbound, ht, hhit, hunit, ?_⟩
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
