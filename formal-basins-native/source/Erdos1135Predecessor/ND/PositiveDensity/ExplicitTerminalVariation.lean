/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCoreVariation
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalShiftImageRate

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

theorem explicitShiftedReferenceKernel_rate {A : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hmix : Tao.syracFineScaleMixingAt A C) :
    ∀ b a K k ell : ℕ, 1 ≤ k → 1 ≤ ell →
      (hell : ell ≤ ndGeom2ShiftedWideSymmetricHorizon b + k) →
      ndTernaryUniformMean (ndGeom2ShiftedWideSymmetricHorizon b + k) (fun y =>
        |ndShiftedReferenceMarkedKernel b a K k y - ndSyracuseUnitReferenceDensity ell
          (Tao.taoZModThreeProjection hell y)|) ≤
        (2 / 3 : ℝ) * (C / (k : ℝ) ^ A + C / (ell : ℝ) ^ A +
          Tao.taoGatedRejectedMass (Tao.geom2PNatListPMF (ndGeom2ShiftedWideSymmetricHorizon b + k))
            (fun full => ∃ i : ndShiftedReferenceSelectedWords b a K,
              full.take i.val.length = i.val)
            (Tao.taoSection7OffsetZMod (ndGeom2ShiftedWideSymmetricHorizon b + k))) := by
  intro b a K k ell hk hellpos hell
  exact explicitReferencePrefixFamily_rate hC hmix
    (ndGeom2ShiftedWideSymmetricHorizon b + k) k ell
    (fun i : ndShiftedReferenceSelectedWords b a K => i.val)
    (fun i => by
      change i.val.length ≤ ndGeom2ShiftedWideSymmetricHorizon b + k
      have h := shiftedReferenceSelectedWords_length_le_horizon b a K i
      omega)
    (fun i => by
      change k ≤ ndGeom2ShiftedWideSymmetricHorizon b + k - i.val.length
      have h := shiftedReferenceSelectedWords_length_le_horizon b a K i
      omega)
    hell hk hellpos (shiftedReferenceSelectedWords_prefix_disjoint b a K)

theorem explicitShiftedReferenceKernel_error {A : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hmix : Tao.syracFineScaleMixingAt A C) :
    ∀ b a K k ell : ℕ, 200 ≤ b →
      a ∈ ndGeom2ShiftedWideSymmetricShiftIndices b → 1 ≤ k → 1 ≤ ell →
      (hell : ell ≤ ndGeom2ShiftedWideSymmetricHorizon b + k) →
      ndTernaryUniformMean (ndGeom2ShiftedWideSymmetricHorizon b + k) (fun y =>
        |ndShiftedReferenceMarkedKernel b a K k y - ndSyracuseUnitReferenceDensity ell
          (Tao.taoZModThreeProjection hell y)|) ≤
        (2 / 3 : ℝ) * (C / (k : ℝ) ^ A + C / (ell : ℝ) ^ A +
          4 * Real.exp (-(b : ℝ) / 2560000) + (1 / 2 : ℝ) ^ (K + 1)) := by
  have hrate := explicitShiftedReferenceKernel_rate hC hmix
  intro b a K k ell hb ha hk hellpos hell
  have h := hrate b a K k ell hk hellpos hell
  rw [shiftedReference_rejectedMass_eq_one_sub_probability b a K _ (by omega)] at h
  have hl := one_sub_tailFactor_mul_shiftRate_le_boundedOvershootCrossingProbability
    (K := K) hb ha
  have htail : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (K + 1) := by positivity
  have he : (0 : ℝ) ≤ Real.exp (-(b : ℝ) / 2560000) := (Real.exp_pos _).le
  nlinarith [mul_nonneg htail he]

private theorem explicit_terminal_exp_le_inverse_sixth {b : ℕ} (hb : 0 < b) :
    4 * Real.exp (-(b : ℝ) / 2560000) ≤ ndRootCoreStripConstant / (b : ℝ) ^ 6 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  let x : ℝ := (b : ℝ) / 2560000
  have hx : 0 < x := by dsimp [x]; positivity
  have ht := Real.pow_div_factorial_le_exp x hx.le 6
  have hexp : Real.exp (-x) ≤ (Nat.factorial 6 : ℝ) / x ^ 6 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_div_iff₀ (Real.exp_pos _) (pow_pos hx _)).mpr
    rw [one_mul, mul_comm]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < Nat.factorial 6)).mp ht
  have hc : 4 * (Nat.factorial 6 : ℝ) * 2560000 ^ 6 ≤ ndRootCoreStripConstant := by
    norm_num [ndRootCoreStripConstant, Nat.factorial]
  calc
    _ ≤ 4 * ((Nat.factorial 6 : ℝ) / x ^ 6) := by
      simpa only [x, neg_div] using mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 4)
    _ = (4 * (Nat.factorial 6 : ℝ) * 2560000 ^ 6) / (b : ℝ) ^ 6 := by dsimp [x]; field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hc (by positivity)

private theorem explicit_terminal_quarter_error_le_inverse_sixth {b : ℕ} (hb : 200 ≤ b)
    {C : ℝ} (hC : 0 ≤ C) :
    2 * C / ((b / 4 : ℕ) : ℝ) ^ 6 + 4 * Real.exp (-(b : ℝ) / 2560000) ≤
      (2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (b : ℝ) ^ 6 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hk0 : (0 : ℝ) < ((b / 4 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < b / 4)
  have hb8 : (b : ℝ) ≤ 8 * ((b / 4 : ℕ) : ℝ) := by exact_mod_cast (by omega : b ≤ 8 * (b / 4))
  have hrec : 1 / ((b / 4 : ℕ) : ℝ) ≤ 8 / (b : ℝ) :=
    (div_le_div_iff₀ hk0 hb0).mpr (by simpa only [one_mul] using hb8)
  have hp := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / ((b / 4 : ℕ) : ℝ)) hrec 6)
    (by positivity : 0 ≤ 2 * C)
  have he := explicit_terminal_exp_le_inverse_sixth (b := b) (by omega)
  calc
    _ ≤ (2 * C) * (8 / (b : ℝ)) ^ 6 + ndRootCoreStripConstant / (b : ℝ) ^ 6 := by
      simp only [div_pow, one_pow, mul_one_div] at hp ⊢
      linarith
    _ = _ := by rw [div_pow]; ring

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem explicit_terminalUnitMass_error {A : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hmix : Tao.syracFineScaleMixingAt A C) :
    ∀ (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
      (cap width : ℕ → ℕ) (n e K k : ℕ), (U.forwardIterate cap n).rootSpan e →
      1 ≤ k → ndGeom2ShiftedWideSymmetricHorizon (U.forwardIterate cap n).floor + k ≤
        2 * (U.forwardIterate cap n).floor →
      ∀ (X : ℝ) (hX : 0 < X)
      (hi : ∀ i : (U.forwardIterate cap n).state.Label,
        ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
          ((U.forwardIterate cap n).state.root i) < X ∧
        X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
          ((U.forwardIterate cap n).state.root i)),
      |U.forwardCoreTerminalUnitMass cap width n K k X hX hi -
        U.forwardCoreMarkedMass cap width n k (fun _ => 1)| ≤
      (e + 1 : ℝ) * U.coreCapacityBudget cap width n * ((2 / 3 : ℝ) *
        (2 * C / (k : ℝ) ^ A + 4 * Real.exp (-((U.forwardIterate cap n).floor : ℝ) / 2560000) +
          (1 / 2 : ℝ) ^ (K + 1))) := by
  have hrate := explicitShiftedReferenceKernel_error hC hmix
  intro U cap width n e K k he hk hq X hX hi
  let V := U.forwardIterate cap n
  letI := V.state.labelFintype
  let q := ndGeom2ShiftedWideSymmetricHorizon V.floor + k
  have hkq : k ≤ q := Nat.le_add_left _ _
  let F (a : ℕ) (y : ZMod (3 ^ q)) := ndShiftedReferenceMarkedKernel V.floor a K k y -
    ndSyracuseUnitReferenceDensity k (Tao.taoZModThreeProjection hkq y)
  let S := V.fullTerminalShiftImage X hX hi
  let u := (2 / 3 : ℝ) * (2 * C / (k : ℝ) ^ A +
    4 * Real.exp (-(V.floor : ℝ) / 2560000) + (1 / 2 : ℝ) ^ (K + 1))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hF (a : ℕ) (ha : a ∈ S) : ndTernaryUniformMean q (fun y => |F a y|) ≤ u := by
    have h := hrate V.floor a K k k V.floor_twoHundred
      (V.fullTerminalShiftImage_subset_legal X hX hi ha) hk hk hkq
    convert h using 1
    dsimp [u]
    ring
  have hs := U.abs_core_adaptive_pairing_le_image_capacity cap width n q hq S
    (V.fullTerminalShift X hX hi) (V.mem_fullTerminalShiftImage X hX hi) F hu hF
  have hmark := U.forwardCoreHistogram_referenceMark_pairing cap width n k q hkq
  rw [U.forwardCoreHistogram_pairing] at hmark
  have heq : U.forwardCoreTerminalUnitMass cap width n K k X hX hi -
      U.forwardCoreMarkedMass cap width n k (fun _ => 1) =
      ∑ i, U.forwardCoreOuterWeight cap width n i *
        F (V.fullTerminalShift X hX hi i) (V.state.root i : ZMod (3 ^ q)) := by
    rw [U.forwardCoreTerminalUnitMass_eq_native_kernel cap width n K k hk X hX hi, ← hmark]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [F, q, V]
    ring
  rw [heq]
  apply hs.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by exact_mod_cast V.fullTerminalShiftImage_card_le he X hX hi)
      (U.coreCapacityBudget_nonneg cap width n)) hu

theorem explicit_quarter_terminalUnitMass_error {A : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hmix : Tao.syracFineScaleMixingAt A C) :
    ∀ (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
      (cap width : ℕ → ℕ) (e : ℕ), U.rootSpan e → ∀ n,
      let V := U.forwardIterate cap n;
      ∀ (X : ℝ) (hX : 0 < X)
      (hi : ∀ i : V.state.Label,
        ndGeom2ShiftedWideSymmetricPhysicalIntervalMin V.floor (V.state.root i) < X ∧
        X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax V.floor (V.state.root i)),
      |U.forwardCoreTerminalUnitMass cap width n (cap n) (V.floor / 4) X hX hi -
        U.coreMarkedSequence cap width n| ≤
      (rootSpanBudget e cap n + 1 : ℝ) * U.coreCapacityBudget cap width n * ((2 / 3 : ℝ) *
        (2 * C / ((V.floor / 4 : ℕ) : ℝ) ^ A + 4 * Real.exp (-(V.floor : ℝ) / 2560000) +
          (1 / 2 : ℝ) ^ (cap n + 1))) := by
  have hrate := explicit_terminalUnitMass_error hC hmix
  intro U cap width e he n V X hX hi
  have hs : V.rootSpan (rootSpanBudget e cap n) := by
    simpa only [V, U.forwardIterate_eq_iterate] using U.iterate_rootSpan he cap n
  have hb := V.floor_twoHundred
  have hq : ndGeom2ShiftedWideSymmetricHorizon V.floor + V.floor / 4 ≤ 2 * V.floor := by
    unfold ndGeom2ShiftedWideSymmetricHorizon ndGeom2ShiftedWideSymmetricWidth
    omega
  exact hrate U cap width n (rootSpanBudget e cap n) (cap n) (V.floor / 4) hs (by omega) hq X hX hi

theorem explicit_terminalUnitMass_le_majorant {C : ℝ}
    (hC : 0 ≤ C) (hmix : Tao.syracFineScaleMixingAt 6 C) :
    ∀ (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
      (cap : ℕ → ℕ) (e L K0 : ℕ), U.rootSpan e →
      (∀ n, cap n ≤ L * (n + 1)) → (∀ n, K0 + n / 100 ≤ cap n) → ∀ n,
      let V := U.forwardIterate cap n;
      ∀ (X : ℝ) (hX : 0 < X)
      (hi : ∀ i : V.state.Label,
        ndGeom2ShiftedWideSymmetricPhysicalIntervalMin V.floor (V.state.root i) < X ∧
        X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax V.floor (V.state.root i)),
      |U.forwardCoreTerminalUnitMass cap ndRootCoreWidth n (cap n) (V.floor / 4) X hX hi -
        U.coreMarkedSequence cap ndRootCoreWidth n| ≤
      U.denominator * ndRootTerminalVariationMajorant U.floor e L K0 C n := by
  have hrate := explicit_quarter_terminalUnitMass_error hC hmix
  intro U cap e L K0 he hcap hcaplo n V X hX hi
  have hr := hrate U cap ndRootCoreWidth e he n X hX hi
  have hbudget := U.coreCapacityBudget_le_geometric cap L hcap n
  have herr := explicit_terminal_quarter_error_le_inverse_sixth V.floor_twoHundred hC
  have hi6 : 1 / (V.floor : ℝ) ^ 6 ≤ (1 / (U.floor : ℝ) ^ 6) * ((200 / 201 : ℝ) ^ 6) ^ n := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / (V.floor : ℝ))
      (U.core_inverse_floor_le_geometric cap n) 6
    simpa only [div_pow, one_pow, mul_pow, ← pow_mul, Nat.mul_comm] using hh
  have hh := mul_le_mul_of_nonneg_left hi6
    (by unfold ndRootCoreStripConstant; positivity : 0 ≤ 2 * C * 8 ^ 6 + ndRootCoreStripConstant)
  simp only [← mul_assoc, mul_one_div] at hh
  have hct := rootCore_cap_failure_le_geometric cap K0 hcaplo n
  have her : 2 * C / ((V.floor / 4 : ℕ) : ℝ) ^ 6 + 4 * Real.exp (-(V.floor : ℝ) / 2560000) +
      (1 / 2 : ℝ) ^ (cap n + 1) ≤
      ((2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (U.floor : ℝ) ^ 6) * ((200 / 201 : ℝ) ^ 6) ^ n +
        (1 / 2 : ℝ) ^ K0 * ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ n := by linarith
  have hspan : (rootSpanBudget e cap n + 1 : ℝ) ≤ ((e + L + 4 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have hs := rootSpanBudget_le_quadratic e L cap hcap n
    have hn : rootSpanBudget e cap n + 1 ≤ (e + L + 4) * (n + 1) ^ 2 := by
      calc
        _ ≤ (e + L + 3) * (n + 1) ^ 2 + 1 := Nat.add_le_add_right hs 1
        _ ≤ (e + L + 3) * (n + 1) ^ 2 + (n + 1) ^ 2 :=
          Nat.add_le_add_left (by simpa using Nat.pow_le_pow_left (show 1 ≤ n + 1 by omega) 2) _
        _ = _ := by ring
    exact_mod_cast hn
  have hD : 0 ≤ U.denominator := by
    letI := U.state.labelFintype
    exact Finset.sum_nonneg fun i _ => U.state.weight_nonneg i
  have hGrowth : 0 ≤ ndRootCoreGrowth := by norm_num [ndRootCoreGrowth]
  calc
    _ ≤ (((e + L + 4 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2) *
      (U.denominator * ((4 * (U.floor : ℝ) ^ (3 / 5 : ℝ) + 1) * (L + 5) *
        ((2 : ℝ) ^ (U.floor + 1) + (16 : ℝ) ^ U.floor)) *
        ((n + 1 : ℕ) : ℝ) ^ 3 * ndRootCoreGrowth ^ n) * ((2 / 3 : ℝ) *
        (((2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (U.floor : ℝ) ^ 6) * ((200 / 201 : ℝ) ^ 6) ^ n +
          (1 / 2 : ℝ) ^ K0 * ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ n)) := by
      apply hr.trans
      apply mul_le_mul
      · exact mul_le_mul hspan hbudget (U.coreCapacityBudget_nonneg cap ndRootCoreWidth n) (by positivity)
      · exact mul_le_mul_of_nonneg_left her (by norm_num)
      · positivity
      · positivity
    _ = _ := by unfold ndRootTerminalVariationMajorant ndRootCoreVariationMajorant; rw [mul_pow, mul_pow]; ring

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
