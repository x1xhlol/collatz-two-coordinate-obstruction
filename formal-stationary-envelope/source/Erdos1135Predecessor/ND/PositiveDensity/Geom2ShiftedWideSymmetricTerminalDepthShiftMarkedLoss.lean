/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalDepthShiftTail
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalShiftImageRate

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators Topology

open Filter

noncomputable section

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

local instance (b a s : ℕ) : Decidable (ndTerminalDepthShiftGood b a s) :=
  Classical.propDecidable _

def forwardCoreTerminalBadDepthShiftUnitMass
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K k : ℕ) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i)) : ℝ := by
  classical
  let V := U.forwardIterate cap n
  letI := V.state.labelFintype
  exact ∑ i : V.state.Label,
    ∑ z : NDGeom2PredictableRootSideUnitChildIncidence ({i} : Finset V.state.Label)
      V.state.root V.floor (V.fullTerminalShift X hX hi i) K,
      ndGeom2PredictableRootSideUnitChildIncidenceWeight (U.forwardCoreOuterWeight cap width n) z *
        ndTerminalDepthShiftBadFilter V.floor (V.fullTerminalShift X hX hi i)
          (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z) *
        ndSyracuseUnitReferenceDensity k
          (ndGeom2PredictableRootSideUnitChildIncidenceSource z : ZMod (3 ^ k))

theorem forwardCoreTerminalBadDepthShiftUnitMass_eq_native_kernel
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K k : ℕ) (hk : 1 ≤ k) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i)) :
    U.forwardCoreTerminalBadDepthShiftUnitMass cap width n K k X hX hi =
      let V := U.forwardIterate cap n;
      letI := V.state.labelFintype;
      ∑ i, U.forwardCoreOuterWeight cap width n i *
        ndRootCoreFilteredKernel V.floor (V.fullTerminalShift X hX hi i) K k
          (ndTerminalDepthShiftBadFilter V.floor (V.fullTerminalShift X hX hi i))
          (ndSyracuseUnitReferenceDensity k)
          (V.state.root i : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon V.floor + k))) := by
  classical
  let V := U.forwardIterate cap n
  letI := V.state.labelFintype
  unfold forwardCoreTerminalBadDepthShiftUnitMass
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_unitIncidence_word_mark_eq_filteredKernel ({i} : Finset V.state.Label)
    V.state.root (U.forwardCoreOuterWeight cap width n) V.floor (V.fullTerminalShift X hX hi i) K k
    V.state.root_odd (by have h := V.floor_twoHundred; omega)
    (fun j => (Nat.pow_le_pow_right (by norm_num) (V.floor_le_base j)).trans (V.state.rootLower j))
    (ndTerminalDepthShiftBadFilter V.floor (V.fullTerminalShift X hX hi i))
    (ndSyracuseUnitReferenceDensity k) (unitReferenceDensity_natCast_eq_zero_of_not_unit hk)]
  rw [← Finset.sum_subtype ({i} : Finset V.state.Label) (fun _ => Iff.rfl)
    (fun j => U.forwardCoreOuterWeight cap width n j *
      ndRootCoreFilteredKernel V.floor (V.fullTerminalShift X hX hi i) K k
        (ndTerminalDepthShiftBadFilter V.floor (V.fullTerminalShift X hX hi i))
        (ndSyracuseUnitReferenceDensity k)
        (V.state.root j : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon V.floor + k))))]
  simp [V]

theorem forwardCoreTerminalBadDepthShiftUnitMass_le
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K k e : ℕ)
    (he : (U.forwardIterate cap n).rootSpan e) (hk : 1 ≤ k)
    (hq : ndGeom2ShiftedWideSymmetricHorizon (U.forwardIterate cap n).floor + k ≤
      2 * (U.forwardIterate cap n).floor)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i)) :
    U.forwardCoreTerminalBadDepthShiftUnitMass cap width n K k X hX hi ≤
      (e + 1 : ℝ) * U.coreCapacityBudget cap width n * ((2 / 3 : ℝ) *
        ((4 * ((U.forwardIterate cap n).floor : ℝ) + 4) *
          Real.exp (-((U.forwardIterate cap n).floor : ℝ) / 16384))) := by
  classical
  let V := U.forwardIterate cap n
  letI := V.state.labelFintype
  let q := ndGeom2ShiftedWideSymmetricHorizon V.floor + k
  let S := V.fullTerminalShiftImage X hX hi
  let F (a : ℕ) := ndRootCoreFilteredKernel V.floor a K k
    (ndTerminalDepthShiftBadFilter V.floor a) (ndSyracuseUnitReferenceDensity k)
  let u := (2 / 3 : ℝ) * ((4 * (V.floor : ℝ) + 4) * Real.exp (-(V.floor : ℝ) / 16384))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hF (a : ℕ) (_ha : a ∈ S) : ndTernaryUniformMean q (fun y => |F a y|) ≤ u := by
    have hn (y) : 0 ≤ F a y := rootCoreFilteredKernel_nonneg V.floor a K k _
      (terminalDepthShiftBadFilter_nonneg _ _) _ (ndSyracuseUnitReferenceDensity_nonneg _) y
    simp_rw [abs_of_nonneg (hn _)]
    exact terminalDepthShift_badKernel_fullMean_le V.floor_twoHundred a K k
  have h := U.abs_core_adaptive_pairing_le_image_capacity cap width n q hq S
    (V.fullTerminalShift X hX hi) (V.mem_fullTerminalShiftImage X hX hi) F hu hF
  rw [U.forwardCoreTerminalBadDepthShiftUnitMass_eq_native_kernel cap width n K k hk X hX hi]
  apply (le_abs_self _).trans
  apply h.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by exact_mod_cast V.fullTerminalShiftImage_card_le he X hX hi)
      (U.coreCapacityBudget_nonneg cap width n)) hu

theorem forward_quarter_terminalBadDepthShiftUnitMass_le
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (e : ℕ) (he : U.rootSpan e) (n K : ℕ)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i)) :
    U.forwardCoreTerminalBadDepthShiftUnitMass cap width n K
        ((U.forwardIterate cap n).floor / 4) X hX hi ≤
      (rootSpanBudget e cap n + 1 : ℝ) * U.coreCapacityBudget cap width n * ((2 / 3 : ℝ) *
        ((4 * ((U.forwardIterate cap n).floor : ℝ) + 4) *
          Real.exp (-((U.forwardIterate cap n).floor : ℝ) / 16384))) := by
  have hs : (U.forwardIterate cap n).rootSpan (rootSpanBudget e cap n) := by
    simpa only [U.forwardIterate_eq_iterate] using U.iterate_rootSpan he cap n
  have hb := (U.forwardIterate cap n).floor_twoHundred
  have hq : ndGeom2ShiftedWideSymmetricHorizon (U.forwardIterate cap n).floor +
      (U.forwardIterate cap n).floor / 4 ≤ 2 * (U.forwardIterate cap n).floor := by
    unfold ndGeom2ShiftedWideSymmetricHorizon ndGeom2ShiftedWideSymmetricWidth
    omega
  exact U.forwardCoreTerminalBadDepthShiftUnitMass_le cap width n K _ _ hs (by omega) hq X hX hi

theorem terminalDepthShift_loss_le_existing_strip_constant {b : ℕ} (hb : 1 ≤ b) :
    (4 * (b : ℝ) + 4) * Real.exp (-(b : ℝ) / 16384) ≤
      ndRootCoreStripConstant / (b : ℝ) ^ 6 := by
  apply (terminalDepthShift_loss_le_inverse_sixth hb).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  norm_num [ndRootCoreStripConstant, Nat.factorial]

theorem forward_terminalBadDepthShiftUnitMass_le_summable_majorant
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (e L : ℕ) (he : U.rootSpan e)
    (hcap : ∀ n, cap n ≤ L * (n + 1)) (n K : ℕ)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i)) :
    U.forwardCoreTerminalBadDepthShiftUnitMass cap ndRootCoreWidth n K
        ((U.forwardIterate cap n).floor / 4) X hX hi ≤
      U.denominator * ndRootTerminalVariationMajorant U.floor e L 0 0 n := by
  let V := U.forwardIterate cap n
  have hr := U.forward_quarter_terminalBadDepthShiftUnitMass_le cap ndRootCoreWidth e he n K X hX hi
  have hbudget := U.coreCapacityBudget_le_geometric cap L hcap n
  have herr := terminalDepthShift_loss_le_existing_strip_constant
    (show 1 ≤ V.floor by have := V.floor_twoHundred; omega)
  have hi6 : 1 / (V.floor : ℝ) ^ 6 ≤
      (1 / (U.floor : ℝ) ^ 6) * ((200 / 201 : ℝ) ^ 6) ^ n := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / (V.floor : ℝ))
      (U.core_inverse_floor_le_geometric cap n) 6
    simpa only [div_pow, one_pow, mul_pow, ← pow_mul, Nat.mul_comm] using hh
  have hh := mul_le_mul_of_nonneg_left hi6
    (by unfold ndRootCoreStripConstant; positivity : 0 ≤ ndRootCoreStripConstant)
  simp only [← mul_assoc, mul_one_div] at hh
  have her : (4 * (V.floor : ℝ) + 4) * Real.exp (-(V.floor : ℝ) / 16384) ≤
      (ndRootCoreStripConstant / (U.floor : ℝ) ^ 6) * ((200 / 201 : ℝ) ^ 6) ^ n +
        ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ n := by
    have hp : 0 ≤ ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ n := by positivity
    linarith only [herr, hh, hp]
  have hspan : (rootSpanBudget e cap n + 1 : ℝ) ≤
      ((e + L + 4 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have hs := rootSpanBudget_le_quadratic e L cap hcap n
    have hn : rootSpanBudget e cap n + 1 ≤ (e + L + 4) * (n + 1) ^ 2 := by
      have hp : 1 ≤ (n + 1) ^ 2 := by
        simpa using Nat.pow_le_pow_left (show 1 ≤ n + 1 by omega) 2
      nlinarith only [hs, hp]
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
        ((ndRootCoreStripConstant / (U.floor : ℝ) ^ 6) * ((200 / 201 : ℝ) ^ 6) ^ n +
          ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ n)) := by
      apply hr.trans
      apply mul_le_mul
      · exact mul_le_mul hspan hbudget (U.coreCapacityBudget_nonneg cap ndRootCoreWidth n)
          (by positivity)
      · exact mul_le_mul_of_nonneg_left her (by norm_num)
      · positivity
      · positivity
    _ = _ := by
      unfold ndRootTerminalVariationMajorant ndRootCoreVariationMajorant
      simp only [mul_pow, pow_zero, one_mul]
      ring

def forwardCoreTerminalGoodDepthShiftUnitMass
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K k : ℕ) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i)) : ℝ :=
  U.forwardCoreTerminalUnitMass cap width n K k X hX hi -
    U.forwardCoreTerminalBadDepthShiftUnitMass cap width n K k X hX hi

private theorem terminal_good_mask_sub (p : Prop) [Decidable p] (x y : ℝ) :
    x * y - x * (if p then 0 else 1) * y = if p then x * y else 0 := by
  split_ifs <;> ring

private theorem terminal_good_fiber_sub {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (p : ∀ i, κ i → Prop) [∀ i z, Decidable (p i z)] (x y : ∀ i, κ i → ℝ) :
    (∑ i, ∑ z, x i z * y i z) -
      (∑ i, ∑ z, x i z * (if p i z then 0 else 1) * y i z) =
      ∑ i, ∑ z, if p i z then x i z * y i z else 0 := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun z _ => terminal_good_mask_sub _ _ _

theorem forwardCoreTerminalGoodDepthShiftUnitMass_eq_sum
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K k : ℕ) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i)) :
    let V := U.forwardIterate cap n;
    letI := V.state.labelFintype;
    U.forwardCoreTerminalGoodDepthShiftUnitMass cap width n K k X hX hi =
      ∑ i : V.state.Label,
        ∑ z : NDGeom2PredictableRootSideUnitChildIncidence ({i} : Finset V.state.Label)
          V.state.root V.floor (V.fullTerminalShift X hX hi i) K,
          if ndTerminalDepthShiftGood V.floor (V.fullTerminalShift X hX hi i)
            (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z).length then
            ndGeom2PredictableRootSideUnitChildIncidenceWeight (U.forwardCoreOuterWeight cap width n) z *
              ndSyracuseUnitReferenceDensity k
                (ndGeom2PredictableRootSideUnitChildIncidenceSource z : ZMod (3 ^ k)) else 0 := by
  classical
  let V := U.forwardIterate cap n
  letI := V.state.labelFintype
  have h := terminal_good_fiber_sub (ι := V.state.Label)
    (κ := fun i => NDGeom2PredictableRootSideUnitChildIncidence ({i} : Finset V.state.Label)
      V.state.root V.floor (V.fullTerminalShift X hX hi i) K)
    (fun i z =>
      ndTerminalDepthShiftGood V.floor (V.fullTerminalShift X hX hi i)
        (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord
          (root := V.state.root) (b := V.floor) (a := V.fullTerminalShift X hX hi i) (K := K) z).length)
    (fun i z => ndGeom2PredictableRootSideUnitChildIncidenceWeight
      (root := V.state.root) (b := V.floor) (a := V.fullTerminalShift X hX hi i) (K := K)
      (U.forwardCoreOuterWeight cap width n) z)
    (fun i z => ndSyracuseUnitReferenceDensity k
      (ndGeom2PredictableRootSideUnitChildIncidenceSource
        (root := V.state.root) (b := V.floor) (a := V.fullTerminalShift X hX hi i) (K := K)
        z : ZMod (3 ^ k)))
  exact h

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
