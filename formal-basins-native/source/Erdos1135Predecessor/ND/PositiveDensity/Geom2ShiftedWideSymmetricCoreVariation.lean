/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricCoreBackwardMean

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

def forwardLastIncidenceEquiv (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) :
    (U.forwardIterate cap (n + 1)).state.Label ≃ ((U.forwardIterate cap n).next (cap n)).state.Label :=
  Equiv.cast (congrArg (fun V => V.state.Label) (U.forwardIterate_succ_eq_next cap n))

def forwardLastParent (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (z : (U.forwardIterate cap (n + 1)).state.Label) :
    (U.forwardIterate cap n).state.Label :=
  ndGeom2PredictableRootSideUnitChildIncidenceLabel (U.forwardLastIncidenceEquiv cap n z)

theorem forwardFirstIncidence_lastParent_eq
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (z : (U.forwardIterate cap (n + 2)).state.Label) :
    U.forwardFirstIncidence cap n (U.forwardLastParent cap (n + 1) z) =
      U.forwardFirstIncidence cap (n + 1) z := by
  induction n generalizing U cap with
  | zero => rfl
  | succ n ih =>
      change ndGeom2PredictableRootSideUnitChildIncidenceLabel
        ((U.next (cap 0)).forwardFirstIncidence (ndGeom2RootSideCapTail cap) n
          ((U.next (cap 0)).forwardLastParent (ndGeom2RootSideCapTail cap) (n + 1) z)) =
        ndGeom2PredictableRootSideUnitChildIncidenceLabel
          ((U.next (cap 0)).forwardFirstIncidence (ndGeom2RootSideCapTail cap) (n + 1) z)
      exact congrArg ndGeom2PredictableRootSideUnitChildIncidenceLabel
        (ih (U.next (cap 0)) (ndGeom2RootSideCapTail cap) z)

theorem forwardCore_iff_last_parent_and_strip
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) (z : (U.forwardIterate cap (n + 1)).state.Label) :
    U.forwardCore cap width (n + 1) z ↔
      U.forwardCore cap width n (U.forwardLastParent cap n z) ∧
        let b := (U.forwardIterate cap n).floor;
        let d := ndGeom2PredictableRootSideUnitChildIncidenceDepth (U.forwardLastIncidenceEquiv cap n z);
        b ≤ d + width b ∧ d ≤ b + width b := by
  induction n generalizing U cap with
  | zero =>
      change (_ ∧ _ ∧ True) ↔ True ∧ (_ ∧ _)
      simp only [and_true, true_and]
      rfl
  | succ n ih =>
      have ht := ih (U.next (cap 0)) (ndGeom2RootSideCapTail cap) z
      have hf := U.forwardFirstIncidence_lastParent_eq cap n z
      simp only [forwardCore]
      rw [hf]
      change (_ ∧ _ ∧ (U.next (cap 0)).forwardCore (ndGeom2RootSideCapTail cap) width (n + 1) z) ↔
        (_ ∧ _ ∧ (U.next (cap 0)).forwardCore (ndGeom2RootSideCapTail cap) width n
          ((U.next (cap 0)).forwardLastParent (ndGeom2RootSideCapTail cap) n z)) ∧ _
      rw [ht]
      tauto

private theorem core_state_cast_weight
    {V W : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState} (h : V = W) (z : V.state.Label) :
    W.state.outerWeight (Equiv.cast (congrArg (fun T => T.state.Label) h) z) = V.state.outerWeight z := by
  cases h
  rfl

private theorem core_state_cast_root
    {V W : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState} (h : V = W) (z : V.state.Label) :
    W.state.root (Equiv.cast (congrArg (fun T => T.state.Label) h) z) = V.state.root z := by
  cases h
  rfl

theorem forwardLastIncidence_weight_eq
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (z : (U.forwardIterate cap (n + 1)).state.Label) :
    ndGeom2PredictableRootSideUnitChildIncidenceWeight (U.forwardIterate cap n).state.outerWeight
      (U.forwardLastIncidenceEquiv cap n z) = (U.forwardIterate cap (n + 1)).state.outerWeight z :=
  core_state_cast_weight (U.forwardIterate_succ_eq_next cap n) z

theorem forwardLastIncidence_source_eq
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (z : (U.forwardIterate cap (n + 1)).state.Label) :
    ndGeom2PredictableRootSideUnitChildIncidenceSource (U.forwardLastIncidenceEquiv cap n z) =
      (U.forwardIterate cap (n + 1)).state.root z :=
  core_state_cast_root (U.forwardIterate_succ_eq_next cap n) z

def forwardCoreOuterWeight (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) (i : (U.forwardIterate cap n).state.Label) : ℝ := by
  classical
  exact if U.forwardCore cap width n i then (U.forwardIterate cap n).state.outerWeight i else 0

theorem forwardCoreMarkedMass_succ_eq_kernel
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n k : ℕ) (hk : 1 ≤ k) :
    U.forwardCoreMarkedMass cap width (n + 1) k (fun _ => 1) =
      let V := U.forwardIterate cap n;
      letI := V.state.labelFintype;
      ∑ i, U.forwardCoreOuterWeight cap width n i *
        ndRootCoreFilteredKernel V.floor (ndGeom2ShiftedWideSymmetricShiftRadius V.floor) (cap n) k
          (ndRootCoreWordFilter V.floor (width V.floor)) (ndSyracuseUnitReferenceDensity k)
          (V.state.root i : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon V.floor + k))) := by
  classical
  let V := U.forwardIterate cap n
  letI := V.state.labelFintype
  letI := (V.next (cap n)).state.labelFintype
  letI := (U.forwardIterate cap (n + 1)).state.labelFintype
  let f (z : (V.next (cap n)).state.Label) :=
    ndGeom2PredictableRootSideUnitChildIncidenceWeight (U.forwardCoreOuterWeight cap width n) z *
      ndRootCoreWordFilter V.floor (width V.floor)
        (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z) *
      ndSyracuseUnitReferenceDensity k
        (ndGeom2PredictableRootSideUnitChildIncidenceSource z : ZMod (3 ^ k))
  have hs : U.forwardCoreMarkedMass cap width (n + 1) k (fun _ => 1) =
      ∑ z : (V.next (cap n)).state.Label, f z := by
    unfold forwardCoreMarkedMass
    apply Fintype.sum_equiv (U.forwardLastIncidenceEquiv cap n)
    intro z
    rw [U.forwardCore_iff_last_parent_and_strip cap width n z,
      ← U.forwardLastIncidence_weight_eq cap n z, ← U.forwardLastIncidence_source_eq cap n z]
    simp only [f, forwardCoreOuterWeight, ndGeom2PredictableRootSideUnitChildIncidenceWeight,
      ndRootCoreWordFilter, ndGeom2PredictableRootSideUnitChildIncidence_rootSideWord_length,
      forwardLastParent, V, mul_one]
    split_ifs <;> simp_all
  have hf := sum_unitIncidence_word_mark_eq_filteredKernel
    V.state.rootSideUniformFloorAllLabels V.state.root (U.forwardCoreOuterWeight cap width n)
    V.floor (ndGeom2ShiftedWideSymmetricShiftRadius V.floor) (cap n) k V.state.root_odd
    (by have h := V.floor_twoHundred; omega)
    (fun i => (Nat.pow_le_pow_right (by norm_num) (V.floor_le_base i)).trans (V.state.rootLower i))
    (ndRootCoreWordFilter V.floor (width V.floor)) (ndSyracuseUnitReferenceDensity k)
    (unitReferenceDensity_natCast_eq_zero_of_not_unit hk)
  rw [hs]
  change (∑ z : (V.next (cap n)).state.Label, f z) = _ at hf
  rw [hf]
  change (∑ i : {i : V.state.Label // i ∈ (Finset.univ : Finset V.state.Label)}, _) = _
  exact (Finset.sum_subtype Finset.univ (fun _ => Iff.rfl) (fun i =>
    U.forwardCoreOuterWeight cap width n i * ndRootCoreFilteredKernel V.floor
      (ndGeom2ShiftedWideSymmetricShiftRadius V.floor) (cap n) k
      (ndRootCoreWordFilter V.floor (width V.floor)) (ndSyracuseUnitReferenceDensity k)
      (V.state.root i : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon V.floor + k))))).symm

theorem forwardCoreHistogram_pairing
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n q : ℕ) (g : ZMod (3 ^ q) → ℝ) :
    (∑ y, U.forwardCoreHistogram cap width n q y * g y) =
      letI := (U.forwardIterate cap n).state.labelFintype;
      ∑ i, U.forwardCoreOuterWeight cap width n i *
        g ((U.forwardIterate cap n).state.root i : ZMod (3 ^ q)) := by
  classical
  letI := (U.forwardIterate cap n).state.labelFintype
  unfold forwardCoreHistogram
  simp_rw [Finset.sum_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : U.forwardCore cap width n i
  · simp [hi, forwardCoreOuterWeight]
  · simp [hi, forwardCoreOuterWeight]

theorem forwardCoreHistogram_referenceMark_pairing
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n k q : ℕ) (hkq : k ≤ q) :
    (∑ y, U.forwardCoreHistogram cap width n q y * ndSyracuseUnitReferenceDensity k
      (Tao.taoZModThreeProjection hkq y)) = U.forwardCoreMarkedMass cap width n k (fun _ => 1) := by
  classical
  rw [U.forwardCoreHistogram_pairing]
  simp only [Tao.taoZModThreeProjection_natCast]
  unfold forwardCoreMarkedMass forwardCoreOuterWeight
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

theorem forwardCoreMarkedMass_increment_eq_histogram
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n k ell : ℕ) (hk : 1 ≤ k)
    (hell : ell ≤ ndGeom2ShiftedWideSymmetricHorizon (U.forwardIterate cap n).floor + k) :
    U.forwardCoreMarkedMass cap width (n + 1) k (fun _ => 1) -
      U.forwardCoreMarkedMass cap width n ell (fun _ => 1) =
      let b := (U.forwardIterate cap n).floor;
      ∑ y, U.forwardCoreHistogram cap width n (ndGeom2ShiftedWideSymmetricHorizon b + k) y *
        (ndRootCoreFilteredKernel b (ndGeom2ShiftedWideSymmetricShiftRadius b) (cap n) k
          (ndRootCoreWordFilter b (width b)) (ndSyracuseUnitReferenceDensity k) y -
          ndSyracuseUnitReferenceDensity ell (Tao.taoZModThreeProjection hell y)) := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, U.forwardCoreHistogram_referenceMark_pairing cap width n ell _ hell,
    U.forwardCoreMarkedMass_succ_eq_kernel cap width n k hk, U.forwardCoreHistogram_pairing]

theorem forwardCoreHistogram_nonneg
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n q : ℕ) (y : ZMod (3 ^ q)) :
    0 ≤ U.forwardCoreHistogram cap width n q y :=
  Finset.sum_nonneg fun i _ => (U.forwardIterate cap n).state.weight_nonneg i

def coreCapacityBudget (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) : ℝ :=
  U.denominator * (((2 * U.coreWidthSum cap width n + 1) *
    (ndRootCoreCapSum cap n + 4 * n + 1) : ℕ) : ℝ) *
      ((2 : ℝ) ^ (U.floor + 1) + (16 : ℝ) ^ U.floor *
        (9 / 16 : ℝ) ^ (U.forwardIterate cap n).floor)

theorem coreCapacityBudget_nonneg (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) : 0 ≤ U.coreCapacityBudget cap width n := by
  letI := U.state.labelFintype
  have hD : 0 ≤ U.denominator := Finset.sum_nonneg fun i _ => U.state.weight_nonneg i
  unfold coreCapacityBudget
  positivity

theorem abs_coreHistogram_pairing_le_capacity_fullL1
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n q : ℕ) (hq : q ≤ 2 * (U.forwardIterate cap n).floor)
    (g : ZMod (3 ^ q) → ℝ) :
    |∑ y, U.forwardCoreHistogram cap width n q y * g y| ≤
      U.coreCapacityBudget cap width n * ndTernaryUniformMean q (fun y => |g y|) := by
  have hqpos : (0 : ℝ) < 3 ^ q := by positivity
  have hcap (y : ZMod (3 ^ q)) : U.forwardCoreHistogram cap width n q y ≤
      U.coreCapacityBudget cap width n / (3 : ℝ) ^ q := by
    apply (le_div_iff₀ hqpos).mpr
    simpa only [coreCapacityBudget, mul_comm] using
      U.threePow_mul_forwardCoreHistogram_le_rootUniform cap width n q hq y
  calc
    _ ≤ ∑ y, |U.forwardCoreHistogram cap width n q y * g y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, U.forwardCoreHistogram cap width n q y * |g y| := by
      simp only [abs_mul, abs_of_nonneg (U.forwardCoreHistogram_nonneg cap width n q _)]
    _ ≤ ∑ y, U.coreCapacityBudget cap width n / (3 : ℝ) ^ q * |g y| :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right (hcap y) (abs_nonneg _)
    _ = _ := by
      rw [← Finset.mul_sum]
      unfold ndTernaryUniformMean ndTernaryUniformScale
      push_cast
      ring

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

def coreMarkedSequence (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) : ℝ :=
  U.forwardCoreMarkedMass cap width n ((U.forwardIterate cap n).floor / 4) (fun _ => 1)

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
