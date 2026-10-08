/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricCoreSummedVariation

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators Topology

open Filter

noncomputable section

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem fullTerminalShift_le_add_rootSpan
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    {e : ℕ} (he : U.rootSpan e) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : U.state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin U.floor (U.state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax U.floor (U.state.root i))
    (i j : U.state.Label) :
    U.fullTerminalShift X hX hi i ≤ U.fullTerminalShift X hX hi j + e := by
  let a := U.fullTerminalShift X hX hi
  have hspeci := U.fullTerminalShift_spec X hX hi i
  have hspecj := U.fullTerminalShift_spec X hX hi j
  by_contra hn
  have hgap : a j + e + 1 ≤ a i := by dsimp [a]; omega
  have hpow : 2 ^ (a j + e + 1) ≤ 2 ^ a i := Nat.pow_le_pow_right (by norm_num) hgap
  have hnum : 2 * (2 ^ a j * 4 ^ U.floor * U.state.root j) ≤
      2 ^ a i * 4 ^ U.floor * U.state.root i := by
    calc
      _ ≤ 2 * (2 ^ a j * 4 ^ U.floor * (2 ^ e * U.state.root i)) := by gcongr; exact he j i
      _ = 2 ^ (a j + e + 1) * 4 ^ U.floor * U.state.root i := by rw [pow_succ, pow_add]; ring
      _ ≤ _ := by gcongr
  have hscale : 2 * ndGeom2ShiftedWideSymmetricPhysicalLowerScale U.floor (a j) (U.state.root j) ≤
      ndGeom2ShiftedWideSymmetricPhysicalLowerScale U.floor (a i) (U.state.root i) := by
    unfold ndGeom2ShiftedWideSymmetricPhysicalLowerScale
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hnum
  dsimp only [a] at hscale
  linarith [hspeci.2.2, hspecj.2.1]

def fullTerminalShiftImage
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : U.state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin U.floor (U.state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax U.floor (U.state.root i)) : Finset ℕ := by
  classical
  letI := U.state.labelFintype
  exact Finset.univ.image (U.fullTerminalShift X hX hi)

theorem fullTerminalShiftImage_card_le
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    {e : ℕ} (he : U.rootSpan e) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : U.state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin U.floor (U.state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax U.floor (U.state.root i)) :
    (U.fullTerminalShiftImage X hX hi).card ≤ e + 1 := by
  classical
  letI := U.state.labelFintype
  let S := U.fullTerminalShiftImage X hX hi
  by_cases hs : S.Nonempty
  · have hmin := Finset.min'_mem S hs
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmin
    have hsub : S ⊆ Finset.Icc (S.min' hs) (S.min' hs + e) := by
      intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      apply Finset.mem_Icc.mpr
      refine ⟨Finset.min'_le _ _ ha, ?_⟩
      rw [← hj]
      exact U.fullTerminalShift_le_add_rootSpan he X hX hi i j
    exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
  · have hh : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change S.card ≤ _
    rw [hh]
    simp

theorem mem_fullTerminalShiftImage
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : U.state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin U.floor (U.state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax U.floor (U.state.root i))
    (i : U.state.Label) : U.fullTerminalShift X hX hi i ∈ U.fullTerminalShiftImage X hX hi := by
  classical
  letI := U.state.labelFintype
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem fullTerminalShiftImage_subset_legal
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : U.state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin U.floor (U.state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax U.floor (U.state.root i)) :
    U.fullTerminalShiftImage X hX hi ⊆ ndGeom2ShiftedWideSymmetricShiftIndices U.floor := by
  classical
  letI := U.state.labelFintype
  intro a ha
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  exact (U.fullTerminalShift_spec X hX hi i).1

theorem abs_core_adaptive_pairing_le_image_capacity
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n q : ℕ) (hq : q ≤ 2 * (U.forwardIterate cap n).floor)
    (S : Finset ℕ) (sigma : (U.forwardIterate cap n).state.Label → ℕ)
    (hS : ∀ i, sigma i ∈ S) (F : ℕ → ZMod (3 ^ q) → ℝ)
    {u : ℝ} (_hu : 0 ≤ u) (hF : ∀ a ∈ S, ndTernaryUniformMean q (fun y => |F a y|) ≤ u) :
    letI := (U.forwardIterate cap n).state.labelFintype;
    |∑ i, U.forwardCoreOuterWeight cap width n i *
      F (sigma i) ((U.forwardIterate cap n).state.root i : ZMod (3 ^ q))| ≤
      (S.card : ℝ) * U.coreCapacityBudget cap width n * u := by
  classical
  letI := (U.forwardIterate cap n).state.labelFintype
  have hw (i) : 0 ≤ U.forwardCoreOuterWeight cap width n i := by
    unfold forwardCoreOuterWeight
    split_ifs
    · exact (U.forwardIterate cap n).state.weight_nonneg i
    · exact le_rfl
  calc
    _ ≤ ∑ i, U.forwardCoreOuterWeight cap width n i *
        |F (sigma i) ((U.forwardIterate cap n).state.root i : ZMod (3 ^ q))| := by
      simpa only [abs_mul, abs_of_nonneg (hw _)] using Finset.abs_sum_le_sum_abs
        (fun i => U.forwardCoreOuterWeight cap width n i * F (sigma i)
          ((U.forwardIterate cap n).state.root i : ZMod (3 ^ q))) Finset.univ
    _ ≤ ∑ i, U.forwardCoreOuterWeight cap width n i *
        ∑ a ∈ S, |F a ((U.forwardIterate cap n).state.root i : ZMod (3 ^ q))| := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      exact Finset.single_le_sum
        (f := fun a => |F a ((U.forwardIterate cap n).state.root i : ZMod (3 ^ q))|)
        (fun a _ => abs_nonneg _) (hS i)
    _ = ∑ a ∈ S, ∑ y, U.forwardCoreHistogram cap width n q y * |F a y| := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      exact (U.forwardCoreHistogram_pairing cap width n q (fun y => |F a y|)).symm
    _ ≤ ∑ _a ∈ S, U.coreCapacityBudget cap width n * u := by
      apply Finset.sum_le_sum
      intro a ha
      apply (le_abs_self _).trans
      apply (U.abs_coreHistogram_pairing_le_capacity_fullL1 cap width n q hq (fun y => |F a y|)).trans
      simpa only [abs_abs] using mul_le_mul_of_nonneg_left (hF a ha) (U.coreCapacityBudget_nonneg cap width n)
    _ = _ := by simp; ring

def forwardCoreTerminalUnitMass
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
        ndSyracuseUnitReferenceDensity k (ndGeom2PredictableRootSideUnitChildIncidenceSource z : ZMod (3 ^ k))

theorem forwardCoreTerminalUnitMass_eq_native_kernel
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K k : ℕ) (hk : 1 ≤ k) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i)) :
    U.forwardCoreTerminalUnitMass cap width n K k X hX hi =
      let V := U.forwardIterate cap n;
      letI := V.state.labelFintype;
      ∑ i, U.forwardCoreOuterWeight cap width n i *
        ndShiftedReferenceMarkedKernel V.floor (V.fullTerminalShift X hX hi i) K k
          (V.state.root i : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon V.floor + k))) := by
  classical
  let V := U.forwardIterate cap n
  letI := V.state.labelFintype
  unfold forwardCoreTerminalUnitMass
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_unitIncidence_referenceMark_eq_original_parent_kernel ({i} : Finset V.state.Label)
    V.state.root (U.forwardCoreOuterWeight cap width n) V.floor (V.fullTerminalShift X hX hi i) K k
    V.state.root_odd (by have h := V.floor_twoHundred; omega)
    (fun j => (Nat.pow_le_pow_right (by norm_num) (V.floor_le_base j)).trans (V.state.rootLower j)) hk]
  rw [← Finset.sum_subtype ({i} : Finset V.state.Label) (fun _ => Iff.rfl)
    (fun j => U.forwardCoreOuterWeight cap width n j *
      ndShiftedReferenceMarkedKernel V.floor (V.fullTerminalShift X hX hi i) K k
        (V.state.root j : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon V.floor + k))))]
  simp [V]

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

def ndRootTerminalVariationMajorant (b e L K0 : ℕ) (C : ℝ) (n : ℕ) : ℝ :=
  ((e + L + 4 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 * ndRootCoreVariationMajorant b L K0 C n

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
