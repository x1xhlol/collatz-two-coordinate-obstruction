/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalDepthShiftMarkedLoss
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalMaskedCensus

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

open Filter

noncomputable section

theorem physical_terminal_depth_mark_le_cap_one_fan
    {Label : Type*} [Fintype Label] {root base shift : Label → ℕ} {K : ℕ}
    (hrootOdd : ∀ i, Odd (root i)) (hbase : ∀ i, 9 ≤ base i)
    (hroot : ∀ i, 16 ^ base i ≤ root i)
    (outerWeight : Label → ℝ) (hw : ∀ i, 0 ≤ outerWeight i)
    (psi : Label → ℕ → ℝ) (hpsi : ∀ i s, 0 ≤ psi i s)
    (g : ℕ → ℝ) (hg : ∀ x, 0 ≤ g x) :
    (∑ z : NDGeom2PredictableRootSideBoundedOvershootIncidence Label root base shift K,
      ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight outerWeight z *
        psi (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z) *
        g (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)) ≤
    ∑ z0 : NDGeom2PredictableRootSideBoundedOvershootIncidence Label root base shift 1,
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight outerWeight z0 *
        psi (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z0)
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z0)) *
        ∑ j : Fin (K / 2 + 1), (1 / 4 : ℝ) ^ j.val *
          g (ndTerminalSourceFan j.val
            (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z0)) := by
  classical
  let f := ndPhysicalTerminalCompression (shift := shift) (K := K) hrootOdd hbase hroot
  let G : (NDGeom2PredictableRootSideBoundedOvershootIncidence Label root base shift 1 ×
      Fin (K / 2 + 1)) → ℝ := fun p =>
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight outerWeight p.1 *
      psi (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel p.1)
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth p.1)) *
      ((1 / 4 : ℝ) ^ p.2.val * g (ndTerminalSourceFan p.2.val
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource p.1)))
  have hG : ∀ p, 0 ≤ G p := by
    intro p
    exact mul_nonneg
      (mul_nonneg (ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight_nonneg
        outerWeight hw p.1) (hpsi _ _)) (mul_nonneg (by positivity) (hg _))
  calc
    _ = ∑ z, G (f z) := by
      apply Finset.sum_congr rfl
      intro z _
      have hs := physicalTerminalCompression_spec hrootOdd hbase hroot z
      have ht := physicalTerminalCompression_weighted_mark hrootOdd hbase hroot outerWeight g z
      dsimp only at hs ht
      dsimp only [G, f]
      calc
        _ = psi (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)
            (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z) *
            (ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight outerWeight z *
              g (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)) := by ring
        _ = _ := by rw [ht, hs.1, hs.2.1]; ring
    _ = ∑ p ∈ Finset.univ.image f, G p :=
      (Finset.sum_image fun z _ w _ h =>
        physicalTerminalCompression_injective hrootOdd hbase hroot h).symm
    _ ≤ ∑ p, G p := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun p _ _ => hG p)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro z0 _
      dsimp [G]
      rw [Finset.mul_sum]

theorem singleton_unit_terminal_depth_mark_le_physical
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (root shift : Label → ℕ) (b K : ℕ)
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hroot : ∀ i, 16 ^ b ≤ root i)
    (outerWeight : Label → ℝ) (hw : ∀ i, 0 ≤ outerWeight i)
    (psi : Label → ℕ → ℝ) (hpsi : ∀ i s, 0 ≤ psi i s)
    (g : ℕ → ℝ) (hg : ∀ x, 0 ≤ g x) :
    (∑ i : Label, ∑ z : NDGeom2PredictableRootSideUnitChildIncidence
      ({i} : Finset Label) root b (shift i) K,
      ndGeom2PredictableRootSideUnitChildIncidenceWeight outerWeight z *
        psi i (ndGeom2PredictableRootSideUnitChildIncidenceDepth z) *
        g (ndGeom2PredictableRootSideUnitChildIncidenceSource z)) ≤
    ∑ z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root (fun _ => b) shift K,
      ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight outerWeight z *
        psi (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z) *
        g (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) := by
  classical
  let f := ndTerminalUnitPhysicalMap root shift b K
  let G : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root (fun _ => b) shift K → ℝ := fun z =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight outerWeight z *
      psi (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z) *
      g (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)
  have hG : ∀ z, 0 ≤ G z := fun z =>
    mul_nonneg (mul_nonneg (ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight_nonneg
      outerWeight hw z) (hpsi _ _)) (hg _)
  calc
    _ = ∑ z : Σ i : Label, NDGeom2PredictableRootSideUnitChildIncidence
        ({i} : Finset Label) root b (shift i) K,
        ndGeom2PredictableRootSideUnitChildIncidenceWeight outerWeight z.2 *
          psi z.1 (ndGeom2PredictableRootSideUnitChildIncidenceDepth z.2) *
          g (ndGeom2PredictableRootSideUnitChildIncidenceSource z.2) :=
      (Fintype.sum_sigma _).symm
    _ = ∑ z, G (f z) := by
      apply Finset.sum_congr rfl
      intro z _
      have h := terminalUnitPhysicalMap_spec root shift b K z
      dsimp [G, f]
      rw [h.1, h.2.1, h.2.2.2.1, h.2.2.2.2]
    _ = ∑ z ∈ Finset.univ.image f, G z :=
      (Finset.sum_image fun z _ w _ h =>
        terminalUnitPhysicalMap_injective hrootOdd hb hroot h).symm
    _ ≤ ∑ z, G z := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun z _ _ => hG z)

def ndTerminalDepthShiftIndicator (b a s : ℕ) : ℝ := by
  classical
  exact if ndTerminalDepthShiftGood b a s then 1 else 0

theorem terminalDepthShiftIndicator_nonneg (b a s : ℕ) :
    0 ≤ ndTerminalDepthShiftIndicator b a s := by
  unfold ndTerminalDepthShiftIndicator
  split_ifs <;> norm_num

theorem terminalDepthShiftIndicator_le_one (b a s : ℕ) :
    ndTerminalDepthShiftIndicator b a s ≤ 1 := by
  unfold ndTerminalDepthShiftIndicator
  split_ifs <;> norm_num

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

private theorem core_outer_nonneg
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) (i : (U.forwardIterate cap n).state.Label) :
    0 ≤ U.forwardCoreOuterWeight cap width n i := by
  unfold forwardCoreOuterWeight
  split_ifs
  · exact (U.forwardIterate cap n).state.weight_nonneg i
  · exact le_rfl

def fullGoodCoreTerminalWeight (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (z : U.FullTerminalAt cap n shift K) : ℝ :=
  ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight (U.forwardCoreOuterWeight cap width n) z *
    ndTerminalDepthShiftIndicator (U.forwardIterate cap n).floor
      (shift (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z)

theorem fullGoodCoreTerminalWeight_nonneg
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (z : U.FullTerminalAt cap n shift K) : 0 ≤ U.fullGoodCoreTerminalWeight cap width n shift K z :=
  mul_nonneg (ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight_nonneg _
    (U.core_outer_nonneg cap width n) z) (terminalDepthShiftIndicator_nonneg _ _ _)

theorem fullGoodCoreTerminalWeight_le_original
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (z : U.FullTerminalAt cap n shift K) :
    U.fullGoodCoreTerminalWeight cap width n shift K z ≤
      ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
        (U.forwardIterate cap n).state.outerWeight z := by
  have hw := ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight_nonneg _
    (U.core_outer_nonneg cap width n) z
  apply (mul_le_mul_of_nonneg_left (terminalDepthShiftIndicator_le_one _ _ _) hw).trans
  rw [mul_one, U.fullCoreTerminalWeight_eq_ite]
  split_ifs
  · exact le_rfl
  · exact ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight_nonneg _
      (U.forwardIterate cap n).state.weight_nonneg z

def fullGoodCoreTerminalMass (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ) : ℝ := by
  classical
  letI := (U.forwardIterate cap n).state.labelFintype
  exact ∑ z : U.FullTerminalAt cap n shift K, U.fullGoodCoreTerminalWeight cap width n shift K z

def fullGoodCoreTerminalSources (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ) : Finset ℕ := by
  classical
  letI := (U.forwardIterate cap n).state.labelFintype
  exact (Finset.univ.filter fun z : U.FullTerminalAt cap n shift K =>
    U.forwardCore cap width n (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) ∧
      ndTerminalDepthShiftGood (U.forwardIterate cap n).floor
        (shift (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z)).image
    ndGeom2PredictableRootSideBoundedOvershootIncidenceSource

theorem fullGoodCoreTerminalSources_subset_fullTerminalSources
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ) :
    U.fullGoodCoreTerminalSources cap width n shift K ⊆ U.fullTerminalSources cap n shift K := by
  classical
  exact Finset.image_mono _ (Finset.filter_subset _ _)

theorem forwardGoodDepthShiftUnitMass_le_full_cap_one_fan
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K k : ℕ) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i)) :
    let V := U.forwardIterate cap n;
    letI := V.state.labelFintype;
    U.forwardCoreTerminalGoodDepthShiftUnitMass cap width n K k X hX hi ≤
      ∑ z : V.FullTerminalIncidence X hX hi,
        U.fullGoodCoreTerminalWeight cap width n (V.fullTerminalShift X hX hi) 1 z *
          ∑ j : Fin (K / 2 + 1), (1 / 4 : ℝ) ^ j.val *
            ndSyracuseUnitReferenceDensity k
              (ndTerminalSourceFan j.val
                (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) : ZMod (3 ^ k)) := by
  classical
  let V := U.forwardIterate cap n
  letI := V.state.labelFintype
  let g := fun x : ℕ => ndSyracuseUnitReferenceDensity k (x : ZMod (3 ^ k))
  let psi := fun i s => ndTerminalDepthShiftIndicator V.floor (V.fullTerminalShift X hX hi i) s
  have hg : ∀ x, 0 ≤ g x := by intro x; exact ndSyracuseUnitReferenceDensity_nonneg _ _
  have hp : ∀ i s, 0 ≤ psi i s := fun _ _ => terminalDepthShiftIndicator_nonneg _ _ _
  have hr : ∀ i, 16 ^ V.floor ≤ V.state.root i := fun i =>
    (Nat.pow_le_pow_right (by norm_num) (V.floor_le_base i)).trans (V.state.rootLower i)
  have h := (singleton_unit_terminal_depth_mark_le_physical V.state.root
    (V.fullTerminalShift X hX hi) V.floor K V.state.root_odd
    (by have := V.floor_twoHundred; omega) hr
    (U.forwardCoreOuterWeight cap width n) (U.core_outer_nonneg cap width n) psi hp g hg).trans
    (physical_terminal_depth_mark_le_cap_one_fan V.state.root_odd
      (fun _ => by have := V.floor_twoHundred; omega) hr
      (U.forwardCoreOuterWeight cap width n) (U.core_outer_nonneg cap width n) psi hp g hg)
  rw [U.forwardCoreTerminalGoodDepthShiftUnitMass_eq_sum]
  simpa only [ndGeom2PredictableRootSideUnitChildIncidence_rootSideWord_length,
    fullGoodCoreTerminalWeight, psi, ndTerminalDepthShiftIndicator, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, g] using h

theorem forwardGoodDepthShiftUnitMass_le_original
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K k : ℕ) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i)) :
    U.forwardCoreTerminalGoodDepthShiftUnitMass cap width n K k X hX hi ≤
      U.forwardCoreTerminalUnitMass cap width n K k X hX hi := by
  apply sub_le_self
  classical
  unfold forwardCoreTerminalBadDepthShiftUnitMass
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun z _ =>
    mul_nonneg (mul_nonneg (ndGeom2PredictableRootSideUnitChildIncidenceWeight_nonneg _
      (fun j _ => U.core_outer_nonneg cap width n j) z)
      (terminalDepthShiftBadFilter_nonneg _ _ _)) (ndSyracuseUnitReferenceDensity_nonneg _ _)

theorem fullGoodCoreTerminal_mass_mul_lower_le_frozenPotential_mul_card
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (hseedNeOne : ∀ i, U.state.root i ≠ 1)
    (hseedHitsOne : ∀ i, ∃ t : ℕ, (Tao.syracuse^[t]) (U.state.root i) = 1)
    (X : ℝ) (hX : 0 < X)
    (hsource : ∀ z : U.FullTerminalAt cap n shift K,
      X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ)) :
    X * U.fullGoodCoreTerminalMass cap width n shift K ≤
      U.parentSourcePotential * (U.fullGoodCoreTerminalSources cap width n shift K).card := by
  classical
  letI := (U.forwardIterate cap n).state.labelFintype
  let S := U.fullGoodCoreTerminalSources cap width n shift K
  let psi := fun x : ℕ => if x ∈ S then (1 : ℝ) else 0
  let W := fun z : U.FullTerminalAt cap n shift K =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
      (U.forwardIterate cap n).state.outerWeight z
  have hW : ∀ z, 0 ≤ W z := fun z =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight_nonneg _
      (U.forwardIterate cap n).state.weight_nonneg z
  have hp : ∀ x, 0 ≤ psi x := by intro x; dsimp [psi]; split_ifs <;> norm_num
  have hm : U.fullGoodCoreTerminalMass cap width n shift K ≤
      ∑ z, W z * psi (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) := by
    apply Finset.sum_le_sum
    intro z _
    unfold fullGoodCoreTerminalWeight
    rw [U.fullCoreTerminalWeight_eq_ite]
    unfold ndTerminalDepthShiftIndicator
    split_ifs with hc hg hg
    · have hs : ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z ∈ S :=
        Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hg⟩, rfl⟩
      simp only [psi, if_pos hs, mul_one]
      exact le_rfl
    all_goals simpa only [mul_zero, zero_mul] using mul_nonneg (hW z) (hp _)
  have hsum : (∑ x ∈ U.fullTerminalSources cap n shift K, psi x) = (S.card : ℝ) := by
    calc
      _ = ∑ x ∈ S, psi x := by
        symm
        apply Finset.sum_subset (U.fullGoodCoreTerminalSources_subset_fullTerminalSources cap width n shift K)
        intro x _ hx
        simp only [psi, S, if_neg hx]
      _ = _ := by simp [psi]
  have hc := U.fullTerminal_weighted_source_charge cap n shift K hseedNeOne hseedHitsOne
    X hX hsource psi hp
  rw [hsum] at hc
  have h := hm.trans hc
  rw [div_mul_eq_mul_div] at h
  exact (by simpa only [mul_comm X] using (le_div_iff₀ hX).mp h)

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
