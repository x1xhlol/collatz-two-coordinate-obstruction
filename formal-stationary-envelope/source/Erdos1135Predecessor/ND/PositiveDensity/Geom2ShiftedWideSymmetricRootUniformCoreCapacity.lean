/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootUniformGroupedCapacity

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

private theorem rootCore_twoPow_balanced_lt (a : ℕ) :
    2 ^ ndBalancedTotal a < 2 * 3 ^ a := by
  rcases a with _ | a
  · norm_num
  · have hthree : 1 < 3 ^ (a + 1) := Nat.one_lt_pow (by omega) (by norm_num)
    have hc : 0 < ndBalancedTotal (a + 1) := Nat.clog_pos (by norm_num) hthree
    have h := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hthree
    change 2 ^ (ndBalancedTotal (a + 1)).pred < 3 ^ (a + 1) at h
    have hp : ndBalancedTotal (a + 1) = (ndBalancedTotal (a + 1)).pred + 1 :=
      (Nat.succ_pred_eq_of_pos hc).symm
    rw [hp, pow_succ]
    omega

theorem rootCore_balanced_add_reverse_le (a b : ℕ) :
    ndBalancedTotal a + ndBalancedTotal b ≤ ndBalancedTotal (a + b) + 1 := by
  have hpow : 2 ^ (ndBalancedTotal a + ndBalancedTotal b) <
      2 ^ (ndBalancedTotal (a + b) + 2) := by
    calc
      _ = 2 ^ ndBalancedTotal a * 2 ^ ndBalancedTotal b := pow_add _ _ _
      _ < (2 * 3 ^ a) * (2 * 3 ^ b) := by
        gcongr <;> exact rootCore_twoPow_balanced_lt _
      _ = 4 * 3 ^ (a + b) := by rw [pow_add]; ring
      _ ≤ 4 * 2 ^ ndBalancedTotal (a + b) :=
        Nat.mul_le_mul_left 4 (three_pow_le_two_pow_ndBalancedTotal _)
      _ = _ := by rw [pow_add]; ring
  have h := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow
  omega

theorem rootCore_selectedWord_total_band {b K : ℕ} {w : List ℕ+}
    (hw : w ∈ ndShiftedReferenceSelectedWords b (ndGeom2ShiftedWideSymmetricShiftRadius b) K) :
    2 * b + ndBalancedTotal w.length ≤ Tao.taoTupleWeight w + ndBalancedTotal b + 1 ∧
      Tao.taoTupleWeight w + ndBalancedTotal b ≤ 2 * b + ndBalancedTotal w.length + K + 1 := by
  have he := (mem_shiftedReferenceSelectedWords_iff b _ K w).mp hw
  have hh := he.1.2.1.2
  have ho := he.2
  simp only [ndGeom2ShiftedWideSymmetricHit, List.take_length,
    ndGeom2ShiftedWideSymmetricBoundedOvershoot] at hh ho
  rcases le_total b w.length with hd | hd
  · have ha := ndBalancedTotal_add_le b (w.length - b)
    have hr := rootCore_balanced_add_reverse_le b (w.length - b)
    rw [Nat.add_sub_of_le hd] at ha hr
    have hz : b - w.length = 0 := by omega
    simp only [hz, ndBalancedTotal_zero] at hh ho
    constructor <;> omega
  · have ha := ndBalancedTotal_add_le w.length (b - w.length)
    have hr := rootCore_balanced_add_reverse_le w.length (b - w.length)
    rw [Nat.add_sub_of_le hd] at ha hr
    have hz : w.length - b = 0 := by omega
    simp only [hz, ndBalancedTotal_zero] at hh ho
    constructor <;> omega

def ndRootCoreCapSum (cap : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => cap 0 + ndRootCoreCapSum (ndGeom2RootSideCapTail cap) n

def ndRootCorePairs (B M K n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc (B - M) (B + M)).biUnion fun D =>
    (Finset.Icc (2 * B + ndBalancedTotal D - (ndBalancedTotal B + 2 * n))
      (2 * B + ndBalancedTotal D + K + 2 * n - ndBalancedTotal B)).image fun A => (D, A)

theorem rootCorePairs_mem {B M K n D A : ℕ}
    (hdlo : B ≤ D + M) (hdhi : D ≤ B + M)
    (halo : 2 * B + ndBalancedTotal D ≤ A + ndBalancedTotal B + 2 * n)
    (hahi : A + ndBalancedTotal B ≤ 2 * B + ndBalancedTotal D + K + 2 * n) :
    (D, A) ∈ ndRootCorePairs B M K n := by
  apply Finset.mem_biUnion.mpr
  refine ⟨D, Finset.mem_Icc.mpr ⟨by omega, hdhi⟩, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨A, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩

theorem rootCorePairs_card_le (B M K n : ℕ) :
    (ndRootCorePairs B M K n).card ≤ (2 * M + 1) * (K + 4 * n + 1) := by
  have hB := ndBalancedTotal_le_two_mul B
  unfold ndRootCorePairs
  calc
    _ ≤ ∑ D ∈ Finset.Icc (B - M) (B + M),
        ((Finset.Icc (2 * B + ndBalancedTotal D - (ndBalancedTotal B + 2 * n))
          (2 * B + ndBalancedTotal D + K + 2 * n - ndBalancedTotal B)).image
            fun A => (D, A)).card := Finset.card_biUnion_le
    _ ≤ ∑ _D ∈ Finset.Icc (B - M) (B + M), (K + 4 * n + 1) := by
      apply Finset.sum_le_sum
      intro D _
      have h := Finset.card_image_le (s := Finset.Icc
        (2 * B + ndBalancedTotal D - (ndBalancedTotal B + 2 * n))
        (2 * B + ndBalancedTotal D + K + 2 * n - ndBalancedTotal B)) (f := fun A => (D, A))
      rw [Nat.card_Icc] at h
      omega
    _ = (Finset.Icc (B - M) (B + M)).card * (K + 4 * n + 1) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (by rw [Nat.card_Icc]; omega)

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

def coreBaseSum (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => U.floor + (U.next (cap 0)).coreBaseSum (ndGeom2RootSideCapTail cap) n

def coreWidthSum (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (width : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => width U.floor + (U.next (cap 0)).coreWidthSum (ndGeom2RootSideCapTail cap) width n

def forwardCore (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (width : ℕ → ℕ) : (n : ℕ) → (U.forwardIterate cap n).state.Label → Prop
  | 0, _ => True
  | n + 1, z =>
      let d := ndGeom2PredictableRootSideUnitChildIncidenceDepth (U.forwardFirstIncidence cap n z)
      U.floor ≤ d + width U.floor ∧ d ≤ U.floor + width U.floor ∧
        (U.next (cap 0)).forwardCore (ndGeom2RootSideCapTail cap) width n z

theorem forwardCore_depth_band
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) (z : (U.forwardIterate cap n).state.Label)
    (hz : U.forwardCore cap width n z) :
    U.coreBaseSum cap n ≤ (U.forwardWord cap n z).length + U.coreWidthSum cap width n ∧
      (U.forwardWord cap n z).length ≤ U.coreBaseSum cap n + U.coreWidthSum cap width n := by
  induction n generalizing U cap with
  | zero => simp [coreBaseSum, coreWidthSum, forwardWord]
  | succ n ih =>
      have h := ih (U := U.next (cap 0)) (cap := ndGeom2RootSideCapTail cap) z hz.2.2
      simp only [forwardWord, List.length_append,
        ndGeom2PredictableRootSideUnitChildIncidence_rootSideWord_length, coreBaseSum, coreWidthSum]
      have hl := hz.1
      have hu := hz.2.1
      constructor <;> omega

theorem forwardWord_total_band
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (z : (U.forwardIterate cap n).state.Label) :
    2 * U.coreBaseSum cap n + ndBalancedTotal (U.forwardWord cap n z).length ≤
        Tao.taoTupleWeight (U.forwardWord cap n z) + ndBalancedTotal (U.coreBaseSum cap n) + 2 * n ∧
      Tao.taoTupleWeight (U.forwardWord cap n z) + ndBalancedTotal (U.coreBaseSum cap n) ≤
        2 * U.coreBaseSum cap n + ndBalancedTotal (U.forwardWord cap n z).length +
          ndRootCoreCapSum cap n + 2 * n := by
  induction n generalizing U cap with
  | zero => simp [coreBaseSum, forwardWord, ndRootCoreCapSum]
  | succ n ih =>
      let iz := U.forwardFirstIncidence cap n z
      let w := ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord iz
      let v := (U.next (cap 0)).forwardWord (ndGeom2RootSideCapTail cap) n z
      let B := (U.next (cap 0)).coreBaseSum (ndGeom2RootSideCapTail cap) n
      have hw := rootCore_selectedWord_total_band (unitIncidenceSelectedWord iz).2.property
      have ht := ih (U := U.next (cap 0)) (cap := ndGeom2RootSideCapTail cap) z
      have hdlo := ndBalancedTotal_add_le w.length v.length
      have hdhi := rootCore_balanced_add_reverse_le w.length v.length
      have hblo := ndBalancedTotal_add_le U.floor B
      have hbhi := rootCore_balanced_add_reverse_le U.floor B
      change 2 * U.floor + ndBalancedTotal w.length ≤ Tao.taoTupleWeight w + ndBalancedTotal U.floor + 1 ∧
        Tao.taoTupleWeight w + ndBalancedTotal U.floor ≤ 2 * U.floor + ndBalancedTotal w.length + cap 0 + 1 at hw
      change 2 * B + ndBalancedTotal v.length ≤ Tao.taoTupleWeight v + ndBalancedTotal B + 2 * n ∧
        Tao.taoTupleWeight v + ndBalancedTotal B ≤ 2 * B + ndBalancedTotal v.length +
          ndRootCoreCapSum (ndGeom2RootSideCapTail cap) n + 2 * n at ht
      simp only [forwardWord, List.length_append, Tao.taoTupleWeight_append, coreBaseSum, ndRootCoreCapSum]
      change 2 * (U.floor + B) + ndBalancedTotal (w.length + v.length) ≤
          Tao.taoTupleWeight w + Tao.taoTupleWeight v + ndBalancedTotal (U.floor + B) + 2 * (n + 1) ∧
        Tao.taoTupleWeight w + Tao.taoTupleWeight v + ndBalancedTotal (U.floor + B) ≤
          2 * (U.floor + B) + ndBalancedTotal (w.length + v.length) +
            (cap 0 + ndRootCoreCapSum (ndGeom2RootSideCapTail cap) n) + 2 * (n + 1)
      constructor <;> omega

theorem forwardCore_pair_mem
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) (z : (U.forwardIterate cap n).state.Label)
    (hz : U.forwardCore cap width n z) :
    ((U.forwardWord cap n z).length, Tao.taoTupleWeight (U.forwardWord cap n z)) ∈
      ndRootCorePairs (U.coreBaseSum cap n) (U.coreWidthSum cap width n) (ndRootCoreCapSum cap n) n := by
  have hd := U.forwardCore_depth_band cap width n z hz
  have ha := U.forwardWord_total_band cap n z
  exact rootCorePairs_mem hd.1 hd.2 ha.1 ha.2

def forwardCoreHistogram
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n q : ℕ) (y : ZMod (3 ^ q)) : ℝ := by
  classical
  letI := (U.forwardIterate cap n).state.labelFintype
  exact ∑ z ∈ Finset.univ.filter (fun z => U.forwardCore cap width n z ∧
      ((U.forwardIterate cap n).state.root z : ZMod (3 ^ q)) = y),
    (U.forwardIterate cap n).state.outerWeight z

theorem forwardCoreHistogram_le_sum_groups
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n q : ℕ) (y : ZMod (3 ^ q)) :
    U.forwardCoreHistogram cap width n q y ≤
      letI := U.state.labelFintype;
      ∑ i, ∑ p ∈ ndRootCorePairs (U.coreBaseSum cap n)
        (U.coreWidthSum cap width n) (ndRootCoreCapSum cap n) n,
          U.forwardRootGroupHistogram cap n i p.1 p.2 q y := by
  classical
  let V := U.forwardIterate cap n
  letI := V.state.labelFintype
  letI := U.state.labelFintype
  let G := ndRootCorePairs (U.coreBaseSum cap n) (U.coreWidthSum cap width n) (ndRootCoreCapSum cap n) n
  let P := (Finset.univ : Finset U.state.Label).product G
  let S := Finset.univ.filter (fun z : V.state.Label => U.forwardCore cap width n z ∧
    (V.state.root z : ZMod (3 ^ q)) = y)
  let key := fun z : V.state.Label => (U.forwardAncestor cap n z,
    ((U.forwardWord cap n z).length, Tao.taoTupleWeight (U.forwardWord cap n z)))
  have hcover : ∀ z ∈ S, key z ∈ P := by
    intro z hz
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
      U.forwardCore_pair_mem cap width n z (Finset.mem_filter.mp hz).2.1⟩
  calc
    U.forwardCoreHistogram cap width n q y = ∑ z ∈ S, ∑ p ∈ P,
        if key z = p then V.state.outerWeight z else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      simp only [Finset.sum_ite_eq, hcover z hz, if_true]
      rfl
    _ = ∑ p ∈ P, ∑ z ∈ S, if key z = p then V.state.outerWeight z else 0 :=
      Finset.sum_comm
    _ ≤ ∑ p ∈ P, U.forwardRootGroupHistogram cap n p.1 p.2.1 p.2.2 q y := by
      apply Finset.sum_le_sum
      intro p _
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro z hz
        obtain ⟨hzS, hk⟩ := Finset.mem_filter.mp hz
        have ha : U.forwardAncestor cap n z = p.1 := congrArg Prod.fst hk
        have hd : (U.forwardWord cap n z).length = p.2.1 := congrArg (fun x => x.2.1) hk
        have hA : Tao.taoTupleWeight (U.forwardWord cap n z) = p.2.2 := congrArg (fun x => x.2.2) hk
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, hd, hA⟩,
          (Finset.mem_filter.mp hzS).2.2⟩
      · intro z _ _
        exact V.state.weight_nonneg z
    _ = _ := Finset.sum_product _ _ _

theorem threePow_mul_forwardCoreHistogram_le_rootUniform
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n q : ℕ) (hq : q ≤ 2 * (U.forwardIterate cap n).floor)
    (y : ZMod (3 ^ q)) :
    (3 : ℝ) ^ q * U.forwardCoreHistogram cap width n q y ≤
      U.denominator *
        (((2 * U.coreWidthSum cap width n + 1) * (ndRootCoreCapSum cap n + 4 * n + 1) : ℕ) : ℝ) *
          ((2 : ℝ) ^ (U.floor + 1) + (16 : ℝ) ^ U.floor *
            (9 / 16 : ℝ) ^ (U.forwardIterate cap n).floor) := by
  classical
  letI := U.state.labelFintype
  let G := ndRootCorePairs (U.coreBaseSum cap n) (U.coreWidthSum cap width n) (ndRootCoreCapSum cap n) n
  let C := (2 : ℝ) ^ (U.floor + 1) + (16 : ℝ) ^ U.floor *
    (9 / 16 : ℝ) ^ (U.forwardIterate cap n).floor
  have hC : 0 ≤ C := by positivity
  have hD : 0 ≤ U.denominator := by
    change 0 ≤ ∑ i : U.state.Label, U.state.outerWeight i
    exact Finset.sum_nonneg fun i _ => U.state.weight_nonneg i
  calc
    _ ≤ ∑ i : U.state.Label, ∑ p ∈ G,
        (3 : ℝ) ^ q * U.forwardRootGroupHistogram cap n i p.1 p.2 q y := by
      simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left
        (U.forwardCoreHistogram_le_sum_groups cap width n q y) (by positivity : 0 ≤ (3 : ℝ) ^ q)
    _ ≤ ∑ i : U.state.Label, ∑ _p ∈ G, U.state.outerWeight i * C := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro p _
      exact U.threePow_mul_forwardRootGroupHistogram_le_rootUniform_edge cap n i p.1 p.2 q hq y
    _ = U.denominator * (G.card : ℝ) * C := by
      change _ = (∑ i : U.state.Label, U.state.outerWeight i) * (G.card : ℝ) * C
      simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hC
      apply mul_le_mul_of_nonneg_left _ hD
      exact_mod_cast rootCorePairs_card_le (U.coreBaseSum cap n) (U.coreWidthSum cap width n)
        (ndRootCoreCapSum cap n) n

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
