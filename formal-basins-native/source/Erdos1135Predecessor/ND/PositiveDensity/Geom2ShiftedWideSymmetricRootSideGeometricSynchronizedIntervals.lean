/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideUniformFloorGeometricIntervalStoppedFlux

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

set_option maxHeartbeats 400000

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

def rootSpan (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (e : ℕ) : Prop :=
  ∀ i j : U.state.Label, U.state.root i ≤ 2 ^ e * U.state.root j

private theorem next_source_upper
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (K : ℕ) (z : (U.next K).state.Label) :
    3 ^ U.floor * (U.next K).state.root z ≤
      2 ^ (K + 1) * 4 ^ U.floor *
        U.state.root (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) := by
  have hlower : ∀ i, 16 ^ U.floor ≤ U.state.root i := fun i =>
    (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans
      (U.state.rootLower i)
  exact ndGeom2PredictableRootSideUnitChildIncidence_threePow_mul_source_le_twoPow_capSucc_mul_fourPow_mul_parent
    U.state.root_odd (by have h := U.floor_twoHundred; omega) hlower z

private theorem next_source_lower
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (K : ℕ) (z : (U.next K).state.Label) :
    4 ^ U.floor *
        U.state.root (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) ≤
      4 * 3 ^ U.floor * (U.next K).state.root z := by
  have hlower : ∀ i, 16 ^ U.floor ≤ U.state.root i := fun i =>
    (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans
      (U.state.rootLower i)
  exact ndGeom2PredictableRootSideUnitChildIncidence_fourPow_mul_parent_le_four_mul_threePow_mul_source
    U.state.root_odd (by have h := U.floor_twoHundred; omega) hlower z

theorem next_rootSpan
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    {e : ℕ} (he : U.rootSpan e) (K : ℕ) :
    (U.next K).rootSpan (e + K + 3) := by
  intro z z'
  have h := calc
    3 ^ U.floor * (U.next K).state.root z ≤
        2 ^ (K + 1) * 4 ^ U.floor *
          U.state.root (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) :=
      U.next_source_upper K z
    _ ≤ 2 ^ (K + 1) * 4 ^ U.floor *
          (2 ^ e * U.state.root
            (ndGeom2PredictableRootSideUnitChildIncidenceLabel z')) :=
      Nat.mul_le_mul_left _ (he _ _)
    _ = 2 ^ (K + 1 + e) * (4 ^ U.floor * U.state.root
          (ndGeom2PredictableRootSideUnitChildIncidenceLabel z')) := by
      rw [pow_add]; ring
    _ ≤ 2 ^ (K + 1 + e) * (4 * 3 ^ U.floor * (U.next K).state.root z') :=
      Nat.mul_le_mul_left _ (U.next_source_lower K z')
    _ = 3 ^ U.floor * (2 ^ (e + K + 3) * (U.next K).state.root z') := by
      have hexp : e + K + 3 = (K + 1 + e) + 2 := by omega
      rw [hexp, pow_add]
      ring
  exact Nat.le_of_mul_le_mul_left h (by positivity)

def rootSpanBudget (e : ℕ) (cap : ℕ → ℕ) (n : ℕ) : ℕ :=
  e + ∑ j ∈ Finset.range n, (cap j + 3)

theorem iterate_rootSpan
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    {e : ℕ} (he : U.rootSpan e) (cap : ℕ → ℕ) (n : ℕ) :
    (U.iterate cap n).rootSpan (rootSpanBudget e cap n) := by
  induction n with
  | zero => simpa [iterate, rootSpanBudget] using he
  | succ n ih =>
      simpa [iterate, rootSpanBudget, Finset.sum_range_succ, Nat.add_assoc]
        using (U.iterate cap n).next_rootSpan ih (cap n)

theorem rootSpanBudget_le_quadratic
    (e L : ℕ) (cap : ℕ → ℕ) (hc : ∀ n, cap n ≤ L * (n + 1)) (n : ℕ) :
    rootSpanBudget e cap n ≤ (e + L + 3) * (n + 1) ^ 2 := by
  induction n with
  | zero => simp [rootSpanBudget]; omega
  | succ n ih =>
      have hc' := hc n
      have hn : 0 ≤ n := Nat.zero_le n
      simp only [rootSpanBudget, Finset.sum_range_succ] at ih ⊢
      nlinarith

private theorem cubic_growth_step (n : ℕ) :
    200 * (n + 1001) ^ 3 ≤ 201 * (n + 1000) ^ 3 := by
  nlinarith [Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]

theorem iterate_floor_cubic_lower
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) :
    U.floor * (n + 1000) ^ 3 ≤ 1000000000 * (U.iterate cap n).floor := by
  induction n with
  | zero => simp [iterate]; omega
  | succ n ih =>
      have hg := U.iterate_twoHundredOne_mul_floor_le_twoHundred_mul_next_floor cap n
      have hc := Nat.mul_le_mul_left U.floor (cubic_growth_step n)
      have hi := Nat.mul_le_mul_left 201 ih
      have ht := Nat.mul_le_mul_left 1000000000 hg
      nlinarith

theorem rootSpanBudget_add_cap_le_floor_div_twoHundred
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (e L : ℕ) (cap : ℕ → ℕ) (hc : ∀ n, cap n ≤ L * (n + 1))
    (n : ℕ) (hn : 1000000000 * (e + L + 3) ≤ n) :
    rootSpanBudget e cap n + cap n ≤ (U.iterate cap n).floor / 200 := by
  let B := e + L + 3
  let t := n + 1000
  have hbudget : rootSpanBudget e cap n + cap n ≤ B * t ^ 2 := by
    have h := rootSpanBudget_le_quadratic e L cap hc (n + 1)
    have hmono : (n + 1 + 1) ^ 2 ≤ t ^ 2 :=
      Nat.pow_le_pow_left (by dsimp [t]; omega) 2
    have h' := h.trans (Nat.mul_le_mul_left (e + L + 3) hmono)
    simp only [rootSpanBudget, Finset.sum_range_succ] at h' ⊢
    dsimp only [B] at h' ⊢
    omega
  have hb := U.floor_twoHundred
  have hg := U.iterate_floor_cubic_lower cap n
  have hl : 200 * t ^ 3 ≤ 1000000000 * (U.iterate cap n).floor :=
    (Nat.mul_le_mul_right (t ^ 3) hb).trans hg
  have ht : 1000000000 * B ≤ t := by dsimp [B, t]; omega
  have hp := Nat.mul_le_mul_right (200 * t ^ 2) ht
  have hscale : 1000000000 * (200 * (B * t ^ 2)) ≤
      200 * t ^ 3 := by
    calc
      _ = (1000000000 * B) * (200 * t ^ 2) := by ring
      _ ≤ t * (200 * t ^ 2) := hp
      _ = _ := by ring
  have hsmall : 200 * (B * t ^ 2) ≤ (U.iterate cap n).floor :=
    Nat.le_of_mul_le_mul_left (hscale.trans hl) (by norm_num)
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 200)).2 (by
    simpa [Nat.mul_comm] using (Nat.mul_le_mul_left 200 hbudget).trans hsmall)

theorem next_intervalMin_lt_every_parentIntervalMax
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    {e K : ℕ} (he : U.rootSpan e)
    (hb : 600 ≤ U.floor) (hbudget : e + K ≤ U.floor / 200)
    (z : (U.next K).state.Label) (i : U.state.Label) :
    ndGeom2ShiftedWideSymmetricPhysicalIntervalMin
        (U.next K).floor ((U.next K).state.root z) <
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMax U.floor (U.state.root i) := by
  have hu := U.next_source_upper K z
  have hs := he (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) i
  have hsource : 3 ^ U.floor * (U.next K).state.root z ≤
      2 ^ ((e + K) + 1) * 4 ^ U.floor * U.state.root i := by
    calc
      _ ≤ 2 ^ (K + 1) * 4 ^ U.floor *
          (2 ^ e * U.state.root i) :=
        hu.trans (Nat.mul_le_mul_left _ hs)
      _ = _ := by
        rw [show e + K + 1 = K + 1 + e by omega, pow_add]
        ring
  exact ndGeom2ShiftedWideSymmetric_geometricIntervalMin_lt_intervalMax_of_shellUpper
    hb hbudget (Odd.pos (U.state.root_odd i)) hsource

private theorem floor_add_two_mul_le_iterate_floor
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) :
    U.floor + 2 * n ≤ (U.iterate cap n).floor := by
  simpa only [U.geometricIntervalStoppedIterate_floor_eq_iterate cap 0 n] using
    U.floor_add_two_mul_le_geometricIntervalStoppedIterate_floor cap 0 n

theorem iterate_eventual_all_parent_overlap
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    {e L : ℕ} (he : U.rootSpan e) (cap : ℕ → ℕ)
    (hc : ∀ n, cap n ≤ L * (n + 1))
    (n : ℕ) (hn : 1000000000 * (e + L + 3) ≤ n)
    (z : (U.iterate cap (n + 1)).state.Label)
    (i : (U.iterate cap n).state.Label) :
    ndGeom2ShiftedWideSymmetricPhysicalIntervalMin
        (U.iterate cap (n + 1)).floor
        ((U.iterate cap (n + 1)).state.root z) <
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
        (U.iterate cap n).floor ((U.iterate cap n).state.root i) := by
  have hf := U.floor_add_two_mul_le_iterate_floor cap n
  have hb := U.floor_twoHundred
  exact (U.iterate cap n).next_intervalMin_lt_every_parentIntervalMax
    (U.iterate_rootSpan he cap n) (by omega)
    (U.rootSpanBudget_add_cap_le_floor_div_twoHundred e L cap hc n hn) z i

private theorem exists_generation_all_intervalMax_ge
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (N : ℕ) (X : ℝ) :
    ∃ t, ∀ i : (U.iterate cap (N + t)).state.Label,
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
        (U.iterate cap (N + t)).floor
        ((U.iterate cap (N + t)).state.root i) := by
  obtain ⟨t, ht⟩ := exists_nat_gt X
  refine ⟨t, fun i => ?_⟩
  let V := U.iterate cap (N + t)
  have hf : t ≤ V.floor := by
    have h := U.floor_add_two_mul_le_iterate_floor cap (N + t)
    dsimp only [V]
    omega
  have hr : 16 ^ V.floor ≤ V.state.root i :=
    (Nat.pow_le_pow_right (by norm_num) (V.floor_le_base i)).trans
      (V.state.rootLower i)
  have hp : t ≤ 2 ^ V.floor :=
    hf.trans (show V.floor < 2 ^ V.floor from Nat.lt_two_pow_self).le
  have hpReal : (t : ℝ) ≤ ((2 ^ V.floor : ℕ) : ℝ) := by exact_mod_cast hp
  exact ht.le.trans (hpReal.trans
    (twoPow_base_le_ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
      (by have h := V.floor_twoHundred; omega) hr))

theorem exists_unstopped_generation_all_intervals_contain
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    {e L : ℕ} (he : U.rootSpan e) (cap : ℕ → ℕ)
    (hc : ∀ n, cap n ≤ L * (n + 1))
    (N : ℕ) (hN : 1000000000 * (e + L + 3) ≤ N) (X : ℝ)
    (hstart : ∀ i : (U.iterate cap N).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
        (U.iterate cap N).floor ((U.iterate cap N).state.root i) < X) :
    ∃ n, N ≤ n ∧ ∀ i : (U.iterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin
          (U.iterate cap n).floor ((U.iterate cap n).state.root i) < X ∧
        X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
          (U.iterate cap n).floor ((U.iterate cap n).state.root i) := by
  classical
  let P := fun t => ∀ i : (U.iterate cap (N + t)).state.Label,
    X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
      (U.iterate cap (N + t)).floor ((U.iterate cap (N + t)).state.root i)
  have hex : ∃ t, P t := U.exists_generation_all_intervalMax_ge cap N X
  generalize htdef : Nat.find hex = t
  have ht : P t := htdef ▸ Nat.find_spec hex
  cases t with
  | zero =>
      refine ⟨N, le_rfl, fun i => ?_⟩
      have ht' : ∀ i : (U.iterate cap N).state.Label,
          X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
            (U.iterate cap N).floor ((U.iterate cap N).state.root i) := by
        simpa only [P, Nat.add_zero] using ht
      exact False.elim (not_lt_of_ge (ht' i) (hstart i))
  | succ k =>
      have hnot : ¬ P k := Nat.find_min hex (by omega)
      dsimp only [P] at hnot
      push Not at hnot
      obtain ⟨j, hj⟩ := hnot
      refine ⟨N + k + 1, by omega, fun i => ?_⟩
      have ht' : ∀ i : (U.iterate cap (N + k + 1)).state.Label,
          X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
            (U.iterate cap (N + k + 1)).floor
            ((U.iterate cap (N + k + 1)).state.root i) := by
        simpa only [P, Nat.succ_eq_add_one, Nat.add_assoc] using ht
      exact ⟨(U.iterate_eventual_all_parent_overlap he cap hc
        (N + k) (by omega) i j).trans hj, ht' i⟩

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
