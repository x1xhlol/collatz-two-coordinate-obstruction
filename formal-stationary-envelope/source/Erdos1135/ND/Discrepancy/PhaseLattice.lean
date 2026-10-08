import Erdos1135.ND.Discrepancy.PhaseToDbar
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A5 Open-Lattice Prefix Certificate

This file isolates the literal three-level lattice count in the frozen v10
A5 phase profile.  Its centered prefix sum is one weak empirical endpoint
error, including at exact lattice widths where the atom at phase zero is
load-bearing.
-/

open scoped BigOperators
open AddCircle

namespace Erdos1135
namespace ND

/-- The real-valued cardinality of the open A5 lattice slice
`(log 2) * (ℤ + 1 - t) ∩ (0,b)`.  For `0 ≤ b ≤ 2` and `t ∈ [0,1)`,
only the three displayed integer cells can contribute. -/
noncomputable def ndA5OpenLatticeCount (b t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 3,
    if 0 < ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) ∧
        ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) < b
    then 1 else 0

private theorem ndA5OpenLatticeCount_zero (t : ℝ) :
    ndA5OpenLatticeCount 0 t = 0 := by
  classical
  unfold ndA5OpenLatticeCount
  apply Finset.sum_eq_zero
  intro k hk
  split_ifs with h
  · linarith
  · rfl

private theorem sum_tailIndicator_sub_eq_neg_mul_weakError
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) (hN : 0 < N) :
    (∑ n ∈ Finset.range N,
      ((if t < ndUnitRep (x n) then (1 : ℝ) else 0) - (1 - t))) =
      -(N : ℝ) * ndWeakEmpiricalError N x t := by
  classical
  have hNr : (N : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hN)
  have htail :
      (∑ n ∈ Finset.range N,
        if t < ndUnitRep (x n) then (1 : ℝ) else 0) =
        (N : ℝ) -
          (((((Finset.range N).filter
            (fun n => ndUnitRep (x n) ≤ t)).card : ℕ) : ℝ)) := by
    calc
      (∑ n ∈ Finset.range N,
          if t < ndUnitRep (x n) then (1 : ℝ) else 0) =
          ∑ n ∈ Finset.range N,
            (1 - if ndUnitRep (x n) ≤ t then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        by_cases h : t < ndUnitRep (x n)
        · simp [h, not_le.mpr h]
        · simp [h, le_of_not_gt h]
      _ = (∑ _n ∈ Finset.range N, (1 : ℝ)) -
          ∑ n ∈ Finset.range N,
            if ndUnitRep (x n) ≤ t then (1 : ℝ) else 0 := by
        rw [Finset.sum_sub_distrib]
      _ = (N : ℝ) -
          (((((Finset.range N).filter
            (fun n => ndUnitRep (x n) ≤ t)).card : ℕ) : ℝ)) := by
        simp
  unfold ndWeakEmpiricalError ndWeakEmpiricalCDF
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [htail]
  field_simp
  ring

private theorem abs_sum_tailIndicator_sub_le
    (N : ℕ) (x : ℕ → UnitAddCircle) (D t : ℝ)
    (hN : 0 < N) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hdisc : ndStrictWeakEndpointDiscrepancyLE N x D) :
    |∑ n ∈ Finset.range N,
      ((if t < ndUnitRep (x n) then (1 : ℝ) else 0) - (1 - t))| ≤
      (N : ℝ) * D := by
  rw [sum_tailIndicator_sub_eq_neg_mul_weakError N x t hN,
    abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg N)]
  exact mul_le_mul_of_nonneg_left (hdisc t ht).2 (Nat.cast_nonneg N)

private theorem ndA5OpenLatticeCount_eq_three_tails
    (b t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    ndA5OpenLatticeCount b t =
      (if 1 - b / Real.log 2 < t then 1 else 0) +
      (if 2 - b / Real.log 2 < t then 1 else 0) +
      (if 3 - b / Real.log 2 < t then 1 else 0) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp (K : ℝ) (hK : 1 ≤ K) :
      (0 < (K - t) * Real.log 2 ∧ (K - t) * Real.log 2 < b) ↔
        K - b / Real.log 2 < t := by
    have hKt : 0 < K - t := sub_pos.mpr (ht.2.trans_le hK)
    constructor
    · rintro ⟨hlower, hupper⟩
      have hdiv : K - t < b / Real.log 2 :=
        (lt_div_iff₀ hlog).2 hupper
      linarith
    · intro hthreshold
      constructor
      · exact mul_pos hKt hlog
      · apply (lt_div_iff₀ hlog).1
        linarith
  simp only [ndA5OpenLatticeCount, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, zero_add]
  simp only [hp 1 (by norm_num), hp 2 (by norm_num),
    hp 3 (by norm_num)]

/-- The literal open-lattice profile has a coefficient-one prefix bound.
The hypothesis deliberately retains the checked strict/weak endpoint pair;
the proof consumes its weak half at the unique active threshold. -/
theorem abs_sum_ndA5OpenLatticeCount_centered_le
    (N : ℕ) (x : ℕ → UnitAddCircle) (D b : ℝ)
    (hN : 0 < N) (hb : b ∈ Set.Icc (0 : ℝ) 2)
    (hdisc : ndStrictWeakEndpointDiscrepancyLE N x D) :
    |∑ n ∈ Finset.range N,
      (ndA5OpenLatticeCount b (ndUnitRep (x n)) -
        b / Real.log 2)| ≤
      (N : ℝ) * D := by
  classical
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo_lt_three_log : (2 : ℝ) < 3 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hb_lt_three_log : b < 3 * Real.log 2 :=
    hb.2.trans_lt htwo_lt_three_log
  by_cases hb_zero : b = 0
  · subst b
    have hD : 0 ≤ D :=
      (abs_nonneg (ndWeakEmpiricalError N x 0)).trans
        ((hdisc 0 (by norm_num)).2)
    simp only [ndA5OpenLatticeCount_zero, zero_div, sub_zero,
      Finset.sum_const_zero, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg N) hD
  · by_cases hb_log : b ≤ Real.log 2
    · let t : ℝ := 1 - b / Real.log 2
      have hratio_nonneg : 0 ≤ b / Real.log 2 :=
        div_nonneg hb.1 hlog.le
      have hratio_le : b / Real.log 2 ≤ 1 := by
        apply (div_le_iff₀ hlog).2
        simpa using hb_log
      have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
        dsimp [t]
        constructor <;> linarith
      have hsum :
          (∑ n ∈ Finset.range N,
            (ndA5OpenLatticeCount b (ndUnitRep (x n)) -
              b / Real.log 2)) =
          ∑ n ∈ Finset.range N,
            ((if t < ndUnitRep (x n) then (1 : ℝ) else 0) -
              (1 - t)) := by
        apply Finset.sum_congr rfl
        intro n hn
        rcases ndUnitRep_mem_Ico (x n) with ⟨hrep0, hrep1⟩
        have h2 : ¬(2 - b / Real.log 2 < ndUnitRep (x n)) := by
          linarith
        have h3 : ¬(3 - b / Real.log 2 < ndUnitRep (x n)) := by
          linarith
        rw [ndA5OpenLatticeCount_eq_three_tails b
          (ndUnitRep (x n)) ⟨hrep0, hrep1⟩]
        simp only [h2, h3, if_false, add_zero]
        dsimp [t]
        ring
      rw [hsum]
      exact abs_sum_tailIndicator_sub_le N x D t hN ht hdisc
    · have hlog_lt_b : Real.log 2 < b := lt_of_not_ge hb_log
      by_cases hb_two_log : b ≤ 2 * Real.log 2
      · let t : ℝ := 2 - b / Real.log 2
        have hratio_lt : 1 < b / Real.log 2 := by
          apply (lt_div_iff₀ hlog).2
          simpa using hlog_lt_b
        have hratio_le : b / Real.log 2 ≤ 2 := by
          apply (div_le_iff₀ hlog).2
          simpa using hb_two_log
        have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
          dsimp [t]
          constructor <;> linarith
        have hsum :
            (∑ n ∈ Finset.range N,
              (ndA5OpenLatticeCount b (ndUnitRep (x n)) -
                b / Real.log 2)) =
            ∑ n ∈ Finset.range N,
              ((if t < ndUnitRep (x n) then (1 : ℝ) else 0) -
                (1 - t)) := by
          apply Finset.sum_congr rfl
          intro n hn
          rcases ndUnitRep_mem_Ico (x n) with ⟨hrep0, hrep1⟩
          have h1 : 1 - b / Real.log 2 < ndUnitRep (x n) := by
            linarith
          have h3 : ¬(3 - b / Real.log 2 < ndUnitRep (x n)) := by
            linarith
          rw [ndA5OpenLatticeCount_eq_three_tails b
            (ndUnitRep (x n)) ⟨hrep0, hrep1⟩]
          simp only [h1, h3, if_true, if_false, add_zero]
          dsimp [t]
          ring
        rw [hsum]
        exact abs_sum_tailIndicator_sub_le N x D t hN ht hdisc
      · have htwo_log_lt_b : 2 * Real.log 2 < b :=
          lt_of_not_ge hb_two_log
        let t : ℝ := 3 - b / Real.log 2
        have hratio_lt : 2 < b / Real.log 2 := by
          apply (lt_div_iff₀ hlog).2
          simpa using htwo_log_lt_b
        have hratio_lt_three : b / Real.log 2 < 3 := by
          apply (div_lt_iff₀ hlog).2
          simpa using hb_lt_three_log
        have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
          dsimp [t]
          constructor <;> linarith
        have hsum :
            (∑ n ∈ Finset.range N,
              (ndA5OpenLatticeCount b (ndUnitRep (x n)) -
                b / Real.log 2)) =
            ∑ n ∈ Finset.range N,
              ((if t < ndUnitRep (x n) then (1 : ℝ) else 0) -
                (1 - t)) := by
          apply Finset.sum_congr rfl
          intro n hn
          rcases ndUnitRep_mem_Ico (x n) with ⟨hrep0, hrep1⟩
          have h1 : 1 - b / Real.log 2 < ndUnitRep (x n) := by
            linarith
          have h2 : 2 - b / Real.log 2 < ndUnitRep (x n) := by
            linarith
          rw [ndA5OpenLatticeCount_eq_three_tails b
            (ndUnitRep (x n)) ⟨hrep0, hrep1⟩]
          simp only [h1, h2, if_true]
          dsimp [t]
          ring
        rw [hsum]
        exact abs_sum_tailIndicator_sub_le N x D t hN ht hdisc

/-- The checked phase-gap endpoint socket supplies the A5 lattice prefix
bound at every positive length and every additive-circle anchor. -/
theorem abs_sum_ndA5OpenLatticeCount_ndPhaseOrbit_le_endpointDbar
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (phi : UnitAddCircle) (b : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 2)
    (N : ℕ) (hN : 0 < N) :
    |∑ n ∈ Finset.range N,
      (ndA5OpenLatticeCount b
          (ndUnitRep (ndPhaseOrbit phi n)) -
        b / Real.log 2)| ≤
      (N : ℝ) * ndEndpointDbar c kappa N := by
  exact abs_sum_ndA5OpenLatticeCount_centered_le N
    (ndPhaseOrbit phi) (ndEndpointDbar c kappa N) b hN hb
    (ndPhaseOrbit_strictWeakEndpointDiscrepancyLE hPhase phi N hN)

end ND
end Erdos1135
