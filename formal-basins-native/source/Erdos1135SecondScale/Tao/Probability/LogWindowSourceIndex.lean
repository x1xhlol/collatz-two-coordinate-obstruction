/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.LogWindowPMF

/-!
# Source-Index Logarithmic Windows

This module bridges Tao's source-index convention `N ↦ 2 * N + 1` with the
odd-value logarithmic windows from `Probability.LogWindowPMF`.  It keeps
real-power endpoint choices for `N_y` out of this finite integer adapter.
-/

namespace Erdos1135SecondScale
namespace Tao

open scoped BigOperators

/-- Odd value represented by a source index. -/
def oddLogSourceIndexToValue (n : ℕ) : ℕ :=
  2 * n + 1

/-- Source index represented by an odd positive value. -/
def oddLogSourceIndexOfValue (m : ℕ) : ℕ :=
  (m - 1) / 2

/-- Source indices whose odd values lie in the inclusive odd window `[lo, hi]`. -/
def oddLogSourceIndexWindow (lo hi : ℕ) : Finset ℕ :=
  (Finset.range (hi + 1)).filter fun n => oddLogSourceIndexToValue n ∈ oddLogWindow lo hi

theorem oddLogSourceIndexToValue_mod_two (n : ℕ) :
    oddLogSourceIndexToValue n % 2 = 1 := by
  unfold oddLogSourceIndexToValue
  omega

theorem oddLogSourceIndexOfValue_oddLogSourceIndexToValue (n : ℕ) :
    oddLogSourceIndexOfValue (oddLogSourceIndexToValue n) = n := by
  unfold oddLogSourceIndexOfValue oddLogSourceIndexToValue
  omega

theorem oddLogSourceIndexToValue_oddLogSourceIndexOfValue {m : ℕ} (hm : m % 2 = 1) :
    oddLogSourceIndexToValue (oddLogSourceIndexOfValue m) = m := by
  unfold oddLogSourceIndexToValue oddLogSourceIndexOfValue
  have hdecomp := Nat.div_add_mod m 2
  omega

theorem oddLogSourceIndexWindow_mem {lo hi n : ℕ} :
    n ∈ oddLogSourceIndexWindow lo hi ↔ oddLogSourceIndexToValue n ∈ oddLogWindow lo hi := by
  rw [oddLogSourceIndexWindow, Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    exact h.2
  · intro h
    have hhi : oddLogSourceIndexToValue n ≤ hi := (oddLogWindow_mem.mp h).2.1
    exact ⟨by unfold oddLogSourceIndexToValue at hhi; omega, h⟩

theorem oddLogSourceIndexWindow_mem_bounds {lo hi n : ℕ} :
    n ∈ oddLogSourceIndexWindow lo hi ↔
      lo ≤ oddLogSourceIndexToValue n ∧ oddLogSourceIndexToValue n ≤ hi := by
  rw [oddLogSourceIndexWindow_mem, oddLogWindow_mem]
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · intro h
    exact ⟨h.1, h.2, oddLogSourceIndexToValue_mod_two n⟩

/-- Equivalence between source indices and odd values inside the same finite window. -/
noncomputable def oddLogSourceIndexValueEquiv (lo hi : ℕ) :
    {n : ℕ // n ∈ oddLogSourceIndexWindow lo hi} ≃
      {m : ℕ // m ∈ oddLogWindow lo hi} where
  toFun n := ⟨oddLogSourceIndexToValue n.1, oddLogSourceIndexWindow_mem.mp n.2⟩
  invFun m := ⟨oddLogSourceIndexOfValue m.1, by
    rw [oddLogSourceIndexWindow_mem]
    have hodd : m.1 % 2 = 1 := (oddLogWindow_mem.mp m.2).2.2
    simp [oddLogSourceIndexToValue_oddLogSourceIndexOfValue hodd, m.2]⟩
  left_inv n := by
    apply Subtype.ext
    exact oddLogSourceIndexOfValue_oddLogSourceIndexToValue n.1
  right_inv m := by
    apply Subtype.ext
    have hodd : m.1 % 2 = 1 := (oddLogWindow_mem.mp m.2).2.2
    exact oddLogSourceIndexToValue_oddLogSourceIndexOfValue hodd

theorem oddLogSourceIndexValueEquiv_apply {lo hi : ℕ}
    (n : {n : ℕ // n ∈ oddLogSourceIndexWindow lo hi}) :
    ((oddLogSourceIndexValueEquiv lo hi n : {m : ℕ // m ∈ oddLogWindow lo hi}) : ℕ) =
      oddLogSourceIndexToValue n.1 := rfl

theorem oddLogSourceIndexValueEquiv_symm_apply {lo hi : ℕ}
    (m : {m : ℕ // m ∈ oddLogWindow lo hi}) :
    (((oddLogSourceIndexValueEquiv lo hi).symm m :
      {n : ℕ // n ∈ oddLogSourceIndexWindow lo hi}) : ℕ) =
      oddLogSourceIndexOfValue m.1 := rfl

/-- Source-index logarithmic PMF with weights inherited from the represented odd values. -/
noncomputable def oddLogSourceIndexPMF (lo hi : ℕ)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) :
    PMF {n : ℕ // n ∈ oddLogSourceIndexWindow lo hi} :=
  PMF.ofFintype
    (fun n : {n : ℕ // n ∈ oddLogSourceIndexWindow lo hi} =>
      ENNReal.ofReal
        (logNatWeight (oddLogSourceIndexToValue n.1) / logFinsetMass (oddLogWindow lo hi)))
    (by
      classical
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · have hsum_value :
            (∑ m : {m : ℕ // m ∈ oddLogWindow lo hi}, logNatWeight m.1) =
              logFinsetMass (oddLogWindow lo hi) := by
          rw [show (Finset.univ : Finset {m : ℕ // m ∈ oddLogWindow lo hi}) =
              (oddLogWindow lo hi).attach by
            exact Finset.univ_eq_attach (oddLogWindow lo hi)]
          unfold logFinsetMass
          exact Finset.sum_attach (oddLogWindow lo hi) (fun m => logNatWeight m)
        have hsum_index :
            (∑ n : {n : ℕ // n ∈ oddLogSourceIndexWindow lo hi},
              logNatWeight (oddLogSourceIndexToValue n.1)) =
                logFinsetMass (oddLogWindow lo hi) := by
          have hsum_equiv :
              (∑ n : {n : ℕ // n ∈ oddLogSourceIndexWindow lo hi},
                logNatWeight (oddLogSourceIndexToValue n.1)) =
                  ∑ m : {m : ℕ // m ∈ oddLogWindow lo hi},
                    logNatWeight m.1 := by
            exact Fintype.sum_equiv (oddLogSourceIndexValueEquiv lo hi)
              (fun n : {n : ℕ // n ∈ oddLogSourceIndexWindow lo hi} =>
                logNatWeight (oddLogSourceIndexToValue n.1))
              (fun m : {m : ℕ // m ∈ oddLogWindow lo hi} =>
                logNatWeight m.1)
              (by intro n; rfl)
          exact hsum_equiv.trans hsum_value
        have hsum_div :
            (∑ n : {n : ℕ // n ∈ oddLogSourceIndexWindow lo hi},
              logNatWeight (oddLogSourceIndexToValue n.1) /
                logFinsetMass (oddLogWindow lo hi)) = 1 := by
          rw [← Finset.sum_div, hsum_index]
          exact div_self hmass.ne'
        rw [hsum_div]
        norm_num
      · intro n _hn
        exact div_nonneg (logNatWeight_nonneg (oddLogSourceIndexToValue n.1)) hmass.le)

theorem oddLogSourceIndexPMF_apply_toReal {lo hi : ℕ}
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (n : {n : ℕ // n ∈ oddLogSourceIndexWindow lo hi}) :
    (oddLogSourceIndexPMF lo hi hmass n).toReal =
      logNatWeight (oddLogSourceIndexToValue n.1) /
        logFinsetMass (oddLogWindow lo hi) := by
  rw [oddLogSourceIndexPMF, PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal
    (div_nonneg (logNatWeight_nonneg (oddLogSourceIndexToValue n.1)) hmass.le)

theorem oddLogSourceIndexPMF_map_value_apply_toReal {lo hi : ℕ}
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (m : {m : ℕ // m ∈ oddLogWindow lo hi}) :
    (((oddLogSourceIndexPMF lo hi hmass).map
      (oddLogSourceIndexValueEquiv lo hi)) m).toReal =
        logNatWeight m.1 / logFinsetMass (oddLogWindow lo hi) := by
  classical
  rw [PMF.map_apply]
  rw [tsum_eq_single ((oddLogSourceIndexValueEquiv lo hi).symm m)]
  · have hvalue :
        oddLogSourceIndexToValue (((oddLogSourceIndexValueEquiv lo hi).symm m).1) = m.1 := by
      exact congrArg Subtype.val (Equiv.apply_symm_apply (oddLogSourceIndexValueEquiv lo hi) m)
    have hhit :
        m = (oddLogSourceIndexValueEquiv lo hi) ((oddLogSourceIndexValueEquiv lo hi).symm m) :=
      (Equiv.apply_symm_apply (oddLogSourceIndexValueEquiv lo hi) m).symm
    rw [if_pos hhit]
    rw [oddLogSourceIndexPMF_apply_toReal]
    simp [hvalue]
  · intro n hn
    have hne : ¬ m = (oddLogSourceIndexValueEquiv lo hi) n := by
      intro hm
      apply hn
      exact (Equiv.symm_apply_apply (oddLogSourceIndexValueEquiv lo hi) n).symm.trans
        (congrArg (oddLogSourceIndexValueEquiv lo hi).symm hm.symm)
    simp [hne]

theorem oddLogSourceIndexPMF_map_value_toReal_eq_oddLogWindowPMF {lo hi : ℕ}
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (m : {m : ℕ // m ∈ oddLogWindow lo hi}) :
    (((oddLogSourceIndexPMF lo hi hmass).map
      (oddLogSourceIndexValueEquiv lo hi)) m).toReal =
        (oddLogWindowPMF lo hi hmass m).toReal := by
  rw [oddLogSourceIndexPMF_map_value_apply_toReal,
    oddLogWindowPMF_apply_toReal]

theorem oddLogSourceIndexPMF_map_value_eq_oddLogWindowPMF {lo hi : ℕ}
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) :
    (oddLogSourceIndexPMF lo hi hmass).map
        (oddLogSourceIndexValueEquiv lo hi) =
      oddLogWindowPMF lo hi hmass := by
  apply PMF.ext
  intro m
  exact (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ m)
    (PMF.apply_ne_top _ m)).mp
      (oddLogSourceIndexPMF_map_value_toReal_eq_oddLogWindowPMF hmass m)

end Tao
end Erdos1135SecondScale
