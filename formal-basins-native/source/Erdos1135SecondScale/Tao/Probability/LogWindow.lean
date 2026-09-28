/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Density.LogDensity

/-!
# Finite Logarithmic Window Probabilities

This module records finite source-window logarithmic weights as real ratios.
It deliberately stays separate from ambient prefix logarithmic density and does
not yet construct a PMF wrapper.
-/

namespace Erdos1135SecondScale
namespace Tao

open scoped BigOperators

/-- Logarithmic source weight for a natural number, with zero assigned no mass. -/
noncomputable def logNatWeight (n : ℕ) : ℝ :=
  if n = 0 then 0 else logWeight (n - 1)

/-- Total logarithmic mass of a finite set of natural numbers. -/
noncomputable def logFinsetMass (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, logNatWeight n

/-- Normalized logarithmic mass of an event inside a finite support set. -/
noncomputable def logFinsetProb (S : Finset ℕ) (E : Set ℕ) : ℝ := by
  classical
  exact (∑ n ∈ S.filter (fun n => n ∈ E), logNatWeight n) / logFinsetMass S

/-- Inclusive finite odd window `[lo, hi]`. -/
def oddLogWindow (lo hi : ℕ) : Finset ℕ :=
  (Finset.Icc lo hi).filter (fun n => n % 2 = 1)

@[simp]
theorem logNatWeight_zero : logNatWeight 0 = 0 := by
  simp [logNatWeight]

@[simp]
theorem logNatWeight_succ (i : ℕ) : logNatWeight (i + 1) = logWeight i := by
  simp [logNatWeight]

theorem logNatWeight_nonneg (n : ℕ) : 0 ≤ logNatWeight n := by
  cases n with
  | zero => simp
  | succ i => simpa using logWeight_nonneg i

theorem logNatWeight_pos_of_pos {n : ℕ} (hn : 0 < n) :
    0 < logNatWeight n := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨i, rfl⟩
  simpa using logWeight_pos i

theorem logFinsetMass_nonneg (S : Finset ℕ) :
    0 ≤ logFinsetMass S := by
  unfold logFinsetMass
  exact Finset.sum_nonneg fun n _hn => logNatWeight_nonneg n

theorem logFinsetMass_pos_of_mem_pos {S : Finset ℕ} {n : ℕ}
    (hnS : n ∈ S) (hnpos : 0 < n) :
    0 < logFinsetMass S := by
  unfold logFinsetMass
  exact Finset.sum_pos'
    (fun m _hm => logNatWeight_nonneg m)
    ⟨n, hnS, logNatWeight_pos_of_pos hnpos⟩

theorem logFinsetProb_univ {S : Finset ℕ}
    (hmass : 0 < logFinsetMass S) :
    logFinsetProb S Set.univ = 1 := by
  classical
  simp [logFinsetProb]
  change logFinsetMass S / logFinsetMass S = 1
  exact div_self hmass.ne'

theorem logFinsetProb_empty (S : Finset ℕ) :
    logFinsetProb S ∅ = 0 := by
  classical
  simp [logFinsetProb]

theorem logFinsetProb_nonneg (S : Finset ℕ) (E : Set ℕ) :
    0 ≤ logFinsetProb S E := by
  classical
  unfold logFinsetProb
  exact div_nonneg
    (Finset.sum_nonneg fun n _hn => logNatWeight_nonneg n)
    (logFinsetMass_nonneg S)

theorem logFinsetProb_le_one {S : Finset ℕ} {E : Set ℕ}
    (hmass : 0 < logFinsetMass S) :
    logFinsetProb S E ≤ 1 := by
  classical
  have hnum_le :
      (∑ n ∈ S.filter (fun n => n ∈ E), logNatWeight n) ≤
        logFinsetMass S := by
    unfold logFinsetMass
    rw [Finset.sum_filter]
    exact Finset.sum_le_sum fun n _hn => by
      by_cases hnE : n ∈ E
      · simp [hnE]
      · simp [hnE, logNatWeight_nonneg n]
  have hdiv := div_le_div_of_nonneg_right hnum_le hmass.le
  simpa [logFinsetProb, hmass.ne'] using hdiv

theorem oddLogWindow_mem {lo hi n : ℕ} :
    n ∈ oddLogWindow lo hi ↔ lo ≤ n ∧ n ≤ hi ∧ n % 2 = 1 := by
  simp [oddLogWindow, and_assoc]

end Tao
end Erdos1135SecondScale
