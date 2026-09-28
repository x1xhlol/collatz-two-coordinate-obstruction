import Erdos1135.Tao.Probability.LogWindowSourceIndex
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Finite Lower Bounds for Odd Logarithmic Windows

This module contains source-index and harmonic-mass facts only.  It has no
residue PMF, `ZMod`, Section 5 schedule, or real-power endpoint argument.
-/

namespace Erdos1135
namespace Tao

open scoped BigOperators

/-- A positive odd-value window is an inclusive interval of source indices. -/
theorem oddLogSourceIndexWindow_eq_Icc {lo hi : ℕ}
    (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) :
    oddLogSourceIndexWindow lo hi =
      Finset.Icc (lo / 2) ((hi - 1) / 2) := by
  ext i
  rw [oddLogSourceIndexWindow_mem_bounds, Finset.mem_Icc]
  change (lo ≤ 2 * i + 1 ∧ 2 * i + 1 ≤ hi) ↔
    lo / 2 ≤ i ∧ i ≤ (hi - 1) / 2
  omega

/-- The source-index weight is the reciprocal of its represented odd value. -/
theorem logNatWeight_oddLogSourceIndexToValue (i : ℕ) :
    logNatWeight (oddLogSourceIndexToValue i) =
      1 / ((2 * i + 1 : ℕ) : ℝ) := by
  simp [logNatWeight, logWeight, oddLogSourceIndexToValue]

theorem oddLogSourceIndexWeight_nonneg (i : ℕ) :
    0 ≤ logNatWeight (oddLogSourceIndexToValue i) :=
  logNatWeight_nonneg _

theorem oddLogSourceIndexWeight_antitone :
    Antitone fun i : ℕ => logNatWeight (oddLogSourceIndexToValue i) := by
  intro i j hij
  change logNatWeight (oddLogSourceIndexToValue j) ≤
    logNatWeight (oddLogSourceIndexToValue i)
  rw [logNatWeight_oddLogSourceIndexToValue,
    logNatWeight_oddLogSourceIndexToValue]
  gcongr

/-- The first source-index weight is bounded by the reciprocal lower endpoint. -/
theorem oddLogSourceIndexWeight_lo_div_two_le {lo : ℕ} (hlo : 1 ≤ lo) :
    logNatWeight (oddLogSourceIndexToValue (lo / 2)) ≤ 1 / (lo : ℝ) := by
  rw [logNatWeight_oddLogSourceIndexToValue]
  gcongr
  exact_mod_cast (show lo ≤ 2 * (lo / 2) + 1 by omega)

/-- Summing source-index weights recovers the odd-value logarithmic mass. -/
theorem sum_oddLogSourceIndexWeight_eq_logFinsetMass {lo hi : ℕ}
    (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) :
    (∑ i ∈ Finset.Icc (lo / 2) ((hi - 1) / 2),
        logNatWeight (oddLogSourceIndexToValue i)) =
      logFinsetMass (oddLogWindow lo hi) := by
  rw [← oddLogSourceIndexWindow_eq_Icc hlo hlohi]
  calc
    (∑ i ∈ oddLogSourceIndexWindow lo hi,
        logNatWeight (oddLogSourceIndexToValue i)) =
        ∑ i : {i : ℕ // i ∈ oddLogSourceIndexWindow lo hi},
          logNatWeight (oddLogSourceIndexToValue i.1) := by
            rw [show (Finset.univ :
                Finset {i : ℕ // i ∈ oddLogSourceIndexWindow lo hi}) =
              (oddLogSourceIndexWindow lo hi).attach by
                exact Finset.univ_eq_attach _]
            exact (Finset.sum_attach _ _).symm
    _ = ∑ m : {m : ℕ // m ∈ oddLogWindow lo hi},
          logNatWeight m.1 := by
            exact Fintype.sum_equiv (oddLogSourceIndexValueEquiv lo hi)
              (fun i : {i : ℕ // i ∈ oddLogSourceIndexWindow lo hi} =>
                logNatWeight (oddLogSourceIndexToValue i.1))
              (fun m : {m : ℕ // m ∈ oddLogWindow lo hi} =>
                logNatWeight m.1)
              (by intro i; rfl)
    _ = logFinsetMass (oddLogWindow lo hi) := by
          rw [show (Finset.univ :
              Finset {m : ℕ // m ∈ oddLogWindow lo hi}) =
            (oddLogWindow lo hi).attach by
              exact Finset.univ_eq_attach _]
          unfold logFinsetMass
          exact Finset.sum_attach _ _

/-- Every source-index weight in the core interval ending at `lo - 1` is at
least `1/(2*lo)`. -/
private theorem one_div_two_mul_lo_le_oddLogSourceIndexWeight
    {lo i : ℕ} (hlo : 1 ≤ lo) (hi : i ≤ lo - 1) :
    1 / (2 * (lo : ℝ)) ≤
      logNatWeight (oddLogSourceIndexToValue i) := by
  rw [logNatWeight_oddLogSourceIndexToValue]
  exact one_div_le_one_div_of_le (by positivity) (by
    exact_mod_cast (show 2 * i + 1 ≤ 2 * lo by omega))

/-- A factor-two odd window has at least one quarter of logarithmic mass. -/
theorem one_fourth_le_logFinsetMass_oddLogWindow
    {lo hi : ℕ} (hlo : 1 ≤ lo) (hwidth : 2 * lo ≤ hi) :
    (1 / 4 : ℝ) ≤ logFinsetMass (oddLogWindow lo hi) := by
  let core := Finset.Icc (lo / 2) (lo - 1)
  let full := Finset.Icc (lo / 2) ((hi - 1) / 2)
  let w : ℕ → ℝ := fun i => logNatWeight (oddLogSourceIndexToValue i)
  have hlohi : lo ≤ hi := by omega
  have hcoreFull : core ⊆ full := by
    dsimp [core, full]
    exact Finset.Icc_subset_Icc le_rfl (by omega)
  have hsumCoreFull : (∑ i ∈ core, w i) ≤ ∑ i ∈ full, w i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hcoreFull
      (fun i _hiFull _hiCore => oddLogSourceIndexWeight_nonneg i)
  have hterm :
      (∑ _i ∈ core, 1 / (2 * (lo : ℝ))) ≤ ∑ i ∈ core, w i := by
    exact Finset.sum_le_sum fun i hiCore => by
      exact one_div_two_mul_lo_le_oddLogSourceIndexWeight hlo
        ((Finset.mem_Icc.mp hiCore).2)
  have hcard : core.card = lo - lo / 2 := by
    dsimp [core]
    simp [Nat.card_Icc]
    omega
  have hcardNat : lo ≤ 2 * core.card := by
    rw [hcard]
    omega
  have hcardReal : (lo : ℝ) ≤ 2 * (core.card : ℝ) := by
    exact_mod_cast hcardNat
  have hloReal : (0 : ℝ) < lo := by exact_mod_cast hlo
  have hnormalize :
      (lo : ℝ) * (1 / (2 * (lo : ℝ))) = 1 / 2 := by
    field_simp
  have hmul := mul_le_mul_of_nonneg_right hcardReal
    (by positivity : 0 ≤ (1 / (2 * (lo : ℝ))))
  rw [hnormalize] at hmul
  have hquarter :
      (1 / 4 : ℝ) ≤ (core.card : ℝ) * (1 / (2 * (lo : ℝ))) := by
    nlinarith
  rw [← sum_oddLogSourceIndexWeight_eq_logFinsetMass hlo hlohi]
  change (1 / 4 : ℝ) ≤ ∑ i ∈ full, w i
  calc
    (1 / 4 : ℝ) ≤ (core.card : ℝ) * (1 / (2 * (lo : ℝ))) := hquarter
    _ = ∑ _i ∈ core, 1 / (2 * (lo : ℝ)) := by simp
    _ ≤ ∑ i ∈ core, w i := hterm
    _ ≤ ∑ i ∈ full, w i := hsumCoreFull

theorem logFinsetMass_oddLogWindow_pos_of_two_mul_le
    {lo hi : ℕ} (hlo : 1 ≤ lo) (hwidth : 2 * lo ≤ hi) :
    0 < logFinsetMass (oddLogWindow lo hi) := by
  linarith [one_fourth_le_logFinsetMass_oddLogWindow hlo hwidth]

example :
    (1 / 4 : ℝ) ≤ logFinsetMass (oddLogWindow 1 2) := by
  exact one_fourth_le_logFinsetMass_oddLogWindow (by norm_num) (by norm_num)

example :
    (1 / 4 : ℝ) ≤ logFinsetMass (oddLogWindow 2 4) := by
  exact one_fourth_le_logFinsetMass_oddLogWindow (by norm_num) (by norm_num)

example :
    (1 / 4 : ℝ) ≤ logFinsetMass (oddLogWindow 3 6) := by
  exact one_fourth_le_logFinsetMass_oddLogWindow (by norm_num) (by norm_num)

end Tao
end Erdos1135
