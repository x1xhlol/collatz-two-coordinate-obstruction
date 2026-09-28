/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.SuccessfulRootTernaryResidueCoverage

namespace Erdos1135Predecessor.ND.PositiveDensity

noncomputable section

@[irreducible] def explicitOnePeriodSuccessfulRootBound (b q : ℕ) : ℕ :=
  4 ^ (2 * b + 1 + 3 ^ q)

theorem explicitOnePeriodSuccessfulRootBound_pos (b q : ℕ) :
    0 < explicitOnePeriodSuccessfulRootBound b q := by
  unfold explicitOnePeriodSuccessfulRootBound
  positivity

theorem exists_onePeriod_bounded_oneStepSuccessful_root_in_residue
    (q b : ℕ) (hb : 1 ≤ b) (r : Fin (3 ^ q)) :
    ∃ M : ℕ, 16 ^ b < M ∧ M < explicitOnePeriodSuccessfulRootBound b q ∧
      Odd M ∧ Tao.syracuse M = 1 ∧ M % 3 ^ q = r := by
  obtain ⟨t, ht⟩ := ndCollapseSource_residue_surjective q r
  let Q := 3 ^ q
  let h := 2 * b + 1
  let v := h / Q + if (t : ℕ) < h % Q then 1 else 0
  let k := (t : ℕ) + v * Q
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have htQ : (t : ℕ) < Q := t.isLt
  have hs : h % Q < Q := Nat.mod_lt h hQ
  have hdiv : h % Q + (h / Q) * Q = h := by
    simpa only [Nat.mul_comm] using Nat.mod_add_div h Q
  have hwindow : h ≤ k ∧ k < h + Q := by
    dsimp [k, v]
    split_ifs with hts <;> simp only [Nat.add_mul, Nat.one_mul, Nat.zero_mul, Nat.add_zero] <;> omega
  have hklo : 2 * b + 1 ≤ k := hwindow.1
  have hkhi : k < 2 * b + 1 + 3 ^ q := hwindow.2
  have hmod : Nat.ModEq (3 ^ q) (ndA5PreviousPhysicalCollapseSource t)
      (ndA5PreviousPhysicalCollapseSource k) :=
    (ndCollapseSource_modEq_of_add_iff q t (v * Q)).2 (Nat.dvd_mul_left _ _)
  have hr : ndA5PreviousPhysicalCollapseSource k % 3 ^ q = r := by
    change ndA5PreviousPhysicalCollapseSource t % 3 ^ q =
      ndA5PreviousPhysicalCollapseSource k % 3 ^ q at hmod
    exact hmod.symm.trans (congrArg Fin.val ht)
  have he := three_mul_ndA5PreviousPhysicalCollapseSource_add_one k
  have hbpow : 16 ≤ 16 ^ b := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 1 ≤ 16) hb
  have hkpow := Nat.pow_le_pow_right (by decide : 1 ≤ 4) hklo
  have hpowid : 4 ^ (2 * b + 1) = 4 * 16 ^ b := by
    rw [pow_add, pow_mul]
    norm_num
    ring
  rw [hpowid] at hkpow
  have hlo : 16 ^ b < ndA5PreviousPhysicalCollapseSource k := by nlinarith
  have hhi : ndA5PreviousPhysicalCollapseSource k < explicitOnePeriodSuccessfulRootBound b q := by
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 4) hkhi.le
    unfold explicitOnePeriodSuccessfulRootBound
    nlinarith
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  refine ⟨ndA5PreviousPhysicalCollapseSource k, hlo, hhi, ?_, ?_, hr⟩
  · rw [hj]
    exact ndA5PreviousPhysicalCollapseSource_odd j
  · rw [hj]
    exact syracuse_ndA5PreviousPhysicalCollapseSource_succ j

theorem exists_onePeriod_bounded_logTimeSuccessful_root_in_residue
    (q b : ℕ) (hb : 1 ≤ b) (r : Fin (3 ^ q)) {C : ℝ} (hC : 1 ≤ C) :
    ∃ M : ℕ, 16 ^ b < M ∧ M < explicitOnePeriodSuccessfulRootBound b q ∧
      M ∈ oddSyracuseLogTimeOneSet C ∧ Tao.syracuse M = 1 ∧ M % 3 ^ q = r := by
  obtain ⟨M, hM, hMb, hodd, hhit, hr⟩ :=
    exists_onePeriod_bounded_oneStepSuccessful_root_in_residue q b hb r
  have hbpow : 16 ≤ 16 ^ b := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 1 ≤ 16) hb
  have h16 : (16 : ℝ) ≤ M := by exact_mod_cast hbpow.trans hM.le
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 16) h16
  have hlog : (1 : ℝ) ≤ Real.log (M : ℝ) := by
    have htwo := Real.log_two_gt_d9
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    linarith
  have hc : (1 : ℝ) ≤ C * Real.log (M : ℝ) :=
    hlog.trans (by simpa using mul_le_mul_of_nonneg_right hC (by linarith : 0 ≤ Real.log (M : ℝ)))
  exact ⟨M, hM, hMb, ⟨hodd.pos, hodd, 1, by simpa using hc, by simpa using hhit⟩, hhit, hr⟩

end

end Erdos1135Predecessor.ND.PositiveDensity
