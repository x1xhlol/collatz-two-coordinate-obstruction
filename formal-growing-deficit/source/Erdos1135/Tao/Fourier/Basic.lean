import Erdos1135.Tao.Syracuse.Syrac
import Mathlib.Analysis.Fourier.ZMod

set_option backward.isDefEq.respectTransparency false

/-!
# Finite Fourier Conventions For Tao's Syracuse Route

This module fixes the first project-local interface between finite PMFs and
mathlib's `ZMod.dft`.  It only records mass-function normalization at frequency
zero; it does not prove Fourier decay, mixing, renewal, or Proposition 1.9
estimates.
-/

open scoped BigOperators
open scoped ZMod

namespace Erdos1135
namespace Tao

/-- Complex-valued mass function attached to a finite PMF. -/
noncomputable def pmfComplexMass {α : Type*} (p : PMF α) : α → ℂ :=
  fun x => ((p x).toReal : ℂ)

/--
The project forward DFT convention on `ZMod N`: unnormalized, with the paper
character represented by `stdAddChar (-(x * xi))`.
-/
noncomputable def taoForwardDFTKernel {N : ℕ} [NeZero N] (x ξ : ZMod N) : ℂ :=
  ZMod.stdAddChar (-(x * ξ))

/--
Named forward-transform convention for the Tao lane.

This is `ZMod.dft_apply`, restated so Section 6/7 modules can cite one
project-local theorem instead of restating the sign convention.
-/
theorem tao_dft_apply {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (ξ : ZMod N) :
    ZMod.dft Φ ξ = ∑ x : ZMod N, taoForwardDFTKernel x ξ • Φ x := by
  rw [ZMod.dft_apply]
  simp [taoForwardDFTKernel]

/--
The project inverse DFT convention on `ZMod N`: normalized by `(N : ℂ)⁻¹` and
using the positive-sign character `stdAddChar (xi * x)`.
-/
theorem tao_invDFT_apply {N : ℕ} [NeZero N] (Ψ : ZMod N → ℂ) (x : ZMod N) :
    ZMod.dft.symm Ψ x =
      (N : ℂ)⁻¹ • ∑ ξ : ZMod N, ZMod.stdAddChar (ξ * x) • Ψ ξ := by
  rw [ZMod.invDFT_apply]

/-- DFT of a finite PMF mass function in the project convention. -/
theorem tao_dft_pmfComplexMass_apply {N : ℕ} [NeZero N]
    (p : PMF (ZMod N)) (ξ : ZMod N) :
    ZMod.dft (pmfComplexMass p) ξ =
      ∑ x : ZMod N, taoForwardDFTKernel x ξ * (((p x).toReal : ℝ) : ℂ) := by
  rw [tao_dft_apply]
  simp [taoForwardDFTKernel, pmfComplexMass, smul_eq_mul]

theorem dft_pmfComplexMass_apply_zero {N : ℕ} [NeZero N] (p : PMF (ZMod N)) :
    ZMod.dft (pmfComplexMass p) 0 = 1 := by
  rw [ZMod.dft_apply_zero]
  have h : (((∑ j, (p j).toReal) : ℝ) : ℂ) = 1 := by
    rw [pmf_sum_toReal p]
    norm_num
  simpa [pmfComplexMass, Complex.ofReal_sum] using h

/-- Zero frequency remains normalized to `1` under the named project convention. -/
theorem tao_dft_pmfComplexMass_apply_zero {N : ℕ} [NeZero N] (p : PMF (ZMod N)) :
    ZMod.dft (pmfComplexMass p) 0 = 1 :=
  dft_pmfComplexMass_apply_zero p

theorem dft_syracPMF_apply_zero (n : ℕ) :
    ZMod.dft (pmfComplexMass (syracPMF n)) 0 = 1 := by
  simpa using dft_pmfComplexMass_apply_zero (N := 3 ^ n) (syracPMF n)

theorem dft_syracPMF_one_apply_zero :
    ZMod.dft (pmfComplexMass (syracPMF 1)) 0 = 1 := by
  simpa using dft_syracPMF_apply_zero 1

theorem dft_syracPMF_two_apply_zero :
    ZMod.dft (pmfComplexMass (syracPMF 2)) 0 = 1 := by
  simpa using dft_syracPMF_apply_zero 2

private theorem zmod3_univ :
    (Finset.univ : Finset (ZMod (3 ^ 1))) = {0, 1, 2} := by
  ext x
  fin_cases x
  · constructor
    · intro _
      decide
    · intro _
      simp
  · constructor
    · intro _
      decide
    · intro _
      simp
  · constructor
    · intro _
      decide
    · intro _
      simp

private theorem zmod3_sum_eq_sum_three {M : Type*} [AddCommMonoid M]
    (f : ZMod (3 ^ 1) → M) :
    (∑ x : ZMod (3 ^ 1), f x) = f 0 + f 1 + f 2 := by
  rw [zmod3_univ]
  have h01 : (0 : ZMod (3 ^ 1)) ≠ 1 := by decide
  have h02 : (0 : ZMod (3 ^ 1)) ≠ 2 := by decide
  have h12 : (1 : ZMod (3 ^ 1)) ≠ 2 := by decide
  simp [h01, h02, h12]
  rw [add_assoc]

theorem dft_syracPMF_one_apply_table (k : ZMod (3 ^ 1)) :
    ZMod.dft (pmfComplexMass (syracPMF 1)) k =
      ZMod.stdAddChar (-(1 * k)) • (((1 / 3 : ℝ) : ℂ)) +
        ZMod.stdAddChar (-(2 * k)) • (((2 / 3 : ℝ) : ℂ)) := by
  rw [ZMod.dft_apply]
  rw [zmod3_sum_eq_sum_three]
  have h0 : (((syracPMF 1 (0 : ZMod (3 ^ 1))).toReal : ℝ) : ℂ) = 0 := by
    rw [syracPMF_one_apply_zero]
    simp
  have h1 : (((syracPMF 1 (1 : ZMod (3 ^ 1))).toReal : ℝ) : ℂ) =
      ((1 / 3 : ℝ) : ℂ) := by
    rw [syracPMF_one_apply_one]
    rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1 / 3 : ℝ))]
  have h2 : (((syracPMF 1 (2 : ZMod (3 ^ 1))).toReal : ℝ) : ℂ) =
      ((2 / 3 : ℝ) : ℂ) := by
    rw [syracPMF_one_apply_two]
    rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (2 / 3 : ℝ))]
  simp only [pmfComplexMass]
  rw [h0, h1, h2]
  simp

private theorem zmod9_univ :
    (Finset.univ : Finset (ZMod (3 ^ 2))) = {0, 1, 2, 3, 4, 5, 6, 7, 8} := by
  ext x
  fin_cases x <;>
    constructor <;>
      intro _ <;>
        decide

private theorem zmod9_sum_eq_sum_nine {M : Type*} [AddCommMonoid M]
    (f : ZMod (3 ^ 2) → M) :
    (∑ x : ZMod (3 ^ 2), f x) =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  rw [zmod9_univ]
  have h01 : (0 : ZMod (3 ^ 2)) ≠ 1 := by decide
  have h02 : (0 : ZMod (3 ^ 2)) ≠ 2 := by decide
  have h03 : (0 : ZMod (3 ^ 2)) ≠ 3 := by decide
  have h04 : (0 : ZMod (3 ^ 2)) ≠ 4 := by decide
  have h05 : (0 : ZMod (3 ^ 2)) ≠ 5 := by decide
  have h06 : (0 : ZMod (3 ^ 2)) ≠ 6 := by decide
  have h07 : (0 : ZMod (3 ^ 2)) ≠ 7 := by decide
  have h08 : (0 : ZMod (3 ^ 2)) ≠ 8 := by decide
  have h12 : (1 : ZMod (3 ^ 2)) ≠ 2 := by decide
  have h13 : (1 : ZMod (3 ^ 2)) ≠ 3 := by decide
  have h14 : (1 : ZMod (3 ^ 2)) ≠ 4 := by decide
  have h15 : (1 : ZMod (3 ^ 2)) ≠ 5 := by decide
  have h16 : (1 : ZMod (3 ^ 2)) ≠ 6 := by decide
  have h17 : (1 : ZMod (3 ^ 2)) ≠ 7 := by decide
  have h18 : (1 : ZMod (3 ^ 2)) ≠ 8 := by decide
  have h23 : (2 : ZMod (3 ^ 2)) ≠ 3 := by decide
  have h24 : (2 : ZMod (3 ^ 2)) ≠ 4 := by decide
  have h25 : (2 : ZMod (3 ^ 2)) ≠ 5 := by decide
  have h26 : (2 : ZMod (3 ^ 2)) ≠ 6 := by decide
  have h27 : (2 : ZMod (3 ^ 2)) ≠ 7 := by decide
  have h28 : (2 : ZMod (3 ^ 2)) ≠ 8 := by decide
  have h34 : (3 : ZMod (3 ^ 2)) ≠ 4 := by decide
  have h35 : (3 : ZMod (3 ^ 2)) ≠ 5 := by decide
  have h36 : (3 : ZMod (3 ^ 2)) ≠ 6 := by decide
  have h37 : (3 : ZMod (3 ^ 2)) ≠ 7 := by decide
  have h38 : (3 : ZMod (3 ^ 2)) ≠ 8 := by decide
  have h45 : (4 : ZMod (3 ^ 2)) ≠ 5 := by decide
  have h46 : (4 : ZMod (3 ^ 2)) ≠ 6 := by decide
  have h47 : (4 : ZMod (3 ^ 2)) ≠ 7 := by decide
  have h48 : (4 : ZMod (3 ^ 2)) ≠ 8 := by decide
  have h56 : (5 : ZMod (3 ^ 2)) ≠ 6 := by decide
  have h57 : (5 : ZMod (3 ^ 2)) ≠ 7 := by decide
  have h58 : (5 : ZMod (3 ^ 2)) ≠ 8 := by decide
  have h67 : (6 : ZMod (3 ^ 2)) ≠ 7 := by decide
  have h68 : (6 : ZMod (3 ^ 2)) ≠ 8 := by decide
  have h78 : (7 : ZMod (3 ^ 2)) ≠ 8 := by decide
  simp [h01, h02, h03, h04, h05, h06, h07, h08,
    h12, h13, h14, h15, h16, h17, h18,
    h23, h24, h25, h26, h27, h28,
    h34, h35, h36, h37, h38,
    h45, h46, h47, h48,
    h56, h57, h58,
    h67, h68, h78]
  abel

theorem dft_syracPMF_two_apply_table (k : ZMod (3 ^ 2)) :
    ZMod.dft (pmfComplexMass (syracPMF 2)) k =
      ZMod.stdAddChar (-(1 * k)) • (((8 / 63 : ℝ) : ℂ)) +
        ZMod.stdAddChar (-(2 * k)) • (((16 / 63 : ℝ) : ℂ)) +
        ZMod.stdAddChar (-(4 * k)) • (((11 / 63 : ℝ) : ℂ)) +
        ZMod.stdAddChar (-(5 * k)) • (((4 / 63 : ℝ) : ℂ)) +
        ZMod.stdAddChar (-(7 * k)) • (((2 / 63 : ℝ) : ℂ)) +
        ZMod.stdAddChar (-(8 * k)) • (((22 / 63 : ℝ) : ℂ)) := by
  rw [ZMod.dft_apply]
  rw [zmod9_sum_eq_sum_nine]
  have h0 : (((syracPMF 2 (0 : ZMod (3 ^ 2))).toReal : ℝ) : ℂ) = 0 := by
    rw [syracPMF_two_apply_zero]
    simp
  have h1 : (((syracPMF 2 (1 : ZMod (3 ^ 2))).toReal : ℝ) : ℂ) =
      ((8 / 63 : ℝ) : ℂ) := by
    rw [syracPMF_two_apply_one]
    rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (8 / 63 : ℝ))]
  have h2 : (((syracPMF 2 (2 : ZMod (3 ^ 2))).toReal : ℝ) : ℂ) =
      ((16 / 63 : ℝ) : ℂ) := by
    rw [syracPMF_two_apply_two]
    rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (16 / 63 : ℝ))]
  have h3 : (((syracPMF 2 (3 : ZMod (3 ^ 2))).toReal : ℝ) : ℂ) = 0 := by
    rw [syracPMF_two_apply_three]
    simp
  have h4 : (((syracPMF 2 (4 : ZMod (3 ^ 2))).toReal : ℝ) : ℂ) =
      ((11 / 63 : ℝ) : ℂ) := by
    rw [syracPMF_two_apply_four]
    rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (11 / 63 : ℝ))]
  have h5 : (((syracPMF 2 (5 : ZMod (3 ^ 2))).toReal : ℝ) : ℂ) =
      ((4 / 63 : ℝ) : ℂ) := by
    rw [syracPMF_two_apply_five]
    rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (4 / 63 : ℝ))]
  have h6 : (((syracPMF 2 (6 : ZMod (3 ^ 2))).toReal : ℝ) : ℂ) = 0 := by
    rw [syracPMF_two_apply_six]
    simp
  have h7 : (((syracPMF 2 (7 : ZMod (3 ^ 2))).toReal : ℝ) : ℂ) =
      ((2 / 63 : ℝ) : ℂ) := by
    rw [syracPMF_two_apply_seven]
    rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (2 / 63 : ℝ))]
  have h8 : (((syracPMF 2 (8 : ZMod (3 ^ 2))).toReal : ℝ) : ℂ) =
      ((22 / 63 : ℝ) : ℂ) := by
    rw [syracPMF_two_apply_eight]
    rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (22 / 63 : ℝ))]
  simp only [pmfComplexMass]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  simp

end Tao
end Erdos1135
