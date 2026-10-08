/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Fourier.Basic
import Mathlib.Analysis.Complex.Norm

/-!
# Section 6 Finite Fourier Parseval Identities

This leaf fixes the `L^2` normalization for the project's unnormalized forward
DFT on `ZMod N`.  Bilinear Parseval has one factor `N`; norm-square Parseval is
then obtained from compatibility with complex conjugation.
-/

open scoped BigOperators
open scoped ComplexConjugate
open scoped ZMod

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Bilinear Parseval for the unnormalized forward DFT. -/
theorem tao_dft_bilinear_parseval
    {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) :
    (∑ k : ZMod N, ZMod.dft f k * ZMod.dft g (-k)) =
      (N : ℂ) * ∑ x : ZMod N, f x * g x := by
  calc
    (∑ k : ZMod N, ZMod.dft f k * ZMod.dft g (-k)) =
      ∑ k : ZMod N, ZMod.dft f k *
        (∑ x : ZMod N,
          ZMod.stdAddChar (-(x * (-k))) * g x) := by
            apply Finset.sum_congr rfl
            intro k _hk
            congr 1
    _ = ∑ k : ZMod N, ∑ x : ZMod N,
        ZMod.dft f k *
          (ZMod.stdAddChar (-(x * (-k))) * g x) := by
            simp only [Finset.mul_sum]
    _ = ∑ x : ZMod N, ∑ k : ZMod N,
        ZMod.dft f k *
          (ZMod.stdAddChar (-(x * (-k))) * g x) := by
            rw [Finset.sum_comm]
    _ = ∑ x : ZMod N,
        ZMod.dft (ZMod.dft f) (-x) * g x := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [ZMod.dft_apply]
            simp only [smul_eq_mul, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _hk
            have hphase : -(x * (-k)) = -(k * (-x)) := by ring
            rw [hphase]
            ring
    _ = ∑ x : ZMod N, ((N : ℂ) * f x) * g x := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [congrFun (ZMod.dft_dft f) (-x)]
            simp [smul_eq_mul]
    _ = (N : ℂ) * ∑ x : ZMod N, f x * g x := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _hx
            ring

private theorem conj_stdAddChar_neg
    {N : ℕ} [NeZero N] (x : ZMod N) :
    conj (ZMod.stdAddChar (-x)) = ZMod.stdAddChar x := by
  change conj ((ZMod.toCircle (-x) : Circle) : ℂ) =
    ((ZMod.toCircle x : Circle) : ℂ)
  rw [show ZMod.toCircle (-x) = (ZMod.toCircle x)⁻¹ by
    exact AddChar.map_neg_eq_inv (ZMod.toCircle (N := N)) x]
  rw [Circle.coe_inv_eq_conj]
  simp

/-- Conjugating a function conjugates its DFT after frequency negation. -/
theorem tao_dft_conj_apply_neg
    {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (fun x => conj (f x)) (-k) =
      conj (ZMod.dft f k) := by
  rw [ZMod.dft_apply, ZMod.dft_apply]
  simp only [smul_eq_mul, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro x _hx
  have hphase : -(x * (-k)) = -(-(x * k)) := by ring
  rw [hphase, conj_stdAddChar_neg]
  ring

/-- Norm-square Parseval for the unnormalized forward DFT.  Exactly one factor
`N` appears. -/
theorem tao_dft_norm_sq_parseval
    {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    (∑ k : ZMod N, ‖ZMod.dft f k‖ ^ 2) =
      (N : ℝ) * ∑ x : ZMod N, ‖f x‖ ^ 2 := by
  have h := tao_dft_bilinear_parseval f (fun x => conj (f x))
  simp_rw [tao_dft_conj_apply_neg] at h
  have hcomplex :
      (((∑ k : ZMod N, ‖ZMod.dft f k‖ ^ 2) : ℝ) : ℂ) =
        (((N : ℝ) * ∑ x : ZMod N, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    simpa [Complex.mul_conj'] using h
  exact_mod_cast hcomplex

/-- `Complex.normSq` form of unnormalized Parseval for algebraic collision
calculations. -/
theorem tao_dft_normSq_parseval
    {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    (∑ k : ZMod N, Complex.normSq (ZMod.dft f k)) =
      (N : ℝ) * ∑ x : ZMod N, Complex.normSq (f x) := by
  simpa [Complex.normSq_eq_norm_sq] using tao_dft_norm_sq_parseval f

end

end Tao
end Erdos1135SecondScale
