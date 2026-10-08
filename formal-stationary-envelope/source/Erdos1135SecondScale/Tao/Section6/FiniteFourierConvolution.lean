/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Fourier.Basic

/-!
# Section 6 Finite Cyclic Convolution

This leaf defines unnormalized cyclic convolution on `ZMod N` and proves that
the project's unnormalized forward DFT sends it to pointwise multiplication.
No cardinality factor appears.
-/

open scoped BigOperators
open scoped ZMod

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Raw, unnormalized cyclic convolution on `ZMod N`. -/
noncomputable def taoZModRawConvolution
    {N : ℕ} [NeZero N] {R : Type*} [CommSemiring R]
    (h tau : ZMod N → R) (x : ZMod N) : R :=
  ∑ y : ZMod N, h y * tau (x - y)

/-- A pointwise-zero left input has zero raw convolution. -/
theorem taoZModRawConvolution_eq_zero_of_left
    {N : ℕ} [NeZero N] {R : Type*} [CommSemiring R]
    (h tau : ZMod N → R) (hzero : ∀ y, h y = 0)
    (x : ZMod N) :
    taoZModRawConvolution h tau x = 0 := by
  simp [taoZModRawConvolution, hzero]

/-- Casting a real raw convolution to `ℂ` commutes with convolution. -/
theorem taoZModRawConvolution_ofReal
    {N : ℕ} [NeZero N] (h tau : ZMod N → ℝ) (x : ZMod N) :
    ((taoZModRawConvolution h tau x : ℝ) : ℂ) =
      taoZModRawConvolution
        (fun y => ((h y : ℝ) : ℂ))
        (fun y => ((tau y : ℝ) : ℂ)) x := by
  simp [taoZModRawConvolution]

private theorem rawConvolution_kernel_add
    {N : ℕ} [NeZero N] (x y xi : ZMod N) :
    taoForwardDFTKernel (x + y) xi =
      taoForwardDFTKernel x xi * taoForwardDFTKernel y xi := by
  unfold taoForwardDFTKernel
  rw [show -((x + y) * xi) = -(x * xi) + -(y * xi) by ring]
  exact AddChar.map_add_eq_mul _ _ _

private theorem rawConvolution_inner_reindex
    {N : ℕ} [NeZero N] (h tau : ZMod N → ℂ)
    (xi y : ZMod N) :
    (∑ x : ZMod N,
        taoForwardDFTKernel x xi * (h y * tau (x - y))) =
      (h y * taoForwardDFTKernel y xi) *
        ∑ z : ZMod N, taoForwardDFTKernel z xi * tau z := by
  calc
    (∑ x : ZMod N,
        taoForwardDFTKernel x xi * (h y * tau (x - y))) =
      ∑ z : ZMod N,
        taoForwardDFTKernel (y + z) xi *
          (h y * tau ((y + z) - y)) := by
            rw [← (Equiv.addLeft y).sum_comp
              Finset.univ
              (fun x : ZMod N =>
                taoForwardDFTKernel x xi * (h y * tau (x - y)))]
            all_goals simp
    _ = ∑ z : ZMod N,
        (h y * taoForwardDFTKernel y xi) *
          (taoForwardDFTKernel z xi * tau z) := by
            apply Finset.sum_congr rfl
            intro z _hz
            rw [rawConvolution_kernel_add]
            ring
    _ = (h y * taoForwardDFTKernel y xi) *
        ∑ z : ZMod N, taoForwardDFTKernel z xi * tau z := by
            rw [Finset.mul_sum]

/-- The unnormalized forward DFT turns raw convolution into pointwise
multiplication, with no factor `N` or `N⁻¹`. -/
theorem tao_dft_rawConvolution
    {N : ℕ} [NeZero N] (h tau : ZMod N → ℂ) (xi : ZMod N) :
    ZMod.dft (taoZModRawConvolution h tau) xi =
      ZMod.dft h xi * ZMod.dft tau xi := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, taoZModRawConvolution, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ y : ZMod N, ∑ x : ZMod N,
        taoForwardDFTKernel x xi * (h y * tau (x - y))) =
      ∑ y : ZMod N,
        (h y * taoForwardDFTKernel y xi) *
          ∑ z : ZMod N, taoForwardDFTKernel z xi * tau z := by
            apply Finset.sum_congr rfl
            intro y _hy
            exact rawConvolution_inner_reindex h tau xi y
    _ = (∑ y : ZMod N,
          taoForwardDFTKernel y xi * h y) *
        (∑ z : ZMod N, taoForwardDFTKernel z xi * tau z) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro y _hy
            ring
    _ = ZMod.dft h xi * ZMod.dft tau xi := by
            rw [ZMod.dft_apply, ZMod.dft_apply]
            simp only [smul_eq_mul, taoForwardDFTKernel]

end

end Tao
end Erdos1135SecondScale
