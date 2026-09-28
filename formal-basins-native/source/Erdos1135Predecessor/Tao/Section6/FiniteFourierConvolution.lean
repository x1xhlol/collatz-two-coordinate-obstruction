/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Basic

open scoped BigOperators

open scoped ZMod

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

noncomputable def taoZModRawConvolution
    {N : ℕ} [NeZero N] {R : Type*} [CommSemiring R]
    (h tau : ZMod N → R) (x : ZMod N) : R :=
  ∑ y : ZMod N, h y * tau (x - y)

theorem taoZModRawConvolution_eq_zero_of_left
    {N : ℕ} [NeZero N] {R : Type*} [CommSemiring R]
    (h tau : ZMod N → R) (hzero : ∀ y, h y = 0)
    (x : ZMod N) :
    taoZModRawConvolution h tau x = 0 := by
  simp [taoZModRawConvolution, hzero]

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

end Erdos1135Predecessor
