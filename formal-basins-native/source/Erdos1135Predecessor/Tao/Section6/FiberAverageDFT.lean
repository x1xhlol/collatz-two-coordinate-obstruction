/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.MixingStatement
import Erdos1135Predecessor.Tao.Section6.ConductorFrequency
import Mathlib.GroupTheory.Coset.Basic

open scoped BigOperators

open scoped ZMod

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

def zmodPowFiberSubgroup (m n : ℕ) : AddSubgroup (ZMod (3 ^ n)) :=
  AddSubgroup.zmultiples ((3 ^ m : ℕ) : ZMod (3 ^ n))

theorem zmodPowFiberSubgroup_card {m n : ℕ} (hmn : m ≤ n) :
    Nat.card (zmodPowFiberSubgroup m n) = 3 ^ (n - m) := by
  rw [zmodPowFiberSubgroup, Nat.card_zmultiples]
  rw [ZMod.addOrderOf_coe (3 ^ m) (pow_ne_zero _ (by norm_num : 3 ≠ 0))]
  rw [Nat.gcd_eq_right_iff_dvd.mpr (pow_dvd_pow 3 hmn)]
  rw [show 3 ^ n = 3 ^ m * 3 ^ (n - m) by
    rw [← pow_add, Nat.add_sub_of_le hmn]]
  rw [Nat.mul_comm, Nat.mul_div_left]
  positivity

theorem zmodPowFiberAverageScale_mul_card {m n : ℕ} (hmn : m ≤ n) :
    zmodPowFiberAverageScale m n * (3 ^ (n - m) : ℝ) = 1 := by
  unfold zmodPowFiberAverageScale
  have hpow : 3 ^ n = 3 ^ m * 3 ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_of_le hmn]
  rw [hpow]
  field_simp
  norm_cast

theorem zmodPowFiberSubgroup_eq_projection_ker
    {m n : ℕ} (hmn : m ≤ n) :
    zmodPowFiberSubgroup m n =
      (taoZModThreeProjection hmn).toAddMonoidHom.ker := by
  ext x
  constructor
  · intro hx
    rw [zmodPowFiberSubgroup, AddSubgroup.mem_zmultiples_iff] at hx
    rcases hx with ⟨k, hk⟩
    rw [AddMonoidHom.mem_ker, ← hk, map_zsmul]
    change k • taoZModThreeProjection hmn
      ((3 ^ m : ℕ) : ZMod (3 ^ n)) = 0
    rw [taoZModThreeProjection_natCast]
    simp
  · intro hx
    rw [AddMonoidHom.mem_ker] at hx
    change taoZModThreeProjection hmn x = 0 at hx
    rw [taoZModThreeProjection_eq_natCast_val hmn] at hx
    have hdvd : 3 ^ m ∣ x.val :=
      (ZMod.natCast_eq_zero_iff x.val (3 ^ m)).mp hx
    rcases hdvd with ⟨k, hk⟩
    rw [zmodPowFiberSubgroup, AddSubgroup.mem_zmultiples_iff]
    refine ⟨(k : ℤ), ?_⟩
    rw [← ZMod.natCast_zmod_val x, hk]
    push_cast
    simp [mul_comm]

theorem zmodSameResidueModPow_iff_projection_eq
    {m n : ℕ} (hmn : m ≤ n) (x y : ZMod (3 ^ n)) :
    zmodSameResidueModPow m n x y ↔
      taoZModThreeProjection hmn x = taoZModThreeProjection hmn y := by
  rw [taoZModThreeProjection_eq_natCast_val hmn,
    taoZModThreeProjection_eq_natCast_val hmn]
  rw [ZMod.natCast_eq_natCast_iff]
  rfl

theorem zmodPowFiberSum_eq_sum_projection_ker
    {m n : ℕ} (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ)
    (y : ZMod (3 ^ n)) :
    zmodPowFiberSum m n c y =
      ∑ h : (taoZModThreeProjection hmn).toAddMonoidHom.ker,
        c (y + h.1) := by
  classical
  let f := (taoZModThreeProjection hmn).toAddMonoidHom
  have hsame (x : ZMod (3 ^ n)) :
      zmodSameResidueModPow m n x y ↔ f x = f y := by
    exact zmodSameResidueModPow_iff_projection_eq hmn x y
  calc
    zmodPowFiberSum m n c y =
        ∑ x : f ⁻¹' {f y}, c x.1 := by
          rw [zmodPowFiberSum]
          simp_rw [hsame]
          rw [← Finset.sum_filter]
          apply Finset.sum_subtype
          simp
    _ = ∑ h : f.ker, c (y + h.1) := by
          apply Fintype.sum_equiv (f.fiberEquivKer y)
          intro x
          change c x.1 = c (y + (f.fiberEquivKer y x).1)
          rw [AddMonoidHom.fiberEquivKer_apply]
          simp

theorem zmodPowProjectionKer_card
    {m n : ℕ} (hmn : m ≤ n) :
    Nat.card ((taoZModThreeProjection hmn).toAddMonoidHom.ker) =
      3 ^ (n - m) := by
  rw [← zmodPowFiberSubgroup_eq_projection_ker hmn]
  exact zmodPowFiberSubgroup_card hmn

private noncomputable def zmodPowKernelAddChar
    {m n : ℕ} (hmn : m ≤ n) (xi : ZMod (3 ^ n)) :
    AddChar ((taoZModThreeProjection hmn).toAddMonoidHom.ker) ℂ :=
  ((ZMod.stdAddChar (N := 3 ^ n)).mulShift xi).compAddMonoidHom
    (taoZModThreeProjection hmn).toAddMonoidHom.ker.subtype

private theorem zmodPowKernelAddChar_eq_one_iff
    {m n : ℕ} (hmn : m ≤ n) (xi : ZMod (3 ^ n)) :
    zmodPowKernelAddChar hmn xi = 1 ↔
      ((3 ^ m : ℕ) : ZMod (3 ^ n)) * xi = 0 := by
  let f := (taoZModThreeProjection hmn).toAddMonoidHom
  let g : ZMod (3 ^ n) := ((3 ^ m : ℕ) : ZMod (3 ^ n))
  constructor
  · intro hchar
    have hg_mem : g ∈ f.ker := by
      rw [← zmodPowFiberSubgroup_eq_projection_ker hmn]
      exact AddSubgroup.mem_zmultiples g
    have hvalue := DFunLike.congr_fun hchar (⟨g, hg_mem⟩ : f.ker)
    have hvalue' : ZMod.stdAddChar (g * xi) = 1 := by
      simpa [zmodPowKernelAddChar, AddChar.mulShift_apply, mul_comm]
        using hvalue
    exact ((ZMod.isPrimitive_stdAddChar (3 ^ n)).zmod_char_eq_one_iff
      (3 ^ n) (g * xi)).mp hvalue'
  · intro hret
    rw [AddChar.eq_one_iff]
    intro h
    have hh_mem : h.1 ∈ zmodPowFiberSubgroup m n := by
      rw [zmodPowFiberSubgroup_eq_projection_ker hmn]
      exact h.2
    rw [zmodPowFiberSubgroup, AddSubgroup.mem_zmultiples_iff] at hh_mem
    rcases hh_mem with ⟨k, hk⟩
    simp only [zmodPowKernelAddChar, AddChar.compAddMonoidHom_apply,
      AddChar.mulShift_apply, mul_comm xi]
    change ZMod.stdAddChar (h.1 * xi) = 1
    rw [← hk]
    rw [zsmul_eq_mul, mul_assoc, hret, mul_zero]
    exact AddChar.map_zero_eq_one _

theorem sum_stdAddChar_projection_ker
    {m n : ℕ} (hmn : m ≤ n) (xi : ZMod (3 ^ n)) :
    (∑ h : (taoZModThreeProjection hmn).toAddMonoidHom.ker,
        ZMod.stdAddChar (h.1 * xi)) =
      if ((3 ^ m : ℕ) : ZMod (3 ^ n)) * xi = 0 then
        (Fintype.card
          ((taoZModThreeProjection hmn).toAddMonoidHom.ker) : ℂ)
      else 0 := by
  classical
  split_ifs with hret
  · simpa [zmodPowKernelAddChar, AddChar.mulShift_apply, mul_comm] using
      (AddChar.sum_eq_card_of_eq_one
        ((zmodPowKernelAddChar_eq_one_iff hmn xi).mpr hret))
  · simpa [zmodPowKernelAddChar, AddChar.mulShift_apply, mul_comm] using
      (AddChar.sum_eq_zero_of_ne_one
        (mt (zmodPowKernelAddChar_eq_one_iff hmn xi).mp hret))

private theorem fiber_kernel_shift
    {N : ℕ} [NeZero N] (x h xi : ZMod N) :
    taoForwardDFTKernel (x - h) xi =
      ZMod.stdAddChar (h * xi) * taoForwardDFTKernel x xi := by
  unfold taoForwardDFTKernel
  rw [show -((x - h) * xi) = h * xi + -(x * xi) by ring]
  exact AddChar.map_add_eq_mul _ _ _

private theorem fiber_inner_reindex
    {m n : ℕ} (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ)
    (xi : ZMod (3 ^ n))
    (h : (taoZModThreeProjection hmn).toAddMonoidHom.ker) :
    (∑ y : ZMod (3 ^ n),
        taoForwardDFTKernel y xi * ((c (y + h.1) : ℝ) : ℂ)) =
      ZMod.stdAddChar (h.1 * xi) *
        ZMod.dft (fun x => ((c x : ℝ) : ℂ)) xi := by
  calc
    (∑ y : ZMod (3 ^ n),
        taoForwardDFTKernel y xi * ((c (y + h.1) : ℝ) : ℂ)) =
      ∑ x : ZMod (3 ^ n),
        taoForwardDFTKernel (x - h.1) xi * ((c x : ℝ) : ℂ) := by
          apply Fintype.sum_equiv (Equiv.addRight h.1)
          intro y
          simp
    _ = ∑ x : ZMod (3 ^ n),
        ZMod.stdAddChar (h.1 * xi) *
          (taoForwardDFTKernel x xi * ((c x : ℝ) : ℂ)) := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [fiber_kernel_shift]
          ring
    _ = ZMod.stdAddChar (h.1 * xi) *
        ZMod.dft (fun x => ((c x : ℝ) : ℂ)) xi := by
          rw [tao_dft_apply]
          simp only [smul_eq_mul]
          rw [Finset.mul_sum]

theorem dft_zmodPowFiberSum
    {m n : ℕ} (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ)
    (xi : ZMod (3 ^ n)) :
    ZMod.dft (fun y => ((zmodPowFiberSum m n c y : ℝ) : ℂ)) xi =
      (∑ h : (taoZModThreeProjection hmn).toAddMonoidHom.ker,
          ZMod.stdAddChar (h.1 * xi)) *
        ZMod.dft (fun y => ((c y : ℝ) : ℂ)) xi := by
  rw [tao_dft_apply]
  simp only [smul_eq_mul]
  simp_rw [zmodPowFiberSum_eq_sum_projection_ker hmn]
  simp only [Complex.ofReal_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ h : (taoZModThreeProjection hmn).toAddMonoidHom.ker,
        ∑ y : ZMod (3 ^ n),
          taoForwardDFTKernel y xi * ((c (y + h.1) : ℝ) : ℂ)) =
      ∑ h : (taoZModThreeProjection hmn).toAddMonoidHom.ker,
        ZMod.stdAddChar (h.1 * xi) *
          ZMod.dft (fun y => ((c y : ℝ) : ℂ)) xi := by
            apply Finset.sum_congr rfl
            intro h _hh
            exact fiber_inner_reindex hmn c xi h
    _ = (∑ h : (taoZModThreeProjection hmn).toAddMonoidHom.ker,
          ZMod.stdAddChar (h.1 * xi)) *
        ZMod.dft (fun y => ((c y : ℝ) : ℂ)) xi := by
          rw [Finset.sum_mul]

theorem dft_zmodPowFiberAverage
    {m n : ℕ} (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ)
    (xi : ZMod (3 ^ n)) :
    ZMod.dft
        (fun y => ((zmodPowFiberAverageScale m n *
          zmodPowFiberSum m n c y : ℝ) : ℂ)) xi =
      if ((3 ^ m : ℕ) : ZMod (3 ^ n)) * xi = 0 then
        ZMod.dft (fun y => ((c y : ℝ) : ℂ)) xi
      else 0 := by
  have hscale :
      ((zmodPowFiberAverageScale m n : ℝ) : ℂ) *
          ((3 ^ (n - m) : ℕ) : ℂ) = 1 := by
    exact_mod_cast zmodPowFiberAverageScale_mul_card hmn
  have hcard :
      Fintype.card
          ((taoZModThreeProjection hmn).toAddMonoidHom.ker) =
        3 ^ (n - m) := by
    rw [← Nat.card_eq_fintype_card]
    exact zmodPowProjectionKer_card hmn
  calc
    ZMod.dft
        (fun y => ((zmodPowFiberAverageScale m n *
          zmodPowFiberSum m n c y : ℝ) : ℂ)) xi =
      ((zmodPowFiberAverageScale m n : ℝ) : ℂ) *
        ZMod.dft
          (fun y => ((zmodPowFiberSum m n c y : ℝ) : ℂ)) xi := by
            rw [tao_dft_apply, tao_dft_apply]
            simp only [smul_eq_mul, Complex.ofReal_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _hy
            ring
    _ = ((zmodPowFiberAverageScale m n : ℝ) : ℂ) *
        ((∑ h : (taoZModThreeProjection hmn).toAddMonoidHom.ker,
            ZMod.stdAddChar (h.1 * xi)) *
          ZMod.dft (fun y => ((c y : ℝ) : ℂ)) xi) := by
            rw [dft_zmodPowFiberSum hmn]
    _ = if ((3 ^ m : ℕ) : ZMod (3 ^ n)) * xi = 0 then
        ZMod.dft (fun y => ((c y : ℝ) : ℂ)) xi
      else 0 := by
        rw [sum_stdAddChar_projection_ker hmn, hcard]
        split_ifs with hret
        · rw [← mul_assoc, hscale, one_mul]
        · simp

theorem dft_zmodPowFiberDifference
    {m n : ℕ} (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ)
    (xi : ZMod (3 ^ n)) :
    ZMod.dft
        (fun y => ((c y - zmodPowFiberAverageScale m n *
          zmodPowFiberSum m n c y : ℝ) : ℂ)) xi =
      if ((3 ^ m : ℕ) : ZMod (3 ^ n)) * xi = 0 then 0
      else ZMod.dft (fun y => ((c y : ℝ) : ℂ)) xi := by
  calc
    ZMod.dft
        (fun y => ((c y - zmodPowFiberAverageScale m n *
          zmodPowFiberSum m n c y : ℝ) : ℂ)) xi =
      ZMod.dft (fun y => ((c y : ℝ) : ℂ)) xi -
        ZMod.dft
          (fun y => ((zmodPowFiberAverageScale m n *
            zmodPowFiberSum m n c y : ℝ) : ℂ)) xi := by
              rw [tao_dft_apply, tao_dft_apply, tao_dft_apply]
              simp only [smul_eq_mul, Complex.ofReal_sub, mul_sub]
              rw [Finset.sum_sub_distrib]
    _ = if ((3 ^ m : ℕ) : ZMod (3 ^ n)) * xi = 0 then 0
        else ZMod.dft (fun y => ((c y : ℝ) : ℂ)) xi := by
          rw [dft_zmodPowFiberAverage hmn]
          split_ifs <;> simp

theorem zmodPowFiberFrequency_retained_iff
    {m n : ℕ} (hmn : m ≤ n) (xi : ZMod (3 ^ n)) :
    ((3 ^ m : ℕ) : ZMod (3 ^ n)) * xi = 0 ↔
      zmodThreePowMultiple n (n - m) xi := by
  rw [zmodThreePowMultiple_iff_dvd_val (Nat.sub_le n m)]
  conv_lhs =>
    rw [← ZMod.natCast_zmod_val xi]
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  have hpow : 3 ^ n = 3 ^ m * 3 ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_of_le hmn]
  generalize xi.val = k
  rw [hpow, Nat.mul_dvd_mul_iff_left (pow_pos (by norm_num) m)]

end

end Tao

end Erdos1135Predecessor
