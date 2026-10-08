/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageSignedAverage

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open scoped BigOperators

namespace TaoSection7Lemma77

theorem lemma77HorizontalPointwiseKernel_sq_eq_signedTranslated
    {C r : ℝ} (hr : 0 ≤ r) (shift : ℤ) (s q : ℕ) :
    lemma77HorizontalPointwiseKernel (r ^ 2) r C s q =
      lemma77SignedTranslatedHorizontalKernel C r shift s
        ((q : ℤ) + shift) := by
  unfold lemma77HorizontalPointwiseKernel
    lemma77SignedTranslatedHorizontalKernel
    lemma77HeightPotentialKernel
  rw [taoLemma22GaussianWeight, if_neg (by omega)]
  simp only [add_sub_cancel_right, Int.cast_natCast]
  unfold lemma77CenteredHorizontalDisplacement
  rw [abs_mul, abs_of_nonneg hr]
  push_cast
  ring_nf

def lemma77SignedHorizontalIntIndex (s : ℕ) (z : ℤ) : ℤ :=
  4 * z - (s : ℤ)

theorem lemma77SignedHorizontalIntIndex_injective (s : ℕ) :
    Function.Injective (lemma77SignedHorizontalIntIndex s) := by
  intro z w h
  unfold lemma77SignedHorizontalIntIndex at h
  omega

theorem lemma77ScalarCenteredHorizontal_eq_signedIndex_div_four
    (s : ℕ) (z : ℤ) :
    lemma77ScalarCenteredHorizontal z s =
      (lemma77SignedHorizontalIntIndex s z : ℝ) / 4 := by
  unfold lemma77ScalarCenteredHorizontal lemma77SignedHorizontalIntIndex
  push_cast
  ring

theorem lemma77SignedHeightGaussianProfile_summable
    {r : ℝ} (hr : 0 < r) (s : ℕ) :
    Summable fun z : ℤ =>
      Real.exp (-((r * lemma77ScalarCenteredHorizontal z s) ^ 2 /
        (1 + (s : ℝ)))) := by
  have hraw :=
    (lemma77ExpNegMulIntSqDiv_summable
      (a := r ^ 2 / 16) (S := 1 + (s : ℝ))
      (by positivity) (by positivity)).comp_injective
        (lemma77SignedHorizontalIntIndex_injective s)
  convert hraw using 1
  ext z
  rw [lemma77ScalarCenteredHorizontal_eq_signedIndex_div_four]
  congr 1
  ring

theorem lemma77SignedHeightLinearProfile_summable
    {r : ℝ} (hr : 0 < r) (s : ℕ) :
    Summable fun z : ℤ =>
      Real.exp (-|r * lemma77ScalarCenteredHorizontal z s|) := by
  have hraw :=
    (lemma77ExpNegMulIntAbs_summable (a := r / 4) (by positivity)).comp_injective
      (lemma77SignedHorizontalIntIndex_injective s)
  convert hraw using 1
  ext z
  rw [lemma77ScalarCenteredHorizontal_eq_signedIndex_div_four,
    abs_mul, abs_div, abs_of_pos hr]
  norm_num
  ring

theorem lemma77HeightPotentialKernel_int_summable
    {C r : ℝ} (hr : 0 < r) (s : ℕ) :
    Summable fun z : ℤ => lemma77HeightPotentialKernel C r z s := by
  let g : ℤ → ℝ := fun z =>
    Real.exp (-((r * lemma77ScalarCenteredHorizontal z s) ^ 2 /
      (1 + (s : ℝ))))
  let l : ℤ → ℝ := fun z =>
    Real.exp (-|r * lemma77ScalarCenteredHorizontal z s|)
  have hg : Summable g := by
    simpa [g] using lemma77SignedHeightGaussianProfile_summable hr s
  have hl : Summable l := by
    simpa [l] using lemma77SignedHeightLinearProfile_summable hr s
  simpa [lemma77HeightPotentialKernel, taoLemma22GaussianWeight,
    lemma77ScalarCenteredHorizontal, g, l] using
      (hg.add hl).mul_left
        (C * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))))

theorem lemma77HeightPotentialKernel_int_tsum_le
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r) (s : ℕ) :
    (∑' z : ℤ, lemma77HeightPotentialKernel C r z s) ≤
      C * (lemma77HorizontalGaussianCountConstant (r ^ 2) +
        lemma77HorizontalLinearCountConstant r) := by
  let S : ℝ := 1 + (s : ℝ)
  let H : ℝ := S ^ (-(1 / 2 : ℝ))
  let idx : ℤ → ℤ := lemma77SignedHorizontalIntIndex s
  let g : ℤ → ℝ := fun z =>
    Real.exp (-((r * lemma77ScalarCenteredHorizontal z s) ^ 2 / S))
  let l : ℤ → ℝ := fun z =>
    Real.exp (-|r * lemma77ScalarCenteredHorizontal z s|)
  let gRaw : ℤ → ℝ := fun u =>
    Real.exp (-((r ^ 2 / 16) * (u : ℝ) ^ 2 / S))
  let lRaw : ℤ → ℝ := fun u =>
    Real.exp (-((r / 4) * |(u : ℝ)|))
  have hS : 0 < S := by dsimp [S]; positivity
  have hS1 : 1 ≤ S := by
    dsimp [S]
    exact le_add_of_nonneg_right (Nat.cast_nonneg s)
  have ha : 0 < r ^ 2 / 16 := by positivity
  have hb : 0 < r / 4 := by positivity
  have hidx : Function.Injective idx := by
    exact lemma77SignedHorizontalIntIndex_injective s
  have hgRaw : Summable gRaw := by
    simpa [gRaw] using lemma77ExpNegMulIntSqDiv_summable ha hS
  have hlRaw : Summable lRaw := by
    simpa [lRaw] using lemma77ExpNegMulIntAbs_summable hb
  have hg_eq : ∀ z, g z = gRaw (idx z) := by
    intro z
    dsimp [g, gRaw, idx]
    rw [lemma77ScalarCenteredHorizontal_eq_signedIndex_div_four]
    congr 1
    ring
  have hl_eq : ∀ z, l z = lRaw (idx z) := by
    intro z
    dsimp [l, lRaw, idx]
    rw [lemma77ScalarCenteredHorizontal_eq_signedIndex_div_four,
      abs_mul, abs_div, abs_of_pos hr]
    norm_num
    ring
  have hg : Summable g := by
    rw [show g = gRaw ∘ idx by funext z; exact hg_eq z]
    exact hgRaw.comp_injective hidx
  have hl : Summable l := by
    rw [show l = lRaw ∘ idx by funext z; exact hl_eq z]
    exact hlRaw.comp_injective hidx
  have hg_bound :
      (∑' z : ℤ, g z) ≤
        lemma77HorizontalGaussianCountConstant (r ^ 2) * Real.sqrt S := by
    calc
      (∑' z : ℤ, g z) = ∑' z : ℤ, gRaw (idx z) :=
        tsum_congr hg_eq
      _ ≤ ∑' u : ℤ, gRaw u :=
        tsum_comp_le_tsum_of_inj hgRaw (fun _ => (Real.exp_pos _).le) hidx
      _ ≤ lemma77HorizontalGaussianCountConstant (r ^ 2) *
          Real.sqrt S := by
        simpa [gRaw, lemma77HorizontalGaussianCountConstant] using
          lemma77ExpNegMulIntSqDiv_tsum_le_sqrt_explicit ha hS1
  have hl_bound :
      (∑' z : ℤ, l z) ≤ lemma77HorizontalLinearCountConstant r := by
    calc
      (∑' z : ℤ, l z) = ∑' z : ℤ, lRaw (idx z) :=
        tsum_congr hl_eq
      _ ≤ ∑' u : ℤ, lRaw u :=
        tsum_comp_le_tsum_of_inj hlRaw (fun _ => (Real.exp_pos _).le) hidx
      _ ≤ lemma77HorizontalLinearCountConstant r := by
        simpa [lRaw, lemma77HorizontalLinearCountConstant] using
          lemma77ExpNegMulIntAbs_tsum_le hb
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hCH : 0 ≤ C * H := mul_nonneg hC hH
  have hG : 0 ≤ lemma77HorizontalGaussianCountConstant (r ^ 2) :=
    lemma77HorizontalGaussianCountConstant_nonneg (sq_pos_of_pos hr)
  have hL : 0 ≤ lemma77HorizontalLinearCountConstant r :=
    lemma77HorizontalLinearCountConstant_nonneg hr
  have hHle : H ≤ 1 := by
    simpa [H, S] using lemma77_rpow_neg_half_one_add_le_one s
  have hHsqrt : H * Real.sqrt S = 1 := by
    simpa [H, S] using lemma77_rpow_neg_half_mul_sqrt_one_add s
  calc
    (∑' z : ℤ, lemma77HeightPotentialKernel C r z s) =
        C * H * ((∑' z : ℤ, g z) + ∑' z : ℤ, l z) := by
      calc
        (∑' z : ℤ, lemma77HeightPotentialKernel C r z s) =
            ∑' z : ℤ, C * H * (g z + l z) := by
          apply tsum_congr
          intro z
          unfold lemma77HeightPotentialKernel
          rw [taoLemma22GaussianWeight, if_neg (by omega)]
          simp only [H, S, g, l, lemma77ScalarCenteredHorizontal,
            Nat.cast_add, Nat.cast_one]
        _ = C * H * ((∑' z : ℤ, g z) + ∑' z : ℤ, l z) := by
          rw [tsum_mul_left, hg.tsum_add hl]
    _ ≤ C * H *
        (lemma77HorizontalGaussianCountConstant (r ^ 2) * Real.sqrt S +
          lemma77HorizontalLinearCountConstant r) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add hg_bound hl_bound) hCH
    _ = C * (lemma77HorizontalGaussianCountConstant (r ^ 2) +
          H * lemma77HorizontalLinearCountConstant r) := by
      calc
        C * H *
            (lemma77HorizontalGaussianCountConstant (r ^ 2) * Real.sqrt S +
              lemma77HorizontalLinearCountConstant r) =
            C * (lemma77HorizontalGaussianCountConstant (r ^ 2) *
                (H * Real.sqrt S) +
              H * lemma77HorizontalLinearCountConstant r) := by ring
        _ = C * (lemma77HorizontalGaussianCountConstant (r ^ 2) +
              H * lemma77HorizontalLinearCountConstant r) := by
          rw [hHsqrt, mul_one]
    _ ≤ C * (lemma77HorizontalGaussianCountConstant (r ^ 2) +
          lemma77HorizontalLinearCountConstant r) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact add_le_add le_rfl (mul_le_of_le_one_left hL hHle)

theorem lemma77SignedTranslatedHorizontalKernel_summable
    {C r : ℝ} (hr : 0 < r) (shift : ℤ) (s : ℕ) :
    Summable fun z : ℤ =>
      lemma77SignedTranslatedHorizontalKernel C r shift s z := by
  simpa [lemma77SignedTranslatedHorizontalKernel, Function.comp_def] using
    (Equiv.subRight shift).summable_iff.mpr
      (lemma77HeightPotentialKernel_int_summable (C := C) hr s)

theorem lemma77SignedTranslatedHorizontalKernel_tsum_eq
    (C r : ℝ) (shift : ℤ) (s : ℕ) :
    (∑' z : ℤ, lemma77SignedTranslatedHorizontalKernel C r shift s z) =
      ∑' z : ℤ, lemma77HeightPotentialKernel C r z s := by
  simpa [lemma77SignedTranslatedHorizontalKernel, Function.comp_def] using
    (Equiv.subRight shift).tsum_eq
      (f := fun z : ℤ => lemma77HeightPotentialKernel C r z s)

theorem lemma77SignedTranslatedHorizontalKernel_tsum_le
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r)
    (shift : ℤ) (s : ℕ) :
    (∑' z : ℤ, lemma77SignedTranslatedHorizontalKernel C r shift s z) ≤
      C * (lemma77HorizontalGaussianCountConstant (r ^ 2) +
        lemma77HorizontalLinearCountConstant r) := by
  rw [lemma77SignedTranslatedHorizontalKernel_tsum_eq]
  exact lemma77HeightPotentialKernel_int_tsum_le hC hr s

end TaoSection7Lemma77

end

end Tao

end Erdos1135Predecessor
