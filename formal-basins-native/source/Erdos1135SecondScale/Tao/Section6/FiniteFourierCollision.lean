/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section6.FiberAverageDFT
import Erdos1135SecondScale.Tao.Section6.FiniteFourierParseval
import Erdos1135SecondScale.Tao.Section6.FiniteFourierConvolution
import Mathlib.Algebra.Order.Chebyshev

/-!
# Section 6 Finite Fourier Collision Bound

This leaf combines the exact fiber multiplier, raw-convolution multiplication,
and unnormalized Parseval.  It is event-free: no positivity, normalization,
PMF, or Corollary 6.3 hypotheses occur here.
-/

open scoped BigOperators
open scoped ZMod

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- The real raw-convolution DFT factors after casting both inputs to
`Complex`. -/
theorem tao_dft_rawConvolution_ofReal
    {N : ℕ} [NeZero N] (h tau : ZMod N → ℝ) (xi : ZMod N) :
    ZMod.dft
        (fun x => ((taoZModRawConvolution h tau x : ℝ) : ℂ)) xi =
      ZMod.dft (fun x => ((h x : ℝ) : ℂ)) xi *
        ZMod.dft (fun x => ((tau x : ℝ) : ℂ)) xi := by
  have hcast :
      (fun x => ((taoZModRawConvolution h tau x : ℝ) : ℂ)) =
        taoZModRawConvolution
          (fun x => ((h x : ℝ) : ℂ))
          (fun x => ((tau x : ℝ) : ℂ)) := by
    funext x
    exact taoZModRawConvolution_ofReal h tau x
  rw [hcast, tao_dft_rawConvolution]

/-- Source-facing discarded spectral energy for a real head and tail. -/
noncomputable def taoZModDiscardedConvolutionEnergy
    (m n : ℕ) (h tau : ZMod (3 ^ n) → ℝ) : ℝ := by
  classical
  exact
    ∑ xi : ZMod (3 ^ n),
      if zmodThreePowMultiple n (n - m) xi then 0 else
        Complex.normSq
          (ZMod.dft (fun x => ((h x : ℝ) : ℂ)) xi *
            ZMod.dft (fun x => ((tau x : ℝ) : ℂ)) xi)

/-- Exact normalization ledger for the discarded spectrum of a real raw
convolution.  There is exactly one factor `3^n` on the spatial side. -/
theorem tao_rawConvolution_fiberDifference_parseval
    {m n : ℕ} (hmn : m ≤ n)
    (h tau : ZMod (3 ^ n) → ℝ) :
    let c := taoZModRawConvolution h tau
    ((3 ^ n : ℕ) : ℝ) *
        ∑ y : ZMod (3 ^ n),
          (c y - zmodPowFiberAverageScale m n *
            zmodPowFiberSum m n c y) ^ 2 =
      taoZModDiscardedConvolutionEnergy m n h tau := by
  classical
  dsimp only
  let d : ZMod (3 ^ n) → ℝ := fun y =>
    taoZModRawConvolution h tau y -
      zmodPowFiberAverageScale m n *
        zmodPowFiberSum m n (taoZModRawConvolution h tau) y
  calc
    ((3 ^ n : ℕ) : ℝ) *
        ∑ y : ZMod (3 ^ n),
          (taoZModRawConvolution h tau y -
            zmodPowFiberAverageScale m n *
              zmodPowFiberSum m n (taoZModRawConvolution h tau) y) ^ 2 =
      ((3 ^ n : ℕ) : ℝ) *
        ∑ y : ZMod (3 ^ n), Complex.normSq ((d y : ℝ) : ℂ) := by
          apply congrArg (((3 ^ n : ℕ) : ℝ) * ·)
          apply Finset.sum_congr rfl
          intro y _hy
          change d y ^ 2 = Complex.normSq ((d y : ℝ) : ℂ)
          rw [Complex.normSq_ofReal]
          ring
    _ = ∑ xi : ZMod (3 ^ n),
        Complex.normSq
          (ZMod.dft (fun y => ((d y : ℝ) : ℂ)) xi) := by
          rw [tao_dft_normSq_parseval]
    _ = taoZModDiscardedConvolutionEnergy m n h tau := by
          unfold taoZModDiscardedConvolutionEnergy
          apply Finset.sum_congr rfl
          intro xi _hxi
          have hretained := zmodPowFiberFrequency_retained_iff hmn xi
          by_cases hret :
              ((3 ^ m : ℕ) : ZMod (3 ^ n)) * xi = 0
          · have hsource : zmodThreePowMultiple n (n - m) xi :=
              hretained.mp hret
            rw [if_pos hsource]
            have hd := dft_zmodPowFiberDifference hmn
              (taoZModRawConvolution h tau) xi
            rw [if_pos hret] at hd
            rw [show ZMod.dft (fun y => ((d y : ℝ) : ℂ)) xi = 0 by
              simpa [d] using hd]
            simp
          · have hsource : ¬zmodThreePowMultiple n (n - m) xi :=
              mt hretained.mpr hret
            rw [if_neg hsource]
            have hd := dft_zmodPowFiberDifference hmn
              (taoZModRawConvolution h tau) xi
            rw [if_neg hret] at hd
            have hdft :
                ZMod.dft (fun y => ((d y : ℝ) : ℂ)) xi =
                  ZMod.dft
                    (fun y => ((taoZModRawConvolution h tau y : ℝ) : ℂ)) xi := by
              simpa [d] using hd
            rw [hdft, tao_dft_rawConvolution_ofReal]

/-- A uniform tail DFT bound on discarded frequencies controls the exact
discarded spectral convolution energy. -/
theorem taoZModDiscardedConvolutionEnergy_le
    {m n : ℕ} (h tau : ZMod (3 ^ n) → ℝ) {delta : ℝ}
    (hdelta : 0 ≤ delta)
    (htau : ∀ xi : ZMod (3 ^ n),
      ¬zmodThreePowMultiple n (n - m) xi →
        ‖ZMod.dft (fun x => ((tau x : ℝ) : ℂ)) xi‖ ≤ delta) :
    taoZModDiscardedConvolutionEnergy m n h tau ≤
      delta ^ 2 * ((3 ^ n : ℕ) : ℝ) *
        ∑ y : ZMod (3 ^ n), h y ^ 2 := by
  classical
  unfold taoZModDiscardedConvolutionEnergy
  calc
    (∑ xi : ZMod (3 ^ n),
        if zmodThreePowMultiple n (n - m) xi then 0 else
          Complex.normSq
            (ZMod.dft (fun x => ((h x : ℝ) : ℂ)) xi *
              ZMod.dft (fun x => ((tau x : ℝ) : ℂ)) xi)) ≤
      ∑ xi : ZMod (3 ^ n),
        delta ^ 2 * Complex.normSq
          (ZMod.dft (fun x => ((h x : ℝ) : ℂ)) xi) := by
            apply Finset.sum_le_sum
            intro xi _hxi
            by_cases hsource : zmodThreePowMultiple n (n - m) xi
            · rw [if_pos hsource]
              exact mul_nonneg (sq_nonneg delta)
                (Complex.normSq_nonneg _)
            · rw [if_neg hsource, Complex.normSq_mul]
              have hnorm := htau xi hsource
              have hsq :
                  Complex.normSq
                      (ZMod.dft (fun x => ((tau x : ℝ) : ℂ)) xi) ≤
                    delta ^ 2 := by
                rw [Complex.normSq_eq_norm_sq]
                exact (sq_le_sq₀ (norm_nonneg _) hdelta).2 hnorm
              calc
                Complex.normSq
                      (ZMod.dft (fun x => ((h x : ℝ) : ℂ)) xi) *
                    Complex.normSq
                      (ZMod.dft (fun x => ((tau x : ℝ) : ℂ)) xi) ≤
                  Complex.normSq
                      (ZMod.dft (fun x => ((h x : ℝ) : ℂ)) xi) *
                    delta ^ 2 :=
                      mul_le_mul_of_nonneg_left hsq
                        (Complex.normSq_nonneg _)
                _ = delta ^ 2 * Complex.normSq
                      (ZMod.dft (fun x => ((h x : ℝ) : ℂ)) xi) := by
                        ring
    _ = delta ^ 2 *
        ∑ xi : ZMod (3 ^ n),
          Complex.normSq
            (ZMod.dft (fun x => ((h x : ℝ) : ℂ)) xi) := by
          rw [Finset.mul_sum]
    _ = delta ^ 2 * (((3 ^ n : ℕ) : ℝ) *
        ∑ y : ZMod (3 ^ n),
          Complex.normSq ((h y : ℝ) : ℂ)) := by
            rw [tao_dft_normSq_parseval]
    _ = delta ^ 2 * ((3 ^ n : ℕ) : ℝ) *
        ∑ y : ZMod (3 ^ n), h y ^ 2 := by
          simp only [Complex.normSq_ofReal, pow_two]
          ring

/-- Event-free Section 6 collision inequality.  Exactly one factor `3^n`
survives; the real head and tail need not be positive or normalized. -/
theorem taoZModPowOscillation_rawConvolution_sq_le
    {m n : ℕ} (hmn : m ≤ n)
    (h tau : ZMod (3 ^ n) → ℝ) {delta : ℝ}
    (hdelta : 0 ≤ delta)
    (htau : ∀ xi : ZMod (3 ^ n),
      ¬zmodThreePowMultiple n (n - m) xi →
        ‖ZMod.dft (fun x => ((tau x : ℝ) : ℂ)) xi‖ ≤ delta) :
    taoZModPowOscillation m n (taoZModRawConvolution h tau) ^ 2 ≤
      delta ^ 2 * ((3 ^ n : ℕ) : ℝ) *
        ∑ y : ZMod (3 ^ n), h y ^ 2 := by
  let c : ZMod (3 ^ n) → ℝ := taoZModRawConvolution h tau
  let d : ZMod (3 ^ n) → ℝ := fun y =>
    c y - zmodPowFiberAverageScale m n * zmodPowFiberSum m n c y
  have hcauchy :
      (∑ y : ZMod (3 ^ n), |d y|) ^ 2 ≤
        ((3 ^ n : ℕ) : ℝ) * ∑ y : ZMod (3 ^ n), d y ^ 2 := by
    have hcs := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (ZMod (3 ^ n))))
      (f := fun y => |d y|)
    simpa [ZMod.card, sq_abs] using hcs
  calc
    taoZModPowOscillation m n (taoZModRawConvolution h tau) ^ 2 =
      (∑ y : ZMod (3 ^ n), |d y|) ^ 2 := by
        simp [taoZModPowOscillation, c, d]
    _ ≤ ((3 ^ n : ℕ) : ℝ) *
        ∑ y : ZMod (3 ^ n), d y ^ 2 := hcauchy
    _ = taoZModDiscardedConvolutionEnergy m n h tau := by
      simpa [c, d] using
        tao_rawConvolution_fiberDifference_parseval hmn h tau
    _ ≤ delta ^ 2 * ((3 ^ n : ℕ) : ℝ) *
        ∑ y : ZMod (3 ^ n), h y ^ 2 :=
      taoZModDiscardedConvolutionEnergy_le h tau hdelta htau

/-- Equivalent collision wrapper with the algebraic annihilator condition
used by generic Fourier consumers. -/
theorem taoZModPowOscillation_rawConvolution_sq_le_of_not_annihilated
    {m n : ℕ} (hmn : m ≤ n)
    (h tau : ZMod (3 ^ n) → ℝ) {delta : ℝ}
    (hdelta : 0 ≤ delta)
    (htau : ∀ xi : ZMod (3 ^ n),
      ((3 ^ m : ℕ) : ZMod (3 ^ n)) * xi ≠ 0 →
        ‖ZMod.dft (fun x => ((tau x : ℝ) : ℂ)) xi‖ ≤ delta) :
    taoZModPowOscillation m n (taoZModRawConvolution h tau) ^ 2 ≤
      delta ^ 2 * ((3 ^ n : ℕ) : ℝ) *
        ∑ y : ZMod (3 ^ n), h y ^ 2 := by
  apply taoZModPowOscillation_rawConvolution_sq_le hmn h tau hdelta
  intro xi hsource
  apply htau xi
  intro hret
  exact hsource ((zmodPowFiberFrequency_retained_iff hmn xi).mp hret)

/-- If every discarded tail coefficient vanishes, then the raw convolution
has zero fine-scale oscillation. -/
theorem taoZModPowOscillation_rawConvolution_eq_zero_of_dft_eq_zero
    {m n : ℕ} (hmn : m ≤ n)
    (h tau : ZMod (3 ^ n) → ℝ)
    (htau : ∀ xi : ZMod (3 ^ n),
      ¬zmodThreePowMultiple n (n - m) xi →
        ZMod.dft (fun x => ((tau x : ℝ) : ℂ)) xi = 0) :
    taoZModPowOscillation m n (taoZModRawConvolution h tau) = 0 := by
  have hsq := taoZModPowOscillation_rawConvolution_sq_le
    hmn h tau (delta := 0) (by norm_num) (by
      intro xi hsource
      rw [htau xi hsource]
      simp)
  have hnonneg := sq_nonneg
    (taoZModPowOscillation m n (taoZModRawConvolution h tau))
  norm_num at hsq
  nlinarith

/-- At `m=n` the fiber average is the identity, so every raw convolution has
zero oscillation.  This includes the singleton endpoint `n=0`. -/
theorem taoZModPowOscillation_rawConvolution_top_eq_zero
    (n : ℕ) (h tau : ZMod (3 ^ n) → ℝ) :
    taoZModPowOscillation n n (taoZModRawConvolution h tau) = 0 := by
  apply taoZModPowOscillation_rawConvolution_eq_zero_of_dft_eq_zero
    (hmn := le_rfl) h tau
  intro xi hsource
  exact (hsource ⟨xi, by simp [zmodThreePowMultiple]⟩).elim

end

end Tao
end Erdos1135SecondScale
