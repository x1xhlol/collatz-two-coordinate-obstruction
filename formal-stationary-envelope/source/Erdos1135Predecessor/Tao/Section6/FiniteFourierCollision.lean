/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Section6.FiberAverageDFT
import Erdos1135Predecessor.Tao.Section6.FiniteFourierConvolution
import Erdos1135Predecessor.Tao.Section6.FiniteFourierParseval
import Mathlib.Algebra.Order.Chebyshev

open scoped BigOperators

open scoped ZMod

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

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

noncomputable def taoZModDiscardedConvolutionEnergy
    (m n : ℕ) (h tau : ZMod (3 ^ n) → ℝ) : ℝ := by
  classical
  exact
    ∑ xi : ZMod (3 ^ n),
      if zmodThreePowMultiple n (n - m) xi then 0 else
        Complex.normSq
          (ZMod.dft (fun x => ((h x : ℝ) : ℂ)) xi *
            ZMod.dft (fun x => ((tau x : ℝ) : ℂ)) xi)

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

end

end Tao

end Erdos1135Predecessor
