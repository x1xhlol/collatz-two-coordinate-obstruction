/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.TerminalTotalCancellation
import Erdos1135Predecessor.Tao.Probability.Geom2ListProjectivity

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

open scoped BigOperators

noncomputable section

theorem nd_tsum_pmf_toReal_eq_one
    {alpha : Type*} (p : PMF alpha) :
    (∑' x : alpha, (p x).toReal) = 1 := by
  have h := congrArg ENNReal.toReal (PMF.tsum_coe p)
  rw [ENNReal.tsum_toReal_eq (PMF.apply_ne_top p)] at h
  simpa using h

theorem nd_pmf_bind_apply_toReal_eq_tsum
    {alpha beta : Type*} (p : PMF alpha) (K : alpha → PMF beta)
    (y : beta) :
    ((p.bind K) y).toReal =
      ∑' x, (p x).toReal * (K x y).toReal := by
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro x
    rw [ENNReal.toReal_mul]
  · intro x
    exact ENNReal.mul_ne_top
      (p.apply_ne_top x) ((K x).apply_ne_top y)

theorem summable_pmf_mul_kernel_atom_toReal
    {alpha beta : Type*} (p : PMF alpha) (K : alpha → PMF beta)
    (y : beta) :
    Summable fun x => (p x).toReal * (K x y).toReal := by
  apply Summable.of_nonneg_of_le
  · intro x
    positivity
  · intro x
    have hK : (K x y).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (by simp) ((K x).coe_le_one y)
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg hK
  · exact Tao.taoPMF_summable_toReal p

theorem summable_pmf_kernel_product_toReal
    {alpha beta : Type*} (p : PMF alpha) (K : alpha → PMF beta) :
    Summable fun xy : alpha × beta =>
      (p xy.1).toReal * (K xy.1 xy.2).toReal := by
  have hnonneg : ∀ xy : alpha × beta,
      0 ≤ (p xy.1).toReal * (K xy.1 xy.2).toReal := by
    intro xy
    positivity
  rw [summable_prod_of_nonneg hnonneg]
  constructor
  · intro x
    exact (Tao.taoPMF_summable_toReal (K x)).mul_left (p x).toReal
  · have heq : (fun x : alpha =>
        ∑' y : beta, (p x).toReal * (K x y).toReal) =
        (fun x => (p x).toReal) := by
      funext x
      rw [tsum_mul_left, nd_tsum_pmf_toReal_eq_one, mul_one]
    rw [heq]
    exact Tao.taoPMF_summable_toReal p

theorem summable_pmf_kernel_mul_of_abs_le
    {alpha beta : Type*} (p : PMF alpha) (K : alpha → PMF beta)
    (phi : beta → ℝ) (H : ℝ) (_hH : 0 ≤ H)
    (hphi : ∀ y, |phi y| ≤ H) :
    Summable fun xy : alpha × beta =>
      (p xy.1).toReal * (K xy.1 xy.2).toReal * phi xy.2 := by
  let majorant : alpha × beta → ℝ := fun xy =>
    (p xy.1).toReal * (K xy.1 xy.2).toReal * H
  have hmajorant : Summable majorant :=
    (summable_pmf_kernel_product_toReal p K).mul_right H
  refine Summable.of_norm_bounded hmajorant ?_
  intro xy
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
  exact mul_le_mul_of_nonneg_left (hphi xy.2)
    (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

theorem ndPMFWeightedExpectation_bind_of_abs_le
    {alpha beta : Type*} (p : PMF alpha) (K : alpha → PMF beta)
    (phi : beta → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hphi : ∀ y, |phi y| ≤ H) :
    ndPMFWeightedExpectation (p.bind K) phi =
      ndPMFWeightedExpectation p
        (fun x => ndPMFWeightedExpectation (K x) phi) := by
  have hrow : ∀ y : beta, Summable fun x : alpha =>
      (p x).toReal * (K x y).toReal * phi y := by
    intro y
    exact (summable_pmf_mul_kernel_atom_toReal p K y).mul_right (phi y)
  have hcol : ∀ x : alpha, Summable fun y : beta =>
      (p x).toReal * (K x y).toReal * phi y := by
    intro x
    simpa [mul_assoc] using
      (summable_pmf_toReal_mul_of_abs_le
        (K x) phi H hH hphi).mul_left (p x).toReal
  have hjoint := summable_pmf_kernel_mul_of_abs_le p K phi H hH hphi
  unfold ndPMFWeightedExpectation
  simp_rw [nd_pmf_bind_apply_toReal_eq_tsum]
  calc
    (∑' y : beta,
        (∑' x : alpha, (p x).toReal * (K x y).toReal) * phi y) =
        ∑' y : beta, ∑' x : alpha,
          (p x).toReal * (K x y).toReal * phi y := by
      apply tsum_congr
      intro y
      rw [← tsum_mul_right]
    _ = ∑' x : alpha, ∑' y : beta,
          (p x).toReal * (K x y).toReal * phi y := by
      exact hjoint.tsum_comm' hcol hrow
    _ = ∑' x : alpha, (p x).toReal *
          ∑' y : beta, (K x y).toReal * phi y := by
      apply tsum_congr
      intro x
      rw [← tsum_mul_left]
      simp only [mul_assoc]

theorem ndPMFWeightedExpectation_pure
    {alpha : Type*} (x : alpha) (phi : alpha → ℝ) :
    ndPMFWeightedExpectation (PMF.pure x) phi = phi x := by
  unfold ndPMFWeightedExpectation
  rw [tsum_eq_single x]
  · simp
  · intro y hy
    simp [hy]

theorem ndPMFWeightedExpectation_map_of_abs_le
    {alpha beta : Type*} (p : PMF alpha) (f : alpha → beta)
    (phi : beta → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hphi : ∀ y, |phi y| ≤ H) :
    ndPMFWeightedExpectation (p.map f) phi =
      ndPMFWeightedExpectation p (fun x => phi (f x)) := by
  rw [← PMF.bind_pure_comp]
  rw [ndPMFWeightedExpectation_bind_of_abs_le p
    (PMF.pure ∘ f) phi H hH hphi]
  apply tsum_congr
  intro x
  change (p x).toReal *
      ndPMFWeightedExpectation (PMF.pure (f x)) phi =
    (p x).toReal * phi (f x)
  rw [ndPMFWeightedExpectation_pure]

theorem ndPMFWeightedExpectation_const_mul
    {alpha : Type*} (p : PMF alpha) (c : ℝ) (phi : alpha → ℝ) :
    ndPMFWeightedExpectation p (fun x => c * phi x) =
      c * ndPMFWeightedExpectation p phi := by
  unfold ndPMFWeightedExpectation
  calc
    (∑' x, (p x).toReal * (c * phi x)) =
        ∑' x, c * ((p x).toReal * phi x) := by
      apply tsum_congr
      intro x
      ring
    _ = c * ∑' x, (p x).toReal * phi x := by
      rw [tsum_mul_left]

theorem ndPMFWeightedExpectation_geom2_append
    (K N : ℕ) (phi : List ℕ+ → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hphi : ∀ full, |phi full| ≤ H) :
    ndPMFWeightedExpectation (Tao.geom2PNatListPMF (K + N)) phi =
      ndPMFWeightedExpectation (Tao.geom2PNatListPMF K) (fun pre =>
        ndPMFWeightedExpectation (Tao.geom2PNatListPMF N) (fun future =>
          phi (pre ++ future))) := by
  let split : List ℕ+ → List ℕ+ × List ℕ+ := fun full =>
    (full.take K, full.drop K)
  let join : List ℕ+ × List ℕ+ → List ℕ+ := fun pair =>
    pair.1 ++ pair.2
  have hjoin : ∀ full : List ℕ+, join (split full) = full := by
    intro full
    exact List.take_append_drop K full
  have hjoinBound : ∀ pair : List ℕ+ × List ℕ+,
      |phi (join pair)| ≤ H := fun pair => hphi (join pair)
  calc
    ndPMFWeightedExpectation (Tao.geom2PNatListPMF (K + N)) phi =
        ndPMFWeightedExpectation
          ((Tao.geom2PNatListPMF (K + N)).map split)
          (fun pair => phi (join pair)) := by
      rw [ndPMFWeightedExpectation_map_of_abs_le
        (Tao.geom2PNatListPMF (K + N)) split
        (fun pair => phi (join pair)) H hH hjoinBound]
      unfold ndPMFWeightedExpectation
      apply tsum_congr
      intro full
      change ((Tao.geom2PNatListPMF (K + N)) full).toReal * phi full =
        ((Tao.geom2PNatListPMF (K + N)) full).toReal *
          phi (join (split full))
      rw [hjoin]
    _ = ndPMFWeightedExpectation
          ((Tao.geom2PNatListPMF K).bind fun pre =>
            (Tao.geom2PNatListPMF N).map fun future => (pre, future))
          (fun pair => phi (join pair)) := by
      rw [Tao.geom2PNatListPMF_map_take_drop_low_eq]
    _ = ndPMFWeightedExpectation (Tao.geom2PNatListPMF K) (fun pre =>
          ndPMFWeightedExpectation
            ((Tao.geom2PNatListPMF N).map fun future => (pre, future))
            (fun pair => phi (join pair))) := by
      rw [ndPMFWeightedExpectation_bind_of_abs_le
        (Tao.geom2PNatListPMF K)
        (fun pre =>
          (Tao.geom2PNatListPMF N).map fun future => (pre, future))
        (fun pair => phi (join pair)) H hH hjoinBound]
    _ = ndPMFWeightedExpectation (Tao.geom2PNatListPMF K) (fun pre =>
          ndPMFWeightedExpectation (Tao.geom2PNatListPMF N) (fun future =>
            phi (pre ++ future))) := by
      unfold ndPMFWeightedExpectation
      apply tsum_congr
      intro pre
      change ((Tao.geom2PNatListPMF K) pre).toReal *
          ndPMFWeightedExpectation
            ((Tao.geom2PNatListPMF N).map fun future => (pre, future))
            (fun pair => phi (join pair)) =
        ((Tao.geom2PNatListPMF K) pre).toReal *
          ndPMFWeightedExpectation (Tao.geom2PNatListPMF N)
            (fun future => phi (pre ++ future))
      rw [ndPMFWeightedExpectation_map_of_abs_le
        (Tao.geom2PNatListPMF N) (fun future => (pre, future))
        (fun pair => phi (join pair)) H hH hjoinBound]

end

end PositiveDensity

end ND

end Erdos1135Predecessor
