/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.CanonicalFirstPassageHorizontal
import Erdos1135SecondScale.Tao.Renewal.Lemma77LocalLimit

/-!
# Canonical First-Passage Tail Bounds

This proof leaf develops the two countable tail estimates used after Tao's
Lemma 7.7: a two-sided horizontal-deviation tail and a vertical-overshoot
tail.  The horizontal lattice is embedded into `ℤ` by `r ↦ 4r - s`, avoiding
any finite carrier or horizontal cutoff.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

namespace TaoSection7Lemma77

/-- Integer lattice coordinate for four times the centered horizontal
displacement. -/
def lemma77HorizontalIntIndex (s r : ℕ) : ℤ :=
  4 * (r : ℤ) - (s : ℤ)

theorem lemma77HorizontalIntIndex_injective (s : ℕ) :
    Function.Injective (lemma77HorizontalIntIndex s) := by
  intro r r' h
  unfold lemma77HorizontalIntIndex at h
  omega

theorem lemma77CenteredHorizontalDisplacement_eq_intIndex_div_four
    (s r : ℕ) :
    lemma77CenteredHorizontalDisplacement s r =
      (lemma77HorizontalIntIndex s r : ℝ) / 4 := by
  unfold lemma77CenteredHorizontalDisplacement lemma77HorizontalIntIndex
  push_cast
  ring

/-- The Gaussian horizontal profile is summable on the natural endpoint
lattice. -/
theorem lemma77HorizontalGaussianProfile_summable
    {a : ℝ} (ha : 0 < a) (s : ℕ) :
    Summable fun r : ℕ =>
      Real.exp
        (-a * ((lemma77CenteredHorizontalDisplacement s r) ^ 2 /
          (1 + (s : ℝ)))) := by
  let S : ℝ := 1 + (s : ℝ)
  let idx : ℕ → ℤ := lemma77HorizontalIntIndex s
  have hS : 0 < S := by positivity
  have ha16 : 0 < a / 16 := by positivity
  have h :=
    (lemma77ExpNegMulIntSqDiv_summable ha16 hS).comp_injective
      (lemma77HorizontalIntIndex_injective s)
  convert h using 1
  ext r
  rw [lemma77CenteredHorizontalDisplacement_eq_intIndex_div_four]
  dsimp [S, idx]
  congr 1
  ring

/-- The linear horizontal profile is summable on the natural endpoint
lattice. -/
theorem lemma77HorizontalLinearProfile_summable
    {b : ℝ} (hb : 0 < b) (s : ℕ) :
    Summable fun r : ℕ =>
      Real.exp
        (-(b * |lemma77CenteredHorizontalDisplacement s r|)) := by
  let idx : ℕ → ℤ := lemma77HorizontalIntIndex s
  have hb4 : 0 < b / 4 := by positivity
  have h :=
    (lemma77ExpNegMulIntAbs_summable hb4).comp_injective
      (lemma77HorizontalIntIndex_injective s)
  convert h using 1
  ext r
  rw [lemma77CenteredHorizontalDisplacement_eq_intIndex_div_four]
  dsimp [idx]
  rw [abs_div]
  norm_num
  ring

/-- Explicit Gaussian lattice-count bound at horizontal scale `1+s`. -/
theorem lemma77HorizontalGaussianProfile_tsum_le_sqrt
    {a : ℝ} (ha : 0 < a) (s : ℕ) :
    (∑' r : ℕ,
      Real.exp
        (-a * ((lemma77CenteredHorizontalDisplacement s r) ^ 2 /
          (1 + (s : ℝ))))) ≤
      (2 * Real.exp ((a / 16) / 4) * Real.exp (a / 16) / (a / 16)) *
        Real.sqrt (1 + (s : ℝ)) := by
  let S : ℝ := 1 + (s : ℝ)
  let idx : ℕ → ℤ := lemma77HorizontalIntIndex s
  let f : ℤ → ℝ := fun z =>
    Real.exp (-((a / 16) * (z : ℝ) ^ 2 / S))
  have hS : 0 < S := by positivity
  have hS1 : 1 ≤ S := by
    dsimp [S]
    exact le_add_of_nonneg_right (Nat.cast_nonneg s)
  have ha16 : 0 < a / 16 := by positivity
  have hsum_eq :
      (∑' r : ℕ,
        Real.exp
          (-a * ((lemma77CenteredHorizontalDisplacement s r) ^ 2 /
            (1 + (s : ℝ))))) =
        ∑' r : ℕ, f (idx r) := by
    apply tsum_congr
    intro r
    rw [lemma77CenteredHorizontalDisplacement_eq_intIndex_div_four]
    dsimp [f, idx, S]
    congr 1
    ring
  have hcomp : Summable fun r : ℕ => f (idx r) :=
    (lemma77ExpNegMulIntSqDiv_summable ha16 hS).comp_injective
      (lemma77HorizontalIntIndex_injective s)
  calc
    (∑' r : ℕ,
      Real.exp
        (-a * ((lemma77CenteredHorizontalDisplacement s r) ^ 2 /
          (1 + (s : ℝ))))) = ∑' r : ℕ, f (idx r) := hsum_eq
    _ ≤ ∑' z : ℤ, f z :=
      tsum_comp_le_tsum_of_inj
        (lemma77ExpNegMulIntSqDiv_summable ha16 hS)
        (fun _ => (Real.exp_pos _).le)
        (lemma77HorizontalIntIndex_injective s)
    _ ≤ (2 * Real.exp ((a / 16) / 4) * Real.exp (a / 16) / (a / 16)) *
        Real.sqrt (1 + (s : ℝ)) := by
      simpa [f, S] using
        lemma77ExpNegMulIntSqDiv_tsum_le_sqrt_explicit ha16 hS1

/-- Explicit uniform linear lattice-count bound. -/
theorem lemma77HorizontalLinearProfile_tsum_le
    {b : ℝ} (hb : 0 < b) (s : ℕ) :
    (∑' r : ℕ,
      Real.exp (-(b * |lemma77CenteredHorizontalDisplacement s r|))) ≤
      2 * (1 - Real.exp (-(b / 4)))⁻¹ := by
  let idx : ℕ → ℤ := lemma77HorizontalIntIndex s
  let f : ℤ → ℝ := fun z =>
    Real.exp (-((b / 4) * |(z : ℝ)|))
  have hb4 : 0 < b / 4 := by positivity
  have hsum_eq :
      (∑' r : ℕ,
        Real.exp (-(b * |lemma77CenteredHorizontalDisplacement s r|))) =
        ∑' r : ℕ, f (idx r) := by
    apply tsum_congr
    intro r
    rw [lemma77CenteredHorizontalDisplacement_eq_intIndex_div_four]
    dsimp [f, idx]
    rw [abs_div]
    norm_num
    ring
  calc
    (∑' r : ℕ,
      Real.exp (-(b * |lemma77CenteredHorizontalDisplacement s r|))) =
        ∑' r : ℕ, f (idx r) := hsum_eq
    _ ≤ ∑' z : ℤ, f z :=
      tsum_comp_le_tsum_of_inj
        (lemma77ExpNegMulIntAbs_summable hb4)
        (fun _ => (Real.exp_pos _).le)
        (lemma77HorizontalIntIndex_injective s)
    _ ≤ 2 * (1 - Real.exp (-(b / 4)))⁻¹ := by
      simpa [f] using lemma77ExpNegMulIntAbs_tsum_le hb4

/-- Explicit constant in the Gaussian horizontal lattice count. -/
def lemma77HorizontalGaussianCountConstant (a : ℝ) : ℝ :=
  2 * Real.exp ((a / 16) / 4) * Real.exp (a / 16) / (a / 16)

/-- Explicit constant in the linear horizontal lattice count. -/
def lemma77HorizontalLinearCountConstant (b : ℝ) : ℝ :=
  2 * (1 - Real.exp (-(b / 4)))⁻¹

theorem lemma77HorizontalGaussianCountConstant_nonneg
    {a : ℝ} (ha : 0 < a) :
    0 ≤ lemma77HorizontalGaussianCountConstant a := by
  unfold lemma77HorizontalGaussianCountConstant
  positivity

theorem lemma77HorizontalLinearCountConstant_nonneg
    {b : ℝ} (hb : 0 < b) :
    0 ≤ lemma77HorizontalLinearCountConstant b := by
  unfold lemma77HorizontalLinearCountConstant
  have hlt : Real.exp (-(b / 4)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hpos : 0 < 1 - Real.exp (-(b / 4)) := by linarith
  positivity

/-- The height prefactor exactly cancels the square-root Gaussian lattice
count. -/
theorem lemma77_rpow_neg_half_mul_sqrt_one_add (s : ℕ) :
    ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) *
      Real.sqrt (1 + (s : ℝ)) = 1 := by
  let S : ℝ := 1 + (s : ℝ)
  have hS : 0 < S := by positivity
  have hsqrt : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  rw [show 1 + (s : ℝ) = S by rfl]
  rw [Real.rpow_neg hS.le, ← Real.sqrt_eq_rpow]
  field_simp [hsqrt.ne']

/-- The height prefactor is at most one. -/
theorem lemma77_rpow_neg_half_one_add_le_one (s : ℕ) :
    (1 + (s : ℝ)) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (le_add_of_nonneg_right (Nat.cast_nonneg s)) (by norm_num)

/-- The horizontally marginalized pointwise kernel is summable over every
natural horizontal endpoint. -/
theorem lemma77HorizontalPointwiseKernel_summable
    {a b C : ℝ} (ha : 0 < a) (hb : 0 < b) (s : ℕ) :
    Summable fun r : ℕ =>
      lemma77HorizontalPointwiseKernel a b C s r := by
  let g : ℕ → ℝ := fun r =>
    Real.exp
      (-a * ((lemma77CenteredHorizontalDisplacement s r) ^ 2 /
        (1 + (s : ℝ))))
  let l : ℕ → ℝ := fun r =>
    Real.exp (-(b * |lemma77CenteredHorizontalDisplacement s r|))
  have hg : Summable g := by
    simpa [g] using lemma77HorizontalGaussianProfile_summable ha s
  have hl : Summable l := by
    simpa [l] using lemma77HorizontalLinearProfile_summable hb s
  simpa [lemma77HorizontalPointwiseKernel, g, l] using
    (hg.add hl).mul_left
      (C * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))))

/-- Uniform total mass bound for the horizontal pointwise kernel. -/
theorem lemma77HorizontalPointwiseKernel_tsum_le
    {a b C : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 ≤ C) (s : ℕ) :
    (∑' r : ℕ, lemma77HorizontalPointwiseKernel a b C s r) ≤
      C * (lemma77HorizontalGaussianCountConstant a +
        lemma77HorizontalLinearCountConstant b) := by
  let S : ℝ := 1 + (s : ℝ)
  let H : ℝ := S ^ (-(1 / 2 : ℝ))
  let g : ℕ → ℝ := fun r =>
    Real.exp (-a * ((lemma77CenteredHorizontalDisplacement s r) ^ 2 / S))
  let l : ℕ → ℝ := fun r =>
    Real.exp (-(b * |lemma77CenteredHorizontalDisplacement s r|))
  have hg : Summable g := by
    simpa [g, S] using lemma77HorizontalGaussianProfile_summable ha s
  have hl : Summable l := by
    simpa [l] using lemma77HorizontalLinearProfile_summable hb s
  have hg_bound :
      (∑' r : ℕ, g r) ≤
        lemma77HorizontalGaussianCountConstant a * Real.sqrt S := by
    simpa [g, S, lemma77HorizontalGaussianCountConstant] using
      lemma77HorizontalGaussianProfile_tsum_le_sqrt ha s
  have hl_bound :
      (∑' r : ℕ, l r) ≤ lemma77HorizontalLinearCountConstant b := by
    simpa [l, lemma77HorizontalLinearCountConstant] using
      lemma77HorizontalLinearProfile_tsum_le hb s
  have hH : 0 ≤ H := by
    dsimp [H]
    positivity
  have hCH : 0 ≤ C * H := mul_nonneg hC hH
  have hG : 0 ≤ lemma77HorizontalGaussianCountConstant a :=
    lemma77HorizontalGaussianCountConstant_nonneg ha
  have hL : 0 ≤ lemma77HorizontalLinearCountConstant b :=
    lemma77HorizontalLinearCountConstant_nonneg hb
  have hHle : H ≤ 1 := by
    simpa [H, S] using lemma77_rpow_neg_half_one_add_le_one s
  have hHsqrt : H * Real.sqrt S = 1 := by
    simpa [H, S] using lemma77_rpow_neg_half_mul_sqrt_one_add s
  calc
    (∑' r : ℕ, lemma77HorizontalPointwiseKernel a b C s r) =
        C * H * ((∑' r : ℕ, g r) + ∑' r : ℕ, l r) := by
      calc
        (∑' r : ℕ, lemma77HorizontalPointwiseKernel a b C s r) =
            ∑' r : ℕ, C * H * (g r + l r) := by
          apply tsum_congr
          intro r
          simp [lemma77HorizontalPointwiseKernel, H, S, g, l]
        _ = C * H * ((∑' r : ℕ, g r) + ∑' r : ℕ, l r) := by
          rw [tsum_mul_left, hg.tsum_add hl]
    _ ≤ C * H *
        (lemma77HorizontalGaussianCountConstant a * Real.sqrt S +
          lemma77HorizontalLinearCountConstant b) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add hg_bound hl_bound) hCH
    _ = C * (lemma77HorizontalGaussianCountConstant a +
          H * lemma77HorizontalLinearCountConstant b) := by
      calc
        C * H *
            (lemma77HorizontalGaussianCountConstant a * Real.sqrt S +
              lemma77HorizontalLinearCountConstant b) =
            C * (lemma77HorizontalGaussianCountConstant a *
                (H * Real.sqrt S) +
              H * lemma77HorizontalLinearCountConstant b) := by ring
        _ = C * (lemma77HorizontalGaussianCountConstant a +
              H * lemma77HorizontalLinearCountConstant b) := by
          rw [hHsqrt, mul_one]
    _ ≤ C * (lemma77HorizontalGaussianCountConstant a +
          lemma77HorizontalLinearCountConstant b) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact add_le_add le_rfl (mul_le_of_le_one_left hL hHle)

/-- Two-sided horizontal-deviation event around the Lemma 7.7 center `s/4`. -/
def lemma77CanonicalHorizontalDeviationEvent (s : ℕ) (t : ℝ) : Set ℕ :=
  {r | t ≤ |lemma77CenteredHorizontalDisplacement s r|}

/-- Explicit two-term envelope for the countable horizontal-deviation tail. -/
def lemma77HorizontalDeviationTailEnvelope
    (a b C : ℝ) (s : ℕ) (t : ℝ) : ℝ :=
  C *
    (lemma77HorizontalGaussianCountConstant (a / 2) *
        Real.exp (-(a / 2) * (t ^ 2 / (1 + (s : ℝ)))) +
      lemma77HorizontalLinearCountConstant (b / 2) *
        Real.exp (-(b / 2) * t))

/-- On a two-sided deviation event, half of each exponent supplies the tail
decay while half remains available for countable lattice summation. -/
theorem lemma77HorizontalPointwiseKernel_le_tailProduct
    {a b C t : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 ≤ C)
    (ht : 0 ≤ t) {s r : ℕ}
    (hr : r ∈ lemma77CanonicalHorizontalDeviationEvent s t) :
    lemma77HorizontalPointwiseKernel a b C s r ≤
      C * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) *
        (Real.exp (-(a / 2) * (t ^ 2 / (1 + (s : ℝ)))) *
            Real.exp (-(a / 2) *
              ((lemma77CenteredHorizontalDisplacement s r) ^ 2 /
                (1 + (s : ℝ)))) +
          Real.exp (-(b / 2) * t) *
            Real.exp (-(b / 2) *
              |lemma77CenteredHorizontalDisplacement s r|)) := by
  let x : ℝ := lemma77CenteredHorizontalDisplacement s r
  let S : ℝ := 1 + (s : ℝ)
  have hS : 0 < S := by positivity
  have htx : t ≤ |x| := by simpa [lemma77CanonicalHorizontalDeviationEvent, x] using hr
  have hsq : t ^ 2 ≤ x ^ 2 := by
    have := (sq_le_sq₀ ht (abs_nonneg x)).2 htx
    simpa [sq_abs] using this
  have hgauss_decay :
      Real.exp (-(a / 2) * (x ^ 2 / S)) ≤
        Real.exp (-(a / 2) * (t ^ 2 / S)) := by
    rw [Real.exp_le_exp]
    have hdiv : t ^ 2 / S ≤ x ^ 2 / S :=
      div_le_div_of_nonneg_right hsq hS.le
    nlinarith [mul_le_mul_of_nonneg_left hdiv (show 0 ≤ a / 2 by positivity)]
  have hlinear_decay :
      Real.exp (-(b / 2) * |x|) ≤ Real.exp (-(b / 2) * t) := by
    rw [Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_left htx (show 0 ≤ b / 2 by positivity)]
  have hgauss_split :
      Real.exp (-a * (x ^ 2 / S)) =
        Real.exp (-(a / 2) * (x ^ 2 / S)) *
          Real.exp (-(a / 2) * (x ^ 2 / S)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hlinear_split :
      Real.exp (-b * |x|) =
        Real.exp (-(b / 2) * |x|) * Real.exp (-(b / 2) * |x|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hgauss :
      Real.exp (-a * (x ^ 2 / S)) ≤
        Real.exp (-(a / 2) * (t ^ 2 / S)) *
          Real.exp (-(a / 2) * (x ^ 2 / S)) := by
    rw [hgauss_split]
    exact mul_le_mul_of_nonneg_right hgauss_decay (Real.exp_pos _).le
  have hlinear :
      Real.exp (-b * |x|) ≤
        Real.exp (-(b / 2) * t) * Real.exp (-(b / 2) * |x|) := by
    rw [hlinear_split]
    exact mul_le_mul_of_nonneg_right hlinear_decay (Real.exp_pos _).le
  unfold lemma77HorizontalPointwiseKernel
  dsimp [x, S] at hgauss hlinear ⊢
  exact mul_le_mul_of_nonneg_left
    (add_le_add hgauss hlinear)
    (mul_nonneg hC (by positivity))

/-- Countable two-sided horizontal kernel tail with no finite cutoff. -/
theorem lemma77HorizontalPointwiseKernel_deviation_tsum_le
    {a b C t : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 ≤ C)
    (ht : 0 ≤ t) (s : ℕ) :
    (∑' r : ℕ,
      (lemma77CanonicalHorizontalDeviationEvent s t).indicator
        (fun r => lemma77HorizontalPointwiseKernel a b C s r) r) ≤
      lemma77HorizontalDeviationTailEnvelope a b C s t := by
  let S : ℝ := 1 + (s : ℝ)
  let H : ℝ := S ^ (-(1 / 2 : ℝ))
  let Eg : ℝ := Real.exp (-(a / 2) * (t ^ 2 / S))
  let El : ℝ := Real.exp (-(b / 2) * t)
  let g : ℕ → ℝ := fun r =>
    Real.exp (-(a / 2) *
      ((lemma77CenteredHorizontalDisplacement s r) ^ 2 / S))
  let l : ℕ → ℝ := fun r =>
    Real.exp (-(b / 2) * |lemma77CenteredHorizontalDisplacement s r|)
  let major : ℕ → ℝ := fun r => C * H * (Eg * g r + El * l r)
  have ha2 : 0 < a / 2 := by positivity
  have hb2 : 0 < b / 2 := by positivity
  have hg : Summable g := by
    simpa [g, S] using lemma77HorizontalGaussianProfile_summable ha2 s
  have hl : Summable l := by
    simpa [l] using lemma77HorizontalLinearProfile_summable hb2 s
  have hmajor : Summable major := by
    exact (((hg.mul_left Eg).add (hl.mul_left El)).mul_left (C * H))
  have hfiltered : Summable fun r : ℕ =>
      (lemma77CanonicalHorizontalDeviationEvent s t).indicator
        (fun r => lemma77HorizontalPointwiseKernel a b C s r) r :=
    (lemma77HorizontalPointwiseKernel_summable ha hb s).indicator _
  have hpoint : ∀ r : ℕ,
      (lemma77CanonicalHorizontalDeviationEvent s t).indicator
          (fun r => lemma77HorizontalPointwiseKernel a b C s r) r ≤
        major r := by
    intro r
    by_cases hr : r ∈ lemma77CanonicalHorizontalDeviationEvent s t
    · rw [Set.indicator_of_mem hr]
      simpa [major, H, S, Eg, El, g, l] using
        lemma77HorizontalPointwiseKernel_le_tailProduct ha hb hC ht hr
    · simp only [Set.indicator, hr, if_false]
      unfold major
      positivity
  have hsum_le := hfiltered.tsum_le_tsum hpoint hmajor
  have hg_bound :
      (∑' r : ℕ, g r) ≤
        lemma77HorizontalGaussianCountConstant (a / 2) * Real.sqrt S := by
    simpa [g, S, lemma77HorizontalGaussianCountConstant] using
      lemma77HorizontalGaussianProfile_tsum_le_sqrt ha2 s
  have hl_bound :
      (∑' r : ℕ, l r) ≤
        lemma77HorizontalLinearCountConstant (b / 2) := by
    simpa [l, lemma77HorizontalLinearCountConstant] using
      lemma77HorizontalLinearProfile_tsum_le hb2 s
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hCH : 0 ≤ C * H := mul_nonneg hC hH
  have hEg : 0 ≤ Eg := (Real.exp_pos _).le
  have hEl : 0 ≤ El := (Real.exp_pos _).le
  have hG : 0 ≤ lemma77HorizontalGaussianCountConstant (a / 2) :=
    lemma77HorizontalGaussianCountConstant_nonneg ha2
  have hL : 0 ≤ lemma77HorizontalLinearCountConstant (b / 2) :=
    lemma77HorizontalLinearCountConstant_nonneg hb2
  have hHle : H ≤ 1 := by
    simpa [H, S] using lemma77_rpow_neg_half_one_add_le_one s
  have hHsqrt : H * Real.sqrt S = 1 := by
    simpa [H, S] using lemma77_rpow_neg_half_mul_sqrt_one_add s
  calc
    (∑' r : ℕ,
      (lemma77CanonicalHorizontalDeviationEvent s t).indicator
        (fun r => lemma77HorizontalPointwiseKernel a b C s r) r) ≤
        ∑' r : ℕ, major r := hsum_le
    _ = C * H * (Eg * (∑' r : ℕ, g r) + El * (∑' r : ℕ, l r)) := by
      unfold major
      rw [tsum_mul_left, (hg.mul_left Eg).tsum_add (hl.mul_left El),
        tsum_mul_left, tsum_mul_left]
    _ ≤ C * H *
        (Eg * (lemma77HorizontalGaussianCountConstant (a / 2) * Real.sqrt S) +
          El * lemma77HorizontalLinearCountConstant (b / 2)) := by
      apply mul_le_mul_of_nonneg_left _ hCH
      exact add_le_add
        (mul_le_mul_of_nonneg_left hg_bound hEg)
        (mul_le_mul_of_nonneg_left hl_bound hEl)
    _ = C *
        (lemma77HorizontalGaussianCountConstant (a / 2) * Eg +
          H * lemma77HorizontalLinearCountConstant (b / 2) * El) := by
      calc
        C * H *
            (Eg *
                (lemma77HorizontalGaussianCountConstant (a / 2) * Real.sqrt S) +
              El * lemma77HorizontalLinearCountConstant (b / 2)) =
            C *
              (lemma77HorizontalGaussianCountConstant (a / 2) * Eg *
                  (H * Real.sqrt S) +
                H * lemma77HorizontalLinearCountConstant (b / 2) * El) := by ring
        _ = C *
            (lemma77HorizontalGaussianCountConstant (a / 2) * Eg +
              H * lemma77HorizontalLinearCountConstant (b / 2) * El) := by
          rw [hHsqrt, mul_one]
    _ ≤ C *
        (lemma77HorizontalGaussianCountConstant (a / 2) * Eg +
          lemma77HorizontalLinearCountConstant (b / 2) * El) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left hL hHle) hEl
    _ = lemma77HorizontalDeviationTailEnvelope a b C s t := by
      rfl

/-- Native PMF event bound from a summable nonnegative real atom majorant. -/
theorem pmf_toOuterMeasure_le_of_apply_le_ofReal
    {α : Type*} (p : PMF α) (E : Set α) (f : α → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf : Summable (E.indicator f))
    (hpoint : ∀ x ∈ E, p x ≤ ENNReal.ofReal (f x)) :
    p.toOuterMeasure E ≤ ENNReal.ofReal (∑' x, E.indicator f x) := by
  classical
  rw [PMF.toOuterMeasure_apply]
  calc
    (∑' x : α, E.indicator (fun x => p x) x) ≤
        ∑' x : α, E.indicator (fun x => ENNReal.ofReal (f x)) x := by
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases hx : x ∈ E
      · simp [Set.indicator, hx, hpoint x hx]
      · simp [Set.indicator, hx]
    _ = ∑' x : α, ENNReal.ofReal (E.indicator f x) := by
      apply tsum_congr
      intro x
      by_cases hx : x ∈ E <;> simp [Set.indicator, hx]
    _ = ENNReal.ofReal (∑' x : α, E.indicator f x) := by
      symm
      apply ENNReal.ofReal_tsum_of_nonneg
      · intro x
        by_cases hx : x ∈ E <;> simp [Set.indicator, hx, hf_nonneg]
      · exact hf

/-- Native two-sided horizontal-deviation tail for the canonical
first-passage law. -/
theorem lemma77CanonicalFirstPassageHorizontalPMF_deviationTail :
    ∃ C32 c32 : ℝ, 0 ≤ C32 ∧ 0 < c32 ∧
      ∀ (start : TaoSection7RenewalPoint) (s : ℕ) (t : ℝ), 0 ≤ t →
        (lemma77CanonicalFirstPassageHorizontalPMF start s).toOuterMeasure
            (lemma77CanonicalHorizontalDeviationEvent s t) ≤
          ENNReal.ofReal
            (lemma77HorizontalDeviationTailEnvelope
              (c32 ^ 2) c32 (300 * C32) s t) := by
  rcases lemma77CanonicalFirstPassageHorizontalPMF_pointwiseKernel with
    ⟨C32, c32, hC32, hc32, hpoint⟩
  refine ⟨C32, c32, hC32, hc32, ?_⟩
  intro start s t ht
  let f : ℕ → ℝ := fun r =>
    lemma77HorizontalPointwiseKernel (c32 ^ 2) c32 (300 * C32) s r
  have ha : 0 < c32 ^ 2 := sq_pos_of_pos hc32
  have hC : 0 ≤ 300 * C32 := mul_nonneg (by norm_num) hC32
  have hf_nonneg : ∀ r, 0 ≤ f r := by
    intro r
    unfold f lemma77HorizontalPointwiseKernel
    positivity
  have hf : Summable f := by
    simpa [f] using
      lemma77HorizontalPointwiseKernel_summable ha hc32 s
        (C := 300 * C32)
  have hnative := pmf_toOuterMeasure_le_of_apply_le_ofReal
    (lemma77CanonicalFirstPassageHorizontalPMF start s)
    (lemma77CanonicalHorizontalDeviationEvent s t) f hf_nonneg
    (hf.indicator _)
    (fun r _ => hpoint start s r)
  calc
    (lemma77CanonicalFirstPassageHorizontalPMF start s).toOuterMeasure
        (lemma77CanonicalHorizontalDeviationEvent s t) ≤
      ENNReal.ofReal
        (∑' r : ℕ,
          (lemma77CanonicalHorizontalDeviationEvent s t).indicator f r) :=
      hnative
    _ ≤ ENNReal.ofReal
        (lemma77HorizontalDeviationTailEnvelope
          (c32 ^ 2) c32 (300 * C32) s t) := by
      apply ENNReal.ofReal_le_ofReal
      simpa [f] using
        lemma77HorizontalPointwiseKernel_deviation_tsum_le
          ha hc32 hC ht s

/-- Upper vertical-overshoot event at natural threshold `T`. -/
def lemma77CanonicalVerticalOvershootTailEvent (s T : ℕ) : Set (ℕ × ℤ) :=
  {x | (s : ℤ) + (T : ℤ) ≤ x.2}

/-- The vertical tail ray is indexed by its horizontal coordinate and a
nonnegative offset beyond `T`. -/
private def lemma77VerticalOvershootTailEquiv (s T : ℕ) :
    ℕ × ℕ ≃ {x : ℕ × ℤ // x ∈ lemma77CanonicalVerticalOvershootTailEvent s T} where
  toFun x :=
    ⟨(x.1, (s : ℤ) + (T : ℤ) + (x.2 : ℤ)), by
      simp only [lemma77CanonicalVerticalOvershootTailEvent, Set.mem_setOf_eq]
      omega⟩
  invFun x :=
    (x.1.1, (x.1.2 - (s : ℤ) - (T : ℤ)).toNat)
  left_inv x := by
    apply Prod.ext
    · rfl
    · simp only
      omega
  right_inv x := by
    rcases x with ⟨⟨r, ell⟩, hx⟩
    simp only [lemma77CanonicalVerticalOvershootTailEvent,
      Set.mem_setOf_eq] at hx
    apply Subtype.ext
    change (r, (s : ℤ) + (T : ℤ) +
      (ell - (s : ℤ) - (T : ℤ)).toNat) = (r, ell)
    apply Prod.ext
    · rfl
    · simp only
      omega

/-- A shifted exponential ray over `ℕ` is summable. -/
theorem lemma77VerticalExponentialTail_summable
    {lambda : ℝ} (hlambda : 0 < lambda) (T : ℕ) :
    Summable fun u : ℕ =>
      Real.exp (-(lambda * (((T + u : ℕ) : ℝ)))) := by
  have hbase := lemma77ExpNegMulNat_summable hlambda
  have hscaled := hbase.mul_left
    (Real.exp (-(lambda * (T : ℝ))))
  convert hscaled using 1
  ext u
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

/-- At the concrete terminal rate, the overshoot ray beginning at `T` has
exact geometric mass `21 * exp (-lambda*T)`. -/
theorem lemma77_tsum_exp_neg_log_21_div_20_from
    (T : ℕ) :
    (∑' u : ℕ,
      Real.exp
        (-(Real.log (21 / 20 : ℝ) * (((T + u : ℕ) : ℝ))))) =
      21 * Real.exp (-(Real.log (21 / 20 : ℝ) * (T : ℝ))) := by
  let lambda : ℝ := Real.log (21 / 20 : ℝ)
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    exact Real.log_pos (by norm_num : (1 : ℝ) < 21 / 20)
  have hfactor :
      (∑' u : ℕ,
        Real.exp (-(lambda * (((T + u : ℕ) : ℝ))))) =
        Real.exp (-(lambda * (T : ℝ))) *
          ∑' u : ℕ, Real.exp (-(lambda * (u : ℝ))) := by
    calc
      (∑' u : ℕ,
          Real.exp (-(lambda * (((T + u : ℕ) : ℝ))))) =
          ∑' u : ℕ,
            Real.exp (-(lambda * (T : ℝ))) *
              Real.exp (-(lambda * (u : ℝ))) := by
        apply tsum_congr
        intro u
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      _ = Real.exp (-(lambda * (T : ℝ))) *
          ∑' u : ℕ, Real.exp (-(lambda * (u : ℝ))) := by
        rw [tsum_mul_left]
  rw [show Real.log (21 / 20 : ℝ) = lambda by rfl, hfactor,
    lemma77ExpNegMulNat_tsum hlambda]
  have hexp : Real.exp (-lambda) = 20 / 21 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : 0 < (21 / 20 : ℝ))]
    norm_num
  rw [hexp]
  norm_num
  ring

/-- Summability of the endpoint kernel after restricting to a vertical tail
ray. -/
theorem lemma77PointwiseEndpointKernel_verticalTail_summable
    {a b C lambda : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hC : 0 ≤ C) (hlambda : 0 < lambda) (s T : ℕ) :
    Summable fun x : ℕ × ℤ =>
      (lemma77CanonicalVerticalOvershootTailEvent s T).indicator
        (fun x => lemma77PointwiseEndpointKernel
          a b C lambda s x.1 (relativeVerticalOvershoot s x.2)) x := by
  let E : Set (ℕ × ℤ) := lemma77CanonicalVerticalOvershootTailEvent s T
  let f : ℕ × ℤ → ℝ := fun x =>
    lemma77PointwiseEndpointKernel
      a b C lambda s x.1 (relativeVerticalOvershoot s x.2)
  let h : ℕ → ℝ := fun r => lemma77HorizontalPointwiseKernel a b C s r
  let v : ℕ → ℝ := fun u =>
    Real.exp (-(lambda * (((T + u : ℕ) : ℝ))))
  have hh : Summable h := by
    simpa [h] using lemma77HorizontalPointwiseKernel_summable ha hb s (C := C)
  have hv : Summable v := by
    simpa [v] using lemma77VerticalExponentialTail_summable hlambda T
  have hh_nonneg : ∀ r, 0 ≤ h r := by
    intro r
    unfold h lemma77HorizontalPointwiseKernel
    positivity
  have hv_nonneg : ∀ u, 0 ≤ v u := fun _ => (Real.exp_pos _).le
  have hprod : Summable fun x : ℕ × ℕ => h x.1 * v x.2 :=
    hh.mul_of_nonneg hv hh_nonneg hv_nonneg
  have hcomp : Summable
      ((fun x : {x : ℕ × ℤ // x ∈ E} => f x.1) ∘
        lemma77VerticalOvershootTailEquiv s T) := by
    convert hprod using 1
    ext x
    unfold f h v
    simp only [Function.comp_apply]
    have hover :
        relativeVerticalOvershoot s
            ((s : ℤ) + (T : ℤ) + (x.2 : ℤ)) =
          ((T + x.2 : ℕ) : ℤ) := by
      unfold relativeVerticalOvershoot
      omega
    change lemma77PointwiseEndpointKernel a b C lambda s x.1
        (relativeVerticalOvershoot s
          ((s : ℤ) + (T : ℤ) + (x.2 : ℤ))) =
      lemma77HorizontalPointwiseKernel a b C s x.1 *
        Real.exp (-(lambda * (((T + x.2 : ℕ) : ℝ))))
    rw [hover]
    have hcast : ((((T + x.2 : ℕ) : ℤ) : ℝ)) =
        (T : ℝ) + (x.2 : ℝ) := by norm_cast
    unfold lemma77PointwiseEndpointKernel lemma77HorizontalPointwiseKernel
    rw [hcast]
    simp only [Nat.cast_add]
    ring_nf
  have hsub : Summable (fun x : {x : ℕ × ℤ // x ∈ E} => f x.1) :=
    (lemma77VerticalOvershootTailEquiv s T).summable_iff.mp hcomp
  have hindicator : Summable (E.indicator f) :=
    summable_subtype_iff_indicator.mp hsub
  simpa [E, f] using hindicator

/-- Exact factorization of the vertically restricted endpoint kernel into
the total horizontal profile and the shifted geometric ray. -/
theorem lemma77PointwiseEndpointKernel_verticalTail_tsum_eq
    {a b C lambda : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hC : 0 ≤ C) (hlambda : 0 < lambda) (s T : ℕ) :
    (∑' x : ℕ × ℤ,
      (lemma77CanonicalVerticalOvershootTailEvent s T).indicator
        (fun x => lemma77PointwiseEndpointKernel
          a b C lambda s x.1 (relativeVerticalOvershoot s x.2)) x) =
      (∑' r : ℕ, lemma77HorizontalPointwiseKernel a b C s r) *
        (∑' u : ℕ,
          Real.exp (-(lambda * (((T + u : ℕ) : ℝ))))) := by
  let E : Set (ℕ × ℤ) := lemma77CanonicalVerticalOvershootTailEvent s T
  let f : ℕ × ℤ → ℝ := fun x =>
    lemma77PointwiseEndpointKernel
      a b C lambda s x.1 (relativeVerticalOvershoot s x.2)
  let h : ℕ → ℝ := fun r => lemma77HorizontalPointwiseKernel a b C s r
  let v : ℕ → ℝ := fun u =>
    Real.exp (-(lambda * (((T + u : ℕ) : ℝ))))
  have hh : Summable h := by
    simpa [h] using lemma77HorizontalPointwiseKernel_summable ha hb s (C := C)
  have hv : Summable v := by
    simpa [v] using lemma77VerticalExponentialTail_summable hlambda T
  have hh_nonneg : ∀ r, 0 ≤ h r := by
    intro r
    unfold h lemma77HorizontalPointwiseKernel
    positivity
  have hv_nonneg : ∀ u, 0 ≤ v u := fun _ => (Real.exp_pos _).le
  have hprod : Summable fun x : ℕ × ℕ => h x.1 * v x.2 :=
    hh.mul_of_nonneg hv hh_nonneg hv_nonneg
  calc
    (∑' x : ℕ × ℤ, E.indicator f x) =
        ∑' x : {x : ℕ × ℤ // x ∈ E}, f x.1 := by
      exact (tsum_subtype E f).symm
    _ = ∑' x : ℕ × ℕ,
        f ((lemma77VerticalOvershootTailEquiv s T x).1) :=
      ((lemma77VerticalOvershootTailEquiv s T).tsum_eq
        (fun x : {x : ℕ × ℤ // x ∈ E} => f x.1)).symm
    _ = ∑' x : ℕ × ℕ, h x.1 * v x.2 := by
      apply tsum_congr
      intro x
      unfold f h v
      have hover :
          relativeVerticalOvershoot s
              ((s : ℤ) + (T : ℤ) + (x.2 : ℤ)) =
            ((T + x.2 : ℕ) : ℤ) := by
        unfold relativeVerticalOvershoot
        omega
      change lemma77PointwiseEndpointKernel a b C lambda s x.1
          (relativeVerticalOvershoot s
            ((s : ℤ) + (T : ℤ) + (x.2 : ℤ))) =
        lemma77HorizontalPointwiseKernel a b C s x.1 *
          Real.exp (-(lambda * (((T + x.2 : ℕ) : ℝ))))
      rw [hover]
      have hcast : ((((T + x.2 : ℕ) : ℤ) : ℝ)) =
          (T : ℝ) + (x.2 : ℝ) := by norm_cast
      unfold lemma77PointwiseEndpointKernel lemma77HorizontalPointwiseKernel
      rw [hcast]
      simp only [Nat.cast_add]
      ring_nf
    _ = (∑' r : ℕ, h r) * (∑' u : ℕ, v u) := by
      rw [hprod.tsum_prod' (fun r => hv.mul_left (h r))]
      simp_rw [tsum_mul_left]
      rw [tsum_mul_right]
    _ = (∑' r : ℕ, lemma77HorizontalPointwiseKernel a b C s r) *
        (∑' u : ℕ,
          Real.exp (-(lambda * (((T + u : ℕ) : ℝ))))) := by
      rfl

/-- Explicit vertical-tail envelope after summing the complete horizontal
profile and the shifted geometric overshoot ray. -/
def lemma77VerticalOvershootTailEnvelope
    (a b C : ℝ) (T : ℕ) : ℝ :=
  21 * C *
    (lemma77HorizontalGaussianCountConstant a +
      lemma77HorizontalLinearCountConstant b) *
    Real.exp (-(Real.log (21 / 20 : ℝ) * (T : ℝ)))

/-- Countable endpoint-kernel upper vertical tail at the concrete terminal
rate. -/
theorem lemma77PointwiseEndpointKernel_verticalTail_tsum_le
    {a b C : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 ≤ C)
    (s T : ℕ) :
    (∑' x : ℕ × ℤ,
      (lemma77CanonicalVerticalOvershootTailEvent s T).indicator
        (fun x => lemma77PointwiseEndpointKernel
          a b C (Real.log (21 / 20 : ℝ)) s x.1
            (relativeVerticalOvershoot s x.2)) x) ≤
      lemma77VerticalOvershootTailEnvelope a b C T := by
  have hlambda : 0 < Real.log (21 / 20 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 21 / 20)
  rw [lemma77PointwiseEndpointKernel_verticalTail_tsum_eq
    ha hb hC hlambda s T,
    lemma77_tsum_exp_neg_log_21_div_20_from]
  have hhorizontal := lemma77HorizontalPointwiseKernel_tsum_le ha hb hC s
  have hexp_nonneg :
      0 ≤ 21 * Real.exp
        (-(Real.log (21 / 20 : ℝ) * (T : ℝ))) := by positivity
  calc
    (∑' r : ℕ, lemma77HorizontalPointwiseKernel a b C s r) *
        (21 * Real.exp
          (-(Real.log (21 / 20 : ℝ) * (T : ℝ)))) ≤
      (C * (lemma77HorizontalGaussianCountConstant a +
          lemma77HorizontalLinearCountConstant b)) *
        (21 * Real.exp
          (-(Real.log (21 / 20 : ℝ) * (T : ℝ)))) :=
      mul_le_mul_of_nonneg_right hhorizontal hexp_nonneg
    _ = lemma77VerticalOvershootTailEnvelope a b C T := by
      unfold lemma77VerticalOvershootTailEnvelope
      ring

/-- Native upper vertical-overshoot tail for the canonical first-passage
endpoint law. -/
theorem lemma77CanonicalFirstPassageEndpointPMF_verticalOvershootTail :
    ∃ C32 c32 : ℝ, 0 ≤ C32 ∧ 0 < c32 ∧
      ∀ (start : TaoSection7RenewalPoint) (s T : ℕ), 1 ≤ T →
        (lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
            (lemma77CanonicalVerticalOvershootTailEvent s T) ≤
          ENNReal.ofReal
            (lemma77VerticalOvershootTailEnvelope
              (c32 ^ 2) c32 (15 * C32) T) := by
  rcases
      lemma77CanonicalFirstPassageEndpointPMF_pointwiseKernel_log_21_div_20
      with ⟨C32, c32, hC32, hc32, hpoint⟩
  refine ⟨C32, c32, hC32, hc32, ?_⟩
  intro start s T hT
  let f : ℕ × ℤ → ℝ := fun x =>
    lemma77PointwiseEndpointKernel
      (c32 ^ 2) c32 (15 * C32) (Real.log (21 / 20 : ℝ))
      s x.1 (relativeVerticalOvershoot s x.2)
  have ha : 0 < c32 ^ 2 := sq_pos_of_pos hc32
  have hC : 0 ≤ 15 * C32 := mul_nonneg (by norm_num) hC32
  have hlambda : 0 < Real.log (21 / 20 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 21 / 20)
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    unfold f lemma77PointwiseEndpointKernel
    positivity
  have hf : Summable
      ((lemma77CanonicalVerticalOvershootTailEvent s T).indicator f) := by
    simpa [f] using
      lemma77PointwiseEndpointKernel_verticalTail_summable
        ha hc32 hC hlambda s T
  have hnative := pmf_toOuterMeasure_le_of_apply_le_ofReal
    (lemma77CanonicalFirstPassageEndpointPMF start s)
    (lemma77CanonicalVerticalOvershootTailEvent s T)
    f hf_nonneg hf (fun x hx => by
      have hell : (s : ℤ) < x.2 := by
        have hx' : (s : ℤ) + (T : ℤ) ≤ x.2 := hx
        omega
      exact hpoint start s x.1 x.2 hell)
  calc
    (lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
        (lemma77CanonicalVerticalOvershootTailEvent s T) ≤
      ENNReal.ofReal
        (∑' x : ℕ × ℤ,
          (lemma77CanonicalVerticalOvershootTailEvent s T).indicator f x) :=
      hnative
    _ ≤ ENNReal.ofReal
        (lemma77VerticalOvershootTailEnvelope
          (c32 ^ 2) c32 (15 * C32) T) := by
      apply ENNReal.ofReal_le_ofReal
      simpa [f] using
        lemma77PointwiseEndpointKernel_verticalTail_tsum_le
          ha hc32 hC s T

/-- Safe real projection of the canonical two-sided horizontal tail. -/
theorem lemma77CanonicalFirstPassageHorizontalPMF_deviationTail_toReal :
    ∃ C32 c32 : ℝ, 0 ≤ C32 ∧ 0 < c32 ∧
      ∀ (start : TaoSection7RenewalPoint) (s : ℕ) (t : ℝ), 0 ≤ t →
        ((lemma77CanonicalFirstPassageHorizontalPMF start s).toOuterMeasure
            (lemma77CanonicalHorizontalDeviationEvent s t)).toReal ≤
          lemma77HorizontalDeviationTailEnvelope
            (c32 ^ 2) c32 (300 * C32) s t := by
  rcases lemma77CanonicalFirstPassageHorizontalPMF_deviationTail with
    ⟨C32, c32, hC32, hc32, hnative⟩
  refine ⟨C32, c32, hC32, hc32, ?_⟩
  intro start s t ht
  have ha2 : 0 < (c32 ^ 2) / 2 := by positivity
  have hb2 : 0 < c32 / 2 := by positivity
  have hG :
      0 ≤ lemma77HorizontalGaussianCountConstant ((c32 ^ 2) / 2) :=
    lemma77HorizontalGaussianCountConstant_nonneg ha2
  have hL :
      0 ≤ lemma77HorizontalLinearCountConstant (c32 / 2) :=
    lemma77HorizontalLinearCountConstant_nonneg hb2
  have henvelope :
      0 ≤ lemma77HorizontalDeviationTailEnvelope
        (c32 ^ 2) c32 (300 * C32) s t := by
    unfold lemma77HorizontalDeviationTailEnvelope
    positivity
  calc
    ((lemma77CanonicalFirstPassageHorizontalPMF start s).toOuterMeasure
        (lemma77CanonicalHorizontalDeviationEvent s t)).toReal ≤
      (ENNReal.ofReal
        (lemma77HorizontalDeviationTailEnvelope
          (c32 ^ 2) c32 (300 * C32) s t)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hnative start s t ht)
    _ = lemma77HorizontalDeviationTailEnvelope
        (c32 ^ 2) c32 (300 * C32) s t :=
      ENNReal.toReal_ofReal henvelope

/-- Safe real projection of the canonical upper vertical-overshoot tail. -/
theorem lemma77CanonicalFirstPassageEndpointPMF_verticalOvershootTail_toReal :
    ∃ C32 c32 : ℝ, 0 ≤ C32 ∧ 0 < c32 ∧
      ∀ (start : TaoSection7RenewalPoint) (s T : ℕ), 1 ≤ T →
        ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
            (lemma77CanonicalVerticalOvershootTailEvent s T)).toReal ≤
          lemma77VerticalOvershootTailEnvelope
            (c32 ^ 2) c32 (15 * C32) T := by
  rcases lemma77CanonicalFirstPassageEndpointPMF_verticalOvershootTail with
    ⟨C32, c32, hC32, hc32, hnative⟩
  refine ⟨C32, c32, hC32, hc32, ?_⟩
  intro start s T hT
  have ha : 0 < c32 ^ 2 := sq_pos_of_pos hc32
  have hG : 0 ≤ lemma77HorizontalGaussianCountConstant (c32 ^ 2) :=
    lemma77HorizontalGaussianCountConstant_nonneg ha
  have hL : 0 ≤ lemma77HorizontalLinearCountConstant c32 :=
    lemma77HorizontalLinearCountConstant_nonneg hc32
  have henvelope :
      0 ≤ lemma77VerticalOvershootTailEnvelope
        (c32 ^ 2) c32 (15 * C32) T := by
    unfold lemma77VerticalOvershootTailEnvelope
    positivity
  calc
    ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
        (lemma77CanonicalVerticalOvershootTailEvent s T)).toReal ≤
      (ENNReal.ofReal
        (lemma77VerticalOvershootTailEnvelope
          (c32 ^ 2) c32 (15 * C32) T)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hnative start s T hT)
    _ = lemma77VerticalOvershootTailEnvelope
        (c32 ^ 2) c32 (15 * C32) T :=
      ENNReal.toReal_ofReal henvelope

/-- Source-facing two-sided horizontal tail with uniform positive constants. -/
theorem lemma77CanonicalFirstPassageHorizontalPMF_deviationTail_commonConstants :
    ∃ Kh ah bh : ℝ, 0 < Kh ∧ 0 < ah ∧ 0 < bh ∧
      ∀ (start : TaoSection7RenewalPoint) (s : ℕ) (t : ℝ), 0 ≤ t →
        (lemma77CanonicalFirstPassageHorizontalPMF start s).toOuterMeasure
            (lemma77CanonicalHorizontalDeviationEvent s t) ≤
          ENNReal.ofReal
            (Kh *
              (Real.exp (-ah * (t ^ 2 / (1 + (s : ℝ)))) +
                Real.exp (-bh * t))) := by
  rcases lemma77CanonicalFirstPassageHorizontalPMF_deviationTail with
    ⟨C32, c32, hC32, hc32, hnative⟩
  let G : ℝ := lemma77HorizontalGaussianCountConstant ((c32 ^ 2) / 2)
  let L : ℝ := lemma77HorizontalLinearCountConstant (c32 / 2)
  let C0 : ℝ := 300 * C32
  let Kh : ℝ := 1 + C0 * (G + L)
  let ah : ℝ := (c32 ^ 2) / 2
  let bh : ℝ := c32 / 2
  have hah : 0 < ah := by dsimp [ah]; positivity
  have hbh : 0 < bh := by dsimp [bh]; positivity
  have hG : 0 ≤ G := by
    dsimp [G]
    exact lemma77HorizontalGaussianCountConstant_nonneg hah
  have hL : 0 ≤ L := by
    dsimp [L]
    exact lemma77HorizontalLinearCountConstant_nonneg hbh
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hKh : 0 < Kh := by
    dsimp [Kh]
    positivity
  refine ⟨Kh, ah, bh, hKh, hah, hbh, ?_⟩
  intro start s t ht
  let Eg : ℝ := Real.exp (-ah * (t ^ 2 / (1 + (s : ℝ))))
  let El : ℝ := Real.exp (-bh * t)
  have hEg : 0 ≤ Eg := (Real.exp_pos _).le
  have hEl : 0 ≤ El := (Real.exp_pos _).le
  have hCG : C0 * G ≤ Kh := by
    dsimp [Kh]
    nlinarith [mul_nonneg hC0 hL]
  have hCL : C0 * L ≤ Kh := by
    dsimp [Kh]
    nlinarith [mul_nonneg hC0 hG]
  calc
    (lemma77CanonicalFirstPassageHorizontalPMF start s).toOuterMeasure
        (lemma77CanonicalHorizontalDeviationEvent s t) ≤
      ENNReal.ofReal
        (lemma77HorizontalDeviationTailEnvelope
          (c32 ^ 2) c32 (300 * C32) s t) := hnative start s t ht
    _ ≤ ENNReal.ofReal (Kh * (Eg + El)) := by
      apply ENNReal.ofReal_le_ofReal
      unfold lemma77HorizontalDeviationTailEnvelope
      change C0 * (G * Eg + L * El) ≤ Kh * (Eg + El)
      calc
        C0 * (G * Eg + L * El) =
            (C0 * G) * Eg + (C0 * L) * El := by ring
        _ ≤ Kh * Eg + Kh * El :=
          add_le_add
            (mul_le_mul_of_nonneg_right hCG hEg)
            (mul_le_mul_of_nonneg_right hCL hEl)
        _ = Kh * (Eg + El) := by ring
    _ = ENNReal.ofReal
        (Kh *
          (Real.exp (-ah * (t ^ 2 / (1 + (s : ℝ)))) +
            Real.exp (-bh * t))) := by rfl

/-- Source-facing upper vertical tail with uniform positive constants. -/
theorem lemma77CanonicalFirstPassageEndpointPMF_verticalOvershootTail_commonRate :
    ∃ Kv dv : ℝ, 0 < Kv ∧ 0 < dv ∧
      ∀ (start : TaoSection7RenewalPoint) (s T : ℕ), 1 ≤ T →
        (lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
            (lemma77CanonicalVerticalOvershootTailEvent s T) ≤
          ENNReal.ofReal
            (Kv * Real.exp (-dv * (T : ℝ))) := by
  rcases lemma77CanonicalFirstPassageEndpointPMF_verticalOvershootTail with
    ⟨C32, c32, hC32, hc32, hnative⟩
  let G : ℝ := lemma77HorizontalGaussianCountConstant (c32 ^ 2)
  let L : ℝ := lemma77HorizontalLinearCountConstant c32
  let dv : ℝ := Real.log (21 / 20 : ℝ)
  let K0 : ℝ := 315 * C32 * (G + L)
  let Kv : ℝ := 1 + K0
  have ha : 0 < c32 ^ 2 := sq_pos_of_pos hc32
  have hG : 0 ≤ G := by
    dsimp [G]
    exact lemma77HorizontalGaussianCountConstant_nonneg ha
  have hL : 0 ≤ L := by
    dsimp [L]
    exact lemma77HorizontalLinearCountConstant_nonneg hc32
  have hdv : 0 < dv := by
    dsimp [dv]
    exact Real.log_pos (by norm_num : (1 : ℝ) < 21 / 20)
  have hK0 : 0 ≤ K0 := by
    dsimp [K0]
    positivity
  have hKv : 0 < Kv := by dsimp [Kv]; linarith
  have hK0_le : K0 ≤ Kv := by dsimp [Kv]; linarith
  refine ⟨Kv, dv, hKv, hdv, ?_⟩
  intro start s T hT
  have hexp : 0 ≤ Real.exp (-dv * (T : ℝ)) := (Real.exp_pos _).le
  calc
    (lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
        (lemma77CanonicalVerticalOvershootTailEvent s T) ≤
      ENNReal.ofReal
        (lemma77VerticalOvershootTailEnvelope
          (c32 ^ 2) c32 (15 * C32) T) := hnative start s T hT
    _ ≤ ENNReal.ofReal (Kv * Real.exp (-dv * (T : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      unfold lemma77VerticalOvershootTailEnvelope
      calc
        21 * (15 * C32) *
              (lemma77HorizontalGaussianCountConstant (c32 ^ 2) +
                lemma77HorizontalLinearCountConstant c32) *
              Real.exp
                (-(Real.log (21 / 20 : ℝ) * (T : ℝ))) =
            K0 * Real.exp (-dv * (T : ℝ)) := by
          dsimp [K0, G, L, dv]
          ring_nf
        _ ≤ Kv * Real.exp (-dv * (T : ℝ)) :=
          mul_le_mul_of_nonneg_right hK0_le hexp

/-- The source threshold `s^(3/5)` leaves at least a half-power
`s^(1/5)` in the Gaussian exponent. -/
theorem lemma77_threeFifths_sq_div_one_add_ge_half_oneFifth
    {x : ℝ} (hx : 1 ≤ x) :
    (1 / 2 : ℝ) * x ^ (1 / 5 : ℝ) ≤
      (x ^ (3 / 5 : ℝ)) ^ 2 / (1 + x) := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy : 0 ≤ x ^ (1 / 5 : ℝ) := Real.rpow_nonneg hx0 _
  have hden : 0 < 1 + x := by linarith
  have hratio :
      (1 / 2 : ℝ) * x ^ (1 / 5 : ℝ) ≤
        (x * x ^ (1 / 5 : ℝ)) / (1 + x) := by
    rw [le_div_iff₀ hden]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) hy]
  have hpow :
      (x ^ (3 / 5 : ℝ)) ^ 2 = x * x ^ (1 / 5 : ℝ) := by
    calc
      (x ^ (3 / 5 : ℝ)) ^ 2 =
          (x ^ (3 / 5 : ℝ)) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (x ^ (3 / 5 : ℝ)) 2).symm
      _ = x ^ ((3 / 5 : ℝ) * 2) := by
        rw [← Real.rpow_mul hx0]
      _ = x ^ (1 + (1 / 5 : ℝ)) := by norm_num
      _ = x ^ 1 * x ^ (1 / 5 : ℝ) := Real.rpow_add hxp 1 (1 / 5)
      _ = x * x ^ (1 / 5 : ℝ) := by simp
  rwa [hpow]

/-- Lemma 7.10's source-scale two-sided horizontal tail. -/
theorem lemma77CanonicalFirstPassageHorizontalPMF_threeFifthsTail :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
      ∀ (start : TaoSection7RenewalPoint) (s : ℕ), 1 ≤ s →
        (lemma77CanonicalFirstPassageHorizontalPMF start s).toOuterMeasure
            (lemma77CanonicalHorizontalDeviationEvent s
              ((s : ℝ) ^ (3 / 5 : ℝ))) ≤
          ENNReal.ofReal
            (K * Real.exp (-c * ((s : ℝ) ^ (1 / 5 : ℝ)))) := by
  rcases
      lemma77CanonicalFirstPassageHorizontalPMF_deviationTail_commonConstants
      with ⟨Kh, ah, bh, hKh, hah, hbh, htail⟩
  let c : ℝ := min (ah / 2) bh
  let K : ℝ := 2 * Kh
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (by positivity) hbh
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, c, hK, hc, ?_⟩
  intro start s hs
  let x : ℝ := s
  let y : ℝ := x ^ (1 / 5 : ℝ)
  let t : ℝ := x ^ (3 / 5 : ℝ)
  have hx : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast hs
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have ht : 0 ≤ t := Real.rpow_nonneg hx0 _
  have hscale : (1 / 2 : ℝ) * y ≤ t ^ 2 / (1 + x) := by
    simpa [x, y, t] using
      lemma77_threeFifths_sq_div_one_add_ge_half_oneFifth hx
  have hlinear_scale : y ≤ t := by
    dsimp [y, t]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hc_gauss : c ≤ ah / 2 := by dsimp [c]; exact min_le_left _ _
  have hc_linear : c ≤ bh := by dsimp [c]; exact min_le_right _ _
  have hgauss_arg : c * y ≤ ah * (t ^ 2 / (1 + x)) := by
    have hcy : c * y ≤ (ah / 2) * y :=
      mul_le_mul_of_nonneg_right hc_gauss (Real.rpow_nonneg hx0 _)
    have hhalf : (ah / 2) * y ≤ ah * (t ^ 2 / (1 + x)) := by
      nlinarith [mul_le_mul_of_nonneg_left hscale hah.le]
    exact hcy.trans hhalf
  have hlinear_arg : c * y ≤ bh * t := by
    calc
      c * y ≤ bh * y :=
        mul_le_mul_of_nonneg_right hc_linear (Real.rpow_nonneg hx0 _)
      _ ≤ bh * t := mul_le_mul_of_nonneg_left hlinear_scale hbh.le
  have hgauss_exp :
      Real.exp (-ah * (t ^ 2 / (1 + x))) ≤ Real.exp (-c * y) := by
    rw [Real.exp_le_exp]
    linarith
  have hlinear_exp : Real.exp (-bh * t) ≤ Real.exp (-c * y) := by
    rw [Real.exp_le_exp]
    linarith
  calc
    (lemma77CanonicalFirstPassageHorizontalPMF start s).toOuterMeasure
        (lemma77CanonicalHorizontalDeviationEvent s ((s : ℝ) ^ (3 / 5 : ℝ))) ≤
      ENNReal.ofReal
        (Kh *
          (Real.exp (-ah * (((s : ℝ) ^ (3 / 5 : ℝ)) ^ 2 /
              (1 + (s : ℝ)))) +
            Real.exp (-bh * ((s : ℝ) ^ (3 / 5 : ℝ))))) :=
      htail start s ((s : ℝ) ^ (3 / 5 : ℝ)) ht
    _ ≤ ENNReal.ofReal (K * Real.exp (-c * y)) := by
      apply ENNReal.ofReal_le_ofReal
      change Kh *
          (Real.exp (-ah * (t ^ 2 / (1 + x))) + Real.exp (-bh * t)) ≤
        K * Real.exp (-c * y)
      have hsum :
          Real.exp (-ah * (t ^ 2 / (1 + x))) + Real.exp (-bh * t) ≤
            2 * Real.exp (-c * y) := by nlinarith
      calc
        Kh *
            (Real.exp (-ah * (t ^ 2 / (1 + x))) + Real.exp (-bh * t)) ≤
          Kh * (2 * Real.exp (-c * y)) :=
            mul_le_mul_of_nonneg_left hsum hKh.le
        _ = K * Real.exp (-c * y) := by
          dsimp [K]
          ring
    _ = ENNReal.ofReal
        (K * Real.exp (-c * ((s : ℝ) ^ (1 / 5 : ℝ)))) := by rfl

/-- Lemma 7.10's source-scale vertical tail at threshold `A²(1+p)`. -/
theorem lemma77CanonicalFirstPassageEndpointPMF_A_sq_mul_one_add_p_tail :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
      ∀ (start : TaoSection7RenewalPoint) (s A p : ℕ), 1 ≤ A →
        (lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
            (lemma77CanonicalVerticalOvershootTailEvent s
              (A ^ 2 * (1 + p))) ≤
          ENNReal.ofReal
            (K * Real.exp (-c * ((A ^ 2 * (1 + p) : ℕ) : ℝ))) := by
  rcases lemma77CanonicalFirstPassageEndpointPMF_verticalOvershootTail_commonRate
    with ⟨K, c, hK, hc, htail⟩
  refine ⟨K, c, hK, hc, ?_⟩
  intro start s A p hA
  apply htail
  nlinarith

end TaoSection7Lemma77

end

end Tao
end Erdos1135SecondScale
