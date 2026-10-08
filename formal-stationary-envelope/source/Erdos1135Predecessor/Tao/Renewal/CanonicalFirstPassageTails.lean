/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageHorizontal
import Erdos1135Predecessor.Tao.Renewal.Lemma77LocalLimit

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Lemma77

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

def lemma77HorizontalGaussianCountConstant (a : ℝ) : ℝ :=
  2 * Real.exp ((a / 16) / 4) * Real.exp (a / 16) / (a / 16)

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

theorem lemma77_rpow_neg_half_mul_sqrt_one_add (s : ℕ) :
    ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) *
      Real.sqrt (1 + (s : ℝ)) = 1 := by
  let S : ℝ := 1 + (s : ℝ)
  have hS : 0 < S := by positivity
  have hsqrt : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  rw [show 1 + (s : ℝ) = S by rfl]
  rw [Real.rpow_neg hS.le, ← Real.sqrt_eq_rpow]
  field_simp [hsqrt.ne']

theorem lemma77_rpow_neg_half_one_add_le_one (s : ℕ) :
    (1 + (s : ℝ)) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (le_add_of_nonneg_right (Nat.cast_nonneg s)) (by norm_num)

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

def lemma77CanonicalHorizontalDeviationEvent (s : ℕ) (t : ℝ) : Set ℕ :=
  {r | t ≤ |lemma77CenteredHorizontalDisplacement s r|}

def lemma77HorizontalDeviationTailEnvelope
    (a b C : ℝ) (s : ℕ) (t : ℝ) : ℝ :=
  C *
    (lemma77HorizontalGaussianCountConstant (a / 2) *
        Real.exp (-(a / 2) * (t ^ 2 / (1 + (s : ℝ)))) +
      lemma77HorizontalLinearCountConstant (b / 2) *
        Real.exp (-(b / 2) * t))

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

def lemma77CanonicalVerticalOvershootTailEvent (s T : ℕ) : Set (ℕ × ℤ) :=
  {x | (s : ℤ) + (T : ℤ) ≤ x.2}

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

def lemma77VerticalOvershootTailEnvelope
    (a b C : ℝ) (T : ℕ) : ℝ :=
  21 * C *
    (lemma77HorizontalGaussianCountConstant a +
      lemma77HorizontalLinearCountConstant b) *
    Real.exp (-(Real.log (21 / 20 : ℝ) * (T : ℝ)))

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

end TaoSection7Lemma77

end

end Tao

end Erdos1135Predecessor
