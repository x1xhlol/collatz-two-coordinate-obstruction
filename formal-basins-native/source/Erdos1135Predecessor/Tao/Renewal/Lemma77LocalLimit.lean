/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma77HorizontalMarginal
import Erdos1135Predecessor.Tao.Renewal.Lemma77PotentialCore

namespace Erdos1135Predecessor

namespace Tao

open scoped BigOperators

noncomputable section

namespace TaoSection7Lemma77

theorem lemma77ExpNegMulNat_summable {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ => Real.exp (-(a * (n : ℝ))) := by
  have hr : ‖Real.exp (-a)‖ < 1 := by
    rw [Real.norm_eq_abs]
    rw [abs_of_pos (Real.exp_pos (-a))]
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeom : Summable fun n : ℕ => (Real.exp (-a)) ^ n :=
    summable_geometric_of_norm_lt_one hr
  convert hgeom using 1
  ext n
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem lemma77ExpNegMulNat_tsum {a : ℝ} (ha : 0 < a) :
    (∑' n : ℕ, Real.exp (-(a * (n : ℝ)))) =
      (1 - Real.exp (-a))⁻¹ := by
  have hbase_nonneg : 0 ≤ Real.exp (-a) := le_of_lt (Real.exp_pos _)
  have hbase_lt : Real.exp (-a) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  rw [← tsum_geometric_of_lt_one hbase_nonneg hbase_lt]
  apply tsum_congr
  intro n
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem lemma77ExpNegMulIntAbs_summable {a : ℝ} (ha : 0 < a) :
    Summable fun z : ℤ => Real.exp (-(a * |(z : ℝ)|)) := by
  apply Summable.of_nat_of_neg_add_one
  · simpa using (lemma77ExpNegMulNat_summable ha)
  · have htail :
        Summable fun n : ℕ =>
          Real.exp (-(a * (((n + 1 : ℕ) : ℝ)))) := by
      simpa [Function.comp_def] using
        (lemma77ExpNegMulNat_summable ha).comp_injective Nat.succ_injective
    convert htail using 1
    ext n
    have habs : |-1 + -(n : ℝ)| = (n : ℝ) + 1 := by
      rw [abs_of_nonpos]
      · ring
      · nlinarith [show 0 ≤ (n : ℝ) by positivity]
    simpa [Int.cast_neg, Int.cast_add, Int.cast_natCast] using (Or.inl habs)

theorem lemma77ExpNegMulIntAbs_tsum_le {a : ℝ} (ha : 0 < a) :
    (∑' z : ℤ, Real.exp (-(a * |(z : ℝ)|))) ≤
      2 * (1 - Real.exp (-a))⁻¹ := by
  let f : ℤ → ℝ := fun z => Real.exp (-(a * |(z : ℝ)|))
  have hf_nat : Summable fun n : ℕ => Real.exp (-(a * (n : ℝ))) :=
    lemma77ExpNegMulNat_summable ha
  have htail_model :
      Summable fun n : ℕ =>
        Real.exp (-(a * (((n + 1 : ℕ) : ℝ)))) := by
    simpa [Function.comp_def] using
      (lemma77ExpNegMulNat_summable ha).comp_injective Nat.succ_injective
  have hf_pos : Summable fun n : ℕ => f (n : ℤ) := by
    simpa [f] using hf_nat
  have hf_neg : Summable fun n : ℕ => f (-(↑n + 1 : ℤ)) := by
    convert htail_model using 1
    ext n
    have habs : |-1 + -(n : ℝ)| = (n : ℝ) + 1 := by
      rw [abs_of_nonpos]
      · ring
      · nlinarith [show 0 ≤ (n : ℝ) by positivity]
    simpa [f, Int.cast_neg, Int.cast_add, Int.cast_natCast] using (Or.inl habs)
  have htail_le :
      (∑' n : ℕ, f (-(↑n + 1 : ℤ))) ≤
        (∑' n : ℕ, Real.exp (-(a * (n : ℝ)))) := by
    have hpoint :
        ∀ n : ℕ, f (-(↑n + 1 : ℤ)) ≤
          Real.exp (-(a * (n : ℝ))) := by
      intro n
      change Real.exp (-(a * |((-(↑n + 1 : ℤ) : ℤ) : ℝ)|)) ≤
        Real.exp (-(a * (n : ℝ)))
      rw [Real.exp_le_exp]
      have habs : |((-(↑n + 1 : ℤ) : ℤ) : ℝ)| = (n : ℝ) + 1 := by
        have habs' : |-1 + -(n : ℝ)| = (n : ℝ) + 1 := by
          rw [abs_of_nonpos]
          · ring
          · nlinarith [show 0 ≤ (n : ℝ) by positivity]
        simpa [Int.cast_neg, Int.cast_add, Int.cast_natCast] using habs'
      rw [habs]
      nlinarith [ha, show 0 ≤ (n : ℝ) by positivity]
    exact hf_neg.tsum_le_tsum hpoint hf_nat
  have hpos_eq :
      (∑' n : ℕ, f (n : ℤ)) =
        (∑' n : ℕ, Real.exp (-(a * (n : ℝ)))) := by
    apply tsum_congr
    intro n
    simp [f]
  have hnat_eq := lemma77ExpNegMulNat_tsum ha
  have hsplit := tsum_of_nat_of_neg_add_one (f := f) hf_pos hf_neg
  calc
    (∑' z : ℤ, Real.exp (-(a * |(z : ℝ)|))) =
        (∑' n : ℕ, f (n : ℤ)) + (∑' n : ℕ, f (-(↑n + 1 : ℤ))) := by
          simpa [f] using hsplit
    _ ≤ (∑' n : ℕ, Real.exp (-(a * (n : ℝ)))) +
          (∑' n : ℕ, Real.exp (-(a * (n : ℝ)))) := by
          exact add_le_add (le_of_eq hpos_eq) htail_le
    _ = 2 * (1 - Real.exp (-a))⁻¹ := by
          rw [hnat_eq]
          ring

theorem lemma77_one_sub_exp_neg_inv_le_exp_div
    {r A : ℝ} (hr : 0 < r) (hrA : r ≤ A) :
    (1 - Real.exp (-r))⁻¹ ≤ Real.exp A / r := by
  have hexp_pos : 0 < Real.exp r := Real.exp_pos r
  have hdiff_ge : r ≤ Real.exp r - 1 := by
    have h := Real.add_one_le_exp r
    linarith
  have hdiff_pos : 0 < Real.exp r - 1 := lt_of_lt_of_le hr hdiff_ge
  have hden_eq : 1 - Real.exp (-r) = (Real.exp r - 1) / Real.exp r := by
    rw [Real.exp_neg]
    field_simp [hexp_pos.ne']
  calc
    (1 - Real.exp (-r))⁻¹ = Real.exp r / (Real.exp r - 1) := by
      rw [hden_eq]
      field_simp [hexp_pos.ne', hdiff_pos.ne']
    _ ≤ Real.exp r / r := by
      exact div_le_div_of_nonneg_left hexp_pos.le hr hdiff_ge
    _ ≤ Real.exp A / r := by
      exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hrA) hr.le

theorem lemma77ExpNegMulIntSqDiv_le_scaledAbs
    {a S : ℝ} (ha : 0 ≤ a) (hS : 0 < S) (z : ℤ) :
    Real.exp (-(a * (z : ℝ) ^ 2 / S)) ≤
      Real.exp (a / 4) *
        Real.exp (-((a / Real.sqrt S) * |(z : ℝ)|)) := by
  let y : ℝ := |(z : ℝ)| / Real.sqrt S
  have hS_nonneg : 0 ≤ S := hS.le
  have hsqrt_pos : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  have hy_sq : y ^ 2 = (z : ℝ) ^ 2 / S := by
    dsimp [y]
    have hsqrt_sq : (Real.sqrt S) ^ 2 = S := Real.sq_sqrt hS_nonneg
    calc
      (|(z : ℝ)| / Real.sqrt S) ^ 2 =
          |(z : ℝ)| ^ 2 / (Real.sqrt S) ^ 2 := by ring
      _ = (z : ℝ) ^ 2 / S := by rw [sq_abs, hsqrt_sq]
  have hyineq : y - 1 / 4 ≤ y ^ 2 := by
    nlinarith [sq_nonneg (y - 1 / 2)]
  have hmul : a * (y - 1 / 4) ≤ a * y ^ 2 :=
    mul_le_mul_of_nonneg_left hyineq ha
  have htarget_y : -(a * y ^ 2) ≤ a / 4 - a * y := by
    nlinarith
  have hrewrite : a * y = (a / Real.sqrt S) * |(z : ℝ)| := by
    dsimp [y]
    field_simp [hsqrt_pos.ne']
  have hquad : -(a * (z : ℝ) ^ 2 / S) ≤
      a / 4 - (a / Real.sqrt S) * |(z : ℝ)| := by
    calc
      -(a * (z : ℝ) ^ 2 / S) = -(a * y ^ 2) := by
        rw [hy_sq]
        ring
      _ ≤ a / 4 - a * y := htarget_y
      _ = a / 4 - (a / Real.sqrt S) * |(z : ℝ)| := by
        rw [hrewrite]
  calc
    Real.exp (-(a * (z : ℝ) ^ 2 / S))
        ≤ Real.exp (a / 4 - (a / Real.sqrt S) * |(z : ℝ)|) := by
          rw [Real.exp_le_exp]
          exact hquad
    _ = Real.exp (a / 4) *
          Real.exp (-((a / Real.sqrt S) * |(z : ℝ)|)) := by
          rw [← Real.exp_add]
          congr 1

theorem lemma77ExpNegMulIntSqDiv_summable
    {a S : ℝ} (ha : 0 < a) (hS : 0 < S) :
    Summable fun z : ℤ => Real.exp (-(a * (z : ℝ) ^ 2 / S)) := by
  let r : ℝ := a / Real.sqrt S
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hright : Summable fun z : ℤ =>
      Real.exp (a / 4) * Real.exp (-(r * |(z : ℝ)|)) :=
    (lemma77ExpNegMulIntAbs_summable hr).mul_left (Real.exp (a / 4))
  have hpoint : ∀ z : ℤ,
      Real.exp (-(a * (z : ℝ) ^ 2 / S)) ≤
        Real.exp (a / 4) * Real.exp (-(r * |(z : ℝ)|)) := by
    intro z
    simpa [r] using lemma77ExpNegMulIntSqDiv_le_scaledAbs ha.le hS z
  exact Summable.of_nonneg_of_le
    (fun z => le_of_lt (Real.exp_pos _)) hpoint hright

theorem lemma77ExpNegMulIntSqDiv_tsum_le_sqrt_explicit
    {a S : ℝ} (ha : 0 < a) (hS : 1 ≤ S) :
    (∑' z : ℤ, Real.exp (-(a * (z : ℝ) ^ 2 / S))) ≤
      (2 * Real.exp (a / 4) * Real.exp a / a) * Real.sqrt S := by
  let r : ℝ := a / Real.sqrt S
  have hS_pos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hsqrt_pos : 0 < Real.sqrt S := Real.sqrt_pos.2 hS_pos
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hsqrt_ge_one : 1 ≤ Real.sqrt S := by
    rw [Real.one_le_sqrt]
    exact hS
  have hr_le_a : r ≤ a := by
    dsimp [r]
    rw [div_le_iff₀ hsqrt_pos]
    nlinarith [ha, hsqrt_ge_one]
  have hleft : Summable fun z : ℤ =>
      Real.exp (-(a * (z : ℝ) ^ 2 / S)) :=
    lemma77ExpNegMulIntSqDiv_summable ha hS_pos
  have hright : Summable fun z : ℤ =>
      Real.exp (a / 4) * Real.exp (-(r * |(z : ℝ)|)) :=
    (lemma77ExpNegMulIntAbs_summable hr).mul_left (Real.exp (a / 4))
  have hpoint : ∀ z : ℤ,
      Real.exp (-(a * (z : ℝ) ^ 2 / S)) ≤
        Real.exp (a / 4) * Real.exp (-(r * |(z : ℝ)|)) := by
    intro z
    simpa [r] using lemma77ExpNegMulIntSqDiv_le_scaledAbs ha.le hS_pos z
  have htail := lemma77ExpNegMulIntAbs_tsum_le hr
  have hrec := lemma77_one_sub_exp_neg_inv_le_exp_div hr hr_le_a
  calc
    (∑' z : ℤ, Real.exp (-(a * (z : ℝ) ^ 2 / S)))
        ≤ ∑' z : ℤ, Real.exp (a / 4) *
            Real.exp (-(r * |(z : ℝ)|)) :=
          hleft.tsum_le_tsum hpoint hright
    _ = Real.exp (a / 4) *
          (∑' z : ℤ, Real.exp (-(r * |(z : ℝ)|))) := by
          rw [tsum_mul_left]
    _ ≤ Real.exp (a / 4) * (2 * (1 - Real.exp (-r))⁻¹) := by
          exact mul_le_mul_of_nonneg_left htail (le_of_lt (Real.exp_pos _))
    _ ≤ Real.exp (a / 4) * (2 * (Real.exp a / r)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hrec (by norm_num : (0 : ℝ) ≤ 2))
            (le_of_lt (Real.exp_pos _))
    _ = (2 * Real.exp (a / 4) * Real.exp a / a) * Real.sqrt S := by
          dsimp [r]
          field_simp [ha.ne', hsqrt_pos.ne']

theorem lemma77HeightPotentialKernel_const_mono
    {C₁ C₂ c : ℝ} (hC : C₁ ≤ C₂) (j : ℤ) (s' : ℕ) :
    lemma77HeightPotentialKernel C₁ c j s' ≤
      lemma77HeightPotentialKernel C₂ c j s' := by
  unfold lemma77HeightPotentialKernel
  have hfactor_nonneg :
      0 ≤ ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
        taoLemma22GaussianWeight (1 + s')
          (c * ((j : ℝ) - (s' : ℝ) / 4)) := by
    exact mul_nonneg (by positivity)
      (taoLemma22GaussianWeight_nonneg (1 + s')
        (c * ((j : ℝ) - (s' : ℝ) / 4)))
  nlinarith [mul_le_mul_of_nonneg_right hC hfactor_nonneg]

theorem lemma77HeightPotentialKernel_add_same_rate
    (C₁ C₂ c : ℝ) (j : ℤ) (s' : ℕ) :
    lemma77HeightPotentialKernel C₁ c j s' +
      lemma77HeightPotentialKernel C₂ c j s' =
        lemma77HeightPotentialKernel (C₁ + C₂) c j s' := by
  unfold lemma77HeightPotentialKernel
  ring

theorem lemma77HeightPotentialKernel_absExp_le
    {K r ch : ℝ} (hK : 0 ≤ K) (_hr : 0 < r) (hch : 0 < ch)
    (hch_le : ch ≤ r) (j : ℤ) (s' : ℕ) :
    K * ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
      Real.exp (-(r * |lemma77ScalarCenteredHorizontal j s'|)) ≤
    lemma77HeightPotentialKernel K ch j s' := by
  let x := lemma77ScalarCenteredHorizontal j s'
  have hheight_nonneg : 0 ≤ (1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ)) := by
    positivity
  have hx_nonneg : 0 ≤ |x| := abs_nonneg x
  have hch_abs : |ch * x| = ch * |x| := by
    rw [abs_mul, abs_of_pos hch]
  have hexp_le :
      Real.exp (-(r * |x|)) ≤ Real.exp (-|ch * x|) := by
    rw [Real.exp_le_exp, hch_abs]
    nlinarith [mul_le_mul_of_nonneg_right hch_le hx_nonneg]
  have hweight_nonneg :
      0 ≤ Real.exp (-(((ch * x) ^ 2) / ((1 + s' : ℕ) : ℝ))) :=
    le_of_lt (Real.exp_pos _)
  have hlinear :
      Real.exp (-|ch * x|) ≤
        Real.exp (-(((ch * x) ^ 2) / ((1 + s' : ℕ) : ℝ))) +
          Real.exp (-|ch * x|) :=
    le_add_of_nonneg_left hweight_nonneg
  have hweight :
      Real.exp (-(r * |x|)) ≤ taoLemma22GaussianWeight (1 + s') (ch * x) := by
    unfold taoLemma22GaussianWeight
    simp
    simpa [hch_abs, abs_of_pos hch] using le_trans hexp_le hlinear
  have hmul :=
    mul_le_mul_of_nonneg_left hweight (mul_nonneg hK hheight_nonneg)
  simpa [lemma77HeightPotentialKernel, lemma77ScalarCenteredHorizontal, x,
    mul_assoc] using hmul

theorem lemma77HeightPotentialKernel_gaussianExp_le
    {K r ch : ℝ} (hK : 0 ≤ K) (_hr : 0 < r) (_hch : 0 < ch)
    (hch_sq : ch ^ 2 ≤ r) (j : ℤ) (s' : ℕ) :
    K * ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
      Real.exp (-(r * (lemma77ScalarCenteredHorizontal j s') ^ 2 /
        (1 + (s' : ℝ)))) ≤
      lemma77HeightPotentialKernel K ch j s' := by
  let x := lemma77ScalarCenteredHorizontal j s'
  let height : ℝ := (1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))
  have hS_pos : 0 < 1 + (s' : ℝ) := by
    positivity
  have hx_sq : 0 ≤ x ^ 2 := sq_nonneg x
  have hsq : (ch * x) ^ 2 ≤ r * x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hch_sq hx_sq]
  have harg :
      (ch * x) ^ 2 / (1 + (s' : ℝ)) ≤
        r * x ^ 2 / (1 + (s' : ℝ)) := by
    exact div_le_div_of_nonneg_right hsq hS_pos.le
  have hexp :
      Real.exp (-(r * x ^ 2 / (1 + (s' : ℝ)))) ≤
        Real.exp (-((ch * x) ^ 2 / (1 + (s' : ℝ)))) := by
    rw [Real.exp_le_exp]
    linarith
  have hweight :
      Real.exp (-(r * x ^ 2 / (1 + (s' : ℝ)))) ≤
        taoLemma22GaussianWeight (1 + s') (ch * x) := by
    unfold taoLemma22GaussianWeight
    simp [Nat.cast_add, Nat.cast_one]
    exact le_trans hexp
      (le_add_of_nonneg_right (le_of_lt (Real.exp_pos _)))
  have hfactor_nonneg : 0 ≤ K * height := by
    exact mul_nonneg hK (by dsimp [height]; positivity)
  have hmul := mul_le_mul_of_nonneg_left hweight hfactor_nonneg
  simpa [lemma77HeightPotentialKernel, lemma77ScalarCenteredHorizontal, x,
    height, mul_assoc] using hmul

theorem lemma77HoldPrefixSignedEndpointMass_nonneg
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ) :
    0 ≤ lemma77HoldPrefixSignedEndpointMass start n j ell := by
  simp [lemma77HoldPrefixSignedEndpointMass, ENNReal.toReal_nonneg]

theorem lemma77HeightPotentialMass_nonneg
    (start : TaoSection7RenewalPoint) (j : ℤ) (s' : ℕ) :
    0 ≤ lemma77HeightPotentialMass start j s' := by
  unfold lemma77HeightPotentialMass
  exact tsum_nonneg fun n =>
    lemma77HoldPrefixSignedEndpointMass_nonneg start n j (s' : ℤ)

def lemma77VerticalSmoothing733Mass
    (beta : ℝ) (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) : ℝ :=
  ∑ lp ∈ Finset.range (s + 1),
    Real.exp (-beta * (lp : ℝ)) *
      lemma77HeightPotentialMass start j (s - lp)

def lemma77VerticalSmoothing733KernelSum
    (C c beta : ℝ) (j : ℤ) (s : ℕ) : ℝ :=
  ∑ lp ∈ Finset.range (s + 1),
    Real.exp (-beta * (lp : ℝ)) *
      lemma77HeightPotentialKernel C c j (s - lp)

structure Lemma77VerticalSmoothing733Input
    (C c beta C33 c33 : ℝ) : Prop where
  constants : 0 < beta ∧ 0 ≤ C33 ∧ 0 < c33
  kernel_sum_bound :
    ∀ j s,
      lemma77VerticalSmoothing733KernelSum C c beta j s ≤
        lemma77HeightPotentialKernel C33 c33 j s

theorem lemma77VerticalSmoothing733_linearBranch_centerDrift_le
    {beta c c33 : ℝ} (hc33 : 0 < c33)
    (hc33_le_c : c33 ≤ c) (hquarter : c33 / 4 ≤ beta / 2)
    (x : ℝ) (lp : ℕ) :
    Real.exp (-(beta * (lp : ℝ))) *
        Real.exp (-(c * |x + (lp : ℝ) / 4|)) ≤
      Real.exp (-((beta / 2) * (lp : ℝ))) *
        Real.exp (-(c33 * |x|)) := by
  let L : ℝ := lp
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Nat.cast_nonneg lp
  have hquarter_nonneg : 0 ≤ L / 4 := by positivity
  have htri0 : |(x + L / 4) - L / 4| ≤ |x + L / 4| + |L / 4| := by
    simpa using abs_sub_le (x + L / 4) 0 (L / 4)
  have htri : |x| ≤ |x + L / 4| + L / 4 := by
    have h_abs : |L / 4| = L / 4 := abs_of_nonneg hquarter_nonneg
    simpa [h_abs] using htri0
  have hscaled : c33 * |x| ≤ c * |x + L / 4| + (beta / 2) * L := by
    have h1 : c33 * |x| ≤ c33 * (|x + L / 4| + L / 4) :=
      mul_le_mul_of_nonneg_left htri hc33.le
    have h2 : c33 * (|x + L / 4| + L / 4) ≤
        c * |x + L / 4| + (beta / 2) * L := by
      have habs_nonneg : 0 ≤ |x + L / 4| := abs_nonneg _
      have hquarter_scaled : c33 * (L / 4) ≤ (beta / 2) * L := by
        nlinarith [mul_le_mul_of_nonneg_right hquarter hL_nonneg]
      nlinarith [mul_le_mul_of_nonneg_right hc33_le_c habs_nonneg,
        hquarter_scaled]
    exact le_trans h1 h2
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  nlinarith [hscaled]

theorem lemma77VerticalSmoothing733_heightScaleTerm_le
    (s lp : ℕ) (hlp : lp ≤ s) :
    ((1 + ((s - lp : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) ≤
      (1 + (lp : ℝ)) * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) := by
  let A : ℝ := 1 + (s : ℝ)
  let B : ℝ := 1 + ((s - lp : ℕ) : ℝ)
  let P : ℝ := 1 + (lp : ℝ)
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hP_pos : 0 < P := by
    dsimp [P]
    positivity
  have hsub : ((s - lp : ℕ) : ℝ) = (s : ℝ) - (lp : ℝ) := by
    rw [Nat.cast_sub hlp]
  have hlpR : (lp : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast hlp
  have hPB : A ≤ P * B := by
    have hnonneg : 0 ≤ (lp : ℝ) * ((s : ℝ) - (lp : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg lp) (sub_nonneg.mpr hlpR)
    dsimp [A, B, P]
    rw [hsub]
    nlinarith [hnonneg]
  have hprod : A ≤ P ^ 2 * B := by
    have hP_ge_one : 1 ≤ P := by
      dsimp [P]
      exact le_add_of_nonneg_right (Nat.cast_nonneg lp)
    have hB_nonneg : 0 ≤ B := hB_pos.le
    have hPB_le : P * B ≤ P ^ 2 * B := by
      nlinarith [mul_le_mul_of_nonneg_right hP_ge_one hB_nonneg]
    exact le_trans hPB hPB_le
  have hsqrt : Real.sqrt A ≤ P * Real.sqrt B := by
    refine (Real.sqrt_le_left (mul_nonneg hP_pos.le (Real.sqrt_nonneg B))).2 ?_
    calc
      A ≤ P ^ 2 * B := hprod
      _ = (P * Real.sqrt B) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hB_pos.le]
  have hsqrtA_pos : 0 < Real.sqrt A := Real.sqrt_pos.2 hA_pos
  have hsqrtB_pos : 0 < Real.sqrt B := Real.sqrt_pos.2 hB_pos
  rw [show 1 + ((s - lp : ℕ) : ℝ) = B by rfl]
  rw [show 1 + (s : ℝ) = A by rfl]
  rw [Real.rpow_neg hB_pos.le, Real.rpow_neg hA_pos.le]
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  change (Real.sqrt B)⁻¹ ≤ P / Real.sqrt A
  rw [le_div_iff₀' hsqrtA_pos]
  change Real.sqrt A / Real.sqrt B ≤ P
  rw [div_le_iff₀ hsqrtB_pos]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hsqrt

theorem lemma77VerticalSmoothing733_gaussianCenterScale_base
    {S T L x : ℝ} (hT : 0 < T) (hS : 0 < S) (hL : 0 ≤ L)
    (hS_eq : S = T + L) :
    x ^ 2 / S ≤ (x + L / 4) ^ 2 / T + L / 16 := by
  have hidentity :
      (x + L / 4) ^ 2 / T + L / 16 - x ^ 2 / S =
        L * (x + S / 4) ^ 2 / (T * S) := by
    subst S
    field_simp [hT.ne']
    ring_nf
  have hnonneg : 0 ≤ L * (x + S / 4) ^ 2 / (T * S) := by
    exact div_nonneg (mul_nonneg hL (sq_nonneg _))
      (mul_nonneg hT.le hS.le)
  nlinarith

theorem lemma77VerticalSmoothing733_gaussianBranch_centerScaleDrift_le
    {beta c c33 : ℝ} (_hc33 : 0 < c33)
    (hquad : 2 * c33 ^ 2 ≤ c ^ 2)
    (hbudget : c33 ^ 2 / 8 ≤ beta / 2)
    {s lp : ℕ} (hlp : lp ≤ s) (x : ℝ) :
    Real.exp (-(beta * (lp : ℝ))) *
        Real.exp (-(((c * (x + (lp : ℝ) / 4)) ^ 2) /
          ((1 + (s - lp : ℕ) : ℝ)))) ≤
      Real.exp (-((beta / 2) * (lp : ℝ))) *
        Real.exp (-(((c33 * x) ^ 2) / (1 + (s : ℝ)))) := by
  let L : ℝ := lp
  let T : ℝ := (1 + (s - lp : ℕ) : ℝ)
  let S : ℝ := 1 + (s : ℝ)
  let y : ℝ := x + L / 4
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    positivity
  have hT_pos : 0 < T := by
    dsimp [T]
    positivity
  have hS_pos : 0 < S := by
    dsimp [S]
    positivity
  have hsub : ((s - lp : ℕ) : ℝ) = (s : ℝ) - (lp : ℝ) := by
    rw [Nat.cast_sub hlp]
  have hS_eq : S = T + L := by
    dsimp [S, T, L]
    rw [hsub]
    ring
  have hbase : x ^ 2 / S ≤ y ^ 2 / T + L / 16 := by
    simpa [y] using
      lemma77VerticalSmoothing733_gaussianCenterScale_base
        (S := S) (T := T) (L := L) (x := x)
        hT_pos hS_pos hL_nonneg hS_eq
  have hc33_sq_nonneg : 0 ≤ c33 ^ 2 := sq_nonneg c33
  have hbase_scaled :
      (c33 * x) ^ 2 / S ≤ c33 ^ 2 * (y ^ 2 / T + L / 16) := by
    calc
      (c33 * x) ^ 2 / S = c33 ^ 2 * (x ^ 2 / S) := by ring
      _ ≤ c33 ^ 2 * (y ^ 2 / T + L / 16) :=
          mul_le_mul_of_nonneg_left hbase hc33_sq_nonneg
  have hquad_weak : c33 ^ 2 ≤ c ^ 2 := by
    nlinarith [hc33_sq_nonneg, hquad]
  have hy_sq_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
  have hgauss_cmp : c33 ^ 2 * (y ^ 2 / T) ≤ (c * y) ^ 2 / T := by
    have hnum : c33 ^ 2 * y ^ 2 ≤ c ^ 2 * y ^ 2 :=
      mul_le_mul_of_nonneg_right hquad_weak hy_sq_nonneg
    have hdiv : c33 ^ 2 * y ^ 2 / T ≤ c ^ 2 * y ^ 2 / T :=
      div_le_div_of_nonneg_right hnum hT_pos.le
    calc
      c33 ^ 2 * (y ^ 2 / T) = c33 ^ 2 * y ^ 2 / T := by ring
      _ ≤ c ^ 2 * y ^ 2 / T := hdiv
      _ = (c * y) ^ 2 / T := by ring
  have hbudget16 : c33 ^ 2 / 16 ≤ beta / 2 := by
    nlinarith [hc33_sq_nonneg, hbudget]
  have hL_cmp : c33 ^ 2 * (L / 16) ≤ (beta / 2) * L := by
    nlinarith [mul_le_mul_of_nonneg_right hbudget16 hL_nonneg]
  have hscaled :
      (c33 * x) ^ 2 / S ≤ (c * y) ^ 2 / T + (beta / 2) * L := by
    have hright : c33 ^ 2 * (y ^ 2 / T + L / 16) ≤
        (c * y) ^ 2 / T + (beta / 2) * L := by
      nlinarith [hgauss_cmp, hL_cmp]
    exact le_trans hbase_scaled hright
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  dsimp [S, T, L, y] at hscaled ⊢
  nlinarith [hscaled]

theorem lemma77VerticalSmoothing733_innerCentered_eq
    (j : ℤ) (s lp : ℕ) (hlp : lp ≤ s) :
    lemma77ScalarCenteredHorizontal j (s - lp) =
      lemma77ScalarCenteredHorizontal j s + (lp : ℝ) / 4 := by
  unfold lemma77ScalarCenteredHorizontal
  rw [Nat.cast_sub hlp]
  ring

theorem lemma77VerticalSmoothing733_kernelSummand_le_outerBranchProfiles
    {C c beta c33 : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hc33 : 0 < c33)
    (hc33_le_c : c33 ≤ c) (hquarter : c33 / 4 ≤ beta / 2)
    (hquad : 2 * c33 ^ 2 ≤ c ^ 2)
    (hbudget : c33 ^ 2 / 8 ≤ beta / 2)
    (j : ℤ) {s lp : ℕ} (hlp : lp ≤ s) :
    Real.exp (-(beta * (lp : ℝ))) *
        lemma77HeightPotentialKernel C c j (s - lp) ≤
      C * (((1 + ((s - lp : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) *
        (Real.exp (-((beta / 2) * (lp : ℝ))) *
          Real.exp (-(((c33 * lemma77ScalarCenteredHorizontal j s) ^ 2) /
            (1 + (s : ℝ)))) +
         Real.exp (-((beta / 2) * (lp : ℝ))) *
          Real.exp (-(c33 * |lemma77ScalarCenteredHorizontal j s|)))) := by
  let x : ℝ := lemma77ScalarCenteredHorizontal j s
  let y : ℝ := lemma77ScalarCenteredHorizontal j (s - lp)
  let H : ℝ := ((1 + ((s - lp : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)))
  have hH_nonneg : 0 ≤ H := by
    dsimp [H]
    positivity
  have hfactor_nonneg : 0 ≤ C * H := mul_nonneg hC hH_nonneg
  have hcenter : y = x + (lp : ℝ) / 4 := by
    dsimp [x, y]
    exact lemma77VerticalSmoothing733_innerCentered_eq j s lp hlp
  have hlin_inner : Real.exp (-|c * y|) = Real.exp (-(c * |y|)) := by
    rw [abs_mul, abs_of_pos hc]
  have hlin :=
    lemma77VerticalSmoothing733_linearBranch_centerDrift_le
      hc33 hc33_le_c hquarter x lp
  have hlin' :
      Real.exp (-(beta * (lp : ℝ))) * Real.exp (-|c * y|) ≤
        Real.exp (-((beta / 2) * (lp : ℝ))) *
          Real.exp (-(c33 * |x|)) := by
    rw [hlin_inner, hcenter]
    exact hlin
  have hgauss :=
    lemma77VerticalSmoothing733_gaussianBranch_centerScaleDrift_le
      hc33 hquad hbudget hlp x
  have hgauss' :
      Real.exp (-(beta * (lp : ℝ))) *
          Real.exp (-(((c * y) ^ 2) / ((1 + (s - lp : ℕ) : ℝ)))) ≤
        Real.exp (-((beta / 2) * (lp : ℝ))) *
          Real.exp (-(((c33 * x) ^ 2) / (1 + (s : ℝ)))) := by
    rw [hcenter]
    exact hgauss
  have hsum :
      Real.exp (-(beta * (lp : ℝ))) *
          Real.exp (-(((c * y) ^ 2) / ((1 + (s - lp : ℕ) : ℝ)))) +
        Real.exp (-(beta * (lp : ℝ))) * Real.exp (-|c * y|) ≤
      Real.exp (-((beta / 2) * (lp : ℝ))) *
          Real.exp (-(((c33 * x) ^ 2) / (1 + (s : ℝ)))) +
        Real.exp (-((beta / 2) * (lp : ℝ))) *
          Real.exp (-(c33 * |x|)) :=
    add_le_add hgauss' hlin'
  have hmul := mul_le_mul_of_nonneg_left hsum hfactor_nonneg
  unfold lemma77HeightPotentialKernel
  dsimp [x, y, H] at hmul ⊢
  unfold taoLemma22GaussianWeight at hmul ⊢
  simp [mul_add, mul_assoc, mul_left_comm, mul_comm] at hmul ⊢
  exact hmul

theorem lemma77VerticalSmoothing733KernelSum_le_heightKernel_of_heightScale
    {C c beta K c33 : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hK : 0 ≤ K) (hc33 : 0 < c33)
    (hc33_le_c : c33 ≤ c) (hquarter : c33 / 4 ≤ beta / 2)
    (hquad : 2 * c33 ^ 2 ≤ c ^ 2)
    (hbudget : c33 ^ 2 / 8 ≤ beta / 2)
    (hheight : ∀ s : ℕ,
      (∑ lp ∈ Finset.range (s + 1),
        Real.exp (-((beta / 2) * (lp : ℝ))) *
          ((1 + ((s - lp : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)))) ≤
        K * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))))
    (j : ℤ) (s : ℕ) :
    lemma77VerticalSmoothing733KernelSum C c beta j s ≤
      lemma77HeightPotentialKernel (C * K + C * K) c33 j s := by
  let R := Finset.range (s + 1)
  let x : ℝ := lemma77ScalarCenteredHorizontal j s
  let Hout : ℝ := (1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))
  let Q : ℝ := Real.exp (-(((c33 * x) ^ 2) / (1 + (s : ℝ))))
  let Lprof : ℝ := Real.exp (-(c33 * |x|))
  let A : ℕ → ℝ := fun lp =>
    Real.exp (-((beta / 2) * (lp : ℝ))) *
      ((1 + ((s - lp : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)))
  have hHout_nonneg : 0 ≤ Hout := by
    dsimp [Hout]
    positivity
  have hQ_nonneg : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hLprof_nonneg : 0 ≤ Lprof := by
    dsimp [Lprof]
    positivity
  have hCK_nonneg : 0 ≤ C * K := mul_nonneg hC hK
  have hA_sum : R.sum A ≤ K * Hout := by
    dsimp [R, A, Hout]
    exact hheight s
  have hpoint : ∀ lp ∈ R,
      Real.exp (-beta * (lp : ℝ)) *
          lemma77HeightPotentialKernel C c j (s - lp) ≤
        C * (A lp * Q + A lp * Lprof) := by
    intro lp hlp_mem
    have hlp : lp ≤ s := by
      dsimp [R] at hlp_mem
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hlp_mem)
    have hp :=
      lemma77VerticalSmoothing733_kernelSummand_le_outerBranchProfiles
        hC hc hc33 hc33_le_c hquarter hquad hbudget j hlp
    calc
      Real.exp (-beta * (lp : ℝ)) *
          lemma77HeightPotentialKernel C c j (s - lp)
          = Real.exp (-(beta * (lp : ℝ))) *
              lemma77HeightPotentialKernel C c j (s - lp) := by
            congr 1
            ring_nf
      _ ≤ C * (((1 + ((s - lp : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) *
          (Real.exp (-((beta / 2) * (lp : ℝ))) *
            Real.exp (-(((c33 * lemma77ScalarCenteredHorizontal j s) ^ 2) /
              (1 + (s : ℝ)))) +
           Real.exp (-((beta / 2) * (lp : ℝ))) *
            Real.exp (-(c33 * |lemma77ScalarCenteredHorizontal j s|)))) := hp
      _ = C * (A lp * Q + A lp * Lprof) := by
        dsimp [A, Q, Lprof, x]
        ring
  have hsum_decomp :
      R.sum (fun n => A n * Q + A n * Lprof) =
        R.sum A * Q + R.sum A * Lprof := by
    rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
  calc
    lemma77VerticalSmoothing733KernelSum C c beta j s ≤
        R.sum (fun n => C * (A n * Q + A n * Lprof)) := by
      unfold lemma77VerticalSmoothing733KernelSum
      dsimp [R]
      exact Finset.sum_le_sum hpoint
    _ = C * R.sum (fun n => A n * Q + A n * Lprof) := by
      exact (Finset.mul_sum R (fun n => A n * Q + A n * Lprof) C).symm
    _ = C * (R.sum A * Q + R.sum A * Lprof) := by
      exact congrArg (fun z => C * z) hsum_decomp
    _ ≤ C * ((K * Hout) * Q + (K * Hout) * Lprof) := by
      have hq : R.sum A * Q ≤ (K * Hout) * Q :=
        mul_le_mul_of_nonneg_right hA_sum hQ_nonneg
      have hl : R.sum A * Lprof ≤ (K * Hout) * Lprof :=
        mul_le_mul_of_nonneg_right hA_sum hLprof_nonneg
      exact mul_le_mul_of_nonneg_left (add_le_add hq hl) hC
    _ = (C * K) * Hout * Q + (C * K) * Hout * Lprof := by
        ring
    _ ≤ lemma77HeightPotentialKernel (C * K) c33 j s +
          lemma77HeightPotentialKernel (C * K) c33 j s := by
      exact add_le_add
        (by
          have h := lemma77HeightPotentialKernel_gaussianExp_le
            (K := C * K) (r := c33 ^ 2) (ch := c33)
            hCK_nonneg (pow_pos hc33 2) hc33 le_rfl j s
          dsimp [Hout, Q, x]
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h)
        (by
          dsimp [Hout, Lprof, x]
          exact lemma77HeightPotentialKernel_absExp_le
            hCK_nonneg hc33 hc33 le_rfl j s)
    _ = lemma77HeightPotentialKernel (C * K + C * K) c33 j s := by
      rw [lemma77HeightPotentialKernel_add_same_rate]

theorem lemma77VerticalSmoothing733Mass_le_kernelSum
    {C c beta : ℝ}
    (hheight : Lemma77HeightPotentialInput C c)
    (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) :
    lemma77VerticalSmoothing733Mass beta start j s ≤
      lemma77VerticalSmoothing733KernelSum C c beta j s := by
  unfold lemma77VerticalSmoothing733Mass
    lemma77VerticalSmoothing733KernelSum
  apply Finset.sum_le_sum
  intro lp _hlp
  exact mul_le_mul_of_nonneg_left
    (hheight.height_potential start j (s - lp))
    (le_of_lt (Real.exp_pos _))

theorem lemma77VerticalSmoothing733Mass_le_of_verticalSmoothing733Input
    {C c beta C33 c33 : ℝ}
    (hheight : Lemma77HeightPotentialInput C c)
    (h733 : Lemma77VerticalSmoothing733Input C c beta C33 c33)
    (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) :
    lemma77VerticalSmoothing733Mass beta start j s ≤
      lemma77HeightPotentialKernel C33 c33 j s :=
  le_trans (lemma77VerticalSmoothing733Mass_le_kernelSum hheight start j s)
    (h733.kernel_sum_bound j s)

def lemma77PositiveHorizontalIncrement (q : ℕ) : ℤ :=
  ((q + 1 : ℕ) : ℤ)

def lemma77HorizontalShift732 (j : ℤ) (q : ℕ) : ℤ :=
  j - lemma77PositiveHorizontalIncrement q

def lemma77HorizontalConvolution732KernelTsum
    (alpha C c : ℝ) (j : ℤ) (s : ℕ) : ℝ :=
  ∑' q : ℕ,
    Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
      lemma77HeightPotentialKernel C c
        (lemma77HorizontalShift732 j q) s

structure Lemma77HorizontalConvolution732Input
    (alpha C33 c33 C32 c32 : ℝ) : Prop where
  constants : 0 < alpha ∧ 0 ≤ C32 ∧ 0 < c32
  kernel_summable :
    ∀ j s,
      Summable (fun q : ℕ =>
        Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
          lemma77HeightPotentialKernel C33 c33
            (lemma77HorizontalShift732 j q) s)
  kernel_tsum_bound :
    ∀ j s,
      lemma77HorizontalConvolution732KernelTsum alpha C33 c33 j s ≤
        lemma77HeightPotentialKernel C32 c32 j s

theorem lemma77HorizontalShift732_centered_eq (j : ℤ) (q s : ℕ) :
    lemma77ScalarCenteredHorizontal (lemma77HorizontalShift732 j q) s =
      lemma77ScalarCenteredHorizontal j s - (((q + 1 : ℕ) : ℝ)) := by
  unfold lemma77HorizontalShift732 lemma77PositiveHorizontalIncrement
    lemma77ScalarCenteredHorizontal
  norm_num
  ring

theorem taoLemma22GaussianWeight_le_two (n : ℕ) (x : ℝ) :
    taoLemma22GaussianWeight n x ≤ 2 := by
  unfold taoLemma22GaussianWeight
  by_cases hn : n = 0
  · simp [hn]
    have hlin : Real.exp (-|x|) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (abs_nonneg x)
    nlinarith
  · simp [hn]
    have hn_pos_nat : 0 < n := Nat.pos_of_ne_zero hn
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
    have hquad_nonneg : 0 ≤ x ^ 2 / (n : ℝ) :=
      div_nonneg (sq_nonneg x) hn_pos.le
    have hquad : Real.exp (-(x ^ 2 / (n : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr hquad_nonneg
    have hlin : Real.exp (-|x|) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (abs_nonneg x)
    nlinarith

theorem lemma77HorizontalConvolution732_weight_smallShift_le
    {c ch x n : ℝ} (hc : 0 < c) (hch : 0 < ch)
    (h2ch : 2 * ch ≤ c) (hn_nonneg : 0 ≤ n)
    (hsmall : n ≤ |x| / 2) (s : ℕ) :
    taoLemma22GaussianWeight (1 + s) (c * (x - n)) ≤
      taoLemma22GaussianWeight (1 + s) (ch * x) := by
  have htri : |x| ≤ |x - n| + |n| := by
    have h := abs_add_le (x - n) n
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  have hn_abs : |n| = n := abs_of_nonneg hn_nonneg
  have hx_le : |x| ≤ 2 * |x - n| := by
    rw [hn_abs] at htri
    nlinarith [htri, hsmall]
  have hch_abs : |ch * x| = ch * |x| := by
    rw [abs_mul, abs_of_pos hch]
  have hc_abs : |c * (x - n)| = c * |x - n| := by
    rw [abs_mul, abs_of_pos hc]
  have habs : |ch * x| ≤ |c * (x - n)| := by
    rw [hch_abs, hc_abs]
    calc
      ch * |x| ≤ ch * (2 * |x - n|) :=
        mul_le_mul_of_nonneg_left hx_le hch.le
      _ = (2 * ch) * |x - n| := by ring
      _ ≤ c * |x - n| :=
        mul_le_mul_of_nonneg_right h2ch (abs_nonneg (x - n))
  have hsq_abs : |ch * x| ^ 2 ≤ |c * (x - n)| ^ 2 := by
    nlinarith [habs, abs_nonneg (ch * x), abs_nonneg (c * (x - n))]
  have hsq : (ch * x) ^ 2 ≤ (c * (x - n)) ^ 2 := by
    calc
      (ch * x) ^ 2 = |ch * x| ^ 2 := by
        rw [sq_abs]
      _ ≤ |c * (x - n)| ^ 2 := hsq_abs
      _ = (c * (x - n)) ^ 2 := by
        rw [sq_abs]
  have hN_pos : 0 < ((1 + s : ℕ) : ℝ) := by positivity
  have hquad_arg :
      (ch * x) ^ 2 / ((1 + s : ℕ) : ℝ) ≤
        (c * (x - n)) ^ 2 / ((1 + s : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hsq hN_pos.le
  have hquad :
      Real.exp (-((c * (x - n)) ^ 2 / ((1 + s : ℕ) : ℝ))) ≤
        Real.exp (-((ch * x) ^ 2 / ((1 + s : ℕ) : ℝ))) := by
    rw [Real.exp_le_exp]
    linarith
  have hlin :
      Real.exp (-|c * (x - n)|) ≤ Real.exp (-|ch * x|) := by
    rw [Real.exp_le_exp]
    linarith
  unfold taoLemma22GaussianWeight
  simp
  simpa [Nat.cast_add, Nat.cast_one] using add_le_add hquad hlin

theorem lemma77HorizontalConvolution732_weightSummand_le_profiles
    {alpha c ch : ℝ} (hc : 0 < c) (hch : 0 < ch)
    (h2ch : 2 * ch ≤ c) (h4ch : 4 * ch ≤ alpha)
    (q s : ℕ) (x : ℝ) :
    Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) *
        taoLemma22GaussianWeight (1 + s)
          (c * (x - (((q + 1 : ℕ) : ℝ)))) ≤
      Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) *
        taoLemma22GaussianWeight (1 + s) (ch * x) +
      2 * Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ)))) *
        Real.exp (-(ch * |x|)) := by
  let n : ℝ := ((q + 1 : ℕ) : ℝ)
  have hn_nonneg : 0 ≤ n := by
    dsimp [n]
    positivity
  have hn_pos : 0 < n := by
    dsimp [n]
    positivity
  by_cases hsmall : n ≤ |x| / 2
  · have hweight :=
      lemma77HorizontalConvolution732_weight_smallShift_le
        hc hch h2ch hn_nonneg hsmall s
        (x := x) (n := n)
    have hmul :
        Real.exp (-(alpha * n)) *
            taoLemma22GaussianWeight (1 + s) (c * (x - n)) ≤
          Real.exp (-(alpha * n)) *
            taoLemma22GaussianWeight (1 + s) (ch * x) :=
      mul_le_mul_of_nonneg_left hweight (le_of_lt (Real.exp_pos _))
    have htail_nonneg :
        0 ≤ 2 * Real.exp (-((alpha / 2) * n)) *
          Real.exp (-(ch * |x|)) := by
      positivity
    dsimp [n] at hmul ⊢
    exact le_trans hmul (le_add_of_nonneg_right htail_nonneg)
  · have hlarge : |x| / 2 < n := lt_of_not_ge hsmall
    have hhalf_tail :
        Real.exp (-((alpha / 2) * n)) ≤ Real.exp (-(ch * |x|)) := by
      rw [Real.exp_le_exp]
      have hx_nonneg : 0 ≤ |x| := abs_nonneg x
      nlinarith [hlarge, h4ch, hch.le, hx_nonneg, hn_pos.le]
    have hweight_bound :
        taoLemma22GaussianWeight (1 + s) (c * (x - n)) ≤ 2 :=
      taoLemma22GaussianWeight_le_two (1 + s) (c * (x - n))
    have hsplit :
        Real.exp (-(alpha * n)) =
          Real.exp (-((alpha / 2) * n)) *
            Real.exp (-((alpha / 2) * n)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hterm :
        Real.exp (-(alpha * n)) *
            taoLemma22GaussianWeight (1 + s) (c * (x - n)) ≤
          2 * Real.exp (-((alpha / 2) * n)) *
            Real.exp (-(ch * |x|)) := by
      calc
        Real.exp (-(alpha * n)) *
            taoLemma22GaussianWeight (1 + s) (c * (x - n)) ≤
          Real.exp (-(alpha * n)) * 2 :=
            mul_le_mul_of_nonneg_left hweight_bound (le_of_lt (Real.exp_pos _))
        _ = 2 * Real.exp (-((alpha / 2) * n)) *
              Real.exp (-((alpha / 2) * n)) := by
            rw [hsplit]
            ring
        _ ≤ 2 * Real.exp (-((alpha / 2) * n)) *
              Real.exp (-(ch * |x|)) := by
            exact mul_le_mul_of_nonneg_left hhalf_tail
              (by positivity)
    have hfirst_nonneg :
        0 ≤ Real.exp (-(alpha * n)) *
          taoLemma22GaussianWeight (1 + s) (ch * x) := by
      exact mul_nonneg (le_of_lt (Real.exp_pos _))
        (taoLemma22GaussianWeight_nonneg (1 + s) (ch * x))
    dsimp [n] at hterm ⊢
    exact le_trans hterm (le_add_of_nonneg_left hfirst_nonneg)

theorem lemma77HorizontalConvolution732_kernelSummand_le_profiles
    {C alpha c ch : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hch : 0 < ch)
    (h2ch : 2 * ch ≤ c) (h4ch : 4 * ch ≤ alpha)
    (j : ℤ) (q s : ℕ) :
    Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) *
        lemma77HeightPotentialKernel C c (lemma77HorizontalShift732 j q) s ≤
      Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) *
        lemma77HeightPotentialKernel C ch j s +
      (2 * C) * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) *
        Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ)))) *
        Real.exp (-(ch * |lemma77ScalarCenteredHorizontal j s|)) := by
  let x : ℝ := lemma77ScalarCenteredHorizontal j s
  let n : ℝ := ((q + 1 : ℕ) : ℝ)
  let H : ℝ := (1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))
  have hH_nonneg : 0 ≤ H := by
    dsimp [H]
    positivity
  have hfactor_nonneg : 0 ≤ C * H := mul_nonneg hC hH_nonneg
  have hcenter :
      lemma77ScalarCenteredHorizontal (lemma77HorizontalShift732 j q) s =
        x - n := by
    dsimp [x, n]
    exact lemma77HorizontalShift732_centered_eq j q s
  have hweight :=
    lemma77HorizontalConvolution732_weightSummand_le_profiles
      hc hch h2ch h4ch q s x
  have hmul := mul_le_mul_of_nonneg_left hweight hfactor_nonneg
  calc
    Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) *
        lemma77HeightPotentialKernel C c (lemma77HorizontalShift732 j q) s =
      (C * H) *
        (Real.exp (-(alpha * n)) *
          taoLemma22GaussianWeight (1 + s) (c * (x - n))) := by
        simp [lemma77HeightPotentialKernel, lemma77ScalarCenteredHorizontal,
          lemma77HorizontalShift732, lemma77PositiveHorizontalIncrement, H, x, n]
        ring_nf
    _ ≤ (C * H) *
        (Real.exp (-(alpha * n)) *
          taoLemma22GaussianWeight (1 + s) (ch * x) +
        2 * Real.exp (-((alpha / 2) * n)) *
          Real.exp (-(ch * |x|))) := hmul
    _ = Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) *
          lemma77HeightPotentialKernel C ch j s +
        (2 * C) * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) *
          Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ)))) *
          Real.exp (-(ch * |lemma77ScalarCenteredHorizontal j s|)) := by
        unfold lemma77HeightPotentialKernel
        dsimp [H, x, n, lemma77ScalarCenteredHorizontal]
        ring_nf

theorem lemma77HorizontalConvolution732Kernel_summable
    {alpha C c ch : ℝ} (hC : 0 ≤ C) (halpha : 0 < alpha)
    (hc : 0 < c) (hch : 0 < ch)
    (h2ch : 2 * ch ≤ c) (h4ch : 4 * ch ≤ alpha)
    (j : ℤ) (s : ℕ) :
    Summable (fun q : ℕ =>
      Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) *
        lemma77HeightPotentialKernel C c (lemma77HorizontalShift732 j q) s) := by
  let x : ℝ := lemma77ScalarCenteredHorizontal j s
  let H : ℝ := (1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))
  let first : ℕ → ℝ := fun q =>
    lemma77HeightPotentialKernel C ch j s *
      Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ))))
  let second : ℕ → ℝ := fun q =>
    ((2 * C) * H * Real.exp (-(ch * |x|))) *
      Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ))))
  have hA_summ :
      Summable fun q : ℕ =>
        Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) := by
    simpa [Function.comp_def, Nat.succ_eq_add_one] using
      (lemma77ExpNegMulNat_summable halpha).comp_injective Nat.succ_injective
  have hhalf : 0 < alpha / 2 := by positivity
  have hB_summ :
      Summable fun q : ℕ =>
        Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ)))) := by
    simpa [Function.comp_def, Nat.succ_eq_add_one] using
      (lemma77ExpNegMulNat_summable hhalf).comp_injective Nat.succ_injective
  have hfirst_summ : Summable first := hA_summ.mul_left _
  have hsecond_summ : Summable second := hB_summ.mul_left _
  have hupper_summ : Summable fun q : ℕ => first q + second q :=
    hfirst_summ.add hsecond_summ
  refine Summable.of_nonneg_of_le ?_ ?_ hupper_summ
  · intro q
    exact mul_nonneg (le_of_lt (Real.exp_pos _))
      (lemma77HeightPotentialKernel_nonneg hC (lemma77HorizontalShift732 j q) s)
  · intro q
    have hpoint :=
      lemma77HorizontalConvolution732_kernelSummand_le_profiles
        hC hc hch h2ch h4ch j q s
    dsimp [first, second, x, H]
    nlinarith [hpoint]

theorem lemma77HorizontalConvolution732KernelTsum_le_heightKernel
    {alpha C c ch : ℝ} (hC : 0 ≤ C) (halpha : 0 < alpha)
    (hc : 0 < c) (hch : 0 < ch)
    (h2ch : 2 * ch ≤ c) (h4ch : 4 * ch ≤ alpha)
    (j : ℤ) (s : ℕ) :
    lemma77HorizontalConvolution732KernelTsum alpha C c j s ≤
      lemma77HeightPotentialKernel
        (C * (∑' q : ℕ,
          Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ))))) +
          (2 * C) * (∑' q : ℕ,
            Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ))))))
        ch j s := by
  let x : ℝ := lemma77ScalarCenteredHorizontal j s
  let H : ℝ := (1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))
  let A : ℝ := ∑' q : ℕ,
    Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ))))
  let B : ℝ := ∑' q : ℕ,
    Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ))))
  let first : ℕ → ℝ := fun q =>
    lemma77HeightPotentialKernel C ch j s *
      Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ))))
  let second : ℕ → ℝ := fun q =>
    ((2 * C) * H * Real.exp (-(ch * |x|))) *
      Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ))))
  have hA_summ :
      Summable fun q : ℕ =>
        Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) := by
    simpa [Function.comp_def, Nat.succ_eq_add_one] using
      (lemma77ExpNegMulNat_summable halpha).comp_injective Nat.succ_injective
  have hhalf : 0 < alpha / 2 := by positivity
  have hB_summ :
      Summable fun q : ℕ =>
        Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ)))) := by
    simpa [Function.comp_def, Nat.succ_eq_add_one] using
      (lemma77ExpNegMulNat_summable hhalf).comp_injective Nat.succ_injective
  have hfirst_summ : Summable first := hA_summ.mul_left _
  have hsecond_summ : Summable second := hB_summ.mul_left _
  have hupper_summ : Summable fun q : ℕ => first q + second q :=
    hfirst_summ.add hsecond_summ
  have hkernel_summ :
      Summable (fun q : ℕ =>
        Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) *
          lemma77HeightPotentialKernel C c
            (lemma77HorizontalShift732 j q) s) :=
    lemma77HorizontalConvolution732Kernel_summable
      hC halpha hc hch h2ch h4ch j s
  have hpoint : ∀ q : ℕ,
      Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) *
          lemma77HeightPotentialKernel C c
            (lemma77HorizontalShift732 j q) s ≤
        first q + second q := by
    intro q
    have h :=
      lemma77HorizontalConvolution732_kernelSummand_le_profiles
        hC hc hch h2ch h4ch j q s
    dsimp [first, second, x, H]
    nlinarith [h]
  have htsum_le :
      lemma77HorizontalConvolution732KernelTsum alpha C c j s ≤
        (∑' q : ℕ, (first q + second q)) := by
    unfold lemma77HorizontalConvolution732KernelTsum
    have hkernel_summ' :
        Summable (fun q : ℕ =>
          Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
            lemma77HeightPotentialKernel C c
              (lemma77HorizontalShift732 j q) s) := by
      simpa [neg_mul] using hkernel_summ
    exact hkernel_summ'.tsum_le_tsum
      (fun i => by simpa [neg_mul] using hpoint i) hupper_summ
  have htsum_upper :
      (∑' q : ℕ, (first q + second q)) =
        (∑' q : ℕ, first q) + (∑' q : ℕ, second q) :=
    hfirst_summ.tsum_add hsecond_summ
  have hfirst_tsum :
      (∑' q : ℕ, first q) =
        lemma77HeightPotentialKernel (C * A) ch j s := by
    have hmul :
        (∑' q : ℕ, first q) =
          lemma77HeightPotentialKernel C ch j s * A := by
      dsimp [first, A]
      rw [tsum_mul_left]
    rw [hmul]
    unfold lemma77HeightPotentialKernel
    ring
  have hsecond_tsum :
      (∑' q : ℕ, second q) =
        ((2 * C) * B) * H * Real.exp (-(ch * |x|)) := by
    have hmul :
        (∑' q : ℕ, second q) =
          ((2 * C) * H * Real.exp (-(ch * |x|))) * B := by
      dsimp [second, B]
      rw [tsum_mul_left]
    rw [hmul]
    ring
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact tsum_nonneg fun q => le_of_lt (Real.exp_pos _)
  have hsecond_absorb :
      ((2 * C) * B) * H * Real.exp (-(ch * |x|)) ≤
        lemma77HeightPotentialKernel ((2 * C) * B) ch j s := by
    have hK_nonneg : 0 ≤ (2 * C) * B := by
      positivity
    dsimp [H, x]
    exact lemma77HeightPotentialKernel_absExp_le
      hK_nonneg hch hch le_rfl j s
  calc
    lemma77HorizontalConvolution732KernelTsum alpha C c j s ≤
        (∑' q : ℕ, (first q + second q)) := htsum_le
    _ = (∑' q : ℕ, first q) + (∑' q : ℕ, second q) := htsum_upper
    _ = lemma77HeightPotentialKernel (C * A) ch j s +
          ((2 * C) * B) * H * Real.exp (-(ch * |x|)) := by
        rw [hfirst_tsum, hsecond_tsum]
    _ ≤ lemma77HeightPotentialKernel (C * A) ch j s +
          lemma77HeightPotentialKernel ((2 * C) * B) ch j s :=
        add_le_add le_rfl hsecond_absorb
    _ = lemma77HeightPotentialKernel (C * A + (2 * C) * B) ch j s := by
        rw [lemma77HeightPotentialKernel_add_same_rate]
    _ = lemma77HeightPotentialKernel
        (C * (∑' q : ℕ,
          Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ))))) +
          (2 * C) * (∑' q : ℕ,
            Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ))))))
        ch j s := by
        dsimp [A, B]

def lemma77HorizontalConvolution732Mass
    (alpha beta : ℝ)
    (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) : ℝ :=
  ∑' q : ℕ,
    Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
      lemma77VerticalSmoothing733Mass beta start
        (lemma77HorizontalShift732 j q) s

theorem lemma77VerticalSmoothing733Mass_nonneg
    (beta : ℝ) (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) :
    0 ≤ lemma77VerticalSmoothing733Mass beta start j s := by
  unfold lemma77VerticalSmoothing733Mass
  apply Finset.sum_nonneg
  intro lp _hlp
  exact mul_nonneg (le_of_lt (Real.exp_pos _))
    (lemma77HeightPotentialMass_nonneg start j (s - lp))

theorem lemma77HorizontalConvolution732Mass_summable_of_verticalSmoothing733Input
    {C c beta C33 c33 alpha C32 c32 : ℝ}
    (hheight : Lemma77HeightPotentialInput C c)
    (h733 : Lemma77VerticalSmoothing733Input C c beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) :
    Summable (fun q : ℕ =>
      Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
        lemma77VerticalSmoothing733Mass beta start
          (lemma77HorizontalShift732 j q) s) := by
  exact Summable.of_nonneg_of_le
    (fun q => mul_nonneg (le_of_lt (Real.exp_pos _))
      (lemma77VerticalSmoothing733Mass_nonneg beta start
        (lemma77HorizontalShift732 j q) s))
    (fun q => mul_le_mul_of_nonneg_left
      (lemma77VerticalSmoothing733Mass_le_of_verticalSmoothing733Input
        hheight h733 start (lemma77HorizontalShift732 j q) s)
      (le_of_lt (Real.exp_pos _)))
    (h732.kernel_summable j s)

theorem lemma77HorizontalConvolution732Mass_le_kernelSum
    {C c beta C33 c33 alpha C32 c32 : ℝ}
    (hheight : Lemma77HeightPotentialInput C c)
    (h733 : Lemma77VerticalSmoothing733Input C c beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) :
    lemma77HorizontalConvolution732Mass alpha beta start j s ≤
      lemma77HorizontalConvolution732KernelTsum alpha C33 c33 j s := by
  calc
    lemma77HorizontalConvolution732Mass alpha beta start j s
        = ∑' q : ℕ,
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              lemma77VerticalSmoothing733Mass beta start
                (lemma77HorizontalShift732 j q) s := by
          rfl
    _ ≤ lemma77HorizontalConvolution732KernelTsum alpha C33 c33 j s :=
        (lemma77HorizontalConvolution732Mass_summable_of_verticalSmoothing733Input
          hheight h733 h732 start j s).tsum_le_tsum
          (fun q => mul_le_mul_of_nonneg_left
            (lemma77VerticalSmoothing733Mass_le_of_verticalSmoothing733Input
              hheight h733 start (lemma77HorizontalShift732 j q) s)
            (le_of_lt (Real.exp_pos _)))
          (h732.kernel_summable j s)

theorem lemma77HorizontalConvolution732Mass_le_of_horizontalConvolution732Input
    {C c beta C33 c33 alpha C32 c32 : ℝ}
    (hheight : Lemma77HeightPotentialInput C c)
    (h733 : Lemma77VerticalSmoothing733Input C c beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) :
    lemma77HorizontalConvolution732Mass alpha beta start j s ≤
      lemma77HeightPotentialKernel C32 c32 j s :=
  le_trans
    (lemma77HorizontalConvolution732Mass_le_kernelSum
      hheight h733 h732 start j s)
    (h732.kernel_tsum_bound j s)

end TaoSection7Lemma77

end

end Tao

end Erdos1135Predecessor
