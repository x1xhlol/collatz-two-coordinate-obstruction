import Erdos1135.Tao.Renewal.CanonicalFirstPassagePointwise

/-!
# Canonical First-Passage Horizontal Marginal

This proof leaf marginalizes the canonical countable endpoint law over its
vertical coordinate.  It keeps the marginalization in native `ENNReal`,
reindexes the strict first-passage support by positive overshoot, and records
the exact geometric factor at rate `log (21/20)`.
-/

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Lemma77

/-- Horizontal marginal of the canonical first-passage endpoint law. -/
noncomputable def lemma77CanonicalFirstPassageHorizontalPMF
    (start : TaoSection7RenewalPoint) (s : ℕ) : PMF ℕ :=
  (lemma77CanonicalFirstPassageEndpointPMF start s).map Prod.fst

/-- The fiber of the first projection over `r` is equivalent to the integer
vertical coordinate. -/
private def lemma77HorizontalFiberEquiv (r : ℕ) :
    ℤ ≃ {x : ℕ × ℤ // x.1 = r} where
  toFun ell := ⟨(r, ell), rfl⟩
  invFun x := x.1.2
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨r', ell⟩, hr'⟩
    apply Subtype.ext
    simp only at hr'
    simp [hr']

/-- Exact integer-height expansion of a horizontal marginal atom. -/
theorem lemma77CanonicalFirstPassageHorizontalPMF_apply_eq_tsum_int
    (start : TaoSection7RenewalPoint) (s r : ℕ) :
    lemma77CanonicalFirstPassageHorizontalPMF start s r =
      ∑' ell : ℤ,
        lemma77CanonicalFirstPassageEndpointPMF start s (r, ell) := by
  rw [lemma77CanonicalFirstPassageHorizontalPMF,
    pmf_map_apply_eq_tsum_fiber]
  simpa using ((lemma77HorizontalFiberEquiv r).tsum_eq
    (fun x => lemma77CanonicalFirstPassageEndpointPMF start s x.1)).symm

/-- Integers strictly above `s` are canonically indexed by a nonnegative
overshoot, with the first height represented by `u = 0`. -/
private def lemma77PositiveEndpointHeightEquiv (s : ℕ) :
    ℕ ≃ {ell : ℤ // (s : ℤ) < ell} where
  toFun u := ⟨(s : ℤ) + 1 + (u : ℤ), by omega⟩
  invFun ell := (ell.1 - (s : ℤ) - 1).toNat
  left_inv u := by
    simp only
    omega
  right_inv ell := by
    apply Subtype.ext
    simp only
    omega

/-- Exact positive-overshoot expansion of a horizontal marginal atom. -/
theorem lemma77CanonicalFirstPassageHorizontalPMF_apply_eq_tsum_overshoot
    (start : TaoSection7RenewalPoint) (s r : ℕ) :
    lemma77CanonicalFirstPassageHorizontalPMF start s r =
      ∑' u : ℕ,
        lemma77CanonicalFirstPassageEndpointPMF start s
          (r, (s : ℤ) + 1 + (u : ℤ)) := by
  rw [lemma77CanonicalFirstPassageHorizontalPMF_apply_eq_tsum_int]
  let f : ℤ → ENNReal := fun ell =>
    lemma77CanonicalFirstPassageEndpointPMF start s (r, ell)
  have hsupp : Function.support f ⊆ {ell : ℤ | (s : ℤ) < ell} := by
    intro ell hell
    exact lemma77CanonicalFirstPassageEndpointPMF_nonzero_support hell |>.2
  calc
    (∑' ell : ℤ, f ell) =
        ∑' ell : {ell : ℤ // (s : ℤ) < ell}, f ell.1 :=
      (tsum_subtype_eq_of_support_subset (f := f)
        (s := {ell : ℤ | (s : ℤ) < ell}) hsupp).symm
    _ = ∑' u : ℕ, f ((s : ℤ) + 1 + (u : ℤ)) :=
      (lemma77PositiveEndpointHeightEquiv s).tsum_eq
        (fun ell => f ell.1) |>.symm

/-- One positive-overshoot exponential term is the corresponding power of
`20/21`. -/
private theorem lemma77_exp_neg_log_21_div_20_positiveOvershoot_eq
    (u : ℕ) :
    Real.exp
        (-(Real.log (21 / 20 : ℝ)) * ((u + 1 : ℕ) : ℝ)) =
      (20 / 21 : ℝ) ^ (u + 1) := by
  rw [show
    -(Real.log (21 / 20 : ℝ)) * ((u + 1 : ℕ) : ℝ) =
      ((u + 1 : ℕ) : ℝ) * (-(Real.log (21 / 20 : ℝ))) by ring]
  rw [Real.exp_nat_mul, Real.exp_neg,
    Real.exp_log (by norm_num : 0 < (21 / 20 : ℝ))]
  norm_num

/-- The positive-overshoot exponential weights are summable. -/
theorem lemma77_summable_exp_neg_log_21_div_20_positiveOvershoot :
    Summable fun u : ℕ =>
      Real.exp
        (-(Real.log (21 / 20 : ℝ)) * ((u + 1 : ℕ) : ℝ)) := by
  have hgeom : Summable (fun u : ℕ => (20 / 21 : ℝ) ^ u) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hshift : Summable (fun u : ℕ => (20 / 21 : ℝ) ^ (u + 1)) := by
    simpa only [pow_succ'] using hgeom.mul_left (20 / 21 : ℝ)
  exact hshift.congr fun u =>
    (lemma77_exp_neg_log_21_div_20_positiveOvershoot_eq u).symm

/-- The positive-overshoot geometric series at Tao's concrete terminal rate
has exact mass `20`. -/
theorem lemma77_tsum_exp_neg_log_21_div_20_positiveOvershoot :
    (∑' u : ℕ,
      Real.exp
        (-(Real.log (21 / 20 : ℝ)) * ((u + 1 : ℕ) : ℝ))) = 20 := by
  let q : ℝ := 20 / 21
  have hq0 : 0 ≤ q := by norm_num [q]
  have hq1 : q < 1 := by norm_num [q]
  calc
    (∑' u : ℕ,
        Real.exp
          (-(Real.log (21 / 20 : ℝ)) * ((u + 1 : ℕ) : ℝ))) =
        ∑' u : ℕ, q ^ (u + 1) := by
      apply tsum_congr
      intro u
      simpa [q] using
        lemma77_exp_neg_log_21_div_20_positiveOvershoot_eq u
    _ = q * ∑' u : ℕ, q ^ u := by
      simp_rw [pow_succ']
      rw [tsum_mul_left]
    _ = q * (1 - q)⁻¹ := by
      rw [tsum_geometric_of_lt_one hq0 hq1]
    _ = 20 := by norm_num [q]

/-- The endpoint kernel after summing its positive vertical overshoot. -/
def lemma77HorizontalPointwiseKernel
    (A B C : ℝ) (s r : ℕ) : ℝ :=
  C * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) *
    (Real.exp
        (-A * ((lemma77CenteredHorizontalDisplacement s r) ^ 2 /
          (1 + (s : ℝ)))) +
      Real.exp (-B * |lemma77CenteredHorizontalDisplacement s r|))

/-- Summing the concrete endpoint kernel over positive overshoot multiplies
its pointwise constant by exactly `20`. -/
theorem lemma77_tsum_pointwiseEndpointKernel_positiveOvershoot
    (C32 c32 : ℝ) (s r : ℕ) :
    (∑' u : ℕ,
      lemma77PointwiseEndpointKernel
        (c32 ^ 2) c32 (15 * C32) (Real.log (21 / 20 : ℝ))
        s r ((u + 1 : ℕ) : ℤ)) =
      lemma77HorizontalPointwiseKernel
        (c32 ^ 2) c32 (300 * C32) s r := by
  unfold lemma77PointwiseEndpointKernel lemma77HorizontalPointwiseKernel
  simp only [Int.cast_natCast]
  rw [tsum_mul_left,
    lemma77_tsum_exp_neg_log_21_div_20_positiveOvershoot]
  ring

/-- Native countable horizontal marginal of the canonical pointwise endpoint
estimate. -/
theorem lemma77CanonicalFirstPassageHorizontalPMF_pointwiseKernel :
    ∃ C32 c32 : ℝ, 0 ≤ C32 ∧ 0 < c32 ∧
      ∀ (start : TaoSection7RenewalPoint) (s r : ℕ),
        lemma77CanonicalFirstPassageHorizontalPMF start s r ≤
          ENNReal.ofReal
            (lemma77HorizontalPointwiseKernel
              (c32 ^ 2) c32 (300 * C32) s r) := by
  rcases
      lemma77CanonicalFirstPassageEndpointPMF_pointwiseKernel_log_21_div_20
      with ⟨C32, c32, hC32, hc32, hpoint⟩
  refine ⟨C32, c32, hC32, hc32, ?_⟩
  intro start s r
  rw [lemma77CanonicalFirstPassageHorizontalPMF_apply_eq_tsum_overshoot]
  calc
    (∑' u : ℕ,
        lemma77CanonicalFirstPassageEndpointPMF start s
          (r, (s : ℤ) + 1 + (u : ℤ))) ≤
        ∑' u : ℕ,
          ENNReal.ofReal
            (lemma77PointwiseEndpointKernel
              (c32 ^ 2) c32 (15 * C32) (Real.log (21 / 20 : ℝ))
              s r ((u + 1 : ℕ) : ℤ)) := by
      apply ENNReal.tsum_le_tsum
      intro u
      have hell : (s : ℤ) < (s : ℤ) + 1 + (u : ℤ) := by omega
      have hover :
          relativeVerticalOvershoot s ((s : ℤ) + 1 + (u : ℤ)) =
            ((u + 1 : ℕ) : ℤ) := by
        unfold relativeVerticalOvershoot
        omega
      simpa [hover] using
        hpoint start s r ((s : ℤ) + 1 + (u : ℤ)) hell
    _ = ENNReal.ofReal
        (∑' u : ℕ,
          lemma77PointwiseEndpointKernel
            (c32 ^ 2) c32 (15 * C32) (Real.log (21 / 20 : ℝ))
            s r ((u + 1 : ℕ) : ℤ)) := by
      symm
      apply ENNReal.ofReal_tsum_of_nonneg
      · intro u
        unfold lemma77PointwiseEndpointKernel
        positivity
      · unfold lemma77PointwiseEndpointKernel
        simp only [Int.cast_natCast]
        exact lemma77_summable_exp_neg_log_21_div_20_positiveOvershoot.mul_left _
    _ = ENNReal.ofReal
        (lemma77HorizontalPointwiseKernel
          (c32 ^ 2) c32 (300 * C32) s r) := by
      rw [lemma77_tsum_pointwiseEndpointKernel_positiveOvershoot]

/-- Safe real projection of the native canonical horizontal marginal bound. -/
theorem lemma77CanonicalFirstPassageHorizontalPMF_pointwiseKernel_toReal :
    ∃ C32 c32 : ℝ, 0 ≤ C32 ∧ 0 < c32 ∧
      ∀ (start : TaoSection7RenewalPoint) (s r : ℕ),
        (lemma77CanonicalFirstPassageHorizontalPMF start s r).toReal ≤
          lemma77HorizontalPointwiseKernel
            (c32 ^ 2) c32 (300 * C32) s r := by
  rcases lemma77CanonicalFirstPassageHorizontalPMF_pointwiseKernel with
    ⟨C32, c32, hC32, hc32, hnative⟩
  refine ⟨C32, c32, hC32, hc32, ?_⟩
  intro start s r
  have hkernel_nonneg :
      0 ≤ lemma77HorizontalPointwiseKernel
        (c32 ^ 2) c32 (300 * C32) s r := by
    unfold lemma77HorizontalPointwiseKernel
    positivity
  calc
    (lemma77CanonicalFirstPassageHorizontalPMF start s r).toReal ≤
        (ENNReal.ofReal
          (lemma77HorizontalPointwiseKernel
            (c32 ^ 2) c32 (300 * C32) s r)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hnative start s r)
    _ = lemma77HorizontalPointwiseKernel
        (c32 ^ 2) c32 (300 * C32) s r :=
      ENNReal.toReal_ofReal hkernel_nonneg

end TaoSection7Lemma77

end

end Tao
end Erdos1135
