import Erdos1135.Tao.Syracuse.Prop19GeomTail
import Erdos1135.Tao.Syracuse.Prop19Truncation

/-!
# Source-faithful Proposition 1.9

This module combines the scale-free truncation kernel with the ideal Geom(2)
tail.  It converts the real-exponential tail to Tao's base-two convention,
handles `n = 0` exactly, and exports the source quantifier order in which the
output exponent depends only on the input scale gap.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- Fixed-constant canonical form of Proposition 1.9. -/
def TaoProp19CanonicalApproximationWithConstants
    (C0 C1 c0 c1 : ℝ) : Prop :=
  ∀ n M : ℕ,
    ((2 : ℝ) + c0) * (n : ℝ) ≤ (M : ℝ) →
      ∀ μ : PMF TaoOddNat,
        taoTV
            (taoProp19SourceResidueLaw μ M)
            (taoCanonicalUniformOddResiduePMF M) ≤
              C0 * ((2 : ℝ) ^ (-(M : ℝ))) →
          taoProp19ValuationTV μ n ≤
            C1 * ((2 : ℝ) ^ (-(c1 * (n : ℝ))))

/-- Public fixed-constant canonical Proposition 1.9 contract. -/
def TaoProp19ValuationApproximationWithConstants
    (C0 C1 c0 c1 : ℝ) : Prop :=
  0 ≤ C0 ∧ 0 ≤ C1 ∧ 0 < c0 ∧ 0 < c1 ∧
    TaoProp19CanonicalApproximationWithConstants C0 C1 c0 c1

/-- Source-faithful quantifier order: `c1` depends only on `c0`, while the
output implied constant may also depend on the input implied constant. -/
def TaoProp19ValuationApproximationStatement : Prop :=
  ∀ c0 : ℝ, 0 < c0 →
    ∃ c1 : ℝ, 0 < c1 ∧
      ∀ C0 : ℝ, 0 ≤ C0 →
        ∃ C1 : ℝ, 0 ≤ C1 ∧
          TaoProp19ValuationApproximationWithConstants C0 C1 c0 c1

/-- A negative real exponential is bounded by the same base-two power. -/
theorem exp_neg_le_two_rpow_neg (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x) ≤ (2 : ℝ) ^ (-x) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := 2) (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hnonneg : 0 ≤ x * (1 - Real.log 2) :=
    mul_nonneg hx (sub_nonneg.mpr hlog)
  nlinarith

theorem taoProp19DecayExponent_le_two_add {c0 : ℝ} (hc0 : 0 < c0) :
    taoProp19DecayExponent c0 ≤ 2 + c0 := by
  have ht := taoProp19TailParameter_le_quarter c0
  have hmul := mul_le_mul_of_nonneg_left ht hc0.le
  unfold taoProp19DecayExponent
  nlinarith

/-- Explicit constants supplied by the checked kernel and ideal-tail route. -/
theorem taoProp19CanonicalApproximationWithConstants_checked
    {c0 C0 : ℝ} (hc0 : 0 < c0) (hC0 : 0 ≤ C0) :
    TaoProp19CanonicalApproximationWithConstants
      C0 (C0 + 2) c0 (taoProp19DecayExponent c0) := by
  intro n M hscale μ hsource
  by_cases hn : n = 0
  · subst n
    rw [taoProp19ValuationTV_zero]
    positivity
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let c1 := taoProp19DecayExponent c0
    let target := (2 : ℝ) ^ (-(c1 * (n : ℝ)))
    have hc1_nonneg : 0 ≤ c1 := (taoProp19DecayExponent_pos hc0).le
    have hx_nonneg : 0 ≤ c1 * (n : ℝ) :=
      mul_nonneg hc1_nonneg (Nat.cast_nonneg n)
    have hoverflowExp :=
      truncatedValuationTupleGeom2PMF_none_le_exp hc0 hnpos hscale
    have hoverflow :
        (truncatedValuationTupleGeom2PMF n M none).toReal ≤ target := by
      exact hoverflowExp.trans
        (exp_neg_le_two_rpow_neg (c1 * (n : ℝ)) hx_nonneg)
    have hc1n_le_M : c1 * (n : ℝ) ≤ (M : ℝ) := by
      have hrate := mul_le_mul_of_nonneg_right
        (taoProp19DecayExponent_le_two_add hc0) (Nat.cast_nonneg n)
      exact hrate.trans hscale
    have hpow : (2 : ℝ) ^ (-(M : ℝ)) ≤ target := by
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (neg_le_neg hc1n_le_M)
    have hsource' :
        taoTV
            (taoProp19SourceResidueLaw μ M)
            (taoCanonicalUniformOddResiduePMF M) ≤ C0 * target :=
      hsource.trans (mul_le_mul_of_nonneg_left hpow hC0)
    calc
      taoProp19ValuationTV μ n ≤
          taoTV
              (taoProp19SourceResidueLaw μ M)
              (taoCanonicalUniformOddResiduePMF M) +
            2 * (truncatedValuationTupleGeom2PMF n M none).toReal :=
        taoProp19ValuationTV_le_sourceTV_add_two_overflow μ n M
      _ ≤ C0 * target + 2 * target :=
        add_le_add hsource'
          (mul_le_mul_of_nonneg_left hoverflow (by norm_num))
      _ = (C0 + 2) * target := by ring

/-- Explicit constants satisfy the public fixed-constant contract. -/
theorem taoProp19ValuationApproximationWithConstants_checked
    {c0 C0 : ℝ} (hc0 : 0 < c0) (hC0 : 0 ≤ C0) :
    TaoProp19ValuationApproximationWithConstants
      C0 (C0 + 2) c0 (taoProp19DecayExponent c0) := by
  exact ⟨hC0, by positivity, hc0, taoProp19DecayExponent_pos hc0,
    taoProp19CanonicalApproximationWithConstants_checked hc0 hC0⟩

/-- Checked source-faithful Proposition 1.9 statement. -/
theorem taoProp19ValuationApproximationStatement_checked :
    TaoProp19ValuationApproximationStatement := by
  intro c0 hc0
  refine ⟨taoProp19DecayExponent c0, taoProp19DecayExponent_pos hc0, ?_⟩
  intro C0 hC0
  refine ⟨C0 + 2, by positivity, ?_⟩
  exact taoProp19ValuationApproximationWithConstants_checked hc0 hC0

end

end Tao
end Erdos1135
