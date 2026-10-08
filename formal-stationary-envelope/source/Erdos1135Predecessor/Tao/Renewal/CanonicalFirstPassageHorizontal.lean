/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageTerminal
import Erdos1135Predecessor.Tao.Renewal.Lemma77PascalGaussian
import Erdos1135Predecessor.Tao.Renewal.Lemma77TerminalHoldMoment

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Lemma77

noncomputable def lemma77CanonicalFirstPassageHorizontalPMF
    (start : TaoSection7RenewalPoint) (s : ℕ) : PMF ℕ :=
  (lemma77CanonicalFirstPassageEndpointPMF start s).map Prod.fst

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

theorem lemma77CanonicalFirstPassageHorizontalPMF_apply_eq_tsum_int
    (start : TaoSection7RenewalPoint) (s r : ℕ) :
    lemma77CanonicalFirstPassageHorizontalPMF start s r =
      ∑' ell : ℤ,
        lemma77CanonicalFirstPassageEndpointPMF start s (r, ell) := by
  rw [lemma77CanonicalFirstPassageHorizontalPMF,
    pmf_map_apply_eq_tsum_fiber]
  simpa using ((lemma77HorizontalFiberEquiv r).tsum_eq
    (fun x => lemma77CanonicalFirstPassageEndpointPMF start s x.1)).symm

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

def lemma77HorizontalPointwiseKernel
    (A B C : ℝ) (s r : ℕ) : ℝ :=
  C * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) *
    (Real.exp
        (-A * ((lemma77CenteredHorizontalDisplacement s r) ^ 2 /
          (1 + (s : ℝ)))) +
      Real.exp (-B * |lemma77CenteredHorizontalDisplacement s r|))

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

end TaoSection7Lemma77

end

end Tao

end Erdos1135Predecessor
