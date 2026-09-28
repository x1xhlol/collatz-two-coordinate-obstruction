import Erdos1135.ND.Fourier.FixedTotalPGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Fixed-Total Bars Centered Moment-Generating Function

This leaf combines the checked actual-bars PGF with Hoeffding's lemma for one
Bernoulli atom.  The resulting centered MGF is the finite producer consumed by
the one-sided prefix-count tail in T3.
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory

namespace Erdos1135
namespace ND

private theorem ndBernoulli_centered_mgf_le
    (p : ℝ≥0) (hp : p ≤ 1) (lambda : ℝ) :
    Real.exp (-lambda * (p : ℝ)) *
        (1 + (p : ℝ) * (Real.exp lambda - 1)) ≤
      Real.exp (lambda ^ 2 / 8) := by
  let μ : Measure Bool := (PMF.bernoulli p hp).toMeasure
  let X : Bool → ℝ := fun b => cond b 1 0
  have hXmeas : AEMeasurable X μ :=
    (measurable_of_finite X).aemeasurable
  have hXbounds : ∀ᵐ b ∂μ, X b ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [] with b
    cases b <;> simp [X]
  have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
    (μ := μ) (X := X) hXmeas hXbounds
  have hmean : ∫ b, X b ∂μ = (p : ℝ) := by
    simpa [μ, X] using PMF.bernoulli_expectation hp
  have hmgf := hsub.mgf_le lambda
  rw [hmean] at hmgf
  simp only [ProbabilityTheory.mgf, μ, X, PMF.integral_eq_sum,
    PMF.bernoulli_apply] at hmgf
  norm_num [ENNReal.coe_toReal, NNReal.coe_sub hp] at hmgf
  have hexp :
      Real.exp (lambda * (1 - (p : ℝ))) =
        Real.exp (-lambda * (p : ℝ)) * Real.exp lambda := by
    rw [show lambda * (1 - (p : ℝ)) =
      -lambda * (p : ℝ) + lambda by ring, Real.exp_add]
  calc
    Real.exp (-lambda * (p : ℝ)) *
        (1 + (p : ℝ) * (Real.exp lambda - 1)) =
        (1 - (p : ℝ)) * Real.exp (-lambda * (p : ℝ)) +
          (p : ℝ) * Real.exp (lambda * (1 - (p : ℝ))) := by
      rw [hexp]
      ring
    _ ≤ Real.exp (lambda ^ 2 / 8) := by
      convert hmgf using 1 <;> ring

/-- The actual fixed-bars prefix count has the centered MGF bound obtained
from its without-replacement PGF and the one-atom Hoeffding estimate. -/
theorem ndFixedTotalBarsPMF_centered_mgf_le
    (n L q : ℕ) (hn : 0 < n) (hL : n ≤ L)
    (hL1 : 1 < L) (hqL : q ≤ L - 1)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    Tao.pmfExpectation (ndFixedTotalBarsPMF n L hn hL)
      (fun B =>
        Real.exp
          (lambda * ((ndBarsPrefixCount B.1 q : ℝ) -
            (q : ℝ) *
              (((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ))))) ≤
      Real.exp ((q : ℝ) * lambda ^ 2 / 8) := by
  let p : ℝ :=
    (((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ))
  have hden : 0 < ((L - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt hL1)
  have hp0 : 0 ≤ p :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt hden)
  have hnumden : ((n - 1 : ℕ) : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le_sub_right hL 1
  have hp1 : p ≤ 1 := (div_le_one hden).2 hnumden
  let pnn : ℝ≥0 := ⟨p, hp0⟩
  have hpnn : pnn ≤ 1 := by
    exact_mod_cast hp1
  have hpgf := ndFixedTotalBarsPMF_pgf_le
    n L q hn hL hL1 hqL (Real.exp lambda) (Real.one_le_exp hlambda)
  change
    Tao.pmfExpectation (ndFixedTotalBarsPMF n L hn hL)
        (fun B =>
          Real.exp
            (lambda * ((ndBarsPrefixCount B.1 q : ℝ) -
              (q : ℝ) * p))) ≤
      Real.exp ((q : ℝ) * lambda ^ 2 / 8)
  change
    Tao.pmfExpectation (ndFixedTotalBarsPMF n L hn hL)
        (fun B => (Real.exp lambda) ^ ndBarsPrefixCount B.1 q) ≤
      (1 + p * (Real.exp lambda - 1)) ^ q at hpgf
  have hexpect :
      Tao.pmfExpectation (ndFixedTotalBarsPMF n L hn hL)
          (fun B =>
            Real.exp
              (lambda * ((ndBarsPrefixCount B.1 q : ℝ) -
                (q : ℝ) * p))) =
        Real.exp (-lambda * (q : ℝ) * p) *
          Tao.pmfExpectation (ndFixedTotalBarsPMF n L hn hL)
            (fun B => (Real.exp lambda) ^ ndBarsPrefixCount B.1 q) := by
    unfold Tao.pmfExpectation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B _hB
    change
      (ndFixedTotalBarsPMF n L hn hL B).toReal *
          Real.exp
            (lambda * ((ndBarsPrefixCount B.1 q : ℝ) -
              (q : ℝ) * p)) =
        Real.exp (-lambda * (q : ℝ) * p) *
          ((ndFixedTotalBarsPMF n L hn hL B).toReal *
            (Real.exp lambda) ^ ndBarsPrefixCount B.1 q)
    rw [show
        lambda * ((ndBarsPrefixCount B.1 q : ℝ) - (q : ℝ) * p) =
          -lambda * (q : ℝ) * p +
            (ndBarsPrefixCount B.1 q : ℝ) * lambda by ring,
      Real.exp_add, Real.exp_nat_mul]
    ring
  have hcenterFactor :
      Real.exp (-lambda * p) *
          (1 + p * (Real.exp lambda - 1)) ≤
        Real.exp (lambda ^ 2 / 8) := by
    simpa [pnn] using ndBernoulli_centered_mgf_le pnn hpnn lambda
  have hfactor0 : 0 ≤ 1 + p * (Real.exp lambda - 1) := by
    rw [show 1 + p * (Real.exp lambda - 1) =
      (1 - p) + p * Real.exp lambda by ring]
    exact add_nonneg (sub_nonneg.mpr hp1)
      (mul_nonneg hp0 (Real.exp_nonneg _))
  calc
    Tao.pmfExpectation (ndFixedTotalBarsPMF n L hn hL)
        (fun B =>
          Real.exp
            (lambda * ((ndBarsPrefixCount B.1 q : ℝ) -
              (q : ℝ) * p))) =
        Real.exp (-lambda * (q : ℝ) * p) *
          Tao.pmfExpectation (ndFixedTotalBarsPMF n L hn hL)
            (fun B =>
              (Real.exp lambda) ^ ndBarsPrefixCount B.1 q) := hexpect
    _ ≤ Real.exp (-lambda * (q : ℝ) * p) *
          (1 + p * (Real.exp lambda - 1)) ^ q :=
      mul_le_mul_of_nonneg_left hpgf (Real.exp_nonneg _)
    _ = (Real.exp (-lambda * p) *
          (1 + p * (Real.exp lambda - 1))) ^ q := by
      rw [mul_pow]
      congr 1
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ (Real.exp (lambda ^ 2 / 8)) ^ q := by
      exact pow_le_pow_left₀
        (mul_nonneg (Real.exp_nonneg _) hfactor0) hcenterFactor q
    _ = Real.exp ((q : ℝ) * lambda ^ 2 / 8) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

end ND
end Erdos1135
