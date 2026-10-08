import TrapNativeShortLaplace
import TrapLaplaceEventBounds
import TrapNativeEnvelopeBootstrap

/-! The fixed-threshold probability limit needed by the native Fourier bootstrap. -/

set_option autoImplicit false

open CollatzResearch

namespace Erdos1135.Tao

noncomputable def trapNativeFewWhiteProbability
    (n J T : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) : ℝ :=
  trapPMFEvent (taoSection7HoldListPMF (n / 2 + 1))
    (fun hs => trapHoldListWhiteCount
      (taoSection7SourceWhiteRenewal (taoSection7SourceWhiteWCutoff n xi epsilon J)) hs ≤ T)

def TrapNativeFewWhiteApproximation (epsilon theta : ℝ) : Prop :=
  ∀ T R : ℕ, ∀ delta : ℝ, 0 < delta → ∃ N : ℕ,
    ∀ n J, N ≤ n → 1 ≤ n → 2 * J ≤ n →
      theta * (n : ℝ) ≤ (2 * J : ℕ) →
      ∀ xi : ZMod (3 ^ n), zmodThreePrimitive n xi →
        trapNativeFewWhiteProbability n J T xi epsilon ≤
          delta + Real.exp ((T : ℝ) + epsilon - epsilon * (R : ℝ))

theorem trap_native_qualitative_of_few_white_approximation
    (epsilon theta : ℝ) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (happrox : TrapNativeFewWhiteApproximation epsilon theta) :
    TrapNativeEnvelopeQualitative theta := by
  intro delta hdelta
  have hthird : 0 < delta / 3 := by positivity
  have hcube : 0 < epsilon ^ 3 := pow_pos hepsilon0 3
  obtain ⟨T, hT⟩ := exists_nat_gt (-Real.log (delta / 3) / epsilon ^ 3)
  have hTexp : Real.exp (-(epsilon ^ 3) * (T : ℝ)) < delta / 3 := by
    rw [← Real.exp_log hthird]
    apply Real.exp_lt_exp.mpr
    have h := (div_lt_iff₀ hcube).mp hT
    nlinarith
  obtain ⟨R, hR⟩ := exists_nat_gt
    (((T : ℝ) + epsilon - Real.log (delta / 3)) / epsilon)
  have hRexp : Real.exp ((T : ℝ) + epsilon - epsilon * (R : ℝ)) < delta / 3 := by
    rw [← Real.exp_log hthird]
    apply Real.exp_lt_exp.mpr
    have h := (div_lt_iff₀ hepsilon0).mp hR
    nlinarith
  obtain ⟨N, hN⟩ := happrox T R (delta / 3) hthird
  refine ⟨N, ?_⟩
  intro n J hNn hn hJ htheta xi hxi
  have hprob := hN n J hNn hn hJ htheta xi hxi
  have henvelope := trap_sourceEnvelope_le_short_holdList_laplace
    n J (n / 2 + 1) xi epsilon hepsilon0.le hepsilon1 (by omega)
  have hlaplace := trap_pmf_laplace_le_low_count_probability
    (taoSection7HoldListPMF (n / 2 + 1))
    (trapHoldListWhiteCount
      (taoSection7SourceWhiteRenewal (taoSection7SourceWhiteWCutoff n xi epsilon J)))
    (epsilon ^ 3) hcube.le T
  change _ ≤ trapNativeFewWhiteProbability n J T xi epsilon +
    Real.exp (-(epsilon ^ 3) * (T : ℝ)) at hlaplace
  exact (henvelope.trans hlaplace).trans (by linarith)

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_native_qualitative_of_few_white_approximation
