import TrapNativeEnvelopeRecursion
import TrapDeficitBootstrap

/-!
The scalar conductor bootstrap instantiated with the actual native source
expectation. Its one analytic input is qualitative uniform decay of that
expectation on macroscopic blocks; the input is not proved in this file.
-/

set_option autoImplicit false

namespace Erdos1135.Tao

/-- Uniform qualitative decay of the native raw Pascal `FThree` product. -/
def TrapNativeEnvelopeQualitative (theta : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ,
    ∀ n J, N ≤ n → 1 ≤ n → 2 * J ≤ n →
      theta * (n : ℝ) ≤ (2 * J : ℕ) →
      ∀ xi : ZMod (3 ^ n), zmodThreePrimitive n xi →
        taoSection7PairSourceEnvelope n xi J 1 0 ≤ epsilon

theorem trap_native_envelope_deficit_all_powers
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hqual : TrapNativeEnvelopeQualitative theta) :
    ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n J, 1 ≤ n → 2 * J ≤ n →
        ∀ xi : ZMod (3 ^ n), zmodThreePrimitive n xi →
          taoSection7PairSourceEnvelope n xi J 1 0 ≤
            C * ((n - 2 * J + 1 : ℕ) / (n : ℝ)) ^ A := by
  have hQ := CollatzResearch.trap_deficit_bootstrap trapSourceEnvelopeQ theta htheta0 htheta1
    (fun n J _ _ => ⟨trap_sourceEnvelopeQ_nonneg n J, trap_sourceEnvelopeQ_le_one n J⟩)
    (fun n J u _ _ huJ hu => trap_sourceEnvelopeQ_recursion n J u huJ hu)
    (by
      intro epsilon hepsilon
      obtain ⟨N, hN⟩ := hqual epsilon hepsilon
      refine ⟨N, ?_⟩
      intro n J hNn hn hJ htheta
      apply ciSup_le
      intro xi
      split_ifs with hxi
      · exact hN n J hNn hn hJ htheta xi hxi
      · exact hepsilon.le)
  intro A
  obtain ⟨C, hC, hbound⟩ := hQ A
  exact ⟨C, hC, fun n J hn hJ xi hxi =>
    (trap_sourceEnvelope_le_Q n J xi hxi).trans (hbound n J hn hJ)⟩

theorem trap_native_SChi_all_powers
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hqual : TrapNativeEnvelopeQualitative theta) :
    ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n, 1 ≤ n → ∀ xi : ZMod (3 ^ n), zmodThreePrimitive n xi →
        ‖taoSection7SChi n xi‖ ≤ C / (n : ℝ) ^ A := by
  intro A
  obtain ⟨C, hC, hbound⟩ :=
    trap_native_envelope_deficit_all_powers theta htheta0 htheta1 hqual A
  refine ⟨C * 2 ^ A, by positivity, ?_⟩
  intro n hn xi hxi
  have hJ : 2 * (n / 2) ≤ n := by omega
  have hD : (n - 2 * (n / 2) + 1 : ℕ) ≤ 2 := by omega
  have hDreal : ((n - 2 * (n / 2) + 1 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hD
  have hschi : ‖taoSection7SChi n xi‖ ≤ taoSection7PairSourceEnvelope n xi (n / 2) 1 0 := by
    simpa only [taoSection7PairSourceEnvelope, taoSection7FactorProduct] using
      norm_taoSection7SChi_le_pascalSource_expectation n xi
  calc
    ‖taoSection7SChi n xi‖ ≤ C * ((n - 2 * (n / 2) + 1 : ℕ) / (n : ℝ)) ^ A :=
      hschi.trans (hbound n (n / 2) hn hJ xi hxi)
    _ ≤ C * (2 / (n : ℝ)) ^ A := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div_of_nonneg_right hDreal (by positivity)
    _ = (C * 2 ^ A) / (n : ℝ) ^ A := by rw [div_pow, mul_div_assoc]

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_native_envelope_deficit_all_powers
#print axioms Erdos1135.Tao.trap_native_SChi_all_powers
