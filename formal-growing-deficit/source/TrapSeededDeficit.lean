import TrapNativeEnvelopeBootstrap
import UnitSourceAffinePMF

/-!
Conditional deficit decay for the literal affine image of the exact geometric
source. The qualitative input is the native raw Pascal envelope; terminal
phases and all finite-modulus seeds are retained in the conclusion.
-/

set_option autoImplicit false

namespace Erdos1135.Tao

theorem trap_unitSourcePairExpectation_deficit_all_powers
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hqual : TrapNativeEnvelopeQualitative theta) :
    ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n k, 1 ≤ n → k ≤ n →
        ∀ xi : ZMod (3 ^ n), zmodThreePrimitive n xi →
          ∀ τ : UnitSourceTerminalPhase,
            ‖unitSourcePairExpectation n xi τ k 1 0‖ ≤
              C * ((n - k + 2 : ℕ) / (n : ℝ)) ^ A := by
  intro A
  obtain ⟨C, hC, hbound⟩ :=
    trap_native_envelope_deficit_all_powers theta htheta0 htheta1 hqual A
  refine ⟨C, hC, ?_⟩
  intro n k hn hk xi hxi τ
  have hJ : 2 * (k / 2) ≤ n := by omega
  have hD : n - 2 * (k / 2) + 1 ≤ n - k + 2 := by omega
  have hDreal : ((n - 2 * (k / 2) + 1 : ℕ) : ℝ) ≤ (n - k + 2 : ℕ) := by
    exact_mod_cast hD
  calc
    ‖unitSourcePairExpectation n xi τ k 1 0‖ ≤
        taoSection7PairSourceEnvelope n xi (k / 2) 1 0 :=
      norm_unitSourcePairExpectation_le_sourceEnvelope n xi τ k 1 0
    _ ≤ C * ((n - 2 * (k / 2) + 1 : ℕ) / (n : ℝ)) ^ A :=
      hbound n (k / 2) hn hJ xi hxi
    _ ≤ C * ((n - k + 2 : ℕ) / (n : ℝ)) ^ A := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div_of_nonneg_right hDreal (by positivity)

theorem trap_seededAffinePMF_deficit_all_powers
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hqual : TrapNativeEnvelopeQualitative theta) :
    ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n k, 1 ≤ n → k ≤ n →
        ∀ xi : ZMod (3 ^ n), zmodThreePrimitive n xi →
          ∀ z : ZMod (3 ^ n),
            ‖ZMod.dft (pmfComplexMass (unitSourceAffinePMF n k z)) xi‖ ≤
              C * ((n - k + 2 : ℕ) / (n : ℝ)) ^ A := by
  intro A
  obtain ⟨C, hC, hbound⟩ :=
    trap_unitSourcePairExpectation_deficit_all_powers theta htheta0 htheta1 hqual A
  refine ⟨C, hC, ?_⟩
  intro n k hn hk xi hxi z
  rw [unitSourceAffinePMF_dft_eq_twistedPairExpectation]
  exact hbound n k hn hk xi hxi (unitSourceSeedPhase n k xi z)

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_unitSourcePairExpectation_deficit_all_powers
#print axioms Erdos1135.Tao.trap_seededAffinePMF_deficit_all_powers
