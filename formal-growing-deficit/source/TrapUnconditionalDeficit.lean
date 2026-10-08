import TrapNativeQualitativeDecay
import TrapSeededDeficit

/-! All-powers conductor-deficit bounds with the qualitative input discharged. -/

set_option autoImplicit false

namespace Erdos1135.Tao

theorem trap_entropy_threshold_five_sixths :
    Real.log 3 < 2 * (5 / 6 : ℝ) * Real.log 2 := by
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 3 ^ 3)
    (by norm_num : (3 : ℝ) ^ 3 < 2 ^ 5)
  rw [Real.log_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

theorem trap_unconditional_native_envelope_deficit_all_powers :
    ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n J, 1 ≤ n → 2 * J ≤ n →
        ∀ xi : ZMod (3 ^ n), zmodThreePrimitive n xi →
          taoSection7PairSourceEnvelope n xi J 1 0 ≤
            C * ((n - 2 * J + 1 : ℕ) / (n : ℝ)) ^ A :=
  trap_native_envelope_deficit_all_powers (5 / 6) (by norm_num) (by norm_num)
    (trap_native_envelope_qualitative (5 / 6) trap_entropy_threshold_five_sixths)

theorem trap_unconditional_native_SChi_all_powers :
    ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n, 1 ≤ n → ∀ xi : ZMod (3 ^ n), zmodThreePrimitive n xi →
        ‖taoSection7SChi n xi‖ ≤ C / (n : ℝ) ^ A :=
  trap_native_SChi_all_powers (5 / 6) (by norm_num) (by norm_num)
    (trap_native_envelope_qualitative (5 / 6) trap_entropy_threshold_five_sixths)

theorem trap_unconditional_unitSourcePairExpectation_deficit_all_powers :
    ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n k, 1 ≤ n → k ≤ n →
        ∀ xi : ZMod (3 ^ n), zmodThreePrimitive n xi →
          ∀ tau : UnitSourceTerminalPhase,
            ‖unitSourcePairExpectation n xi tau k 1 0‖ ≤
              C * ((n - k + 2 : ℕ) / (n : ℝ)) ^ A :=
  trap_unitSourcePairExpectation_deficit_all_powers (5 / 6) (by norm_num) (by norm_num)
    (trap_native_envelope_qualitative (5 / 6) trap_entropy_threshold_five_sixths)

theorem trap_unconditional_seededAffinePMF_deficit_all_powers :
    ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n k, 1 ≤ n → k ≤ n →
        ∀ xi : ZMod (3 ^ n), zmodThreePrimitive n xi →
          ∀ z : ZMod (3 ^ n),
            ‖ZMod.dft (pmfComplexMass (unitSourceAffinePMF n k z)) xi‖ ≤
              C * ((n - k + 2 : ℕ) / (n : ℝ)) ^ A :=
  trap_seededAffinePMF_deficit_all_powers (5 / 6) (by norm_num) (by norm_num)
    (trap_native_envelope_qualitative (5 / 6) trap_entropy_threshold_five_sixths)

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_unconditional_native_envelope_deficit_all_powers
#print axioms Erdos1135.Tao.trap_unconditional_native_SChi_all_powers
#print axioms Erdos1135.Tao.trap_unconditional_unitSourcePairExpectation_deficit_all_powers
#print axioms Erdos1135.Tao.trap_unconditional_seededAffinePMF_deficit_all_powers
