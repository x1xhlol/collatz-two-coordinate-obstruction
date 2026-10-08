import TrapNativeQualitativeReduction

/-! Positive stop thresholds suffice for the uniform few-white approximation. -/

set_option autoImplicit false

namespace Erdos1135.Tao

theorem trap_native_few_white_approximation_of_positive_stops
    (epsilon theta : ℝ) (hepsilon : 0 ≤ epsilon)
    (hpositive : ∀ T R : ℕ, 0 < R → ∀ delta : ℝ, 0 < delta → ∃ N : ℕ,
      ∀ n J, N ≤ n → 1 ≤ n → 2 * J ≤ n →
        theta * (n : ℝ) ≤ (2 * J : ℕ) →
        ∀ xi : ZMod (3 ^ n), zmodThreePrimitive n xi →
          trapNativeFewWhiteProbability n J T xi epsilon ≤
            delta + Real.exp ((T : ℝ) + epsilon - epsilon * (R : ℝ))) :
    TrapNativeFewWhiteApproximation epsilon theta := by
  intro T R delta hdelta
  obtain ⟨N, hN⟩ := hpositive T (R + 1) (Nat.succ_pos R) delta hdelta
  refine ⟨N, ?_⟩
  intro n J hn hn1 hJ htheta xi hxi
  apply (hN n J hn hn1 hJ htheta xi hxi).trans
  apply add_le_add le_rfl
  apply Real.exp_le_exp.mpr
  push_cast
  nlinarith

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_native_few_white_approximation_of_positive_stops
