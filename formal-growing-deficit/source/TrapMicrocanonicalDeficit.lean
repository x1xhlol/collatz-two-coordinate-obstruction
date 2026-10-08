import TrapMicrocanonicalSource
import TrapUnconditionalDeficit

/-! Primitive Fourier decay for the literal source conditioned on its weight. -/

set_option autoImplicit false

namespace Erdos1135.Tao

theorem trap_unconditional_affineTwistedExpectation_deficit_all_powers :
    ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n k, 1 ≤ n → k ≤ n →
        ∀ xi : ZMod (3 ^ n), zmodThreePrimitive n xi →
          ∀ z : ZMod (3 ^ n), ∀ tau : UnitSourceTerminalPhase,
            ‖unitSourceAffineTwistedExpectation n k xi z tau‖ ≤
              C * ((n - k + 2 : ℕ) / (n : ℝ)) ^ A := by
  intro A
  obtain ⟨C, hC, hbound⟩ :=
    trap_unconditional_unitSourcePairExpectation_deficit_all_powers A
  refine ⟨C, hC, ?_⟩
  intro n k hn hk xi hxi z tau
  rw [unitSourceAffineTwistedExpectation_eq_pairExpectation]
  exact hbound n k hn hk xi hxi _

theorem trap_unconditional_sliceFourierMass_deficit_all_powers :
    ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n k, 1 ≤ n → k ≤ n →
        ∀ xi : ZMod (3 ^ n), zmodThreePrimitive n xi →
          ∀ z : ZMod (3 ^ n), ∀ s : ℕ,
            ‖unitSourceSliceFourierMass n k xi z s‖ ≤
              C * ((n - k + 2 : ℕ) / (n : ℝ)) ^ A := by
  intro A
  obtain ⟨C, hC, hbound⟩ :=
    trap_unconditional_affineTwistedExpectation_deficit_all_powers A
  refine ⟨C, hC, ?_⟩
  intro n k hn hk xi hxi z s
  rw [unitSourceSliceFourierMass_eq_two_phases, norm_div]
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [htwo]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have h := norm_add_le
    (unitSourceAffineTwistedExpectation n k xi z unitSourceConstantPhase)
    (unitSourceAffineTwistedExpectation n k xi z (unitSourceSliceSign s))
  have hp := hbound n k hn hk xi hxi z unitSourceConstantPhase
  have hm := hbound n k hn hk xi hxi z (unitSourceSliceSign s)
  linarith

theorem trap_unconditional_conditionedAffinePMF_deficit_all_powers :
    ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n k, 1 ≤ n → k ≤ n →
        ∀ xi : ZMod (3 ^ n), zmodThreePrimitive n xi →
          ∀ z : ZMod (3 ^ n), ∀ s : ℕ,
            ∀ hs : 0 < unitSourceExponentMass k s,
              ‖ZMod.dft (pmfComplexMass
                (unitSourceConditionedAffinePMF n k s z hs)) xi‖ ≤
                C * ((n - k + 2 : ℕ) / (n : ℝ)) ^ A / unitSourceExponentMass k s := by
  intro A
  obtain ⟨C, hC, hbound⟩ := trap_unconditional_sliceFourierMass_deficit_all_powers A
  refine ⟨C, hC, ?_⟩
  intro n k hn hk xi hxi z s hs
  rw [unitSourceConditionedAffinePMF_dft_eq_normalized, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  exact div_le_div_of_nonneg_right (hbound n k hn hk xi hxi z s) hs.le

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_unconditional_conditionedAffinePMF_deficit_all_powers
