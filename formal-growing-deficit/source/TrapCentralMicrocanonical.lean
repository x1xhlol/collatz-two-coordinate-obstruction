import TrapCentralBinomial
import TrapExactExponentMass
import TrapMicrocanonicalMassFloor

/-! The explicit central-exponent conditioning event has superpolynomial Fourier decay. -/

set_option autoImplicit false

namespace Erdos1135.Tao

theorem unitSourceExponentMass_central_lower (k : ℕ) (hk : 1 ≤ k) :
    1 / (4 * (k : ℝ)) ≤ unitSourceExponentMass k (2 * k) := by
  rw [unitSourceExponentMass_central_eq_choose k hk]
  exact trap_central_geometric_mass_lower k hk

theorem unitSourceExponentMass_central_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < unitSourceExponentMass k (2 * k) :=
  lt_of_lt_of_le (by positivity) (unitSourceExponentMass_central_lower k hk)

theorem unitSourceExponentMass_central_mass_floor (k : ℕ) (hk : 4 ≤ k) :
    1 / (k : ℝ) ^ 2 ≤ unitSourceExponentMass k (2 * k) := by
  have hkreal : 4 ≤ (k : ℝ) := by exact_mod_cast hk
  calc
    1 / (k : ℝ) ^ 2 ≤ 1 / (4 * (k : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    _ ≤ unitSourceExponentMass k (2 * k) :=
      unitSourceExponentMass_central_lower k (by omega)

theorem trap_unconditional_centralConditionedAffinePMF_polynomial_deficit
    (A : ℕ) (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k d : ℕ) (hk : 4 ≤ k),
      (d : ℝ) ≤ (k : ℝ) ^ beta →
        ∀ xi : ZMod (3 ^ (k + d)), zmodThreePrimitive (k + d) xi →
          ∀ z : ZMod (3 ^ (k + d)),
            ‖ZMod.dft (pmfComplexMass
              (unitSourceConditionedAffinePMF (k + d) k (2 * k) z
                (unitSourceExponentMass_central_pos k (by omega)))) xi‖ ≤
                  C / (k : ℝ) ^ A := by
  obtain ⟨C, hC, hbound⟩ :=
    trap_unconditional_conditionedAffinePMF_polynomial_deficit_mass_floor
      A 2 beta hbeta0 hbeta1
  refine ⟨C, hC, ?_⟩
  intro k d hk hd xi hxi z
  exact hbound k d (by omega) hd xi hxi z (2 * k)
    (unitSourceExponentMass_central_pos k (by omega))
    (unitSourceExponentMass_central_mass_floor k hk)

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_unconditional_centralConditionedAffinePMF_polynomial_deficit
