import TrapConcentrationChoice
import TrapFewWhitePositiveStops
import TrapGoodPathProbabilityReduction
import TrapHoldGoodProbability

/-! Uniform qualitative decay of the actual source envelope above the entropy threshold. -/

set_option autoImplicit false
open Filter CollatzResearch
open scoped Topology

namespace Erdos1135.Tao

theorem trap_native_few_white_approximation
    (parameters : TrapRenewalParameters) (theta : ℝ)
    (htheta : Real.log 3 < 2 * theta * Real.log 2) :
    TrapNativeFewWhiteApproximation parameters.epsilon theta := by
  apply trap_native_few_white_approximation_of_positive_stops
    parameters.epsilon theta parameters.scalar.epsilon_pos.le
  intro T R hR delta hdelta
  have htheta0 : 0 < theta := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    nlinarith
  obtain ⟨Nstops, hNstops⟩ := eventually_native_few_white_le_bad_good_path_add_stops
    parameters R T hR theta htheta trapConcentrationH trapConcentrationV trapConcentrationD
    (fun n => Nat.cast_nonneg _) (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    trap_concentration_H_sublinear trap_concentration_H_sublinear trap_concentration_D_sublinear
  obtain ⟨Nbad, hNbad⟩ := eventually_atTop.mp
    (trap_concentration_failure_tendsto.eventually (gt_mem_nhds hdelta))
  refine ⟨max Nstops Nbad, ?_⟩
  intro n J hn hn1 hJn hthetaJ xi hxi
  have hJ : 0 < J := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hpositive : (0 : ℝ) < ((2 * J : ℕ) : ℝ) :=
      (mul_pos htheta0 hn0).trans_le hthetaJ
    exact Nat.pos_of_ne_zero (by intro hzero; simp [hzero] at hpositive)
  have hD : 0 < trapConcentrationD n := Real.rpow_pos_of_pos
    (by exact_mod_cast (show 0 < n by omega)) _
  have hbad := (trap_holdList_bad_good_probability_le n J (trapConcentrationH n) hJ hJn
    (trapConcentrationV n) (trapConcentrationD n) hD).trans
      (trap_concentration_error_bound n J hn1 hJ hJn)
  have hsmall : trapConcentrationFailure n ≤ delta :=
    (hNbad n ((le_max_right _ _).trans hn)).le
  exact (hNstops n ((le_max_left _ _).trans hn) J hJn hthetaJ xi hxi).trans
    (add_le_add (hbad.trans hsmall) le_rfl)

theorem trap_native_envelope_qualitative
    (theta : ℝ) (htheta : Real.log 3 < 2 * theta * Real.log 2) :
    TrapNativeEnvelopeQualitative theta := by
  obtain ⟨parameters⟩ := nonempty_trapRenewalParameters
  apply trap_native_qualitative_of_few_white_approximation
    parameters.epsilon theta parameters.scalar.epsilon_pos
    (parameters.scalar.epsilon_lt_one_hundredth.le.trans (by norm_num))
  exact trap_native_few_white_approximation parameters theta htheta

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_native_few_white_approximation
#print axioms Erdos1135.Tao.trap_native_envelope_qualitative
