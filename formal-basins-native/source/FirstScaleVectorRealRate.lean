import BanachPassageTransport
import RealCanonicalClockRates
import LogarithmicRateComparison

open Filter
open scoped Topology

namespace CollatzCanonical.LabelLaw
open Erdos1135.Tao CollatzClockAudit

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem first_scale_eventual_vector_real_rate (F : ℕ → V)
    (hF : ∀ q, ‖F q‖ ≤ 1) (hpass : EventuallyPassageInvariant F) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ᶠ x : ℝ in atTop,
        (∀ branch : TaoSection5SourceBranch, 0 < logFinsetMass
          (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch))) ∧
        ∀ (hmass₁ : 0 < logFinsetMass
            (oddLogWindow (realClockSourceLo x .alpha) (realClockSourceHi x .alpha)))
          (hmass₂ : 0 < logFinsetMass
            (oddLogWindow (realClockSourceLo x .alphaSq) (realClockSourceHi x .alphaSq))),
          ‖pmfMeanV
              (oddLogWindowPMF (realClockSourceLo x .alpha) (realClockSourceHi x .alpha) hmass₁)
              (fun q => F q.1) -
            pmfMeanV
              (oddLogWindowPMF (realClockSourceLo x .alphaSq) (realClockSourceHi x .alphaSq) hmass₂)
              (fun q => F q.1)‖ ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨errNoHit, errTV, C, c, hC, hc, hrates, hTV⟩ :=
    taoProp111RealFirstPassageStabilizationRate_checked
  refine ⟨5 * C, min c 1, by positivity, lt_min hc zero_lt_one, min_le_right _ _, ?_⟩
  filter_upwards [eventually_real_local_clock_and_landing_rates, hrates, hpass,
    eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)]
    with x hmass hrates hpass hx hlog
  refine ⟨hmass.1, ?_⟩
  intro hmass₁ hmass₂
  have he := native_real_windows_vector_comparison F hF x hx hpass
    (realClockSourceLo x .alpha) (realClockSourceHi x .alpha)
    (realClockSourceLo x .alphaSq) (realClockSourceHi x .alphaSq) hmass₁ hmass₂
  have hpair : TaoProp111RealWindowPair x
      (realClockSourceLo x .alpha) (realClockSourceHi x .alpha)
      (realClockSourceLo x .alphaSq) (realClockSourceHi x .alphaSq) := ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨hno₁, hno₂, htv⟩ := hTV x _ _ _ _ hx hpair hmass₁ hmass₂
  have hlogle : Real.log x ≤ x := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < x)
    linarith
  have hpoly : x ^ (-c) ≤ (Real.log x) ^ (-c) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hlogle (by linarith)
  have hweak : (Real.log x) ^ (-c) ≤ (Real.log x) ^ (-min c 1) :=
    Real.rpow_le_rpow_of_exponent_le hlog (neg_le_neg (min_le_left c 1))
  have hterm := mul_le_mul_of_nonneg_left (hpoly.trans hweak) hC
  have htvTerm := mul_le_mul_of_nonneg_left hweak hC
  have hnoRate := hrates.2.2.1
  have htvRate := hrates.2.2.2
  nlinarith

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.first_scale_eventual_vector_real_rate
