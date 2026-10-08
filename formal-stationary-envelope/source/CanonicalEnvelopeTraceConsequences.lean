import CanonicalEnvelopeCylinderTrace
import CanonicalEnvelopePeriodicExtension

set_option autoImplicit false

open Filter
open scoped Topology
open CollatzCylinderPacking.Arithmetic CollatzCanonical.CesaroAbel

namespace CollatzCanonical.IntegerStationaryEnvelope

theorem canonicalRho_eventually_native_trace_lower {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      actualDensityValue actualFirstHitDensity n - ε ≤ canonicalRho k n := by
  have h := canonicalIntegerEnvelope_eventually_cylinder_lower n hn hε
  simpa only [canonicalIntegerEnvelope_natCast_eq hn, actualIntegerTrace,
    ENNReal.toReal_ofReal (actualDensityValue_nonneg_of_pos hn)] using h

theorem canonicalRho_cesaro_abs_native_trace {n : ℕ} (hn : 0 < n) :
    Tendsto (cesaroMean (fun k =>
      |canonicalRho k n - actualDensityValue actualFirstHitDensity n|)) atTop (𝓝 0) :=
  canonicalRho_cesaro_abs_trace_of_envelope_eq n hn (canonicalIntegerEnvelope_natCast_eq hn)

theorem canonicalRho_mean_abs_native_trace {n : ℕ} (hn : 0 < n) :
    Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K,
      |canonicalRho k n - actualDensityValue actualFirstHitDensity n|) / (K : ℝ))
      atTop (𝓝 0) :=
  canonicalRho_mean_abs_trace_of_envelope_eq n hn (canonicalIntegerEnvelope_natCast_eq hn)

#print axioms canonicalRho_eventually_native_trace_lower
#print axioms canonicalRho_cesaro_abs_native_trace
#print axioms canonicalRho_mean_abs_native_trace

end CollatzCanonical.IntegerStationaryEnvelope
