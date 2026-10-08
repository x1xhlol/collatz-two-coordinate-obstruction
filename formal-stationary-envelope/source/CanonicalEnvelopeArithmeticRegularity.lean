import CanonicalEnvelopePeriodicExtension

set_option autoImplicit false

open Filter
open scoped Topology ENNReal
open CollatzCylinderPacking.Arithmetic

namespace CollatzCanonical.IntegerStationaryEnvelope

theorem canonicalIntegerStep_natCast_tendsto_trace {n : ℕ} (hn : 0 < n) :
    Tendsto (fun k => canonicalIntegerStep k (n : ℤ_[3])) atTop
      (𝓝 (actualIntegerTrace n)) := by
  have h := tendsto_atTop_iSup (padicIntegerStep_monotone actualIntegerTrace (n : ℤ_[3]))
  change Tendsto (fun k => canonicalIntegerStep k (n : ℤ_[3])) atTop
    (𝓝 (canonicalIntegerEnvelope (n : ℤ_[3]))) at h
  rwa [canonicalIntegerEnvelope_natCast_eq hn] at h

theorem canonicalIntegerStep_natCast_toReal_tendsto_trace {n : ℕ} (hn : 0 < n) :
    Tendsto (fun k => (canonicalIntegerStep k (n : ℤ_[3])).toReal) atTop
      (𝓝 (actualDensityValue actualFirstHitDensity n)) := by
  have h := (ENNReal.tendsto_toReal (ne_of_lt (actualIntegerTrace_lt_top n))).comp
    (canonicalIntegerStep_natCast_tendsto_trace hn)
  simpa only [Function.comp_def, actualIntegerTrace,
    ENNReal.toReal_ofReal (actualDensityValue_nonneg_of_pos hn)] using h

theorem actual_trace_residue_lower {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∀ m : ℕ, 0 < m → m % 3 ^ k = n % 3 ^ k →
      actualDensityValue actualFirstHitDensity n - ε <
        actualDensityValue actualFirstHitDensity m := by
  obtain ⟨k, hk⟩ := ((canonicalIntegerStep_natCast_toReal_tendsto_trace hn).eventually
    (lt_mem_nhds (show actualDensityValue actualFirstHitDensity n - ε <
      actualDensityValue actualFirstHitDensity n by linarith))).exists
  refine ⟨k, fun m hm hmod => ?_⟩
  have he : PadicInt.toZModPow k (m : ℤ_[3]) = PadicInt.toZModPow k (n : ℤ_[3]) := by
    simp only [map_natCast]
    have h := congrArg (fun q : ℕ => (q : ZMod (3 ^ k))) hmod
    simpa only [ZMod.natCast_mod] using h
  have hs : canonicalIntegerStep k (m : ℤ_[3]) = canonicalIntegerStep k (n : ℤ_[3]) :=
    padicIntegerStep_eq_of_projection_eq actualIntegerTrace k he
  have hb := ENNReal.toReal_mono (ne_of_lt (actualIntegerTrace_lt_top m))
    (padicIntegerStep_natCast_le actualIntegerTrace k m hm)
  change (canonicalIntegerStep k (m : ℤ_[3])).toReal ≤ (actualIntegerTrace m).toReal at hb
  rw [hs, actualIntegerTrace, ENNReal.toReal_ofReal (actualDensityValue_nonneg_of_pos hm)] at hb
  exact hk.trans_le hb

#print axioms canonicalIntegerStep_natCast_tendsto_trace
#print axioms actual_trace_residue_lower

end CollatzCanonical.IntegerStationaryEnvelope
