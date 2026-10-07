import FinitePrefixSourceBound
import CountableMassSqueeze

set_option autoImplicit false

open Filter Topology

namespace CollatzCylinderPacking.Arithmetic.InverseDoob

theorem actual_prefix_source_mass_tendsto_one {n : ℕ} (hn : 0 < n)
    (hu : n % 3 ≠ 0) (hnodd : n % 2 = 1) (hnp : Nonperiodic n) (k : ℕ) :
    Tendsto (fun t : ℝ => ∑' p, prefixSourceMass n k t p) atTop (𝓝 1) := by
  have hupper : ∀ᶠ t : ℝ in atTop,
      ∑' p, prefixSourceMass n k t p ≤ fullSourceMass n t :=
    Eventually.of_forall (prefixSourceMass_tsum_le hnodd hnp)
  have hb : Tendsto (fullSourceMass n) atTop
      (𝓝 (∑' p, (finitePrefixPMF n k p).toReal)) := by
    rw [finitePrefixPMF_toReal_tsum]
    exact fullSourceMass_tendsto hn hu
  have h := ActualInverseDoob.tendsto_tsum_of_nonneg_of_mass_upper_bound
    (prefixSourceMass_nonneg n k) (fun p => ENNReal.toReal_nonneg)
    (prefixSourceMass_summable hnodd hnp) (finitePrefixPMF_toReal_summable n k)
    (prefixSourceMass_tendsto hn hu hnp k) hupper hb
  simpa only [finitePrefixPMF_toReal_tsum] using h

/-- Total-variation convergence of the actual weighted source measures on
the countable space of fixed finite inverse prefixes. -/
theorem actual_fixed_prefix_total_variation {n : ℕ} (hn : 0 < n)
    (hu : n % 3 ≠ 0) (hnodd : n % 2 = 1) (hnp : Nonperiodic n) (k : ℕ) :
    Tendsto (fun t : ℝ => ∑' p, |prefixSourceMass n k t p -
      (finitePrefixPMF n k p).toReal|) atTop (𝓝 0) := by
  apply ActualInverseDoob.tendsto_tsum_abs_sub_of_nonneg
    (prefixSourceMass_nonneg n k) (fun p => ENNReal.toReal_nonneg)
    (prefixSourceMass_summable hnodd hnp) (finitePrefixPMF_toReal_summable n k)
    (prefixSourceMass_tendsto hn hu hnp k)
  rw [finitePrefixPMF_toReal_tsum]
  exact actual_prefix_source_mass_tendsto_one hn hu hnodd hnp k

end CollatzCylinderPacking.Arithmetic.InverseDoob
