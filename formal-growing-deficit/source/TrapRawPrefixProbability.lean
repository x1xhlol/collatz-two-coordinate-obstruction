import TrapPascalPrefixProbability
import TrapHoldSourceSupport

/-! Exact regenerated raw-prefix concentration on the original Hold source. -/

set_option autoImplicit false

namespace Erdos1135.Tao
open CollatzResearch

theorem trap_hold_source_bad_prefix_probability_le
    (J N : ℕ) (hJ : 0 < J) (hJN : J ≤ N) (D : ℝ) (hD : 0 < D) :
    trapPMFEvent (taoSection7HoldSourcePrefixListPMF N)
        (fun xs => ¬ TrapPascalPrefixGood J D (taoSection7RawPrefixOfHoldBlocks J xs)) ≤
      ((2 * J : ℕ) : ℝ) * (2 * Real.exp
        (-min (D ^ 2 / (32 * ((2 * J : ℕ) : ℝ))) (D / 8))) := by
  have h := trap_pascal_bad_prefix_probability_le J hJ D hD
  rw [← taoSection7HoldSourcePrefixListPMF_map_rawPrefix_eq_of_le J N hJN,
    trap_pmf_event_map] at h
  exact h

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_hold_source_bad_prefix_probability_le
