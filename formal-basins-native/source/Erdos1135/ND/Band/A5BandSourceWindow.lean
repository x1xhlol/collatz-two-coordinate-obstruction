import Erdos1135.ND.Band.A5BandPartition

/-!
# Exact A5 bands lie in the common Section 5 source window

This low-level support leaf keeps the valid-band guard visible.  It is shared
by deterministic passage localization and the standalone no-hit route.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- A valid exact A5 band lies inside the inherited Tao source window. -/
theorem ndA5OddBand_mem_taoSection5SourceWindow
    {B N j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hB : 1 ≤ B)
    (hj : j < ndA5BandCount B branch)
    (hband : N ∈ ndA5OddBand B branch j) :
    N ∈ Tao.oddLogWindow
      (Tao.taoSection5SourceLo B branch)
      (Tao.taoSection5SourceHi B branch) := by
  have hcount : 0 < ndA5BandCount B branch := Nat.zero_lt_of_lt hj
  have hmemUnion :
      N ∈ (Finset.range (ndA5BandCount B branch)).biUnion
        (ndA5OddBand B branch) := by
    rw [Finset.mem_biUnion]
    exact ⟨j, Finset.mem_range.mpr hj, hband⟩
  rw [biUnion_range_ndA5OddBand_eq_source_rpow hB hcount] at hmemUnion
  have hsource := mem_oddHalfOpenRealWindow.mp hmemUnion
  have hYnonneg : 0 ≤ Tao.taoSection5SourceY B branch := by
    rw [Tao.taoSection5SourceY_eq_branch_rpow]
    exact Real.rpow_nonneg (Nat.cast_nonneg B) _
  change N ∈ Tao.taoNyOddWindow
    (Tao.taoSection5SourceY B branch) Tao.taoAlpha
  rw [Tao.taoNyOddWindow_mem hYnonneg]
  simpa only [alpha] using
    ⟨hsource.1, hsource.2.1.le, hsource.2.2⟩

end

end ND
end Erdos1135
