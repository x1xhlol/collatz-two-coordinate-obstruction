import BasinIndicatorTransport
import RealCanonicalClockRates
import Erdos1135.ND.Discrepancy.A5ReferenceNDM2
import Erdos1135.ND.RhinPhaseGap

set_option autoImplicit false

open Filter
open scoped Topology

namespace CollatzCanonical.NativeTao
open Erdos1135 CollatzClockAudit CollatzCylinderPacking.Arithmetic

theorem unconditional_natural_passage_rates :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : 1 ≤ x) (branch : Tao.TaoSection5SourceBranch),
      let y := ND.transportSourceY x branch
      ∃ hwindow : (ND.oddBlock y).Nonempty,
      ∃ hmass : 0 < Tao.logFinsetMass (ND.oddBlock y),
        ND.uniformNoHitProbability x y hwindow ≤ 184 * x ^ (-(1 / 32000 : ℝ)) ∧
        ND.passFullL1 x y hx hwindow hmass ≤ 384256 * (Real.log x) ^ (-(1 / 40 : ℝ)) := by
  obtain ⟨c, hc⟩ := ND.existsPhaseGapRhin
  exact ND.eventually_ndA5RealSameBranchRateBounds hc (by norm_num)
    (by norm_num) (by norm_num)

theorem natural_source_eq_clock (x : ℝ) (branch : Tao.TaoSection5SourceBranch) :
    ND.transportSourceY x branch = realClockSourceY x branch := by
  cases branch <;> rfl

theorem natural_block_eq_clock (x : ℝ) (branch : Tao.TaoSection5SourceBranch) :
    ND.oddBlock (ND.transportSourceY x branch) =
      Tao.oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch) := by
  rw [natural_source_eq_clock]
  rfl

theorem natural_pass_eq_native (x : ℝ) (q : ℕ) (hx : 1 ≤ x) :
    ND.passLocationOrOne x q hx = Tao.syracusePassLocationRealFloorOrOne x q hx := rfl

theorem native_large_landing_iff (x : ℝ) (hx : 1 ≤ x) (q : Tao.TaoOddNat) :
    q ∈ realLargeLandingGoodEvent x ↔
      x ^ (1 / 2 : ℝ) < ((ND.passLocationOrOne x q.1 hx).1 : ℝ) := by
  constructor
  · rintro ⟨n, hn, hlarge⟩
    rw [natural_pass_eq_native, native_real_passLocation_eq_of_first hx hn]
    exact hlarge
  · intro hlarge
    have hfloor : Tao.syracuseHitsAtMost q.1 (Nat.floor x) := by
      by_contra h
      have he : (ND.passLocationOrOne x q.1 hx).1 = 1 := by
        simp [ND.passLocationOrOne, h]
      rw [he] at hlarge
      have hs := Real.one_le_rpow hx (by norm_num : (0 : ℝ) ≤ 1 / 2)
      norm_num at hlarge
      linarith
    let n := Tao.syracuseFirstPassageTime q.1 (Nat.floor x) hfloor
    have hn : Tao.syracuseFirstHitAtMostReal x q.1 n :=
      (Tao.syracuseFirstHitAtMostReal_iff_floor (by linarith : 0 ≤ x)).mpr
        (Tao.syracuseFirstHitAtMost_of_hitsAtMost q.1 (Nat.floor x) hfloor)
    refine ⟨n, hn, ?_⟩
    rw [natural_pass_eq_native, native_real_passLocation_eq_of_first hx hn] at hlarge
    exact hlarge

theorem natural_bad_landing_probability {x y : ℝ} (hx : 1 ≤ x)
    (hmass : 0 < Tao.logFinsetMass (ND.oddBlock y)) :
    Tao.pmfProb (ND.logOddBlockPMF y hmass)
      {q | ((ND.passLocationOrOne x q.1 hx).1 : ℝ) ≤ x ^ (1 / 2 : ℝ)} =
    ((Tao.oddLogWindowOddNatPMF (Tao.taoNyLo y) (Tao.taoNyHi y ND.alpha)
      hmass).toOuterMeasure (realLargeLandingGoodEvent x)ᶜ).toReal := by
  rw [← native_odd_source_bad_probability]
  apply congrArg (Tao.pmfProb _)
  ext q
  simp only [Set.mem_setOf_eq, native_large_landing_iff x hx, not_lt]
  rfl

#print axioms unconditional_natural_passage_rates
#print axioms native_large_landing_iff
#print axioms natural_bad_landing_probability

end CollatzCanonical.NativeTao
