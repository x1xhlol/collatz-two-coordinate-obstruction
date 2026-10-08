/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshOuterBadJBoundary
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshOutsideEprimeNative

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

theorem
    lemma79_exists_qmBoundaryFarBelow_entryTriangle_currentScaleControls
    {n m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hactive : TaoSection7Prop78ActiveCoverData n xi epsilon)
    {entry : TaoSection7RenewalPoint}
    (hboundary : taoSection7QmBoundary (n / 2) m entry)
    (hfar :
      TaoSection7QmBoundaryFarBelow
        (taoSection7Prop78BoundaryThreshold m)
        hactive.family entry)
    (hm : 2 ≤ m) :
    ∃ Delta ∈ hactive.family,
      Delta.Mem entry.toPoint ∧
      taoSection7Prop78BoundaryThreshold m <
        (lemma79EntryVerticalGap Delta entry.toPoint : ℝ) ∧
      Delta.cornerL - entry.l =
        (lemma79EntryVerticalGap Delta entry.toPoint : ℤ) ∧
      TaoSection7Lemma710CurrentScaleControls
        n Delta entry.toPoint (m : ℝ)
          (lemma79EntryVerticalGap Delta entry.toPoint : ℝ) := by
  rcases
      lemma79_exists_qmBoundaryFarBelow_entryTriangle_gap_bounds
        hactive hboundary hfar with
    ⟨Delta, hDelta, hmem, hfarGap, hgapUpper⟩
  have hdomain :=
    taoSection7QmBoundary_toPoint_sourceDomain hboundary
  have hsub : n / 2 - (entry.j : ℕ) = m := by
    unfold taoSection7QmBoundary at hboundary
    omega
  have hcurrent :
      taoSection7Lemma710CurrentM n entry.toPoint = (m : ℝ) := by
    unfold taoSection7Lemma710CurrentM
    simpa [TaoSection7RenewalPoint.toPoint] using
      congrArg (fun k : ℕ => (k : ℝ)) hsub
  have hgap :
      Delta.verticalDepth entry.toPoint =
        (lemma79EntryVerticalGap Delta entry.toPoint : ℤ) := by
    simpa [TaoSection7Triangle.verticalDepth] using
      lemma79EntryVerticalGap_coe_of_mem hmem
  have hgapAlign :
      Delta.cornerL - entry.l =
        (lemma79EntryVerticalGap Delta entry.toPoint : ℤ) := by
    simpa [TaoSection7RenewalPoint.toPoint] using
      lemma79EntryVerticalGap_coe_of_mem hmem
  have hSdef :
      (lemma79EntryVerticalGap Delta entry.toPoint : ℝ) =
        ((Delta.verticalDepth entry.toPoint : ℤ) : ℝ) := by
    rw [hgap]
    norm_num
  have hm_gt_one : 1 < m := by omega
  have hm_gt_one_real : (1 : ℝ) < (m : ℝ) := by
    exact_mod_cast hm_gt_one
  have hMlower :
      (m : ℝ) / (Real.log (m : ℝ)) ^ 2 ≤
        (lemma79EntryVerticalGap Delta entry.toPoint : ℝ) := by
    unfold taoSection7Prop78BoundaryThreshold at hfarGap
    exact hfarGap.le
  refine ⟨Delta, hDelta, hmem, hfarGap, hgapAlign, ?_⟩
  exact
    { M_def := hcurrent.symm
      S_def := hSdef
      domain := hdomain
      M_large := hm_gt_one_real
      logM_pos := Real.log_pos hm_gt_one_real
      S_nonneg := Nat.cast_nonneg _
      hMlower := hMlower
      upper_752 := hgapUpper }

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
