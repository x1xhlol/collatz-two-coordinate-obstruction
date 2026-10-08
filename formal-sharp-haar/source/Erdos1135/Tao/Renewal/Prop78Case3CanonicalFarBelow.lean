import Erdos1135.Tao.Renewal.Prop78Case3EventualScale
import Erdos1135.Tao.Renewal.Prop78Case3PriorityScalar
import Erdos1135.Tao.Renewal.QEndpointFreshEStarUniform
import Erdos1135.Tao.Renewal.QEndpointFreshMiddleMass
import Erdos1135.Tao.Renewal.QEndpointFreshOutsideEprimeBoundary
import Erdos1135.Tao.Renewal.QEndpointFreshOuterBadJAbsorption
import Erdos1135.Tao.Renewal.QEndpointFreshPriorityPartition
import Erdos1135.Tao.Renewal.QEndpointFreshCloseout

/-!
# Canonical Case 3 Far-Below Bound

This leaf composes the canonical endpoint-fresh bad-`J`, middle-mass, and
priority-partition estimates for one active far-below triangle.  It leaves
the later boundary reindexing outside the probability calculation.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- The direct canonical one-triangle Case 3 estimate, after one uniform
`EStar` cutoff and the eventual scale threshold have been fixed. -/
theorem exists_taoSection7Prop78_case3_farBelow_canonical_threshold
    {constants : TaoSection7Lemma710Constants}
    {A : ℕ} {epsilon : ℝ}
    (fixed : TaoSection7Case3FixedParameters constants A epsilon)
    (S0 : ℕ)
    (hEStar : TaoSection7Case3CanonicalEStarData fixed S0)
    (L : ℕ)
    (hlocalizedMass : ∀ start s,
      (1 / 2 : ℝ) ≤
        ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
          (lemma77CanonicalLocalizedEndpointEvent s L)).toReal)
    (hcollar :
      taoSection7Case2HorizontalCollar L ^ 2 + (L : ℝ) ^ 2 ≤
        taoSection7TriangleSeparation epsilon ^ 2) :
    ∃ C3 : ℕ,
      TaoSection7Prop78Threshold A epsilon C3 ∧
      ∀ (n : ℕ) (xi : ZMod (3 ^ n))
        (hxi : zmodThreePrimitive n xi)
        (m : ℕ), C3 ≤ m → m ≤ n / 2 →
        ∀ entry : TaoSection7RenewalPoint,
          taoSection7QmBoundary (n / 2) m entry →
          TaoSection7QmBoundaryFarBelow
              (taoSection7Prop78BoundaryThreshold m)
              (taoSection7CanonicalTriangleFamily hxi fixed.scalar) entry →
          taoSection7SourceActualQ n xi epsilon entry ≤
            ((m : ℝ) ^ A)⁻¹ *
              taoSection7SourceActualQmAtCutoff
                n A (m - 1) xi epsilon := by
  obtain ⟨Cscale, hscale⟩ :=
    exists_taoSection7Case3EventualScaleThreshold fixed S0
  obtain ⟨Cbad, hbad⟩ :=
    lemma79CanonicalEndpointFreshPMF_outerBadJ_weighted_toReal_le_half
      A fixed.P
  let C3 := max taoSection7Prop78LowerThreshold (max Cscale Cbad)
  refine ⟨C3, ⟨by exact ⟨Nat.le_max_left _ _⟩, ?_⟩⟩
  intro n xi hxi m hm hm_hi entry hboundary hfar
  have hinner : max Cscale Cbad ≤ m :=
    (Nat.le_max_right _ _).trans hm
  have hfacts := hscale m ((Nat.le_max_left _ _).trans hinner)
  have hCbad : Cbad ≤ m := (Nat.le_max_right _ _).trans hinner
  have hPcut : fixed.P ≤ n / 2 := hfacts.P_le_m.trans hm_hi
  have hPmaxCut : fixed.Pmax ≤ n / 2 :=
    (Nat.le_of_lt fixed.Pmax_lt_P).trans hPcut
  have hone_le_m : 1 ≤ m :=
    (by decide : 1 ≤ 2).trans hfacts.two_le_m

  let hactive :=
    TaoSection7Prop78ActiveCoverData.of_canonical hxi fixed.scalar
  have hfar' :
      TaoSection7QmBoundaryFarBelow
        (taoSection7Prop78BoundaryThreshold m) hactive.family entry := by
    change TaoSection7QmBoundaryFarBelow
      (taoSection7Prop78BoundaryThreshold m)
      (taoSection7CanonicalTriangleFamily hxi fixed.scalar) entry
    exact hfar
  obtain ⟨Delta, hDelta, hmem, hfarGap, hgapAlign, hcurrent⟩ :=
    lemma79_exists_qmBoundaryFarBelow_entryTriangle_currentScaleControls
      hactive hboundary hfar' hfacts.two_le_m

  let gap := lemma79EntryVerticalGap Delta entry.toPoint
  change Delta ∈
    taoSection7CanonicalTriangleFamily hxi fixed.scalar at hDelta
  change taoSection7Prop78BoundaryThreshold m < (gap : ℝ) at hfarGap
  change Delta.cornerL - entry.l = (gap : ℤ) at hgapAlign
  change TaoSection7Lemma710CurrentScaleControls
    n Delta entry.toPoint (m : ℝ) (gap : ℝ) at hcurrent
  have hS0gap : S0 ≤ gap :=
    (Nat.cast_lt.mp
      (lt_of_le_of_lt hfacts.S0_le_boundaryThreshold hfarGap)).le

  have hestar :=
    hEStar.event_toReal_le
      (n := n) (m := m) (J := n / 2) (fpGap := gap)
      (entry := entry)
      (family := taoSection7CanonicalTriangleFamily hxi fixed.scalar)
      (old := Delta) (M := (m : ℝ))
      hS0gap hPmaxCut hgapAlign hmem
      (taoSection7CanonicalTriangleFamily_pairwiseDisjoint hxi fixed.scalar)
      hDelta hcurrent hfacts.two_le_m rfl
      hfacts.to_allowedCapAdmissibility

  have hmiddle :=
    lemma79CanonicalEndpointFreshPMF_middle_toReal_le_canonicalEStar_add_fSlack
      L hlocalizedMass hxi fixed.scalar hcollar
      entry gap fixed.P m fixed.T fixed.R fixed.Amarkov fixed.Aweight
      8 (4 * fixed.Aweight) hboundary hPcut fixed.R_pos
      fixed.iterate_room fixed.Amarkov_eq fixed.white_room
  have hmiddle' := hmiddle.trans (add_le_add hestar le_rfl)

  have hbad' := hbad (J := n / 2) hPcut entry gap m hCbad hcurrent.upper_752
  have hbadCanonical :
      (m : ℝ) ^ A *
        ((lemma79CanonicalEndpointFreshPMF
            (n / 2) entry gap).toOuterMeasure
          (lemma79CanonicalEndpointFreshOuterBadJEvent fixed.P m)).toReal ≤
        1 / 2 := by
    simpa [lemma79CanonicalEndpointFreshOuterBadJEvent,
      taoSection7Case3Outer754LargeHorizontalEvent,
      lemma79EndpointFreshHorizontalAdvance] using hbad'

  have hpriority :=
    lemma79CanonicalEndpointFreshPMF_outer754Weight_summable_and_le_priorityPartition_one
      (n := n) (A := A) (m := m) (P := fixed.P) (T := fixed.T)
      (xi := xi) (epsilon := epsilon)
      fixed.scalar.epsilon_pos.le hone_le_m
      fixed.priority_threshold entry gap

  have hexpect :
      taoSection7PMFExpectation
          (lemma79CanonicalEndpointFreshPMF (n / 2) entry gap)
          (lemma79EndpointFreshOuter754Weight
            n A m fixed.P xi epsilon entry) ≤ 1 := by
    calc
      _ ≤ (m : ℝ) ^ A *
            ((lemma79CanonicalEndpointFreshPMF
              (n / 2) entry gap).toOuterMeasure
                (lemma79CanonicalEndpointFreshOuterBadJEvent fixed.P m)).toReal +
          (10 : ℝ) ^ A *
            ((lemma79CanonicalEndpointFreshPMF
              (n / 2) entry gap).toOuterMeasure
                ((lemma79CanonicalEndpointFreshOuterBadJEvent fixed.P m)ᶜ ∩
                  lemma79CanonicalEndpointFreshLowWhiteEvent
                    n fixed.P fixed.T xi epsilon entry)).toReal +
          (10 : ℝ) ^ A * Real.exp (-((10 : ℝ) * (A : ℝ))) :=
        hpriority.2
      _ ≤ 1 / 2 +
          (10 : ℝ) ^ A *
            ((fixed.Aweight : ℝ) ^ 2 /
                ((4 : ℝ) ^ (4 * fixed.Aweight)) +
              1 / ((10 : ℝ) ^ (fixed.Aweight + 3))) +
          (10 : ℝ) ^ A * Real.exp (-((10 : ℝ) * (A : ℝ))) :=
        add_le_add
          (add_le_add hbadCanonical
            (mul_le_mul_of_nonneg_left hmiddle' (by positivity))) le_rfl
      _ ≤ 61 / 100 := fixed.weighted_priority_budget_le_sixtyOneHundredths
      _ ≤ 1 := by norm_num

  exact
    taoSection7SourceActualQ_le_endpointFreshOuter754_of_expectation_le_one
      fixed.scalar.epsilon_pos.le hone_le_m hPcut entry gap hboundary
      hpriority.1 hexpect

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
