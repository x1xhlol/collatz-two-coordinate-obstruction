import Erdos1135.Tao.Renewal.QEndpointFreshOuterBadJAbsorption
import Erdos1135.Tao.Renewal.Prop78Case3ActiveCoverStopping

/-!
# Boundary-Far-Below Canonical OuterBadJ

This source-facing leaf selects the same triangle carried by the Proposition
7.8 far-below branch, identifies its natural entry gap, and feeds the checked
canonical endpoint/fresh one-rate tail.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- The exact far-below triangle supplies both the lower depth witness and the
current-scale upper bound for its natural entry gap. -/
theorem lemma79_exists_qmBoundaryFarBelow_entryTriangle_gap_bounds
    {n m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hactive : TaoSection7Prop78ActiveCoverData n xi epsilon)
    {entry : TaoSection7RenewalPoint}
    (hboundary : taoSection7QmBoundary (n / 2) m entry)
    (hfar :
      TaoSection7QmBoundaryFarBelow
        (taoSection7Prop78BoundaryThreshold m)
        hactive.family entry) :
    ∃ Delta ∈ hactive.family,
      Delta.Mem entry.toPoint ∧
      taoSection7Prop78BoundaryThreshold m <
        (lemma79EntryVerticalGap Delta entry.toPoint : ℝ) ∧
      (lemma79EntryVerticalGap Delta entry.toPoint : ℝ) ≤
        (Real.log 9 / Real.log 2) * (m : ℝ) := by
  rcases hfar with ⟨Delta, hDelta, hmem, hfarDepth⟩
  have hdomain :=
    taoSection7QmBoundary_toPoint_sourceDomain hboundary
  have hright :
      TaoSection7TriangleRightEdgeInStrip ((n / 2 : ℕ) : ℝ) Delta :=
    hactive.rightEdge hDelta
  have hupper :=
    taoSection7Lemma710_verticalDepth_le_log9_div_log2_mul_currentM_of_domain
      hmem hdomain hright
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
  refine ⟨Delta, hDelta, hmem, ?_, ?_⟩
  · simpa [hgap] using hfarDepth
  · simpa [hgap, hcurrent] using hupper

/-- The boundary-selected far-below triangle feeds the full canonical
endpoint/fresh one-rate OuterBadJ bound on its exact natural gap. -/
theorem
    lemma79CanonicalEndpointFreshPMF_outerBadJ_singleRate_toReal_le_of_qmBoundaryFarBelow :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
      ∀ {n m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
        (hactive : TaoSection7Prop78ActiveCoverData n xi epsilon)
        {entry : TaoSection7RenewalPoint}, 1 ≤ m →
          taoSection7QmBoundary (n / 2) m entry →
          TaoSection7QmBoundaryFarBelow
              (taoSection7Prop78BoundaryThreshold m)
              hactive.family entry →
          ∀ {P J : ℕ}, P ≤ J →
            ∃ Delta ∈ hactive.family,
              Delta.Mem entry.toPoint ∧
              taoSection7Prop78BoundaryThreshold m <
                (lemma79EntryVerticalGap Delta entry.toPoint : ℝ) ∧
              ((lemma79CanonicalEndpointFreshPMF J entry
                    (lemma79EntryVerticalGap Delta entry.toPoint)).toOuterMeasure
                  {atom |
                    9 * m ≤ 10 *
                      (atom.1.1 +
                        lemma77HoldPrefixHorizontalDelta P atom.2)}).toReal ≤
                (K + Real.exp ((P : ℝ) / 2)) *
                  Real.exp (-c * (m : ℝ)) := by
  rcases
      lemma79CanonicalEndpointFreshPMF_outerBadJ_singleRate_toReal_le with
    ⟨K, c, hK, hc, htail⟩
  refine ⟨K, c, hK, hc, ?_⟩
  intro n m xi epsilon hactive entry hm hboundary hfar P J hPJ
  rcases lemma79_exists_qmBoundaryFarBelow_entryTriangle_gap_bounds
      hactive hboundary hfar with
    ⟨Delta, hDelta, hmem, hfarGap, hgap⟩
  refine ⟨Delta, hDelta, hmem, hfarGap, ?_⟩
  exact htail hPJ entry
    (lemma79EntryVerticalGap Delta entry.toPoint) m hm hgap

/-- The same far-below triangle feeds the polynomially weighted half-budget at
every sufficiently large fixed-P boundary scale. -/
theorem
    lemma79CanonicalEndpointFreshPMF_outerBadJ_weighted_toReal_le_half_of_qmBoundaryFarBelow
    (B P : ℕ) :
    ∃ C : ℕ,
      ∀ {n m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
        (hactive : TaoSection7Prop78ActiveCoverData n xi epsilon)
        {entry : TaoSection7RenewalPoint}, C ≤ m →
          P ≤ n / 2 →
          taoSection7QmBoundary (n / 2) m entry →
          TaoSection7QmBoundaryFarBelow
              (taoSection7Prop78BoundaryThreshold m)
              hactive.family entry →
            ∃ Delta ∈ hactive.family,
              Delta.Mem entry.toPoint ∧
              taoSection7Prop78BoundaryThreshold m <
                (lemma79EntryVerticalGap Delta entry.toPoint : ℝ) ∧
              (m : ℝ) ^ B *
                ((lemma79CanonicalEndpointFreshPMF
                    (n / 2) entry
                    (lemma79EntryVerticalGap Delta entry.toPoint)).toOuterMeasure
                  {atom |
                    9 * m ≤ 10 *
                      (atom.1.1 +
                        lemma77HoldPrefixHorizontalDelta P atom.2)}).toReal ≤
                  1 / 2 := by
  rcases
      lemma79CanonicalEndpointFreshPMF_outerBadJ_weighted_toReal_le_half
        B P with
    ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro n m xi epsilon hactive entry hm hPJ hboundary hfar
  rcases lemma79_exists_qmBoundaryFarBelow_entryTriangle_gap_bounds
      hactive hboundary hfar with
    ⟨Delta, hDelta, hmem, hfarGap, hgap⟩
  refine ⟨Delta, hDelta, hmem, hfarGap, ?_⟩
  exact hC hPJ entry
    (lemma79EntryVerticalGap Delta entry.toPoint) m hm hgap

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
