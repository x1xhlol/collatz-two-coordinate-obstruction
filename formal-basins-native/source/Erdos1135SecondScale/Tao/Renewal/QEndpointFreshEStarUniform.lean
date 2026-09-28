/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Prop78Case3FixedParameters
import Erdos1135SecondScale.Tao.Renewal.QEndpointFreshEStarCountable

/-!
# Uniform Canonical EStar Provenance

This leaf preserves the source-uniform Lemma 7.10 constants while choosing
the fixed Case 3 parameters and countable `EStar` cutoff.  Its probability
field is already specialized to base `8`, cutoff `4 * Aweight`, and the exact
fixed survival horizon; finite-sum absorption is discharged internally.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

/-- The countable canonical `EStar` estimate specialized to one fixed Case 3
packet and its source-uniform depth cutoff. -/
structure TaoSection7Case3CanonicalEStarData
    {constants : TaoSection7Lemma710Constants}
    {A : ℕ} {epsilon : ℝ}
    (fixed : TaoSection7Case3FixedParameters constants A epsilon)
    (S0 : ℕ) : Prop where
  event_toReal_le :
    ∀ (n m J fpGap : ℕ)
      (entry : TaoSection7RenewalPoint)
      (family : Set TaoSection7Triangle)
      (old : TaoSection7Triangle) (M : ℝ),
      S0 ≤ fpGap →
      fixed.Pmax ≤ J →
      old.cornerL - entry.l = (fpGap : ℤ) →
      old.Mem entry.toPoint →
      TaoSection7TriangleFamilyPairwiseDisjoint family →
      old ∈ family →
      TaoSection7Lemma710CurrentScaleControls
        n old entry.toPoint M (fpGap : ℝ) →
      2 ≤ m →
      M = (m : ℝ) →
      TaoSection7Case3BaseKcutAllowedCapAdmissibility
        (Finset.range (fixed.Pmax + 1))
        8 m (4 * fixed.Aweight) fixed.Pmax →
      ((lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
          (lemma79CanonicalEndpointFreshEStarEvent
            entry family 8 (4 * fixed.Aweight) fixed.T fixed.R)).toReal ≤
        (fixed.Aweight : ℝ) ^ 2 /
          ((4 : ℝ) ^ (4 * fixed.Aweight))

/-- One genuine Lemma 7.10 constants witness works uniformly for every later
admissible `epsilon` and requested positive exponent `A`. -/
theorem exists_taoSection7Case3CanonicalEStarData :
    ∃ constants : TaoSection7Lemma710Constants,
      ∀ {epsilon : ℝ},
        TaoSection7ClaimStarScalarPacket epsilon →
        ∀ (A : ℕ), 1 ≤ A →
          ∃ fixed : TaoSection7Case3FixedParameters constants A epsilon,
            ∃ S0 : ℕ,
              TaoSection7Case3CanonicalEStarData fixed S0 := by
  rcases
      lemma79CanonicalEndpointFreshEStarEvent_toReal_le_baseKcutBudget with
    ⟨constants, hcountable⟩
  refine ⟨constants, ?_⟩
  intro epsilon hscalar A hA
  rcases
      nonempty_taoSection7Case3FixedParameters constants A hA hscalar with
    ⟨fixed⟩
  rcases
      hcountable fixed.Aweight 8 (4 * fixed.Aweight) fixed.T fixed.R
        fixed.Aweight_ge_eight with
    ⟨S0, hbound⟩
  rw [← fixed.Pmax_eq] at hbound
  refine ⟨fixed, S0, ⟨?_⟩⟩
  intro n m J fpGap entry family old M
    hS0 hPmaxJ hgap hmem hpair hold hscale hm hM hcap
  exact
    hbound n m J fpGap entry family old M
      hS0 hPmaxJ hgap hmem hpair hold hscale hm hM hcap
      fixed.to_absorptionInputs

end

end Tao
end Erdos1135SecondScale
