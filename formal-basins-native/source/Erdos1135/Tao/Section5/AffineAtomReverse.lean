import Erdos1135.Tao.Section5.ReversePrefixScalar
import Erdos1135.Tao.Section5.PassLocationStepBack
import Erdos1135.Tao.Syracuse.AffineOdd

/-!
# Section 5 Affine-Atom Reverse Implication

This leaf decodes an odd affine endpoint and combines the checked
reverse-prefix scalar budget with the step-back event identity. It proves only
the reverse implication from a fixed affine atom to the original passage
event; forward lost-window localization and probability partitions remain
separate.
-/

namespace Erdos1135
namespace Tao

open Filter

noncomputable section

/-- An odd affine endpoint of a closed-typical tuple determines the actual
orbit endpoint and keeps every earlier iterate above the threshold. -/
theorem taoSection5_affineAtom_strictPrefix_and_endpoint
    {B N M r : ℕ} {as : List ℕ+}
    (hM : Odd M)
    (hAff : taoAffList as (N : ℚ) = (M : ℚ))
    (htyp : taoSection5TypicalTuple B r as)
    (hr : r ≤ taoSection5N0 B)
    (hlower : taoSection5CanonicalLostLower B ≤ (M : ℝ))
    (hbudget : taoSection5ReversePrefixScalarBudget B) :
    (∀ j < r, B < (syracuse^[j]) N) ∧
      (syracuse^[r]) N = M := by
  rcases taoAffList_oddNat_decode as N M hM hAff with
    ⟨hN, hvalues, hendpoint⟩
  have hvaluesR :
      syracuseValuationPNatList r N hN = as := by
    simpa only [htyp.1] using hvalues
  have hendpointR : (syracuse^[r]) N = M := by
    simpa only [htyp.1] using hendpoint
  have htypActual :
      taoSection5TypicalTuple B r
        (syracuseValuationPNatList r N hN) := by
    rw [hvaluesR]
    exact htyp
  have hlowerActual :
      taoSection5CanonicalLostLower B ≤ ((syracuse^[r]) N : ℝ) := by
    simpa only [hendpointR] using hlower
  exact
    ⟨taoSection5_strictPrefix_of_typical_endpoint_lower
        hN hr htypActual hlowerActual hbudget,
      hendpointR⟩

/-- A fixed closed-typical affine atom with endpoint in the canonical target
reconstructs the original passage event. This core has no source branch or
source-interior input. -/
theorem taoSection5PassEventAtTime_of_affineAtom
    {B n N M : ℕ} {E : Set ℕ} {as : List ℕ+}
    (hm : taoSection5M0 B ≤ n)
    (hr : n - taoSection5M0 B ≤ taoSection5N0 B)
    (has : as ∈ taoSection5TypicalTuples B
      (n - taoSection5M0 B))
    (hM : M ∈ taoSection5EPrime B E)
    (hAff : taoAffList as (N : ℚ) = (M : ℚ))
    (hbudget : taoSection5ReversePrefixScalarBudget B) :
    taoSection5PassEventAtTime B N n E := by
  have htyp := mem_taoSection5TypicalTuples_iff.mp has
  rcases mem_taoSection5EPrime_iff.mp hM with
    ⟨hMlower, _hMupper, hModd, hMhit, hMterminal⟩
  have hlower : taoSection5CanonicalLostLower B ≤ (M : ℝ) :=
    Nat.ceil_le.mp hMlower
  rcases taoSection5_affineAtom_strictPrefix_and_endpoint
      hModd hAff htyp hr hlower hbudget with
    ⟨hprefix, hendpoint⟩
  apply (taoSection5PassEventAtTime_iff_stepBack E hm).2
  refine ⟨hprefix, ?_, ?_⟩
  · simpa only [hendpoint] using hMhit
  · simpa only [hendpoint] using hMterminal

/-- Scheduled specialization: membership in a branch passage-time interval
supplies exactly the step-back and horizon bounds needed by the branch-free
affine-atom core. -/
theorem taoSection5PassEventAtTime_of_scheduledAffineAtom
    {B n N M : ℕ} {E : Set ℕ}
    {branch : TaoSection5SourceBranch} {as : List ℕ+}
    (facts : TaoSection5PassScheduleFacts B)
    (hn : n ∈ taoSection5PassTimes B branch)
    (has : as ∈ taoSection5TypicalTuples B
      (n - taoSection5M0 B))
    (hM : M ∈ taoSection5EPrime B E)
    (hAff : taoAffList as (N : ℚ) = (M : ℚ))
    (hbudget : taoSection5ReversePrefixScalarBudget B) :
    taoSection5PassEventAtTime B N n E :=
  taoSection5PassEventAtTime_of_affineAtom
    (facts.m0_le hn) (facts.sub_le_n0 hn) has hM hAff hbudget

/-- Uniform eventual reverse implication for every scheduled branch, time,
closed-typical tuple, and canonical target atom. -/
theorem eventually_taoSection5PassEventAtTime_of_scheduledAffineAtom :
    ∀ᶠ B : ℕ in atTop,
      ∀ {n N M : ℕ} {E : Set ℕ}
          {branch : TaoSection5SourceBranch} {as : List ℕ+},
        n ∈ taoSection5PassTimes B branch →
        as ∈ taoSection5TypicalTuples B (n - taoSection5M0 B) →
        M ∈ taoSection5EPrime B E →
        taoAffList as (N : ℚ) = (M : ℚ) →
        taoSection5PassEventAtTime B N n E := by
  filter_upwards
    [eventually_taoSection5PassScheduleFacts,
      eventually_taoSection5ReversePrefixScalarBudget]
      with B facts hbudget
  intro n N M E branch as hn has hM hAff
  exact taoSection5PassEventAtTime_of_scheduledAffineAtom
    facts hn has hM hAff hbudget

end

end Tao
end Erdos1135
