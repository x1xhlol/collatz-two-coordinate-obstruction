/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section6.HeadGateLocalization
import Erdos1135SecondScale.Tao.Probability.GatedSubmass
import Erdos1135SecondScale.Tao.Syracuse.ValuationDistribution

/-!
# Section 6 Fixed Head Submass

This leaf maps Tao's checked head gate to the source-facing Corollary 6.3
residue as an unnormalized gated submass.  It specializes repaired Corollary
6.3 to obtain the exact collision bound `sum h^2 <= (1/2)^l`.  No tail or
convolution is introduced here.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- The full `Option` law retaining rejected head mass at `none`. -/
noncomputable def taoSection6HeadOptionPMF
    (CA : ℝ) (n k l : ℕ) : PMF (Option (ZMod (3 ^ n))) :=
  taoGatedOptionPMF
    (geom2PNatListPMF (k + 1))
    (taoSection6HeadGate CA n k l)
    (taoCor63SourceOffsetZMod n l)

/-- The unnormalized accepted head-residue mass. -/
noncomputable def taoSection6HeadSubmass
    (CA : ℝ) (n k l : ℕ) (y : ZMod (3 ^ n)) : ℝ :=
  taoGatedSubmass
    (geom2PNatListPMF (k + 1))
    (taoSection6HeadGate CA n k l)
    (taoCor63SourceOffsetZMod n l)
    y

/-- Repaired Corollary 6.3 makes the source residue injective on Tao's full
head gate.  The crossing conjunct remains present even though separation uses
only length, exact weight, and inclusive typicality. -/
theorem taoSection6HeadResidue_injOn_of_separation
    (hsep : TaoCor63StarSourceResidueSeparationStatement)
    {CA : ℝ} (hCA : 17 ≤ CA)
    {n : ℕ} (hn : Classical.choose (hsep CA hCA) ≤ n)
    {k l : ℕ} (hrange : taoCor63StarLRange CA n l) :
    Set.InjOn (taoCor63SourceOffsetZMod n l)
      {head | taoSection6HeadGate CA n k l head} := by
  intro as has bs hbs hsource
  exact Classical.choose_spec (hsep CA hCA)
    n hn k l hrange as bs
      (taoSection6HeadGate_length has)
      (taoSection6HeadGate_length hbs)
      (taoSection6HeadGate_weight has)
      (taoSection6HeadGate_weight hbs)
      (taoSection6HeadGate_typical has)
      (taoSection6HeadGate_typical hbs)
      hsource

/-- Once singleton typicality localizes the gate to the repaired star range,
the source residue is injective without an external range premise. -/
theorem taoSection6HeadResidue_injOn_of_separation_of_log_ge_four
    (hsep : TaoCor63StarSourceResidueSeparationStatement)
    {CA : ℝ} (hCA : 17 ≤ CA)
    {n : ℕ} (hn : Classical.choose (hsep CA hCA) ≤ n)
    (hlog : 4 ≤ Real.log (n : ℝ))
    {k l : ℕ} :
    Set.InjOn (taoCor63SourceOffsetZMod n l)
      {head | taoSection6HeadGate CA n k l head} := by
  intro as has bs hbs hsource
  exact taoSection6HeadResidue_injOn_of_separation
    hsep hCA hn
      (taoSection6HeadGate_starLRange_of_log_ge_four hCA hlog has)
      has hbs hsource

/-- Every accepted iid Geom(2) head atom has exactly the fixed weight
`(1/2)^l`. -/
theorem geom2PNatListPMF_apply_toReal_eq_headGate_weight
    {CA : ℝ} {n k l : ℕ} {head : List ℕ+}
    (hgate : taoSection6HeadGate CA n k l head) :
    (geom2PNatListPMF (k + 1) head).toReal = (1 / 2 : ℝ) ^ l := by
  rw [← taoSection6HeadGate_length hgate]
  rw [geom2PNatListPMF_apply_length_toReal_eq_weight]
  rw [taoSection6HeadGate_weight hgate]

/-- A fixed head slice with no accepted head has zero head submass. -/
theorem taoSection6HeadSubmass_eq_zero_of_headGate_empty
    {CA : ℝ} {n k l : ℕ}
    (hempty : ¬ ∃ head : List ℕ+,
      taoSection6HeadGate CA n k l head)
    (y : ZMod (3 ^ n)) :
    taoSection6HeadSubmass CA n k l y = 0 := by
  unfold taoSection6HeadSubmass
  exact taoGatedSubmass_eq_zero_of_not_exists_gate
    (geom2PNatListPMF (k + 1))
    (taoSection6HeadGate CA n k l)
    (taoCor63SourceOffsetZMod n l)
    hempty y

/-- The exact fixed-head collision bound under a supplied repaired Corollary
6.3 source-residue separation theorem. -/
theorem taoSection6HeadSubmass_sum_sq_le_of_separation
    (hsep : TaoCor63StarSourceResidueSeparationStatement)
    {CA : ℝ} (hCA : 17 ≤ CA)
    {n : ℕ} (hn : Classical.choose (hsep CA hCA) ≤ n)
    (k l : ℕ) (hrange : taoCor63StarLRange CA n l) :
    (∑ y : ZMod (3 ^ n),
      (taoSection6HeadSubmass CA n k l y) ^ 2) ≤
        (1 / 2 : ℝ) ^ l := by
  unfold taoSection6HeadSubmass
  apply taoGatedSubmass_sum_sq_le
    (geom2PNatListPMF (k + 1))
    (taoSection6HeadGate CA n k l)
    (taoCor63SourceOffsetZMod n l)
  · positivity
  · exact taoSection6HeadResidue_injOn_of_separation
      hsep hCA hn hrange
  · intro head hgate
    exact le_of_eq
      (geom2PNatListPMF_apply_toReal_eq_headGate_weight hgate)

/-- The fixed-head collision bound after crossing localization, with no
external star-range premise. -/
theorem taoSection6HeadSubmass_sum_sq_le_of_separation_of_log_ge_four
    (hsep : TaoCor63StarSourceResidueSeparationStatement)
    {CA : ℝ} (hCA : 17 ≤ CA)
    {n : ℕ} (hn : Classical.choose (hsep CA hCA) ≤ n)
    (hlog : 4 ≤ Real.log (n : ℝ))
    (k l : ℕ) :
    (∑ y : ZMod (3 ^ n),
      (taoSection6HeadSubmass CA n k l y) ^ 2) ≤
        (1 / 2 : ℝ) ^ l := by
  unfold taoSection6HeadSubmass
  apply taoGatedSubmass_sum_sq_le
    (geom2PNatListPMF (k + 1))
    (taoSection6HeadGate CA n k l)
    (taoCor63SourceOffsetZMod n l)
  · positivity
  · exact taoSection6HeadResidue_injOn_of_separation_of_log_ge_four
      hsep hCA hn hlog
  · intro head hgate
    exact le_of_eq
      (geom2PNatListPMF_apply_toReal_eq_headGate_weight hgate)

/-- Conditional eventual adapter retaining an external repaired star-range
premise. -/
theorem exists_taoSection6HeadSubmass_sum_sq_le_of_lrange
    (CA : ℝ) (hCA : 17 ≤ CA) :
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ k l : ℕ, taoCor63StarLRange CA n l →
        (∑ y : ZMod (3 ^ n),
          (taoSection6HeadSubmass CA n k l y) ^ 2) ≤
            (1 / 2 : ℝ) ^ l := by
  let hsep : TaoCor63StarSourceResidueSeparationStatement :=
    TaoCor63StarSourceResidueSeparationStatement.from_quarter_route
  refine ⟨Classical.choose (hsep CA hCA), ?_⟩
  intro n hn k l hrange
  exact taoSection6HeadSubmass_sum_sq_le_of_separation
    hsep hCA hn k l hrange

/-- Source-faithful eventual fixed-head collision bound from the checked
repaired Corollary 6.3 quarter route and crossing localization. -/
theorem exists_taoSection6HeadSubmass_sum_sq_le
    (CA : ℝ) (hCA : 17 ≤ CA) :
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ k l : ℕ,
        (∑ y : ZMod (3 ^ n),
          (taoSection6HeadSubmass CA n k l y) ^ 2) ≤
            (1 / 2 : ℝ) ^ l := by
  let hsep : TaoCor63StarSourceResidueSeparationStatement :=
    TaoCor63StarSourceResidueSeparationStatement.from_quarter_route
  obtain ⟨Nlog, hNlog⟩ := taoCor63_exists_nat_log_gt 4
  refine ⟨max (Classical.choose (hsep CA hCA)) Nlog, ?_⟩
  intro n hn k l
  have hnsep : Classical.choose (hsep CA hCA) ≤ n :=
    (le_max_left _ _).trans hn
  have hnlog : Nlog ≤ n := (le_max_right _ _).trans hn
  exact taoSection6HeadSubmass_sum_sq_le_of_separation_of_log_ge_four
    hsep hCA hnsep (le_of_lt (hNlog n hnlog)) k l

end

end Tao
end Erdos1135SecondScale
