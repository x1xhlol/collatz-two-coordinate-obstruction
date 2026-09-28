/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.CanonicalFirstPassageLocalizedMass
import Erdos1135SecondScale.Tao.Renewal.Prop78Case2Geometry
import Erdos1135SecondScale.Tao.Renewal.QEndpointFreshEStarUniform

/-!
# Absolute Proposition 7.8 Parameters

This leaf chooses the absolute localized endpoint window, Claim-Star scale,
and Lemma 7.10 constants before any requested polynomial exponent.  The
resulting Type-valued packet preserves that source quantifier order for the
later three-case Proposition 7.8 assembly.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Lemma77

/-- Absolute data shared by all requested positive exponents in the canonical
Proposition 7.8 route. -/
structure TaoSection7Prop78AbsolutePacket where
  constants : TaoSection7Lemma710Constants
  L : ℕ
  one_le_L : 1 ≤ L
  localizedMass :
    ∀ start s,
      (1 / 2 : ℝ) ≤
        ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
          (lemma77CanonicalLocalizedEndpointEvent s L)).toReal
  epsilon : ℝ
  scalar : TaoSection7ClaimStarScalarPacket epsilon
  collar :
    taoSection7Case2HorizontalCollar L ^ 2 + (L : ℝ) ^ 2 ≤
      taoSection7TriangleSeparation epsilon ^ 2
  uniformEStar :
    ∀ A : ℕ, 1 ≤ A →
      ∃ fixed :
          TaoSection7Case3FixedParameters constants A epsilon,
        ∃ S0 : ℕ,
          TaoSection7Case3CanonicalEStarData fixed S0

/-- There is one absolute packet whose constants, window, and epsilon work
for every later requested positive exponent. -/
theorem nonempty_taoSection7Prop78AbsolutePacket :
    Nonempty TaoSection7Prop78AbsolutePacket := by
  obtain ⟨L, hone_le_L, hlocalizedMass⟩ :=
    lemma77CanonicalFirstPassageEndpointPMF_localized_absoluteMass
  obtain ⟨constants, huniformEStar⟩ :=
    exists_taoSection7Case3CanonicalEStarData
  let X : ℝ :=
    taoSection7Case2HorizontalCollar L ^ 2 + (L : ℝ) ^ 2
  let E : ℝ := X + 1
  let epsilon : ℝ := Real.exp (-10 * E)
  have hX_nonneg : 0 ≤ X := by
    dsimp [X]
    positivity
  have hone_le_E : 1 ≤ E := by
    dsimp [E]
    linarith
  have hepsilon_pos : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hepsilon_le : epsilon ≤ Real.exp (-10) := by
    dsimp [epsilon]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hscalar : TaoSection7ClaimStarScalarPacket epsilon :=
    TaoSection7ClaimStarScalarPacket.of_le_exp_neg_ten
      hepsilon_pos hepsilon_le
  have hinvEpsilon : 1 / epsilon = Real.exp (10 * E) := by
    dsimp [epsilon]
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  have hseparation : taoSection7TriangleSeparation epsilon = E := by
    unfold taoSection7TriangleSeparation taoSection7TriangleLogScale
    rw [hinvEpsilon, Real.log_exp]
    ring
  have hcollar :
      taoSection7Case2HorizontalCollar L ^ 2 + (L : ℝ) ^ 2 ≤
        taoSection7TriangleSeparation epsilon ^ 2 := by
    rw [hseparation]
    change X ≤ E ^ 2
    dsimp [E]
    nlinarith [sq_nonneg X]
  exact ⟨{
    constants := constants
    L := L
    one_le_L := hone_le_L
    localizedMass := hlocalizedMass
    epsilon := epsilon
    scalar := hscalar
    collar := hcollar
    uniformEStar := fun A hA => huniformEStar hscalar A hA
  }⟩

end

end Tao
end Erdos1135SecondScale
