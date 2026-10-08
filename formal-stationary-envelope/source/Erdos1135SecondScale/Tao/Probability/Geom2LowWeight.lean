/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.Geom2CenteredMoment

/-!
# Strict Low-Weight Tail for Positive Geom(2) Lists

This neutral leaf isolates the strict valuation-weight event used in Tao's
Section 5 no-hit argument.  It proves the ideal iid Geom(2) event has mass at
most `exp (-n/3200)`, including the zero-length endpoint.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- The strict low-weight event complementary to the inclusive deterministic
descent trigger `19*n <= 10*weight`. -/
def taoLowValuationWeightEvent (n : ℕ) : Set (List ℕ+) :=
  {as | 10 * taoTupleWeight as < 19 * n}

/-- The strict low-weight event for an iid positive Geom(2) list has the
explicit one-sided Chernoff bound used by the Section 5 no-hit route. -/
theorem geom2PNatListPMF_lowWeightEvent_le_exp (n : ℕ) :
    ((geom2PNatListPMF n).toOuterMeasure
      (taoLowValuationWeightEvent n)).toReal ≤
        Real.exp (-((n : ℝ) / 3200)) := by
  by_cases hn : n = 0
  · subst n
    have hevent : taoLowValuationWeightEvent 0 = ∅ := by
      ext as
      simp [taoLowValuationWeightEvent]
    rw [hevent]
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let E : Set (List ℕ+) :=
      {as | taoGeom2CenteredListWeight as < -((n : ℝ) / 10)}
    have hfinite : (geom2PNatListPMF n).toOuterMeasure E ≠ ⊤ := by
      apply ne_of_lt
      calc
        (geom2PNatListPMF n).toOuterMeasure E ≤
            (geom2PNatListPMF n).toOuterMeasure Set.univ :=
          (geom2PNatListPMF n).toOuterMeasure.mono (Set.subset_univ E)
        _ = 1 := ((geom2PNatListPMF n).toOuterMeasure_apply_eq_one_iff
          Set.univ).2 (Set.subset_univ _)
        _ < ⊤ := ENNReal.one_lt_top
    have hnative :
        (geom2PNatListPMF n).toOuterMeasure
            (taoLowValuationWeightEvent n) ≤
          (geom2PNatListPMF n).toOuterMeasure E := by
      apply (geom2PNatListPMF n).toOuterMeasure_mono
      rintro as ⟨hlow, has⟩
      have hlength : as.length = n :=
        geom2PNatListPMF_support_length_eq has
      have hlowReal :
          10 * (taoTupleWeight as : ℝ) < 19 * (n : ℝ) := by
        exact_mod_cast hlow
      dsimp [E]
      unfold taoGeom2CenteredListWeight
      rw [hlength]
      nlinarith
    have hreal := ENNReal.toReal_mono hfinite hnative
    have htail := geom2PNatListPMF_centeredWeight_lowerTail_le
      n (t := (1 / 160 : ℝ)) (lambda := (n : ℝ) / 10)
        (by norm_num) (by norm_num)
    change ((geom2PNatListPMF n).toOuterMeasure E).toReal ≤ _ at htail
    have hexponent :
        -(1 / 160 : ℝ) * ((n : ℝ) / 10) +
            8 * (1 / 160 : ℝ) ^ 2 * (n : ℝ) =
          -((n : ℝ) / 3200) := by
      ring
    rw [hexponent] at htail
    exact hreal.trans htail

end

end Tao
end Erdos1135SecondScale
