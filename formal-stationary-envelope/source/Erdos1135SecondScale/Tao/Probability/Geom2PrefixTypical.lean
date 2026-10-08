/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.Geom2CenteredMoment
import Erdos1135SecondScale.Tao.Probability.Geom2ListProjectivity

/-!
# Positive-Prefix Concentration for Geom(2) Lists

This neutral leaf bounds failure of one common centered-weight threshold over
all positive prefixes of an iid positive Geom(2) list.  It uses one finite
union after projecting each prefix to its exact marginal law.  No Section 5
or Proposition 1.9 definition is imported.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Lists having a positive prefix whose centered valuation weight exceeds
the common threshold.  The index is positive by construction. -/
def taoGeom2PrefixBadEvent (lambda : ℝ) (n : ℕ) : Set (List ℕ+) :=
  {as | ∃ j : Fin n,
    lambda < |taoGeom2CenteredListWeight (as.take (j.1 + 1))|}

@[simp] theorem taoGeom2PrefixBadEvent_zero (lambda : ℝ) :
    taoGeom2PrefixBadEvent lambda 0 = ∅ := by
  ext as
  simp [taoGeom2PrefixBadEvent]

/-- The bad event at one positive prefix has exactly the corresponding
short-list failure mass. -/
theorem geom2PNatListPMF_prefixBad_outerMeasure_toReal
    {n : ℕ} (j : Fin n) (lambda : ℝ) :
    ((geom2PNatListPMF n).toOuterMeasure
        {as | lambda <
          |taoGeom2CenteredListWeight (as.take (j.1 + 1))|}).toReal =
      ((geom2PNatListPMF (j.1 + 1)).toOuterMeasure
        {pre | lambda < |taoGeom2CenteredListWeight pre|}).toReal := by
  have hj : j.1 + 1 ≤ n := by omega
  rw [← geom2PNatListPMF_map_take_low_eq_of_le hj]
  rw [PMF.toOuterMeasure_map_apply]
  rfl

/-- A single finite union bounds all positive-prefix failures. -/
theorem geom2PNatListPMF_prefixBad_le_sum
    (n : ℕ) {lambda : ℝ} (hlambda : 0 < lambda) :
    ((geom2PNatListPMF n).toOuterMeasure
        (taoGeom2PrefixBadEvent lambda n)).toReal ≤
      ∑ j : Fin n,
        2 * Real.exp
          (-min
            (lambda ^ 2 / (32 * ((j.1 + 1 : ℕ) : ℝ)))
            (lambda / 8)) := by
  let p := geom2PNatListPMF n
  let Bad : Fin n → Set (List ℕ+) := fun j =>
    {as | lambda <
      |taoGeom2CenteredListWeight (as.take (j.1 + 1))|}
  have hevent : taoGeom2PrefixBadEvent lambda n = ⋃ j, Bad j := by
    ext as
    simp [taoGeom2PrefixBadEvent, Bad]
  have hnative :
      p.toOuterMeasure (taoGeom2PrefixBadEvent lambda n) ≤
        ∑ j : Fin n, p.toOuterMeasure (Bad j) := by
    rw [hevent]
    exact MeasureTheory.measure_iUnion_fintype_le _ _
  have htermfinite (j : Fin n) : p.toOuterMeasure (Bad j) ≠ ⊤ := by
    apply ne_of_lt
    calc
      p.toOuterMeasure (Bad j) ≤ p.toOuterMeasure Set.univ :=
        p.toOuterMeasure.mono (Set.subset_univ _)
      _ = 1 := (p.toOuterMeasure_apply_eq_one_iff Set.univ).2
        (Set.subset_univ _)
      _ < ⊤ := ENNReal.one_lt_top
  have hfinite :
      (∑ j : Fin n, p.toOuterMeasure (Bad j)) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro j hj
    exact htermfinite j
  have hreal := ENNReal.toReal_mono hfinite hnative
  rw [ENNReal.toReal_sum] at hreal
  · calc
      ((geom2PNatListPMF n).toOuterMeasure
          (taoGeom2PrefixBadEvent lambda n)).toReal ≤
          ∑ j : Fin n, (p.toOuterMeasure (Bad j)).toReal := by
            simpa [p] using hreal
      _ = ∑ j : Fin n,
          ((geom2PNatListPMF (j.1 + 1)).toOuterMeasure
            {pre | lambda < |taoGeom2CenteredListWeight pre|}).toReal := by
            apply Finset.sum_congr rfl
            intro j hj
            simpa [p, Bad] using
              geom2PNatListPMF_prefixBad_outerMeasure_toReal j lambda
      _ ≤ ∑ j : Fin n,
          2 * Real.exp
            (-min
              (lambda ^ 2 / (32 * ((j.1 + 1 : ℕ) : ℝ)))
              (lambda / 8)) := by
            apply Finset.sum_le_sum
            intro j hj
            exact geom2PNatListPMF_centeredWeight_absTail_le_min
              (Nat.succ_pos j.1) hlambda
  · intro j hj
    exact htermfinite j

/-- The union sum is bounded by the number of positive prefixes times the
tail at the full list length. -/
theorem geom2PNatListPMF_prefixBad_le_nat_mul
    {n : ℕ} (hn : 0 < n) {lambda : ℝ} (hlambda : 0 < lambda) :
    ((geom2PNatListPMF n).toOuterMeasure
        (taoGeom2PrefixBadEvent lambda n)).toReal ≤
      (n : ℝ) *
        (2 * Real.exp
          (-min
            (lambda ^ 2 / (32 * (n : ℝ)))
            (lambda / 8))) := by
  have hsum := geom2PNatListPMF_prefixBad_le_sum n hlambda
  refine hsum.trans ?_
  calc
    (∑ j : Fin n,
        2 * Real.exp
          (-min
            (lambda ^ 2 / (32 * ((j.1 + 1 : ℕ) : ℝ)))
            (lambda / 8))) ≤
      ∑ _j : Fin n,
        2 * Real.exp
          (-min
            (lambda ^ 2 / (32 * (n : ℝ)))
            (lambda / 8)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j.1 + 1 ≤ n := by omega
      have hdenN : (0 : ℝ) < 32 * (n : ℝ) := by positivity
      have hdenJ : (0 : ℝ) < 32 * ((j.1 + 1 : ℕ) : ℝ) := by positivity
      have hden :
          32 * (((j.1 + 1 : ℕ) : ℝ)) ≤ 32 * (n : ℝ) := by
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjn) (by norm_num)
      have hfrac :
          lambda ^ 2 / (32 * (n : ℝ)) ≤
            lambda ^ 2 / (32 * (((j.1 + 1 : ℕ) : ℝ))) := by
        rw [div_le_div_iff₀ hdenN hdenJ]
        nlinarith [sq_nonneg lambda]
      have hmin :
          min (lambda ^ 2 / (32 * (n : ℝ))) (lambda / 8) ≤
            min
              (lambda ^ 2 / (32 * (((j.1 + 1 : ℕ) : ℝ))))
              (lambda / 8) :=
        min_le_min hfrac le_rfl
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (neg_le_neg hmin)) (by norm_num)
    _ = (n : ℝ) *
        (2 * Real.exp
          (-min
            (lambda ^ 2 / (32 * (n : ℝ)))
            (lambda / 8))) := by
      simp

end

end Tao
end Erdos1135SecondScale
