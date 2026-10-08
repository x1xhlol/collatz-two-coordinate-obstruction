/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageTails
import Mathlib.Tactic

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Lemma77

theorem pmf_compl_union_toReal_ge_half
    {α : Type*} (p : PMF α) (H V : Set α)
    (hH : (p.toOuterMeasure H).toReal ≤ 1 / 4)
    (hV : (p.toOuterMeasure V).toReal ≤ 1 / 4) :
    (1 / 2 : ℝ) ≤ (p.toOuterMeasure ((H ∪ V)ᶜ)).toReal := by
  have huniv : p.toOuterMeasure Set.univ = 1 :=
    (p.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
  have hfinite (E : Set α) : p.toOuterMeasure E ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      p.toOuterMeasure E ≤ p.toOuterMeasure Set.univ :=
        p.toOuterMeasure.mono (Set.subset_univ E)
      _ = 1 := huniv
  have hbad : (p.toOuterMeasure (H ∪ V)).toReal ≤ 1 / 2 := by
    have hu := MeasureTheory.measure_union_le (μ := p.toOuterMeasure) H V
    have hu' :
        (p.toOuterMeasure (H ∪ V)).toReal ≤
          (p.toOuterMeasure H + p.toOuterMeasure V).toReal :=
      ENNReal.toReal_mono
        (ENNReal.add_ne_top.2 ⟨hfinite H, hfinite V⟩) hu
    rw [ENNReal.toReal_add (hfinite H) (hfinite V)] at hu'
    linarith
  have hcar : p.toOuterMeasure.IsCaratheodory (H ∪ V) := by
    change @MeasurableSet α p.toOuterMeasure.caratheodory (H ∪ V)
    rw [PMF.toOuterMeasure_caratheodory]
    trivial
  have hsplitENN :
      p.toOuterMeasure Set.univ =
        p.toOuterMeasure (Set.univ ∩ (H ∪ V)) +
          p.toOuterMeasure (Set.univ \ (H ∪ V)) :=
    hcar Set.univ
  have hsplit :
      1 = (p.toOuterMeasure (H ∪ V)).toReal +
        (p.toOuterMeasure ((H ∪ V)ᶜ)).toReal := by
    have h := congrArg ENNReal.toReal hsplitENN
    simpa [huniv, ENNReal.toReal_add, hfinite, Set.diff_eq] using h
  linarith

def lemma77CanonicalLocalizedEndpointEvent
    (s B : ℕ) : Set (ℕ × ℤ) :=
  {x |
    |lemma77CenteredHorizontalDisplacement s x.1| <
      (B : ℝ) * Real.sqrt (1 + (s : ℝ)) ∧
    x.2 < (s : ℤ) + (B : ℤ)}

end TaoSection7Lemma77

end

end Tao

end Erdos1135Predecessor
