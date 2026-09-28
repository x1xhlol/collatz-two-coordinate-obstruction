import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic.Linarith

/-!
# One-Time PMF Complement Charges

This neutral leaf compares two arbitrary events that agree after intersection
with one gate.  Their mass discrepancy costs the rejected mass once, with
coefficient one and no finiteness assumption on the carrier.
-/

namespace Erdos1135
namespace ND

/-- If two events agree on a gate, their PMF masses differ by at most the
mass outside that gate. -/
theorem abs_pmfOuterMass_sub_le_compl_of_inter_eq
    {α : Type*} (p : PMF α) {A D G : Set α}
    (hAD : A ∩ G = D ∩ G) :
    |(p.toOuterMeasure A).toReal -
        (p.toOuterMeasure D).toReal| ≤
      (p.toOuterMeasure Gᶜ).toReal := by
  have huniv : p.toOuterMeasure Set.univ = 1 :=
    (p.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
  have hfinite (S : Set α) : p.toOuterMeasure S ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      p.toOuterMeasure S ≤ p.toOuterMeasure Set.univ :=
        p.toOuterMeasure.mono (Set.subset_univ S)
      _ = 1 := huniv
  have hA : A ⊆ D ∪ Gᶜ := by
    intro x hxA
    by_cases hxG : x ∈ G
    · left
      have hxDG : x ∈ D ∩ G := by
        rw [← hAD]
        exact ⟨hxA, hxG⟩
      exact hxDG.1
    · exact Or.inr hxG
  have hD : D ⊆ A ∪ Gᶜ := by
    intro x hxD
    by_cases hxG : x ∈ G
    · left
      have hxAG : x ∈ A ∩ G := by
        rw [hAD]
        exact ⟨hxD, hxG⟩
      exact hxAG.1
    · exact Or.inr hxG
  have hADEnn :
      p.toOuterMeasure A ≤
        p.toOuterMeasure D + p.toOuterMeasure Gᶜ :=
    (p.toOuterMeasure.mono hA).trans
      (MeasureTheory.measure_union_le (μ := p.toOuterMeasure) D Gᶜ)
  have hDAEnn :
      p.toOuterMeasure D ≤
        p.toOuterMeasure A + p.toOuterMeasure Gᶜ :=
    (p.toOuterMeasure.mono hD).trans
      (MeasureTheory.measure_union_le (μ := p.toOuterMeasure) A Gᶜ)
  have hADReal :
      (p.toOuterMeasure A).toReal ≤
        (p.toOuterMeasure D + p.toOuterMeasure Gᶜ).toReal :=
    ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hfinite D, hfinite Gᶜ⟩) hADEnn
  have hDAReal :
      (p.toOuterMeasure D).toReal ≤
        (p.toOuterMeasure A + p.toOuterMeasure Gᶜ).toReal :=
    ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hfinite A, hfinite Gᶜ⟩) hDAEnn
  rw [ENNReal.toReal_add (hfinite D) (hfinite Gᶜ)] at hADReal
  rw [ENNReal.toReal_add (hfinite A) (hfinite Gᶜ)] at hDAReal
  rw [abs_le]
  constructor <;> linarith

end ND
end Erdos1135
