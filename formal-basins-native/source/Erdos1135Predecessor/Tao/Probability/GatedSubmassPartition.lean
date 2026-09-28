/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Probability.GatedSubmass

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

theorem taoPMFToOuterMeasure_biUnion_finset_eq_sum
    {ι α : Type*} [DecidableEq ι]
    (p : PMF α) (I : Finset ι) (F : ι → Set α)
    (hdisjoint : Set.PairwiseDisjoint (I : Set ι) F) :
    p.toOuterMeasure (⋃ i ∈ I, F i) =
      ∑ i ∈ I, p.toOuterMeasure (F i) := by
  classical
  letI : MeasurableSpace α := ⊤
  have hmeasure :
      p.toMeasure (⋃ i ∈ I, F i) = ∑ i ∈ I, p.toMeasure (F i) :=
    MeasureTheory.measure_biUnion_finset hdisjoint (by simp)
  calc
    p.toOuterMeasure (⋃ i ∈ I, F i) =
        p.toMeasure (⋃ i ∈ I, F i) := by
      symm
      exact p.toMeasure_apply_eq_toOuterMeasure_apply (by simp)
    _ = ∑ i ∈ I, p.toMeasure (F i) := hmeasure
    _ = ∑ i ∈ I, p.toOuterMeasure (F i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact p.toMeasure_apply_eq_toOuterMeasure_apply (by simp)

theorem taoGatedOptionPMF_apply_some_eq_toOuterMeasure
    {α β : Type*} (p : PMF α) (G : α → Prop) (f : α → β) (y : β) :
    taoGatedOptionPMF p G f (some y) =
      p.toOuterMeasure {a | G a ∧ f a = y} := by
  classical
  unfold taoGatedOptionPMF
  rw [← PMF.toOuterMeasure_apply_singleton]
  rw [PMF.toOuterMeasure_map_apply]
  congr 1
  ext a
  simp [taoGatedOptionKey_eq_some_iff]

theorem taoGatedOptionPMF_finset_union_apply_some
    {ι α β : Type*} [DecidableEq ι]
    (p : PMF α) (I : Finset ι) (G : ι → α → Prop) (f : α → β)
    (hdisjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ∀ a, G i a → G j a → False)
    (y : β) :
    taoGatedOptionPMF p (fun a => ∃ i ∈ I, G i a) f (some y) =
      ∑ i ∈ I, taoGatedOptionPMF p (G i) f (some y) := by
  classical
  let F : ι → Set α := fun i => {a | G i a ∧ f a = y}
  have hpair : Set.PairwiseDisjoint (I : Set ι) F := by
    intro i hi j hj hij
    change Disjoint (F i) (F j)
    rw [Set.disjoint_left]
    intro a hai haj
    exact hdisjoint i hi j hj hij a hai.1 haj.1
  have hunion :
      {a | (∃ i ∈ I, G i a) ∧ f a = y} = ⋃ i ∈ I, F i := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, F]
    aesop
  have houter :
      p.toOuterMeasure (⋃ i ∈ I, F i) =
        ∑ i ∈ I, p.toOuterMeasure (F i) :=
    taoPMFToOuterMeasure_biUnion_finset_eq_sum p I F hpair
  rw [taoGatedOptionPMF_apply_some_eq_toOuterMeasure]
  simp_rw [taoGatedOptionPMF_apply_some_eq_toOuterMeasure]
  rw [hunion, houter]

theorem taoGatedSubmass_finset_union_eq_sum
    {ι α β : Type*} [DecidableEq ι]
    (p : PMF α) (I : Finset ι) (G : ι → α → Prop) (f : α → β)
    (hdisjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ∀ a, G i a → G j a → False)
    (y : β) :
    taoGatedSubmass p (fun a => ∃ i ∈ I, G i a) f y =
      ∑ i ∈ I, taoGatedSubmass p (G i) f y := by
  unfold taoGatedSubmass
  rw [taoGatedOptionPMF_finset_union_apply_some p I G f hdisjoint y]
  rw [ENNReal.toReal_sum]
  intro i hi
  exact (taoGatedOptionPMF p (G i) f).apply_ne_top (some y)

end

end Tao

end Erdos1135Predecessor
