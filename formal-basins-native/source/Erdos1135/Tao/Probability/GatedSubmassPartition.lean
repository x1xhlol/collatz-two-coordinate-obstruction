import Erdos1135.Tao.Probability.GatedSubmass

/-!
# Finite Partitions of Gated Submasses

This generic leaf identifies accepted atoms with native source-fiber mass and
proves finite additivity for pairwise-disjoint source gates.  The source type
may be infinite; conversion to `ℝ` occurs only after the finite `ENNReal`
identity is established.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

/-- Native finite additivity for a pairwise-disjoint finite family of source
sets.  The source type may be infinite; the proof passes through the discrete
measure associated to the PMF before returning to its outer measure. -/
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

/-- A gated accepted atom is exactly the native mass of its source fiber. -/
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

/-- Native finite additivity for a pairwise-disjoint family of gates. -/
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

/-- Real-valued finite additivity, obtained only after the native equality. -/
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

/-- A singleton source gate contributes its source atom exactly at the mapped
target and zero at every other target. -/
theorem taoGatedSubmass_singleton_gate_apply
    {α β : Type*} [DecidableEq β]
    (p : PMF α) (a₀ : α) (f : α → β) (y : β) :
    taoGatedSubmass p (fun a => a = a₀) f y =
      if y = f a₀ then (p a₀).toReal else 0 := by
  classical
  by_cases hy : y = f a₀
  · subst y
    rw [if_pos rfl]
    exact taoGatedSubmass_singleton_gate p a₀ f
  · rw [if_neg hy]
    unfold taoGatedSubmass
    rw [taoGatedOptionPMF_apply_some_eq_toOuterMeasure]
    have hempty : {a : α | a = a₀ ∧ f a = y} = ∅ := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨rfl, hfy⟩
      exact hy hfy.symm
    rw [hempty]
    simp

/-- A finite weighted source sum is exactly the weighted accepted target
submass for the corresponding finite membership gate. -/
theorem sum_mul_taoGatedSubmass_mem_eq
    {α β : Type*} [Fintype β]
    (p : PMF α) (I : Finset α) (f : α → β) (c : β → ℝ) :
    (∑ a ∈ I, (p a).toReal * c (f a)) =
      ∑ y : β, c y * taoGatedSubmass p (fun a => a ∈ I) f y := by
  classical
  let G : α → α → Prop := fun a₀ a => a = a₀
  have hdisjoint :
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ∀ a, G i a → G j a → False := by
    intro i _hi j _hj hij a hai haj
    exact hij (hai.symm.trans haj)
  have hgate :
      (fun a => ∃ i ∈ I, G i a) = fun a => a ∈ I := by
    funext a
    apply propext
    simp [G]
  have hpartition (y : β) :
      taoGatedSubmass p (fun a => a ∈ I) f y =
        ∑ a ∈ I, taoGatedSubmass p (G a) f y := by
    simpa only [hgate] using
      taoGatedSubmass_finset_union_eq_sum p I G f hdisjoint y
  calc
    (∑ a ∈ I, (p a).toReal * c (f a)) =
        ∑ a ∈ I, ∑ y : β,
          c y * taoGatedSubmass p (G a) f y := by
      apply Finset.sum_congr rfl
      intro a _ha
      simp only [G, taoGatedSubmass_singleton_gate_apply]
      simp
      ring
    _ = ∑ y : β, ∑ a ∈ I,
          c y * taoGatedSubmass p (G a) f y := by
      rw [Finset.sum_comm]
    _ = ∑ y : β, c y * ∑ a ∈ I,
          taoGatedSubmass p (G a) f y := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.mul_sum]
    _ = ∑ y : β, c y *
          taoGatedSubmass p (fun a => a ∈ I) f y := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [hpartition]

end

end Tao
end Erdos1135
