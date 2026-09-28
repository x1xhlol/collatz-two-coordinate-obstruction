/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Probability.GatedSubmassPartition

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

noncomputable def taoGatedRejectedMass
    {α β : Type*} (p : PMF α) (G : α → Prop) (f : α → β) : ℝ :=
  (taoGatedOptionPMF p G f none).toReal

theorem taoGatedOptionPMF_apply_none_eq_toOuterMeasure
    {α β : Type*} (p : PMF α) (G : α → Prop) (f : α → β) :
    taoGatedOptionPMF p G f none =
      p.toOuterMeasure {a | ¬ G a} := by
  classical
  unfold taoGatedOptionPMF
  rw [← PMF.toOuterMeasure_apply_singleton]
  rw [PMF.toOuterMeasure_map_apply]
  congr 1
  ext a
  simp [taoGatedOptionKey]

theorem taoGatedRejectedMass_eq_toOuterMeasure
    {α β : Type*} (p : PMF α) (G : α → Prop) (f : α → β) :
    taoGatedRejectedMass p G f =
      (p.toOuterMeasure {a | ¬ G a}).toReal := by
  unfold taoGatedRejectedMass
  rw [taoGatedOptionPMF_apply_none_eq_toOuterMeasure]

theorem taoGatedRejectedMass_nonneg
    {α β : Type*} (p : PMF α) (G : α → Prop) (f : α → β) :
    0 ≤ taoGatedRejectedMass p G f :=
  ENNReal.toReal_nonneg

theorem taoGatedRejectedMass_mono
    {α β : Type*} (p : PMF α) {E G : α → Prop} (f : α → β)
    (hEG : ∀ a, E a → G a) :
    taoGatedRejectedMass p G f ≤ taoGatedRejectedMass p E f := by
  unfold taoGatedRejectedMass
  apply ENNReal.toReal_mono
    ((taoGatedOptionPMF p E f).apply_ne_top none)
  rw [taoGatedOptionPMF_apply_none_eq_toOuterMeasure]
  rw [taoGatedOptionPMF_apply_none_eq_toOuterMeasure]
  apply p.toOuterMeasure.mono
  intro a ha hEa
  exact ha (hEG a hEa)

theorem taoGatedSubmass_true_eq_map_apply_toReal
    {α β : Type*} (p : PMF α) (f : α → β) (y : β) :
    taoGatedSubmass p (fun _ => True) f y = ((p.map f) y).toReal := by
  unfold taoGatedSubmass
  congr 1
  rw [taoGatedOptionPMF_apply_some_eq_toOuterMeasure]
  rw [← PMF.toOuterMeasure_apply_singleton]
  rw [PMF.toOuterMeasure_map_apply]
  congr 1
  ext a
  simp

theorem taoGatedSubmass_map_apply_split
    {α β : Type*} (p : PMF α) (G : α → Prop) (f : α → β) (y : β) :
    ((p.map f) y).toReal =
      taoGatedSubmass p G f y +
        taoGatedSubmass p (fun a => ¬ G a) f y := by
  classical
  let H : Bool → α → Prop := fun b a => if b then G a else ¬ G a
  have hdisjoint :
      ∀ i ∈ (Finset.univ : Finset Bool),
        ∀ j ∈ (Finset.univ : Finset Bool), i ≠ j →
          ∀ a, H i a → H j a → False := by
    intro i hi j hj hij a hia hja
    cases i <;> cases j
    · exact hij rfl
    · exact hia hja
    · exact hja hia
    · exact hij rfl
  have hunion :
      (fun a => ∃ i ∈ (Finset.univ : Finset Bool), H i a) =
        fun _ => True := by
    funext a
    apply propext
    constructor
    · intro _ha
      trivial
    · intro _ha
      by_cases hGa : G a
      · exact ⟨true, by simp [H, hGa]⟩
      · exact ⟨false, by simp [H, hGa]⟩
  have hpartition :=
    taoGatedSubmass_finset_union_eq_sum
      p (Finset.univ : Finset Bool) H f hdisjoint y
  rw [hunion, taoGatedSubmass_true_eq_map_apply_toReal] at hpartition
  simpa [H, add_comm] using hpartition

theorem taoGatedSubmass_sum_add_rejected_eq_one
    {α β : Type*} [Fintype β]
    (p : PMF α) (G : α → Prop) (f : α → β) :
    (∑ y, taoGatedSubmass p G f y) + taoGatedRejectedMass p G f = 1 := by
  have hsum := pmf_sum_toReal (taoGatedOptionPMF p G f)
  rw [Fintype.sum_option] at hsum
  simpa [taoGatedSubmass, taoGatedRejectedMass, add_comm] using hsum

theorem taoGatedSubmass_complement_sum_eq_rejectedMass
    {α β : Type*} [Fintype β]
    (p : PMF α) (G : α → Prop) (f : α → β) :
    (∑ y, taoGatedSubmass p (fun a => ¬ G a) f y) =
      taoGatedRejectedMass p G f := by
  have hmap : (∑ y, ((p.map f) y).toReal) = 1 := pmf_sum_toReal (p.map f)
  have hsplit :
      (∑ y, ((p.map f) y).toReal) =
        (∑ y, taoGatedSubmass p G f y) +
          ∑ y, taoGatedSubmass p (fun a => ¬ G a) f y := by
    calc
      (∑ y, ((p.map f) y).toReal) =
          ∑ y, (taoGatedSubmass p G f y +
            taoGatedSubmass p (fun a => ¬ G a) f y) := by
              apply Finset.sum_congr rfl
              intro y hy
              exact taoGatedSubmass_map_apply_split p G f y
      _ = (∑ y, taoGatedSubmass p G f y) +
          ∑ y, taoGatedSubmass p (fun a => ¬ G a) f y := by
            rw [Finset.sum_add_distrib]
  have htotal := taoGatedSubmass_sum_add_rejected_eq_one p G f
  linarith

end

end Tao

end Erdos1135Predecessor
