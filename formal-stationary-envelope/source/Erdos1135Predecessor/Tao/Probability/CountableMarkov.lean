/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Probability.Finite

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

noncomputable def taoPMFENNExpectation
    {α : Type*} (p : PMF α) (F : α → ENNReal) : ENNReal :=
  ∑' a, p a * F a

theorem taoPMFENNExpectation_map
    {α β : Type*} (p : PMF α) (f : α → β) (G : β → ENNReal) :
    taoPMFENNExpectation (p.map f) G =
      taoPMFENNExpectation p (G ∘ f) := by
  classical
  unfold taoPMFENNExpectation
  calc
    (∑' b, (p.map f) b * G b) =
        ∑' b, (∑' a, if b = f a then p a else 0) * G b := by
      apply tsum_congr
      intro b
      rw [PMF.map_apply]
    _ = ∑' b, ∑' a, (if b = f a then p a else 0) * G b := by
      apply tsum_congr
      intro b
      rw [ENNReal.tsum_mul_right]
    _ = ∑' a, ∑' b, (if b = f a then p a else 0) * G b := by
      rw [ENNReal.tsum_comm]
    _ = ∑' a, p a * G (f a) := by
      apply tsum_congr
      intro a
      rw [tsum_eq_single (f a)]
      · simp
      · intro b hba
        simp [hba]
    _ = ∑' a, p a * (G ∘ f) a := by rfl

theorem taoPMFENNExpectation_bind
    {α β : Type*} (p : PMF α) (q : α → PMF β) (G : β → ENNReal) :
    taoPMFENNExpectation (p.bind q) G =
      ∑' a, p a * taoPMFENNExpectation (q a) G := by
  classical
  unfold taoPMFENNExpectation
  calc
    (∑' b, (p.bind q) b * G b) =
        ∑' b, (∑' a, p a * q a b) * G b := by
      apply tsum_congr
      intro b
      rw [PMF.bind_apply]
    _ = ∑' b, ∑' a, (p a * q a b) * G b := by
      apply tsum_congr
      intro b
      rw [ENNReal.tsum_mul_right]
    _ = ∑' a, ∑' b, (p a * q a b) * G b := by
      rw [ENNReal.tsum_comm]
    _ = ∑' a, p a * ∑' b, q a b * G b := by
      apply tsum_congr
      intro a
      calc
        (∑' b, (p a * q a b) * G b) =
            ∑' b, p a * (q a b * G b) := by
          apply tsum_congr
          intro b
          ac_rfl
        _ = p a * ∑' b, q a b * G b := ENNReal.tsum_mul_left

theorem taoPMFENNExpectation_mul_const
    {α : Type*} (p : PMF α) (F : α → ENNReal) (C : ENNReal) :
    taoPMFENNExpectation p (fun a => F a * C) =
      taoPMFENNExpectation p F * C := by
  unfold taoPMFENNExpectation
  calc
    (∑' a, p a * (F a * C)) = ∑' a, (p a * F a) * C := by
      apply tsum_congr
      intro a
      ac_rfl
    _ = (∑' a, p a * F a) * C := ENNReal.tsum_mul_right

theorem taoPMFENNExpectation_indicator_one_eq_toOuterMeasure
    {α : Type*} (p : PMF α) (E : Set α) :
    taoPMFENNExpectation p (E.indicator fun _ => 1) =
      p.toOuterMeasure E := by
  classical
  unfold taoPMFENNExpectation
  rw [PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ E <;> simp [Set.indicator, ha]

theorem tao_pmfToOuterMeasure_gt_mul_le_expectation
    {α : Type*} (p : PMF α) (F : α → ENNReal) (cutoff : ENNReal) :
    p.toOuterMeasure {a | cutoff < F a} * cutoff ≤
      taoPMFENNExpectation p F := by
  let E : Set α := {a | cutoff < F a}
  rw [← taoPMFENNExpectation_indicator_one_eq_toOuterMeasure]
  rw [← taoPMFENNExpectation_mul_const]
  unfold taoPMFENNExpectation
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : a ∈ E
  · have hcut : cutoff ≤ F a := le_of_lt ha
    have hmem : cutoff < F a := by simpa [E] using ha
    simp only [Set.indicator, Set.mem_setOf_eq, hmem, if_true, one_mul]
    exact mul_le_mul_right hcut _
  · have hnot : ¬ cutoff < F a := by simpa [E] using ha
    simp [Set.indicator, hnot]

end

end Tao

end Erdos1135Predecessor
