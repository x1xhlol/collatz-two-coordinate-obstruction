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

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable def taoGatedOptionKey
    {α β : Type*} (G : α → Prop) (f : α → β) : α → Option β := by
  classical
  exact fun a => if G a then some (f a) else none

noncomputable def taoGatedOptionPMF
    {α β : Type*} (p : PMF α) (G : α → Prop) (f : α → β) :
    PMF (Option β) :=
  p.map (taoGatedOptionKey G f)

noncomputable def taoGatedSubmass
    {α β : Type*} (p : PMF α) (G : α → Prop) (f : α → β)
    (y : β) : ℝ :=
  (taoGatedOptionPMF p G f (some y)).toReal

@[simp]
theorem taoGatedOptionKey_eq_some_iff
    {α β : Type*} (G : α → Prop) (f : α → β) (a : α) (y : β) :
    taoGatedOptionKey G f a = some y ↔ G a ∧ f a = y := by
  classical
  by_cases hG : G a <;> simp [taoGatedOptionKey, hG]

theorem taoGatedSubmass_nonneg
    {α β : Type*} (p : PMF α) (G : α → Prop) (f : α → β)
    (y : β) :
    0 ≤ taoGatedSubmass p G f y :=
  ENNReal.toReal_nonneg

theorem taoGatedSubmass_sum_le_one
    {α β : Type*} [Fintype β]
    (p : PMF α) (G : α → Prop) (f : α → β) :
    (∑ y, taoGatedSubmass p G f y) ≤ 1 := by
  classical
  have hsum := pmf_sum_toReal (taoGatedOptionPMF p G f)
  rw [Fintype.sum_option] at hsum
  have hnone :
      0 ≤ (taoGatedOptionPMF p G f none).toReal :=
    ENNReal.toReal_nonneg
  unfold taoGatedSubmass
  linarith

theorem taoGatedSubmass_le_of_injOn
    {α β : Type*} (p : PMF α) (G : α → Prop) (f : α → β)
    {w : ℝ} (hw : 0 ≤ w)
    (hinj : Set.InjOn f {a | G a})
    (hatom : ∀ a, G a → (p a).toReal ≤ w)
    (y : β) :
    taoGatedSubmass p G f y ≤ w := by
  classical
  by_cases hfiber : ∃ a, taoGatedOptionKey G f a = some y
  · obtain ⟨a, ha⟩ := hfiber
    have ha_data := (taoGatedOptionKey_eq_some_iff G f a y).mp ha
    have hmap : taoGatedOptionPMF p G f (some y) = p a := by
      unfold taoGatedOptionPMF
      rw [PMF.map_apply]
      rw [tsum_eq_single a]
      · rw [if_pos ha.symm]
      · intro a' ha_ne
        by_cases ha' : some y = taoGatedOptionKey G f a'
        · have ha'_data :=
            (taoGatedOptionKey_eq_some_iff G f a' y).mp ha'.symm
          have haa : a' = a :=
            hinj ha'_data.1 ha_data.1
              (ha'_data.2.trans ha_data.2.symm)
          exact (ha_ne haa).elim
        · simp [ha']
    unfold taoGatedSubmass
    rw [hmap]
    exact hatom a ha_data.1
  · have hzero : taoGatedOptionPMF p G f (some y) = 0 := by
      unfold taoGatedOptionPMF
      rw [PMF.map_apply, ENNReal.tsum_eq_zero]
      intro a
      have hne : ¬ some y = taoGatedOptionKey G f a := by
        intro ha
        exact hfiber ⟨a, ha.symm⟩
      simp [hne]
    unfold taoGatedSubmass
    rw [hzero]
    simpa using hw

theorem taoGatedSubmass_sum_sq_le
    {α β : Type*} [Fintype β]
    (p : PMF α) (G : α → Prop) (f : α → β)
    {w : ℝ} (hw : 0 ≤ w)
    (hinj : Set.InjOn f {a | G a})
    (hatom : ∀ a, G a → (p a).toReal ≤ w) :
    (∑ y, (taoGatedSubmass p G f y) ^ 2) ≤ w := by
  classical
  calc
    (∑ y, (taoGatedSubmass p G f y) ^ 2) ≤
        ∑ y, w * taoGatedSubmass p G f y := by
      apply Finset.sum_le_sum
      intro y _hy
      simpa [pow_two] using
        mul_le_mul_of_nonneg_right
          (taoGatedSubmass_le_of_injOn p G f hw hinj hatom y)
          (taoGatedSubmass_nonneg p G f y)
    _ = w * ∑ y, taoGatedSubmass p G f y := by
      rw [Finset.mul_sum]
    _ ≤ w * 1 :=
      mul_le_mul_of_nonneg_left (taoGatedSubmass_sum_le_one p G f) hw
    _ = w := by ring

theorem taoGatedSubmass_false_eq_zero
    {α β : Type*} (p : PMF α) (f : α → β) (y : β) :
    taoGatedSubmass p (fun _ => False) f y = 0 := by
  classical
  unfold taoGatedSubmass taoGatedOptionPMF
  rw [PMF.map_apply]
  simp [taoGatedOptionKey]

theorem taoGatedSubmass_eq_zero_of_not_exists_gate
    {α β : Type*} (p : PMF α) (G : α → Prop) (f : α → β)
    (hG : ¬ ∃ a, G a) (y : β) :
    taoGatedSubmass p G f y = 0 := by
  have hfalse : G = fun _ => False := by
    funext a
    apply propext
    constructor
    · intro ha
      exact (hG ⟨a, ha⟩).elim
    · intro ha
      exact ha.elim
  rw [hfalse]
  exact taoGatedSubmass_false_eq_zero p f y

end Tao

end Erdos1135Predecessor
