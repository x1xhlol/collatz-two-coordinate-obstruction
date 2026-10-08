import Mathlib.Data.Finset.Max
import Mathlib.Tactic

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic.FairEnergy

theorem nat_card_mul_succ_le_twice_sum (s : Finset ℕ) :
    s.card * (s.card + 1) ≤ 2 * ∑ n ∈ s, (n + 1) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have ha : a ∉ s := fun h => (Nat.lt_irrefl a) (hmax a h)
    have hc : s.card ≤ a := by
      calc
        s.card ≤ (Finset.range a).card :=
          Finset.card_le_card (fun n hn => Finset.mem_range.mpr (hmax n hn))
        _ = a := Finset.card_range a
    rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    nlinarith

theorem card_sq_le_twice_quotient_weight {ι : Type*} (s : Finset ι)
    (q : ι → ℕ) (Y : ι → ℝ)
    (hinj : Set.InjOn q (↑s : Set ι))
    (hqY : ∀ w ∈ s, (q w : ℝ) ≤ Y w) :
    (s.card : ℝ) ^ 2 ≤ 2 * ∑ w ∈ s, (1 + Y w) := by
  classical
  have hn : (s.image q).card ^ 2 ≤ 2 * ∑ n ∈ s.image q, (n + 1) := by
    have h := nat_card_mul_succ_le_twice_sum (s.image q)
    nlinarith
  have hr : ((s.image q).card : ℝ) ^ 2 ≤
      2 * ∑ n ∈ s.image q, ((n : ℝ) + 1) := by
    exact_mod_cast hn
  rw [Finset.card_image_of_injOn hinj, Finset.sum_image hinj] at hr
  exact hr.trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun w hw => by linarith [hqY w hw]) (by norm_num))

end CollatzCylinderPacking.Arithmetic.FairEnergy
