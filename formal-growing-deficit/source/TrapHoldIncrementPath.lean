import TrapHoldIncrementBounds
import Erdos1135.Tao.Renewal.RenewalPathBasic

/-! Translating bounds on each Hold increment to the literal finite path. -/

set_option autoImplicit false

namespace Erdos1135.Tao

theorem trap_hold_path_step_is_increment
    (start : TaoSection7RenewalPoint) (full : List TaoSection7RenewalPoint)
    (q : ℕ) (hq : q < full.length) :
    ∃ h ∈ full, taoSection7RenewalPathPoint start full (q + 1) =
      taoSection7RenewalPathPoint start full q + h := by
  induction q generalizing start full with
  | zero =>
      cases full with
      | nil => simp at hq
      | cons h hs => exact ⟨h, by simp, by simp⟩
  | succ q ih =>
      cases full with
      | nil => simp at hq
      | cons h hs =>
          obtain ⟨next, hnext, heq⟩ := ih (start + h) hs (by simpa using hq)
          exact ⟨next, by simp [hnext], heq⟩

theorem trap_hold_increment_bounds_path
    (H : ℕ) (V : ℝ) (start : TaoSection7RenewalPoint)
    (full : List TaoSection7RenewalPoint)
    (hgood : ∀ h ∈ full, TrapHoldIncrementGood (H : ℝ) V h) :
    ∀ q < full.length,
      ((taoSection7RenewalPathPoint start full (q + 1)).j : ℕ) ≤
        (taoSection7RenewalPathPoint start full q).j + H ∧
      (taoSection7RenewalPathPoint start full q).l ≤
        (taoSection7RenewalPathPoint start full (q + 1)).l ∧
      ((taoSection7RenewalPathPoint start full (q + 1)).l : ℝ) ≤
        (taoSection7RenewalPathPoint start full q).l + V := by
  intro q hq
  obtain ⟨h, hmem, heq⟩ := trap_hold_path_step_is_increment start full q hq
  obtain ⟨hl, hj, hv⟩ := hgood h hmem
  have hjNat : (h.j : ℕ) ≤ H := by exact_mod_cast hj
  rw [heq]
  simp only [TaoSection7RenewalPoint.add_j, PNat.add_coe,
    TaoSection7RenewalPoint.add_l, Int.cast_add]
  exact ⟨Nat.add_le_add_left hjNat _, by omega, add_le_add le_rfl hv⟩

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_hold_increment_bounds_path
