import TrapNativeShortLaplace
import Erdos1135.Tao.Renewal.RenewalPathBasic

/-! Zero-inclusive white counts and horizontal monotonicity on actual finite Hold paths. -/

set_option autoImplicit false

open scoped BigOperators

namespace Erdos1135.Tao

theorem trap_qWhiteVisitCount_eq_sum_range
    (W : TaoSection7RenewalPoint → Prop) (start : TaoSection7RenewalPoint)
    (holds : List TaoSection7RenewalPoint) :
    taoSection7QWhiteVisitCount W start holds =
      ∑ q ∈ Finset.range (holds.length + 1),
        taoSection7QWhiteIndicator W (taoSection7RenewalPathPoint start holds q) := by
  induction holds generalizing start with
  | nil => simp [taoSection7QWhiteVisitCount]
  | cons h hs ih =>
      rw [taoSection7QWhiteVisitCount, List.length_cons, Finset.sum_range_succ']
      simp only [taoSection7RenewalPathPoint_cons_succ, taoSection7RenewalPathPoint_zero]
      rw [ih]
      exact Nat.add_comm _ _

theorem trap_holdPath_j_ge_start
    (start : TaoSection7RenewalPoint) (holds : List TaoSection7RenewalPoint) (q : ℕ) :
    (start.j : ℕ) ≤ (taoSection7RenewalPathPoint start holds q).j := by
  induction q generalizing start holds with
  | zero => simp
  | succ q ih =>
      cases holds with
      | nil => simp
      | cons h hs =>
          rw [taoSection7RenewalPathPoint_cons_succ]
          have htail := ih (start + h) hs
          have hbase : (start.j : ℕ) ≤ ((start + h).j : ℕ) := by
            simp only [TaoSection7RenewalPoint.add_j, PNat.add_coe]
            omega
          exact hbase.trans htail

theorem trap_holdPath_j_monotone
    (start : TaoSection7RenewalPoint) (holds : List TaoSection7RenewalPoint) :
    Monotone fun q => ((taoSection7RenewalPathPoint start holds q).j : ℕ) := by
  intro q t hqt
  have h := trap_holdPath_j_ge_start
    (taoSection7RenewalPathPoint start holds q) (holds.drop q) (t - q)
  rw [taoSection7RenewalPathPoint_drop_add, Nat.add_sub_of_le hqt] at h
  exact h

theorem trap_positive_count_le_qWhiteVisitCount
    (W : TaoSection7RenewalPoint → Prop) (start : TaoSection7RenewalPoint)
    (holds : List TaoSection7RenewalPoint) (t : ℕ) (ht : t ≤ holds.length) :
    (∑ q ∈ Finset.Icc 1 t,
      taoSection7QWhiteIndicator W (taoSection7RenewalPathPoint start holds q)) ≤
        taoSection7QWhiteVisitCount W start holds := by
  rw [trap_qWhiteVisitCount_eq_sum_range]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    have := (Finset.mem_Icc.mp hq).2
    exact Finset.mem_range.mpr (by omega)
  · intro q _ _
    exact Nat.zero_le _

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_qWhiteVisitCount_eq_sum_range
#print axioms Erdos1135.Tao.trap_holdPath_j_monotone
#print axioms Erdos1135.Tao.trap_positive_count_le_qWhiteVisitCount
