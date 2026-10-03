import NativeSyracuseClockBridge
import ShortcutOddEndpoints
import Mathlib.Dynamics.PeriodicPts.Defs

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CollatzCanonical.PeriodicCensusFloor

open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.NativeTao Erdos1135

theorem odd_shortcut_periodic_syracuse_periodic {q : ℕ} (hq : Odd q)
    (hp : ∃ r : ℕ, 0 < r ∧ iterate r q = q) :
    ∃ r : ℕ, 0 < r ∧ (Tao.syracuse^[r]) q = q := by
  obtain ⟨r, hr, he⟩ := hp
  obtain ⟨j, hj⟩ := shortcut_odd_endpoint_is_syracuse_clock r q hq
    (by simpa only [he] using hq)
  have hjp : 0 < j := by
    by_contra hn
    have hz : j = 0 := by omega
    simp [hz, Tao.syracuseValuationPNatList, Tao.taoTupleWeight] at hj
    omega
  refine ⟨j, hjp, ?_⟩
  rw [← syracuse_shortcut_landing j q hq, ← hj]
  exact he

theorem odd_periodic_syracuse_injective {q r : ℕ} (hq : Odd q) (hr : Odd r)
    (hqp : ∃ k : ℕ, 0 < k ∧ iterate k q = q)
    (hrp : ∃ k : ℕ, 0 < k ∧ iterate k r = r)
    (he : Tao.syracuse q = Tao.syracuse r) : q = r := by
  obtain ⟨i, hi, hqi⟩ := odd_shortcut_periodic_syracuse_periodic hq hqp
  obtain ⟨j, hj, hrj⟩ := odd_shortcut_periodic_syracuse_periodic hr hrp
  exact Function.IsPeriodicPt.eq_of_apply_eq hqi hrj hi hj he

theorem syracuse_of_power_relation {q y a : ℕ} (hy : Odd y)
    (he : 3 * q + 1 = 2 ^ a * y) :
    Tao.syracuse q = y ∧ Tao.syracuseExponent q = a := by
  have hnd : ¬ 2 ∣ y := by
    exact fun hd => (Nat.not_even_iff_odd.mpr hy) (even_iff_two_dvd.mpr hd)
  have hyp : 0 < y := by obtain ⟨u, hu⟩ := hy; omega
  constructor
  · rw [Tao.syracuse_eq_ordCompl_two, he]
    exact Nat.ordCompl_pow_mul_of_not_dvd a Nat.prime_two hnd
  · unfold Tao.syracuseExponent Terras.twoAdicExponent
    rw [he, Nat.factorization_mul (pow_ne_zero a (by decide)) hyp.ne']
    simp [Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hnd]

theorem exists_short_inverse_syracuse {y : ℕ} (hy : Odd y) (hy3 : y % 3 ≠ 0) :
    ∃ q a : ℕ, Odd q ∧ 0 < a ∧ a ≤ 2 ∧ 3 * q + 1 = 2 ^ a * y := by
  have hyp : 0 < y := by obtain ⟨u, hu⟩ := hy; omega
  have hyodd : y % 2 = 1 := Nat.odd_iff.mp hy
  rcases (show y % 3 = 1 ∨ y % 3 = 2 by omega) with h1 | h2
  · refine ⟨(4 * y - 1) / 3, 2, ?_, by decide, by decide, ?_⟩
    · apply Nat.odd_iff.mpr
      omega
    · norm_num
      omega
  · refine ⟨(2 * y - 1) / 3, 1, ?_, by decide, by decide, ?_⟩
    · apply Nat.odd_iff.mpr
      omega
    · norm_num
      omega

theorem exists_two_short_unit_syracuse_predecessors {y : ℕ}
    (hy : Odd y) (hy3 : y % 3 ≠ 0) :
    ∃ q r : ℕ, q ≠ r ∧ Odd q ∧ q % 3 ≠ 0 ∧ Tao.syracuse q = y ∧
      Tao.syracuseExponent q ≤ 6 ∧ Odd r ∧ r % 3 ≠ 0 ∧
      Tao.syracuse r = y ∧ Tao.syracuseExponent r ≤ 6 := by
  obtain ⟨q, a, hq, hap, ha, he⟩ := exists_short_inverse_syracuse hy hy3
  have hqp : 0 < q := by obtain ⟨u, hu⟩ := hq; omega
  have hq1 : Odd (4 * q + 1) := by apply Nat.odd_iff.mpr; omega
  have hq2 : Odd (16 * q + 5) := by apply Nat.odd_iff.mpr; omega
  have he1 : 3 * (4 * q + 1) + 1 = 2 ^ (a + 2) * y := by
    rw [pow_add]
    norm_num
    nlinarith [he]
  have he2 : 3 * (16 * q + 5) + 1 = 2 ^ (a + 4) * y := by
    rw [pow_add]
    norm_num
    nlinarith [he]
  obtain ⟨hs, hex⟩ := syracuse_of_power_relation hy he
  obtain ⟨hs1, hex1⟩ := syracuse_of_power_relation hy he1
  obtain ⟨hs2, hex2⟩ := syracuse_of_power_relation hy he2
  by_cases hq3 : q % 3 = 0
  · refine ⟨4 * q + 1, 16 * q + 5, by omega, hq1, by omega, hs1,
      by omega, hq2, by omega, hs2, by omega⟩
  · by_cases hq13 : (4 * q + 1) % 3 = 0
    · refine ⟨q, 16 * q + 5, by omega, hq, hq3, hs, by omega,
        hq2, by omega, hs2, by omega⟩
    · exact ⟨q, 4 * q + 1, by omega, hq, hq3, hs, by omega,
        hq1, hq13, hs1, by omega⟩

/-- One of the first three inverse Syracuse branches is a unit nonperiodic leaf. -/
theorem exists_short_unit_nonperiodic_syracuse_predecessor {y : ℕ}
    (hy : Odd y) (hy3 : y % 3 ≠ 0) :
    ∃ q : ℕ, 0 < q ∧ Odd q ∧ q % 3 ≠ 0 ∧ Tao.syracuse q = y ∧
      Tao.syracuseExponent q ≤ 6 ∧
      ¬ ∃ k : ℕ, 0 < k ∧ iterate k q = q := by
  classical
  obtain ⟨q, r, hqr, hq, hq3, hqs, hqa, hr, hr3, hrs, hra⟩ :=
    exists_two_short_unit_syracuse_predecessors hy hy3
  have hqp : 0 < q := by obtain ⟨u, hu⟩ := hq; omega
  have hrp : 0 < r := by obtain ⟨u, hu⟩ := hr; omega
  by_cases hper : ∃ k : ℕ, 0 < k ∧ iterate k q = q
  · refine ⟨r, hrp, hr, hr3, hrs, hra, ?_⟩
    intro hrper
    exact hqr (odd_periodic_syracuse_injective hq hr hper hrper (hqs.trans hrs.symm))
  · exact ⟨q, hqp, hq, hq3, hqs, hqa, hper⟩

#print axioms odd_shortcut_periodic_syracuse_periodic
#print axioms odd_periodic_syracuse_injective
#print axioms syracuse_of_power_relation
#print axioms exists_short_inverse_syracuse
#print axioms exists_two_short_unit_syracuse_predecessors
#print axioms exists_short_unit_nonperiodic_syracuse_predecessor

end CollatzCanonical.PeriodicCensusFloor
