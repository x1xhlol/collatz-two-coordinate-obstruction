import SyracuseLabelInvariance
import Erdos1135.Tao.ColMin
import Erdos1135.Tao.Syracuse.CollatzBridge

set_option autoImplicit false

namespace CollatzCanonical.LabelLaw
open Erdos1135 Erdos1135.Tao

theorem ordCompl_two_eq_self_of_odd {q : ℕ} (hq : Odd q) : ordCompl[2] q = q := by
  apply (Nat.ordCompl_eq_self_iff_zero_or_not_dvd q Nat.prime_two).mpr
  exact Or.inr (fun h => (Nat.not_even_iff_odd.mpr hq) (even_iff_two_dvd.mpr h))

theorem ordCompl_two_odd {q : ℕ} (hq : 0 < q) : Odd (ordCompl[2] q) := by
  apply Nat.not_even_iff_odd.mp
  intro h
  exact Nat.not_dvd_ordCompl Nat.prime_two (by omega : q ≠ 0) (even_iff_two_dvd.mp h)

theorem ordCompl_collatzStep_of_even {q : ℕ} (hq : Even q) :
    ordCompl[2] (collatzStep q) = ordCompl[2] q := by
  rw [collatzStep_eq_div_two_of_even hq]
  exact Nat.ordCompl_div_of_dvd Nat.prime_two (even_iff_two_dvd.mp hq)

theorem ordCompl_collatzStep_of_odd {q : ℕ} (hq : Odd q) :
    ordCompl[2] (collatzStep q) = syracuse (ordCompl[2] q) := by
  rw [collatzStep_eq_three_mul_add_one_of_not_even (Nat.not_even_iff_odd.mpr hq),
    ordCompl_two_eq_self_of_odd hq]
  rfl

theorem ordCompl_collatz_iterate_mem_syracuse (q n : ℕ) :
    ∃ k : ℕ, (syracuse^[k]) (ordCompl[2] q) = ordCompl[2] ((collatzStep^[n]) q) := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      rw [Function.iterate_succ_apply']
      by_cases heven : Even ((collatzStep^[n]) q)
      · exact ⟨k, by rw [ordCompl_collatzStep_of_even heven]; exact hk⟩
      · refine ⟨k + 1, ?_⟩
        rw [Function.iterate_succ_apply', hk,
          ordCompl_collatzStep_of_odd (Nat.not_even_iff_odd.mp heven)]

theorem reaches_ordCompl_two (q : ℕ) : Reaches q (ordCompl[2] q) := by
  have h := reaches_powTwo_mul (q.factorization 2) (ordCompl[2] q)
  convert h using 1
  exact (Nat.ordProj_mul_ordCompl_eq_self q 2).symm

theorem syracuse_minimum_oddPart_le_collatz_iterate (q n : ℕ) :
    syracuseGlobalMinimum (ordCompl[2] q) ≤ (collatzStep^[n]) q := by
  obtain ⟨k, hk⟩ := ordCompl_collatz_iterate_mem_syracuse q n
  calc
    syracuseGlobalMinimum (ordCompl[2] q) ≤ (syracuse^[k]) (ordCompl[2] q) :=
      syracuseGlobalMinimum_le _ _
    _ = ordCompl[2] ((collatzStep^[n]) q) := hk
    _ ≤ (collatzStep^[n]) q := Nat.ordCompl_le _ _

theorem collatzOrbitMin_eq_syracuseGlobalMinimum_oddPart {q : ℕ} (hq : 0 < q) :
    collatzOrbitMin q = syracuseGlobalMinimum (ordCompl[2] q) := by
  apply le_antisymm
  · obtain ⟨k, hk⟩ := syracuseGlobalMinimum_mem (ordCompl[2] q)
    obtain ⟨n, hn⟩ := (reaches_ordCompl_two q).trans
      (reaches_syracuse_iterate (ordCompl_two_odd hq) k)
    rw [← hk, ← hn]
    exact collatzOrbitMin_le_iterate q n
  · obtain ⟨n, hn⟩ := collatzOrbitMin_mem q
    rw [← hn]
    exact syracuse_minimum_oddPart_le_collatz_iterate q n

theorem collatzOrbitMin_eq_syracuseGlobalMinimum_of_odd {q : ℕ} (hq : Odd q) :
    collatzOrbitMin q = syracuseGlobalMinimum q := by
  rw [collatzOrbitMin_eq_syracuseGlobalMinimum_oddPart (by obtain ⟨k, hk⟩ := hq; omega : 0 < q),
    ordCompl_two_eq_self_of_odd hq]

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.ordCompl_collatz_iterate_mem_syracuse
#print axioms CollatzCanonical.LabelLaw.collatzOrbitMin_eq_syracuseGlobalMinimum_oddPart
#print axioms CollatzCanonical.LabelLaw.collatzOrbitMin_eq_syracuseGlobalMinimum_of_odd
