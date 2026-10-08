/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Syracuse.Defs

namespace Erdos1135Predecessor

namespace Tao

def syracuseExponent (N : ℕ) : ℕ :=
  Terras.twoAdicExponent (3 * N + 1)

theorem syracuse_eq_ordCompl_two (N : ℕ) :
    syracuse N = ordCompl[2] (3 * N + 1) :=
  rfl

theorem syracuse_odd (N : ℕ) :
    Odd (syracuse N) := by
  rw [syracuse_eq_ordCompl_two]
  exact Nat.not_even_iff_odd.mp (by
    intro heven
    have hdiv : (2 : ℕ) ∣ ordCompl[2] (3 * N + 1) := even_iff_two_dvd.mp heven
    exact Nat.not_dvd_ordCompl Nat.prime_two (by omega : 3 * N + 1 ≠ 0) hdiv)

theorem syracuse_pos (N : ℕ) :
    0 < syracuse N := by
  rw [syracuse_eq_ordCompl_two]
  exact Nat.ordCompl_pos 2 (by omega : 3 * N + 1 ≠ 0)

theorem two_pow_syracuseExponent_mul_syracuse (N : ℕ) :
    (2 : ℕ) ^ syracuseExponent N * syracuse N = 3 * N + 1 := by
  simpa [syracuse, Terras.oddOnly, syracuseExponent, Terras.twoAdicExponent]
    using Nat.ordProj_mul_ordCompl_eq_self (3 * N + 1) 2

theorem syracuseExponent_pos_of_odd {N : ℕ} (hN : Odd N) :
    0 < syracuseExponent N := by
  have hnum_ne : 3 * N + 1 ≠ 0 := by omega
  have hdiv : (2 : ℕ) ∣ 3 * N + 1 := by
    rcases hN with ⟨k, hk⟩
    use 3 * k + 2
    omega
  unfold syracuseExponent Terras.twoAdicExponent
  exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two hnum_ne hdiv

end Tao

end Erdos1135Predecessor
