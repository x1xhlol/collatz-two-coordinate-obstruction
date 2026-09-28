import Erdos1135.Orbit
import Erdos1135.Tao.Syracuse.Basic

/-!
# Standard Collatz Bridge For Syracuse Orbits

This leaf realizes the deterministic part of Tao's equation (1.1).  It uses
the canonical raw `collatzStep`: one odd step is followed by every division by
two encoded in a Syracuse step.
-/

namespace Erdos1135
namespace Tao

/-- Raw Collatz iteration removes an initial power of two in exactly that many
steps. -/
theorem collatz_iterate_powTwo_mul (a M : ℕ) :
    (collatzStep^[a]) ((2 : ℕ) ^ a * M) = M := by
  induction a with
  | zero =>
      simp
  | succ a ih =>
      have hEven : Even ((2 : ℕ) ^ (a + 1) * M) := by
        refine ⟨(2 : ℕ) ^ a * M, ?_⟩
        rw [pow_succ]
        ring
      rw [Function.iterate_succ_apply,
        collatzStep_eq_div_two_of_even hEven]
      have hdiv :
          ((2 : ℕ) ^ (a + 1) * M) / 2 = (2 : ℕ) ^ a * M := by
        rw [pow_succ]
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          Nat.mul_div_left ((2 : ℕ) ^ a * M) (by norm_num : 0 < (2 : ℕ))
      rw [hdiv]
      exact ih

/-- The dyadic multiple reaches its odd factor under the raw Collatz map. -/
theorem reaches_powTwo_mul (a M : ℕ) :
    Reaches ((2 : ℕ) ^ a * M) M :=
  ⟨a, collatz_iterate_powTwo_mul a M⟩

/-- One Syracuse step from an odd input is exactly one raw odd Collatz step
followed by `syracuseExponent M` raw halving steps. -/
theorem collatz_iterate_syracuse_block {M : ℕ} (hM : Odd M) :
    (collatzStep^[syracuseExponent M + 1]) M = syracuse M := by
  rw [Function.iterate_add_apply, Function.iterate_one,
    collatzStep_eq_three_mul_add_one_of_not_even
      (Nat.not_even_iff_odd.mpr hM),
    ← two_pow_syracuseExponent_mul_syracuse M]
  exact collatz_iterate_powTwo_mul (syracuseExponent M) (syracuse M)

/-- An odd input reaches its next Syracuse value under raw Collatz iteration. -/
theorem reaches_syracuse {M : ℕ} (hM : Odd M) :
    Reaches M (syracuse M) :=
  ⟨syracuseExponent M + 1, collatz_iterate_syracuse_block hM⟩

/-- Every finite Syracuse iterate of an odd input occurs in its raw standard
Collatz orbit. -/
theorem reaches_syracuse_iterate {M : ℕ} (hM : Odd M) (k : ℕ) :
    Reaches M ((syracuse^[k]) M) := by
  induction k generalizing M with
  | zero =>
      simpa using reaches_refl M
  | succ k ih =>
      have hhead : Reaches M (syracuse M) := reaches_syracuse hM
      have htail : Reaches (syracuse M) ((syracuse^[k]) (syracuse M)) :=
        ih (syracuse_odd M)
      simpa only [Function.iterate_succ_apply] using hhead.trans htail

end Tao
end Erdos1135
