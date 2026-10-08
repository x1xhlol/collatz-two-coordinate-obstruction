import Erdos1135.Tao.Probability.PascalPrime

/-!
# Section 7 Pre-Hit Path Mass Factorization

This module records finite path-mass wrappers for Tao's pre-Hold decomposition.
It reuses the canonical `Geom(4)` and Pascal-prime source-mass APIs; it does
not construct the `Hold` PMF.
-/

namespace Erdos1135
namespace Tao

/--
Current-worker finite path factorization: under the canonical source guards,
the unconditioned mass of seeing `pre` before the first hit `3` is the
zero-based `Geom(4)` miss mass times the conditioned Pascal-prime source path
mass of `pre`.
-/
theorem taoSection7UnconditionedPreHitPathMass_eq_geom4Miss_mul_sourcePath
    {pre : List ℕ}
    (h2 : taoSection7AllGeTwo pre) (hno : taoSection7NoThree pre) :
    taoSection7UnconditionedPreHitPathMass pre =
      taoSection7Geom4MissMass pre.length *
        taoSection7PascalPrimeSourcePathMass pre := by
  rw [← taoSection7FinitePreHitBlockPMFMass_eq_unconditioned h2 hno]
  rw [taoSection7FinitePreHitBlockPMFMass]
  rw [taoSection7PascalPrimePMFSourcePathMass_eq_source h2]

/--
One-based first-hit version of the same factorization, matching the Hold point
index `pre.length + 1`.
-/
theorem taoSection7UnconditionedPreHitPathMass_eq_firstHitMass_mul_sourcePath
    {pre : List ℕ}
    (h2 : taoSection7AllGeTwo pre) (hno : taoSection7NoThree pre) :
    taoSection7UnconditionedPreHitPathMass pre =
      taoSection7Geom4FirstHitMass
          ⟨pre.length + 1, Nat.succ_pos pre.length⟩ *
        taoSection7PascalPrimeSourcePathMass pre := by
  rw [taoSection7UnconditionedPreHitPathMass_eq_geom4Miss_mul_sourcePath h2 hno]
  rw [taoSection7Geom4FirstHitMass_eq_missMass pre.length]

end Tao
end Erdos1135
