/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Basic
import Erdos1135Predecessor.Tao.Probability.Finite
import Erdos1135Predecessor.Tao.Syracuse.Defs
import Erdos1135Predecessor.Terras.Density.NaturalDensity
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

open Filter

def rawCollatzLogTimeOneSet (Ctime : ℝ) : Set ℕ :=
  {N : ℕ | 0 < N ∧ ∃ m : ℕ,
    (m : ℝ) ≤ Ctime * Real.log (N : ℝ) ∧
      (collatzStep^[m]) N = 1}

theorem rawCollatzLogTimeOneSet_mono {Ctime Dtime : ℝ}
    (hCD : Ctime ≤ Dtime) :
    rawCollatzLogTimeOneSet Ctime ⊆ rawCollatzLogTimeOneSet Dtime := by
  intro N hN
  rcases hN with ⟨hNpos, m, hm, hreach⟩
  refine ⟨hNpos, m, ?_, hreach⟩
  have hNOne : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.2 hNpos.ne')
  exact hm.trans (mul_le_mul_of_nonneg_right hCD (Real.log_nonneg hNOne))

end PositiveDensity

end ND

end Erdos1135Predecessor
