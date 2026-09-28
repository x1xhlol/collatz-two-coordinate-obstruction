import Erdos1135.ND.Statement
import Mathlib.Algebra.Order.Round

/-!
# Conditional Phase-Gap Interface

The first ND milestone consumes the phase estimate below as a visible theorem
hypothesis.  No Rhin or other irrationality-measure result is asserted here.
-/

namespace Erdos1135
namespace ND

/-- `log_2 3`, represented with natural logarithms. -/
noncomputable def logTwoThree : ℝ :=
  Real.log 3 / Real.log 2

/-- Distance from a real number to the nearest integer.

Mathlib's `round` breaks half-integer ties toward positive infinity; the
absolute distance is independent of that tie convention. -/
noncomputable def nearestIntegerNorm (x : ℝ) : ℝ :=
  |x - (round x : ℝ)|

/-- The v10 phase input `||q log_2 3|| ≥ c q^(1-kappa)`.

A natural `q ≥ 1` represents exactly the positive integer frequencies used
downstream. The parameter restrictions are part of the hypothesis. -/
structure PhaseGap (c kappa : ℝ) : Prop where
  c_pos : 0 < c
  c_le_one : c ≤ 1
  two_lt_kappa : 2 < kappa
  gap : ∀ q : ℕ, 0 < q →
    c * Real.rpow (q : ℝ) (1 - kappa) ≤
      nearestIntegerNorm ((q : ℝ) * logTwoThree)

/-- Public conditional target for the first ND milestone.

The phase input is a theorem hypothesis; this definition declares no axiom. -/
def ConditionalNDChainStatement (c kappa : ℝ) : Prop :=
  PhaseGap c kappa → NDChainStatement

end ND
end Erdos1135
