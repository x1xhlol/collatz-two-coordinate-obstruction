/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.NonconvergenceDensityAmplification

/-!
# Positive lower density of ordinary Collatz predecessors

This interface records three consequences of the general-target
extension. The ordinary map sends odd n to 3*n+1 and even n to n/2.
Counts use positive starts strictly below a natural cutoff. Density constants
may depend on the target; no clock or density limit is asserted.
-/

namespace CollatzPredecessorDensity
noncomputable section

abbrev Reaches (n a : ℕ) : Prop := Erdos1135Predecessor.Reaches n a

abbrev predecessors (a : ℕ) : Set ℕ :=
  Erdos1135Predecessor.ND.PositiveDensity.ordinaryPredecessorSet a

abbrev nonconvergentStarts : Set ℕ :=
  Erdos1135Predecessor.ND.PositiveDensity.positiveNonconvergentSet

abbrev countBelow (s : Set ℕ) (X : ℕ) : ℕ :=
  Erdos1135Predecessor.Terras.natCount s X

def HasPositiveLowerDensity (s : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
    c * (X : ℝ) ≤ (countBelow s X : ℝ)

/-- An explicit statistical hypothesis: proportions arbitrarily close to
one occur at arbitrarily large cutoffs. A density-one limit implies this
hypothesis, but no such statistical assertion is established here. -/
abbrev ArbitrarilyDenseConvergence : Prop :=
  Erdos1135Predecessor.ND.PositiveDensity.ArbitrarilyDenseOrdinaryConvergence

theorem predecessors_positive_lower_density
    {a : ℕ} (ha : 0 < a) (hthree : ¬ 3 ∣ a) :
    HasPositiveLowerDensity (predecessors a) := by
  exact Erdos1135Predecessor.ND.PositiveDensity.generalTarget_predecessors_positive_lower_density ha hthree

theorem nonconvergence_positive_lower_density_of_counterexample
    (hbad : ∃ n : ℕ, 0 < n ∧ ¬ Reaches n 1) :
    HasPositiveLowerDensity nonconvergentStarts := by
  exact Erdos1135Predecessor.ND.PositiveDensity.positive_nonconvergence_lower_density_of_counterexample hbad

theorem universal_reaches_one_of_arbitrarily_dense_convergence
    (hstat : ArbitrarilyDenseConvergence) :
    ∀ n : ℕ, 0 < n → Reaches n 1 := by
  exact Erdos1135Predecessor.ND.PositiveDensity.universal_reaches_one_of_arbitrarily_dense_convergence hstat

end
end CollatzPredecessorDensity
