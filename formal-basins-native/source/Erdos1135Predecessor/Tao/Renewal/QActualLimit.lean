/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.QActualRecursion
import Mathlib.Topology.Order.MonotoneConvergence

open scoped BigOperators Topology

namespace Erdos1135Predecessor

namespace Tao

theorem taoSection7QFiniteTerminalOneApprox_antitone
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) :
    Antitone fun K : ℕ =>
      taoSection7QFiniteTerminalOneApprox K epsilon W p := by
  intro K L hKL
  obtain ⟨D, rfl⟩ := Nat.exists_eq_add_of_le hKL
  exact taoSection7QFiniteTerminalOneApprox_add_le_left hepsilon K D W p

noncomputable def taoSection7ActualQFiniteLimit
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop) :
    TaoSection7RenewalPoint → ℝ :=
  fun p => ⨅ K : ℕ, taoSection7QFiniteTerminalOneApprox K epsilon W p

theorem taoSection7ActualQFiniteLimit_statement
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop) :
    TaoSection7ActualQFiniteLimitStatement epsilon W
      (taoSection7ActualQFiniteLimit epsilon W) := by
  intro p
  unfold taoSection7ActualQFiniteLimit
  refine tendsto_atTop_ciInf
    (taoSection7QFiniteTerminalOneApprox_antitone hepsilon W p) ?_
  refine ⟨0, ?_⟩
  intro x hx
  rcases hx with ⟨K, rfl⟩
  exact taoSection7QFiniteTerminalOneApprox_nonneg K epsilon W p

theorem taoSection7ActualQFiniteLimit_bounded01
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop) :
    TaoSection7QBounded01 (taoSection7ActualQFiniteLimit epsilon W) := by
  intro p
  have hQ := taoSection7ActualQFiniteLimit_statement hepsilon W
  exact
    ⟨taoSection7ActualQ_nonneg_of_finiteLimit hQ p,
      taoSection7ActualQ_le_one_of_finiteLimit hepsilon hQ p⟩

theorem taoSection7ActualQFiniteLimit_fullHoldQRecursion
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) :
    taoSection7ActualQFiniteLimit epsilon W p =
      taoSection7FullHoldQRecursionRHS epsilon W
        (taoSection7ActualQFiniteLimit epsilon W) p := by
  exact taoSection7ActualQ_fullHoldQRecursion_of_finiteLimit hepsilon
    (taoSection7ActualQFiniteLimit_statement hepsilon W) p

end Tao

end Erdos1135Predecessor
