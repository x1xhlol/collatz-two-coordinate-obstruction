import Erdos1135.Tao.Renewal.QActualRecursion
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Section 7 Actual Q Limit Constructor

This module constructs the generic terminal-one limit object from the finite
approximants by pointwise infimum.  It remains generic over the renewal
predicate `W`; it does not instantiate Tao's source cutoff `Q` or source `Q_m`.
-/

open scoped BigOperators Topology

namespace Erdos1135
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

/--
Generic actual-`Q` candidate obtained as the pointwise infimum of terminal-one
finite approximants.
-/
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

theorem taoSection7ActualQ_le_terminalOneApprox_of_finiteLimit
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {W : TaoSection7RenewalPoint → Prop}
    {Q : TaoSection7RenewalPoint → ℝ}
    (hQ : TaoSection7ActualQFiniteLimitStatement epsilon W Q)
    (p : TaoSection7RenewalPoint) (K : ℕ) :
    Q p ≤ taoSection7QFiniteTerminalOneApprox K epsilon W p := by
  exact le_of_tendsto (hQ p)
    (Filter.eventually_atTop.mpr
      ⟨K, fun L hKL => by
        obtain ⟨D, rfl⟩ := Nat.exists_eq_add_of_le hKL
        exact taoSection7QFiniteTerminalOneApprox_add_le_left
          hepsilon K D W p⟩)

theorem taoSection7ActualQ_le_terminalOneApprox_zero_of_finiteLimit
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {W : TaoSection7RenewalPoint → Prop}
    {Q : TaoSection7RenewalPoint → ℝ}
    (hQ : TaoSection7ActualQFiniteLimitStatement epsilon W Q)
    (p : TaoSection7RenewalPoint) :
    Q p ≤ taoSection7QWhiteFactor epsilon W p := by
  calc
    Q p ≤ taoSection7QFiniteTerminalOneApprox 0 epsilon W p :=
      taoSection7ActualQ_le_terminalOneApprox_of_finiteLimit
        hepsilon hQ p 0
    _ = taoSection7QWhiteFactor epsilon W p :=
      taoSection7QFiniteTerminalOneApprox_zero epsilon W p

theorem taoSection7ActualQ_le_terminalOneApprox_succ_of_finiteLimit
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {W : TaoSection7RenewalPoint → Prop}
    {Q : TaoSection7RenewalPoint → ℝ}
    (hQ : TaoSection7ActualQFiniteLimitStatement epsilon W Q)
    (p : TaoSection7RenewalPoint) (K : ℕ) :
    Q p ≤
      taoSection7QWhiteFactor epsilon W p *
        taoSection7HoldExpectationFull
          (fun h : TaoSection7RenewalPoint =>
            taoSection7QFiniteTerminalOneApprox K epsilon W (p + h)) := by
  calc
    Q p ≤ taoSection7QFiniteTerminalOneApprox (K + 1) epsilon W p :=
      taoSection7ActualQ_le_terminalOneApprox_of_finiteLimit
        hepsilon hQ p (K + 1)
    _ =
      taoSection7QWhiteFactor epsilon W p *
        taoSection7HoldExpectationFull
          (fun h : TaoSection7RenewalPoint =>
            taoSection7QFiniteTerminalOneApprox K epsilon W (p + h)) :=
      taoSection7QFiniteTerminalOneApprox_succ hepsilon K W p

end Tao
end Erdos1135
