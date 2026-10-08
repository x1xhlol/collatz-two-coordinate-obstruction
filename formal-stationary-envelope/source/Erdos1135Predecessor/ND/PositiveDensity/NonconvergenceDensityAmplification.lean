/- This private replay copy replaces the deprecated proof tactic `push_neg` by `push Not` only.
   Definitions and theorem statements are unchanged; see provenance/envelope-linter-patches.json. -/

/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.GeneralTargetPositiveDensity
import Erdos1135Predecessor.StoppingTime
import Erdos1135Predecessor.ND.PositiveDensity.PredecessorCountSupport

namespace Erdos1135Predecessor.ND.PositiveDensity

def positiveNonconvergentSet : Set ℕ :=
  {n : ℕ | 0 < n ∧ ¬ Erdos1135Predecessor.Reaches n 1}

theorem positive_nonconvergence_lower_density_of_counterexample
    (hbad : ∃ n : ℕ, 0 < n ∧ ¬ Erdos1135Predecessor.Reaches n 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      c * (X : ℝ) ≤ (Terras.natCount positiveNonconvergentSet X : ℝ) := by
  obtain ⟨n, hn, hn_bad⟩ := hbad
  have htarget : ∃ a : ℕ, 0 < a ∧ ¬ 3 ∣ a ∧ Erdos1135Predecessor.Reaches n a := by
    obtain ⟨k, M, hodd, hfactor⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
    refine ⟨3 * M + 1, by omega, ?_, ?_⟩
    · rintro ⟨t, ht⟩
      omega
    · rw [hfactor]
      exact (Tao.reaches_powTwo_mul k M).trans
        (Erdos1135Predecessor.reaches_of_step_eq
          (Erdos1135Predecessor.collatzStep_eq_three_mul_add_one_of_not_even
            (Nat.not_even_iff_odd.mpr hodd)))
  obtain ⟨a, ha, hthree, hreach⟩ := htarget
  have ha_bad : ¬ Erdos1135Predecessor.Reaches a 1 := fun h => hn_bad (hreach.trans h)
  have hsub : ordinaryPredecessorSet a ⊆ positiveNonconvergentSet := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro hx_one
    obtain ⟨t, ht⟩ := hx.2
    exact ha_bad (Erdos1135Predecessor.reachesOne_tail_of_reachesOne_of_iterate_eq ht hx_one)
  obtain ⟨c, hc, X0, hX0⟩ := generalTarget_predecessors_positive_lower_density ha hthree
  refine ⟨c, hc, X0, ?_⟩
  intro X hX
  exact (hX0 X hX).trans (by exact_mod_cast Terras.natCount_mono hsub X)

def ArbitrarilyDenseOrdinaryConvergence : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ N : ℕ, ∃ X : ℕ,
    N ≤ X ∧ 0 < X ∧
      (1 - epsilon) * (X : ℝ) ≤ (Terras.natCount (ordinaryPredecessorSet 1) X : ℝ)

theorem universal_reaches_one_of_arbitrarily_dense_convergence
    (hstat : ArbitrarilyDenseOrdinaryConvergence) :
    ∀ n : ℕ, 0 < n → Erdos1135Predecessor.Reaches n 1 := by
  classical
  by_contra hnot
  push Not at hnot
  obtain ⟨c, hc, X0, hbad⟩ := positive_nonconvergence_lower_density_of_counterexample hnot
  obtain ⟨X, hX0, hXpos, hgood⟩ := hstat (c / 2) (by positivity) X0
  have hb := hbad X hX0
  have hd : Disjoint positiveNonconvergentSet (ordinaryPredecessorSet 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hx.2 hy.2
  have hsum : Terras.natCount positiveNonconvergentSet X +
      Terras.natCount (ordinaryPredecessorSet 1) X ≤ X := by
    rw [← Terras.natCount_union_of_disjoint hd]
    exact Terras.natCount_le _ _
  have hsumR : (Terras.natCount positiveNonconvergentSet X : ℝ) +
      (Terras.natCount (ordinaryPredecessorSet 1) X : ℝ) ≤ X := by exact_mod_cast hsum
  have hXp : (0 : ℝ) < X := by exact_mod_cast hXpos
  nlinarith [mul_pos hc hXp]

end Erdos1135Predecessor.ND.PositiveDensity
