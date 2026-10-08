import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-!
# Exact-Zero-Head Abel Localization

This file isolates the finite summation-by-parts algebra used by the frozen
v10 A5 phase profile.  Its weights have a literal zero prefix, so every short
Abel coefficient vanishes and an antitone positive-length discrepancy bound
can be pinned at the first nonzero index.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

/-- The absolute Abel factor, with the terminal weight kept absolute for
arbitrary signed weights. -/
noncomputable def ndAbsAbelFactor
    (omega : ℕ → ℝ) (V : ℕ) : ℝ :=
  |omega (V - 1)| * (V : ℝ) +
    ∑ i ∈ Finset.range (V - 1),
      |omega i - omega (i + 1)| * ((i + 1 : ℕ) : ℝ)

/-- Exact-zero-head finite Abel localization.  If the first `P` weights
vanish, only prefix lengths at least `P` contribute, so an antitone endpoint
majorant is consumed at `D P` and never at the totalized input zero. -/
theorem ndZeroHeadAbel_of_antitonePrefix
    (omega B : ℕ → ℝ) (D : ℕ → ℝ)
    (V P : ℕ) (Q : ℝ)
    (hP : 0 < P) (hPV : P < V)
    (hQ : 0 ≤ Q)
    (hD : ∀ m, 0 ≤ D m)
    (hanti : AntitoneOn D (Set.Ici 1))
    (hzero : ∀ n, n < P → omega n = 0)
    (hprefix : ∀ m, 0 < m → m ≤ V →
      |∑ n ∈ Finset.range m, B n| ≤
        Q * (m : ℝ) * D m) :
    |∑ n ∈ Finset.range V, omega n * B n| ≤
      Q * D P * ndAbsAbelFactor omega V := by
  classical
  have hQDP : 0 ≤ Q * D P := mul_nonneg hQ (hD P)
  have hPrefixLong (m : ℕ) (hPm : P ≤ m) (hmV : m ≤ V) :
      |∑ n ∈ Finset.range m, B n| ≤
        Q * D P * (m : ℝ) := by
    have hmpos : 0 < m := hP.trans_le hPm
    have hDmP : D m ≤ D P :=
      hanti
        (by simpa only [Set.mem_Ici] using hP)
        (by simpa only [Set.mem_Ici] using hmpos)
        hPm
    calc
      |∑ n ∈ Finset.range m, B n| ≤
          Q * (m : ℝ) * D m := hprefix m hmpos hmV
      _ ≤ Q * (m : ℝ) * D P :=
        mul_le_mul_of_nonneg_left hDmP
          (mul_nonneg hQ (Nat.cast_nonneg m))
      _ = Q * D P * (m : ℝ) := by ac_rfl
  have hAbel :
      (∑ n ∈ Finset.range V, omega n * B n) =
        omega (V - 1) * (∑ n ∈ Finset.range V, B n) -
          ∑ i ∈ Finset.range (V - 1),
            (omega (i + 1) - omega i) *
              (∑ n ∈ Finset.range (i + 1), B n) := by
    simpa only [smul_eq_mul] using
      (Finset.sum_range_by_parts omega B V)
  have hTerminal :
      |omega (V - 1) * (∑ n ∈ Finset.range V, B n)| ≤
        Q * D P * (|omega (V - 1)| * (V : ℝ)) := by
    rw [abs_mul]
    calc
      |omega (V - 1)| * |∑ n ∈ Finset.range V, B n| ≤
          |omega (V - 1)| * (Q * D P * (V : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (hPrefixLong V hPV.le le_rfl) (abs_nonneg _)
      _ = Q * D P * (|omega (V - 1)| * (V : ℝ)) := by
        ac_rfl
  have hIncrement (i : ℕ) (hi : i ∈ Finset.range (V - 1)) :
      |(omega (i + 1) - omega i) *
          (∑ n ∈ Finset.range (i + 1), B n)| ≤
        Q * D P *
          (|omega i - omega (i + 1)| * ((i + 1 : ℕ) : ℝ)) := by
    by_cases hshort : i + 1 < P
    · have hiP : i < P := (Nat.lt_succ_self i).trans hshort
      have hcoeff : omega (i + 1) - omega i = 0 := by
        rw [hzero (i + 1) hshort, hzero i hiP]
        exact sub_self 0
      rw [hcoeff, zero_mul, abs_zero]
      exact mul_nonneg hQDP
        (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg (i + 1)))
    · have hPm : P ≤ i + 1 := Nat.le_of_not_gt hshort
      have himV : i + 1 ≤ V :=
        (Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)).trans
          (Nat.sub_le V 1)
      rw [abs_mul]
      calc
        |omega (i + 1) - omega i| *
              |∑ n ∈ Finset.range (i + 1), B n| ≤
            |omega (i + 1) - omega i| *
              (Q * D P * ((i + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (hPrefixLong (i + 1) hPm himV) (abs_nonneg _)
        _ = Q * D P *
            (|omega i - omega (i + 1)| * ((i + 1 : ℕ) : ℝ)) := by
          rw [abs_sub_comm]
          ac_rfl
  have hBulk :
      |∑ i ∈ Finset.range (V - 1),
          (omega (i + 1) - omega i) *
            (∑ n ∈ Finset.range (i + 1), B n)| ≤
        Q * D P *
          ∑ i ∈ Finset.range (V - 1),
            |omega i - omega (i + 1)| * ((i + 1 : ℕ) : ℝ) := by
    calc
      |∑ i ∈ Finset.range (V - 1),
          (omega (i + 1) - omega i) *
            (∑ n ∈ Finset.range (i + 1), B n)| ≤
          ∑ i ∈ Finset.range (V - 1),
            |(omega (i + 1) - omega i) *
              (∑ n ∈ Finset.range (i + 1), B n)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (V - 1),
          Q * D P *
            (|omega i - omega (i + 1)| * ((i + 1 : ℕ) : ℝ)) :=
        Finset.sum_le_sum fun i hi => hIncrement i hi
      _ = Q * D P *
          ∑ i ∈ Finset.range (V - 1),
            |omega i - omega (i + 1)| * ((i + 1 : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
  rw [hAbel]
  calc
    |omega (V - 1) * (∑ n ∈ Finset.range V, B n) -
        ∑ i ∈ Finset.range (V - 1),
          (omega (i + 1) - omega i) *
            (∑ n ∈ Finset.range (i + 1), B n)| ≤
      |omega (V - 1) * (∑ n ∈ Finset.range V, B n)| +
        |∑ i ∈ Finset.range (V - 1),
          (omega (i + 1) - omega i) *
            (∑ n ∈ Finset.range (i + 1), B n)| := abs_sub _ _
    _ ≤ Q * D P * (|omega (V - 1)| * (V : ℝ)) +
        Q * D P *
          ∑ i ∈ Finset.range (V - 1),
            |omega i - omega (i + 1)| * ((i + 1 : ℕ) : ℝ) :=
      add_le_add hTerminal hBulk
    _ = Q * D P * ndAbsAbelFactor omega V := by
      unfold ndAbsAbelFactor
      rw [mul_add]

end ND
end Erdos1135
