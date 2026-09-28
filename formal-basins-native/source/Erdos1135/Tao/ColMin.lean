import Erdos1135.Tao.Statement
import Mathlib.Data.Nat.Lattice

/-!
# Source-facing Collatz Orbit Minimum Interface

This module connects the proof-facing `collatzHitsBelowReal` statement surface
to Tao's published `Colmin` phrasing, without changing the active analytic
consumer.
-/

namespace Erdos1135
namespace Tao

/-- Values attained by the standard Collatz orbit of `N`. -/
noncomputable def collatzOrbitValues (N : ℕ) : Set ℕ :=
  Set.range (fun m : ℕ => (collatzStep^[m]) N)

/-- Natural-number minimum of the standard Collatz orbit of `N`. -/
noncomputable def collatzOrbitMin (N : ℕ) : ℕ :=
  sInf (collatzOrbitValues N)

theorem collatzOrbitValues_nonempty (N : ℕ) :
    (collatzOrbitValues N).Nonempty := by
  refine ⟨N, ?_⟩
  exact ⟨0, by simp⟩

theorem collatzOrbitMin_mem (N : ℕ) :
    collatzOrbitMin N ∈ collatzOrbitValues N := by
  simpa [collatzOrbitMin] using Nat.sInf_mem (collatzOrbitValues_nonempty N)

theorem collatzOrbitMin_le_iterate (N m : ℕ) :
    collatzOrbitMin N ≤ (collatzStep^[m]) N := by
  exact Nat.sInf_le (show (collatzStep^[m]) N ∈ collatzOrbitValues N from ⟨m, rfl⟩)

theorem collatzHitsBelowReal_iff_collatzOrbitMin_lt {N : ℕ} {b : ℝ} :
    collatzHitsBelowReal N b ↔ (collatzOrbitMin N : ℝ) < b := by
  constructor
  · rintro ⟨m, hm⟩
    exact lt_of_le_of_lt
      (Nat.cast_le.mpr (collatzOrbitMin_le_iterate N m)) hm
  · intro h
    rcases collatzOrbitMin_mem N with ⟨m, hm⟩
    exact ⟨m, by simpa [hm] using h⟩

/-- Tao's almost-bounded statement in source-facing `Colmin` form. -/
def TaoAlmostBoundedColMinStatement : Prop :=
  ∀ f : ℕ → ℝ,
    GrowsToInfinity f →
      HasLogDensity {N : ℕ | 0 < N ∧ (collatzOrbitMin N : ℝ) < f N} 1

theorem TaoAlmostBoundedStatement_iff_colMin :
    TaoAlmostBoundedStatement ↔ TaoAlmostBoundedColMinStatement := by
  constructor
  · intro h f hf
    simpa [TaoAlmostBoundedColMinStatement,
      collatzHitsBelowReal_iff_collatzOrbitMin_lt] using h f hf
  · intro h f hf
    simpa [TaoAlmostBoundedColMinStatement,
      collatzHitsBelowReal_iff_collatzOrbitMin_lt] using h f hf

end Tao
end Erdos1135
