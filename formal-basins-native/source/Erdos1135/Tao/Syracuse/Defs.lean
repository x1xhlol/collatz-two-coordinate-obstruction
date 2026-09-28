import Erdos1135.Terras.Core.Defs

/-!
# Syracuse Map Definitions For The Tao Lane

This module keeps the first Syracuse surface Nat-valued and independent of logarithmic density.
Real threshold and density statement targets live in `Erdos1135.Tao.Syracuse.Statement`.
-/

namespace Erdos1135
namespace Tao

/-- Tao's Syracuse map, represented by the Terras odd-only map. -/
abbrev syracuse : ℕ → ℕ :=
  Terras.oddOnly

/-- The Syracuse orbit of `N` eventually hits at most the natural threshold `B`. -/
def syracuseHitsAtMost (N B : ℕ) : Prop :=
  ∃ m : ℕ, (syracuse^[m]) N ≤ B

/-- Fixed-threshold odd Syracuse good set for later finite-threshold assembly. -/
def syracuseThresholdGood (B : ℕ) : Set ℕ :=
  {N : ℕ | Odd N ∧ syracuseHitsAtMost N B}

end Tao
end Erdos1135
