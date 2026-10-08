/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Terras.Core.Defs

/-!
# Syracuse Map Definitions For The Tao Lane

This module keeps the first Syracuse surface Nat-valued and independent of logarithmic density.
Real threshold and density statement targets live in `Erdos1135SecondScale.Tao.Syracuse.Statement`.
-/

namespace Erdos1135SecondScale
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
end Erdos1135SecondScale
