/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Syracuse.Syrac
import Mathlib.Analysis.Fourier.ZMod

open scoped BigOperators

open scoped ZMod

namespace Erdos1135Predecessor

namespace Tao

noncomputable def pmfComplexMass {α : Type*} (p : PMF α) : α → ℂ :=
  fun x => ((p x).toReal : ℂ)

noncomputable def taoForwardDFTKernel {N : ℕ} [NeZero N] (x ξ : ZMod N) : ℂ :=
  ZMod.stdAddChar (-(x * ξ))

theorem tao_dft_apply {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (ξ : ZMod N) :
    ZMod.dft Φ ξ = ∑ x : ZMod N, taoForwardDFTKernel x ξ • Φ x := by
  rw [ZMod.dft_apply]
  simp [taoForwardDFTKernel]

theorem tao_dft_pmfComplexMass_apply {N : ℕ} [NeZero N]
    (p : PMF (ZMod N)) (ξ : ZMod N) :
    ZMod.dft (pmfComplexMass p) ξ =
      ∑ x : ZMod N, taoForwardDFTKernel x ξ * (((p x).toReal : ℝ) : ℂ) := by
  rw [tao_dft_apply]
  simp [taoForwardDFTKernel, pmfComplexMass, smul_eq_mul]

end Tao

end Erdos1135Predecessor
