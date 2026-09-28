/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Basic
import Mathlib.Analysis.Complex.Norm

open scoped BigOperators

open scoped ZMod

namespace Erdos1135Predecessor

namespace Tao

def zmodThreeMultiple (n : ℕ) (ξ : ZMod (3 ^ n)) : Prop :=
  ∃ η : ZMod (3 ^ n), ξ = (3 : ZMod (3 ^ n)) * η

def zmodThreePrimitive (n : ℕ) (ξ : ZMod (3 ^ n)) : Prop :=
  ¬ zmodThreeMultiple n ξ

def syracPMFPrimitiveDFTBound (n : ℕ) (B : ℝ) : Prop :=
  ∀ ξ : ZMod (3 ^ n), zmodThreePrimitive n ξ →
    ‖ZMod.dft (pmfComplexMass (syracPMF n)) ξ‖ ≤ B

def syracPMFPrimitivePolynomialDecayAt (A : ℕ) (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    syracPMFPrimitiveDFTBound n (C / (n : ℝ) ^ A)

theorem syracPMFPrimitivePolynomialDecayAt.apply
    {A n : ℕ} {C : ℝ}
    (h : syracPMFPrimitivePolynomialDecayAt A C) (hn : 1 ≤ n)
    {ξ : ZMod (3 ^ n)} (hξ : zmodThreePrimitive n ξ) :
    ‖ZMod.dft (pmfComplexMass (syracPMF n)) ξ‖ ≤ C / (n : ℝ) ^ A :=
  h n hn ξ hξ

end Tao

end Erdos1135Predecessor
