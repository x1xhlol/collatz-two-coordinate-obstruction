/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Fourier.TV

/-!
# Proposition 1.17 Statement Surfaces

This module records source-shaped target predicates for Tao's primitive
frequency Fourier decay.  It proves no coefficient decay and does not turn the
primitive-frequency statement into the stronger all-nonzero bound consumed by
the coarse full-L1 TV bridge.
-/

open scoped BigOperators
open scoped ZMod

namespace Erdos1135SecondScale
namespace Tao

/-- Frequencies divisible by `3` inside `ZMod (3^n)`. -/
def zmodThreeMultiple (n : ℕ) (ξ : ZMod (3 ^ n)) : Prop :=
  ∃ η : ZMod (3 ^ n), ξ = (3 : ZMod (3 ^ n)) * η

/-- Primitive, or high-frequency, classes in `ZMod (3^n)`: not divisible by `3`. -/
def zmodThreePrimitive (n : ℕ) (ξ : ZMod (3 ^ n)) : Prop :=
  ¬ zmodThreeMultiple n ξ

theorem zmodThreePrimitive.ne_zero {n : ℕ} {ξ : ZMod (3 ^ n)}
    (hξ : zmodThreePrimitive n ξ) : ξ ≠ 0 := by
  intro hzero
  exact hξ ⟨0, by simp [hzero]⟩

/-- Fixed-level primitive-frequency coefficient bound for `syracPMF n`. -/
def syracPMFPrimitiveDFTBound (n : ℕ) (B : ℝ) : Prop :=
  ∀ ξ : ZMod (3 ^ n), zmodThreePrimitive n ξ →
    ‖ZMod.dft (pmfComplexMass (syracPMF n)) ξ‖ ≤ B

theorem syracPMFPrimitiveDFTBound_of_nonzero {n : ℕ} {B : ℝ}
    (hB : syracPMFNonzeroDFTBound n B) :
    syracPMFPrimitiveDFTBound n B := by
  intro ξ hξ
  exact hB ξ hξ.ne_zero

/--
Polynomial primitive-frequency decay at a fixed exponent.

This uses natural exponents `A`; it is the formal analogue of a source bound
`≪_A n^{-A}` and avoids committing to a real-power API at the statement layer.
-/
def syracPMFPrimitivePolynomialDecayAt (A : ℕ) (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    syracPMFPrimitiveDFTBound n (C / (n : ℝ) ^ A)

/-- Polynomial decay for the stronger all-nonzero coefficient-bound surface. -/
def syracPMFNonzeroPolynomialDecayAt (A : ℕ) (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    syracPMFNonzeroDFTBound n (C / (n : ℝ) ^ A)

theorem syracPMFPrimitivePolynomialDecayAt_of_nonzero
    {A : ℕ} {C : ℝ} (h : syracPMFNonzeroPolynomialDecayAt A C) :
    syracPMFPrimitivePolynomialDecayAt A C := by
  intro n hn
  exact syracPMFPrimitiveDFTBound_of_nonzero (h n hn)

/--
Statement-shaped target corresponding to Tao's Proposition 1.17 in the current
finite-PMF vocabulary.

It is intentionally a `Prop` target: no decay estimate is proved here.
-/
def TaoProp117PrimitivePolynomialDecayStatement : Prop :=
  ∀ A : ℕ, 0 < A →
    ∃ C : ℝ, 0 ≤ C ∧ syracPMFPrimitivePolynomialDecayAt A C

/--
Stronger all-nonzero polynomial decay target.

This is not Tao's Proposition 1.17 as printed; it is the shape consumed by the
coarse full-L1 TV guard after a future lower-frequency reduction.
-/
def TaoAllNonzeroPolynomialDecayStatement : Prop :=
  ∀ A : ℕ, 0 < A →
    ∃ C : ℝ, 0 ≤ C ∧ syracPMFNonzeroPolynomialDecayAt A C

/--
Statement target for the missing reduction from primitive-frequency decay to
the stronger all-nonzero coefficient-bound surface.

This is intentionally only a `Prop` target, not an axiom and not a proof.
-/
def TaoPrimitiveToAllNonzeroReductionStatement : Prop :=
  TaoProp117PrimitivePolynomialDecayStatement →
    TaoAllNonzeroPolynomialDecayStatement

theorem TaoProp117PrimitivePolynomialDecayStatement.bound
    (h : TaoProp117PrimitivePolynomialDecayStatement)
    {A : ℕ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ syracPMFPrimitivePolynomialDecayAt A C :=
  h A hA

theorem TaoAllNonzeroPolynomialDecayStatement.bound
    (h : TaoAllNonzeroPolynomialDecayStatement)
    {A : ℕ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ syracPMFNonzeroPolynomialDecayAt A C :=
  h A hA

theorem TaoProp117PrimitivePolynomialDecayStatement.of_all_nonzero
    (h : TaoAllNonzeroPolynomialDecayStatement) :
    TaoProp117PrimitivePolynomialDecayStatement := by
  intro A hA
  rcases h A hA with ⟨C, hC_nonneg, hC⟩
  exact ⟨C, hC_nonneg, syracPMFPrimitivePolynomialDecayAt_of_nonzero hC⟩

theorem syracPMFPrimitivePolynomialDecayAt.apply
    {A n : ℕ} {C : ℝ}
    (h : syracPMFPrimitivePolynomialDecayAt A C) (hn : 1 ≤ n)
    {ξ : ZMod (3 ^ n)} (hξ : zmodThreePrimitive n ξ) :
    ‖ZMod.dft (pmfComplexMass (syracPMF n)) ξ‖ ≤ C / (n : ℝ) ^ A :=
  h n hn ξ hξ

theorem syracPMFNonzeroPolynomialDecayAt.apply
    {A n : ℕ} {C : ℝ}
    (h : syracPMFNonzeroPolynomialDecayAt A C) (hn : 1 ≤ n)
    {ξ : ZMod (3 ^ n)} (hξ : ξ ≠ 0) :
    ‖ZMod.dft (pmfComplexMass (syracPMF n)) ξ‖ ≤ C / (n : ℝ) ^ A :=
  h n hn ξ hξ

end Tao
end Erdos1135SecondScale
