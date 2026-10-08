import Erdos1135.Tao.Fourier.TV

/-!
# Proposition 1.14 Statement Surface

This module records Tao's fine-scale mixing statement surface for
`Syrac(Z/3^nZ)`.  It intentionally proves no mixing estimate and no Fourier
decay theorem.
-/

open scoped BigOperators
open scoped ZMod

namespace Erdos1135
namespace Tao

/--
Congruence of two residues in `ZMod (3^n)` after projection to modulus `3^m`.

This is a statement-facing version of the source condition `Y' = Y mod 3^m`
inside `Z/3^nZ`.  Consumers should use it under the source-side hypothesis
`m <= n`.
-/
def zmodSameResidueModPow (m n : ℕ) (x y : ZMod (3 ^ n)) : Prop :=
  x.val % (3 ^ m) = y.val % (3 ^ m)

/-- Sum of a mass vector over the `3^m`-residue fiber through `y` in `ZMod (3^n)`. -/
noncomputable def zmodPowFiberSum (m n : ℕ) (c : ZMod (3 ^ n) → ℝ)
    (y : ZMod (3 ^ n)) : ℝ := by
  classical
  exact ∑ y' : ZMod (3 ^ n), if zmodSameResidueModPow m n y' y then c y' else 0

/-- Tao's source factor `3^(m-n)` written as a real ratio. -/
noncomputable def zmodPowFiberAverageScale (m n : ℕ) : ℝ :=
  ((3 ^ m : ℕ) : ℝ) / ((3 ^ n : ℕ) : ℝ)

/-- Source oscillation `Osc_{m,n}` from equation (1.27). -/
noncomputable def taoZModPowOscillation (m n : ℕ)
    (c : ZMod (3 ^ n) → ℝ) : ℝ := by
  classical
  exact
    ∑ y : ZMod (3 ^ n),
      |c y - zmodPowFiberAverageScale m n * zmodPowFiberSum m n c y|

/-- The zero mass vector has zero oscillation at every pair of scales. -/
@[simp] theorem taoZModPowOscillation_zero (m n : ℕ) :
    taoZModPowOscillation m n (fun _ => 0) = 0 := by
  simp [taoZModPowOscillation, zmodPowFiberSum]

/-- The source mass vector for `Syrac(Z/3^n Z)`. -/
noncomputable def syracPMFMassVector (n : ℕ) : ZMod (3 ^ n) → ℝ :=
  fun y => (syracPMF n y).toReal

/-- The left-hand side of Tao Proposition 1.14, equation (1.26). -/
noncomputable def syracFineScaleOscillation (m n : ℕ) : ℝ :=
  taoZModPowOscillation m n (syracPMFMassVector n)

/--
Fixed-polynomial-rate fine-scale mixing bound for `Syrac(Z/3^n Z)`.

The source has `≪_A m^{-A}` for every fixed positive exponent `A`; the constant
`C` below is the corresponding hidden constant.
-/
def syracFineScaleMixingAt (A : ℕ) (C : ℝ) : Prop :=
  ∀ n m : ℕ, 1 ≤ m → m ≤ n →
    syracFineScaleOscillation m n ≤ C / (m : ℝ) ^ A

/-- Source-shaped target for Tao Proposition 1.14. -/
def TaoProp114FineScaleMixingStatement : Prop :=
  ∀ A : ℕ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧ syracFineScaleMixingAt A C

theorem TaoProp114FineScaleMixingStatement.bound
    (h : TaoProp114FineScaleMixingStatement) {A : ℕ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ syracFineScaleMixingAt A C :=
  h A hA

theorem syracFineScaleMixingAt.apply {A : ℕ} {C : ℝ}
    (h : syracFineScaleMixingAt A C) {n m : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    syracFineScaleOscillation m n ≤ C / (m : ℝ) ^ A :=
  h n m hm hmn

end Tao
end Erdos1135
