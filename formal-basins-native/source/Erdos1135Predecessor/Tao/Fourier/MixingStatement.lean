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

def zmodSameResidueModPow (m n : ℕ) (x y : ZMod (3 ^ n)) : Prop :=
  x.val % (3 ^ m) = y.val % (3 ^ m)

noncomputable def zmodPowFiberSum (m n : ℕ) (c : ZMod (3 ^ n) → ℝ)
    (y : ZMod (3 ^ n)) : ℝ := by
  classical
  exact ∑ y' : ZMod (3 ^ n), if zmodSameResidueModPow m n y' y then c y' else 0

noncomputable def zmodPowFiberAverageScale (m n : ℕ) : ℝ :=
  ((3 ^ m : ℕ) : ℝ) / ((3 ^ n : ℕ) : ℝ)

noncomputable def taoZModPowOscillation (m n : ℕ)
    (c : ZMod (3 ^ n) → ℝ) : ℝ := by
  classical
  exact
    ∑ y : ZMod (3 ^ n),
      |c y - zmodPowFiberAverageScale m n * zmodPowFiberSum m n c y|

@[simp] theorem taoZModPowOscillation_zero (m n : ℕ) :
    taoZModPowOscillation m n (fun _ => 0) = 0 := by
  simp [taoZModPowOscillation, zmodPowFiberSum]

noncomputable def syracPMFMassVector (n : ℕ) : ZMod (3 ^ n) → ℝ :=
  fun y => (syracPMF n y).toReal

noncomputable def syracFineScaleOscillation (m n : ℕ) : ℝ :=
  taoZModPowOscillation m n (syracPMFMassVector n)

def syracFineScaleMixingAt (A : ℕ) (C : ℝ) : Prop :=
  ∀ n m : ℕ, 1 ≤ m → m ≤ n →
    syracFineScaleOscillation m n ≤ C / (m : ℝ) ^ A

end Tao

end Erdos1135Predecessor
