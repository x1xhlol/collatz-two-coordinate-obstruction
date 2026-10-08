/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Outer754HorizontalFactor
import Erdos1135Predecessor.Tao.Renewal.Prop78Case3Event

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

noncomputable def taoSection7Case3Outer754ExponentialFactor
    {Ω : Type*} (epsilon : ℝ) (whiteCount : Ω → ℕ) : Ω → ℝ :=
  fun ω => Real.exp (-(epsilon ^ 3) * (whiteCount ω : ℝ))

noncomputable def taoSection7Case3Outer754SourceExponentialFactor
    {Ω : Type*} (P : ℕ) (epsilon : ℝ)
    (W : Ω → ℕ → Prop) [∀ ω, DecidablePred (W ω)] : Ω → ℝ :=
  taoSection7Case3Outer754ExponentialFactor epsilon
    (fun ω => taoSection7Case3WindowWhiteCount (W ω) P)

noncomputable def taoSection7Case3Outer754SourceWeight
    {Ω : Type*} (A m P : ℕ) (epsilon : ℝ)
    (Jtot : Ω → ℕ)
    (W : Ω → ℕ → Prop) [∀ ω, DecidablePred (W ω)] : Ω → ℝ :=
  fun ω =>
    taoSection7Case3Outer754SourceExponentialFactor P epsilon W ω *
      taoSection7Case3Outer754HorizontalFactor A m Jtot ω

end

end Tao

end Erdos1135Predecessor
