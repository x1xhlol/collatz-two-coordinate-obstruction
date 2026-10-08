import Erdos1135.Tao.Renewal.Outer754HorizontalFactor
import Erdos1135.Tao.Renewal.Prop78Case3Event

/-!
# Outer (7.54) Source Weight

Lightweight ownership for the white-count exponential and its product with
the outer horizontal factor. Countable and finite carriers share these
definitions; expectation and event-budget theorems live in higher modules.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- Exponential white-count factor in Tao's outer `(7.54)` weight. -/
noncomputable def taoSection7Case3Outer754ExponentialFactor
    {Ω : Type*} (epsilon : ℝ) (whiteCount : Ω → ℕ) : Ω → ℝ :=
  fun ω => Real.exp (-(epsilon ^ 3) * (whiteCount ω : ℝ))

/-- Product of the exponential white discount and horizontal factor. -/
noncomputable def taoSection7Case3Outer754Weight
    {Ω : Type*} (A m : ℕ) (epsilon : ℝ)
    (Jtot whiteCount : Ω → ℕ) : Ω → ℝ :=
  fun ω =>
    taoSection7Case3Outer754ExponentialFactor epsilon whiteCount ω *
      taoSection7Case3Outer754HorizontalFactor A m Jtot ω

/-- Source-window specialization using the checked Case 3 low-window count. -/
noncomputable def taoSection7Case3Outer754SourceExponentialFactor
    {Ω : Type*} (P : ℕ) (epsilon : ℝ)
    (W : Ω → ℕ → Prop) [∀ ω, DecidablePred (W ω)] : Ω → ℝ :=
  taoSection7Case3Outer754ExponentialFactor epsilon
    (fun ω => taoSection7Case3WindowWhiteCount (W ω) P)

/-- Source-window outer `(7.54)` weight. -/
noncomputable def taoSection7Case3Outer754SourceWeight
    {Ω : Type*} (A m P : ℕ) (epsilon : ℝ)
    (Jtot : Ω → ℕ)
    (W : Ω → ℕ → Prop) [∀ ω, DecidablePred (W ω)] : Ω → ℝ :=
  fun ω =>
    taoSection7Case3Outer754SourceExponentialFactor P epsilon W ω *
      taoSection7Case3Outer754HorizontalFactor A m Jtot ω

end

end Tao
end Erdos1135
