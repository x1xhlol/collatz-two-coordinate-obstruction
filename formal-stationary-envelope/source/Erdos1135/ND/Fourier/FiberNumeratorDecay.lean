import Erdos1135.ND.Fourier.FiberHoldTransport
import Erdos1135.Tao.Fourier.Prop71CanonicalAssembly

/-!
# Fixed-Fiber Numerator Decay

This leaf feeds the checked fixed-total numerator into the inherited
Proposition 7.8 pointwise and outer bounds.  The resulting estimate is uniform
in the selected total `L`; endpoint normalization and its central-window loss
are deliberately left to the conditioned-M1 assembly.
-/

namespace Erdos1135
namespace ND

/-- The unnormalized fixed-total Section 7 numerator has arbitrary positive
natural polynomial decay, uniformly in the selected total. -/
theorem exists_ndSection7FiberNumerator_polynomial_decay
    (A : ℕ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, 1 ≤ n →
        ∀ xi : ZMod (3 ^ n), Tao.zmodThreePrimitive n xi →
          ∀ L : ℕ,
            ‖ndSection7FiberNumerator n L xi‖ ≤
              C / (n : ℝ) ^ A := by
  obtain ⟨packet⟩ := Tao.nonempty_taoSection7Prop78AbsolutePacket
  have hA1 : 1 ≤ A := by omega
  obtain ⟨C, _hC, hpoint⟩ :=
    Tao.exists_taoSection7Prop78_canonical_pointwise_737 packet A hA1
  let K : ℝ :=
    (C : ℝ) ^ A * (8 : ℝ) ^ A *
      Tao.taoSection7Geom4PolynomialMoment A
  have hCpow : 0 ≤ (C : ℝ) ^ A :=
    pow_nonneg (Nat.cast_nonneg C) A
  have h8pow : 0 ≤ (8 : ℝ) ^ A := by positivity
  have hmoment : 0 ≤ Tao.taoSection7Geom4PolynomialMoment A :=
    Tao.taoSection7Geom4PolynomialMoment_nonneg A
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg hCpow h8pow) hmoment
  have hepsilon0 : 0 ≤ packet.epsilon :=
    packet.scalar.epsilon_pos.le
  have hepsilon1 : packet.epsilon ≤ 1 :=
    packet.scalar.epsilon_le_one_hundredth.trans (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro n hn xi hxi L
  have hn_pos : 0 < n := by omega
  calc
    ‖ndSection7FiberNumerator n L xi‖ ≤
        Tao.taoSection7HoldExpectationFull
          (Tao.taoSection7SourceActualQ n xi packet.epsilon) :=
      norm_ndSection7FiberNumerator_le_holdExpectation_sourceActualQ
        n L xi hepsilon0 hepsilon1
    _ ≤ K / (n : ℝ) ^ A := by
      simpa [K] using
        (Tao.taoSection7SourceActualQ_outer736_of_pointwise_decay
          (n := n) (A := A) (xi := xi)
          (epsilon := packet.epsilon) (D := (C : ℝ) ^ A)
          hn_pos hepsilon0 hCpow (hpoint n xi hxi))

end ND
end Erdos1135
