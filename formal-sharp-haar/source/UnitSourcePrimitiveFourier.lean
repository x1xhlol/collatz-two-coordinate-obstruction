import UnitSourceAffinePMF
import UnitSourceEnvelopeActualQ
import Erdos1135.Tao.Fourier.Prop71CanonicalAssembly

/-!
# Primitive Fourier decay with a retained seed

At conductor `n`, the literal affine PMF after `n-1` geometric steps has
polynomial decay at every primitive frequency, uniformly over its seed.
The missing adjacent pair costs at most `4/3`; all subsequent renewal bounds
are the existing canonical native theorems. No Section 6 mixing conclusion
or unit-source density theorem is asserted in this packet.
-/

set_option autoImplicit false

namespace Erdos1135.Tao

theorem unitSourceAffinePMF_norm_dft_le_four_thirds_actualQ
    (n : ℕ) (xi z : ZMod (3 ^ n))
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    ‖ZMod.dft (pmfComplexMass (unitSourceAffinePMF n (n - 1) z)) xi‖ ≤
      (4 / 3 : ℝ) * taoSection7HoldExpectationFull
        (taoSection7SourceActualQ n xi epsilon) := by
  rw [unitSourceAffinePMF_dft_eq_twistedPairExpectation]
  calc
    ‖unitSourcePairExpectation n xi (unitSourceSeedPhase n (n - 1) xi z)
        (n - 1) 1 0‖ ≤ taoSection7PairSourceEnvelope n xi ((n - 1) / 2) 1 0 :=
      norm_unitSourcePairExpectation_le_sourceEnvelope n xi
        (unitSourceSeedPhase n (n - 1) xi z) (n - 1) 1 0
    _ ≤ (4 / 3 : ℝ) * taoSection7PairSourceEnvelope n xi (n / 2) 1 0 :=
      unitSourcePairEnvelope_deficit_one n xi 1 0
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (unitSourceFullEnvelope_le_actualQ n xi hepsilon0 hepsilon1) (by norm_num)

/-- Primitive Fourier decay for the literal affine geometric PMF after
`n-1` steps at conductor `n`, uniformly over the finite-modulus seed. The
only analytic input is the existing canonical renewal packet. -/
theorem unitSourceAffinePMF_primitive_polynomial_decay
    (A : ℕ) (hA : 0 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ xi : ZMod (3 ^ n), zmodThreePrimitive n xi →
        ∀ z : ZMod (3 ^ n),
          ‖ZMod.dft (pmfComplexMass (unitSourceAffinePMF n (n - 1) z)) xi‖ ≤
            K / (n : ℝ) ^ A := by
  obtain ⟨packet⟩ := nonempty_taoSection7Prop78AbsolutePacket
  have hA1 : 1 ≤ A := by omega
  obtain ⟨C, _hC, hpoint⟩ :=
    exists_taoSection7Prop78_canonical_pointwise_737 packet A hA1
  let K₀ : ℝ := (C : ℝ) ^ A * (8 : ℝ) ^ A *
    taoSection7Geom4PolynomialMoment A
  have hCpow : 0 ≤ (C : ℝ) ^ A := pow_nonneg (Nat.cast_nonneg C) A
  have hK₀ : 0 ≤ K₀ := by
    dsimp [K₀]
    exact mul_nonneg (mul_nonneg hCpow (by positivity))
      (taoSection7Geom4PolynomialMoment_nonneg A)
  have hepsilon0 : 0 ≤ packet.epsilon := packet.scalar.epsilon_pos.le
  have hepsilon1 : packet.epsilon ≤ 1 :=
    packet.scalar.epsilon_le_one_hundredth.trans (by norm_num)
  refine ⟨(4 / 3 : ℝ) * K₀, mul_nonneg (by norm_num) hK₀, ?_⟩
  intro n hn xi hxi z
  have hQ : taoSection7HoldExpectationFull
      (taoSection7SourceActualQ n xi packet.epsilon) ≤ K₀ / (n : ℝ) ^ A := by
    simpa [K₀] using
      (taoSection7SourceActualQ_outer736_of_pointwise_decay
        (n := n) (A := A) (xi := xi)
        (epsilon := packet.epsilon) (D := (C : ℝ) ^ A)
        (by omega : 0 < n) hepsilon0 hCpow (hpoint n xi hxi))
  calc
    _ ≤ (4 / 3 : ℝ) * taoSection7HoldExpectationFull
        (taoSection7SourceActualQ n xi packet.epsilon) :=
      unitSourceAffinePMF_norm_dft_le_four_thirds_actualQ
        n xi z hepsilon0 hepsilon1
    _ ≤ (4 / 3 : ℝ) * (K₀ / (n : ℝ) ^ A) :=
      mul_le_mul_of_nonneg_left hQ (by norm_num)
    _ = _ := by ring

#print axioms unitSourceAffinePMF_primitive_polynomial_decay

end Erdos1135.Tao
