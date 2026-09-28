import Erdos1135.Tao.Fourier.Section7SChiActualQ
import Erdos1135.Tao.Fourier.Section7SourceLaw
import Erdos1135.Tao.Renewal.Outer736HoldExpectation
import Erdos1135.Tao.Renewal.Prop78Pointwise737

/-!
# Canonical Proposition 7.1 Assembly

This leaf composes pointwise `(7.37)`, outer `(7.36)`, and the checked source
character law.  It closes the current positive-natural-exponent Proposition
7.1 surface and the primitive-frequency Proposition 1.17 surface.  Tao's
literal arbitrary-real-exponent adapter remains a separate statement-fidelity
step.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- One absolute Proposition 7.8 packet supplies Section 7 character decay
for every later requested positive natural exponent. -/
theorem TaoSection7Prop78AbsolutePacket.to_prop71_character_decay
    (packet : TaoSection7Prop78AbsolutePacket) :
    TaoProp71CharacterDecayStatement := by
  intro A hA
  have hA1 : 1 ≤ A := by omega
  obtain ⟨C, _hC, hpoint⟩ :=
    exists_taoSection7Prop78_canonical_pointwise_737 packet A hA1
  let K : ℝ :=
    (C : ℝ) ^ A * (8 : ℝ) ^ A *
      taoSection7Geom4PolynomialMoment A
  have hCpow : 0 ≤ (C : ℝ) ^ A :=
    pow_nonneg (Nat.cast_nonneg C) A
  have h8pow : 0 ≤ (8 : ℝ) ^ A := by positivity
  have hmoment : 0 ≤ taoSection7Geom4PolynomialMoment A :=
    taoSection7Geom4PolynomialMoment_nonneg A
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg hCpow h8pow) hmoment
  have hepsilon0 : 0 ≤ packet.epsilon :=
    packet.scalar.epsilon_pos.le
  have hepsilon1 : packet.epsilon ≤ 1 :=
    packet.scalar.epsilon_le_one_hundredth.trans (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro n hn xi hxi
  have hn_pos : 0 < n := by omega
  calc
    ‖taoSection7SChi n xi‖ ≤
        taoSection7HoldExpectationFull
          (taoSection7SourceActualQ n xi packet.epsilon) :=
      norm_taoSection7SChi_le_holdExpectation_sourceActualQ
        n xi hepsilon0 hepsilon1
    _ ≤ K / (n : ℝ) ^ A := by
      simpa [K] using
        (taoSection7SourceActualQ_outer736_of_pointwise_decay
          (n := n) (A := A) (xi := xi)
          (epsilon := packet.epsilon) (D := (C : ℝ) ^ A)
          hn_pos hepsilon0 hCpow (hpoint n xi hxi))

/-- Unconditional current Proposition 7.1 surface, with the absolute packet
selected before the requested exponent. -/
theorem taoProp71CharacterDecay : TaoProp71CharacterDecayStatement := by
  obtain ⟨packet⟩ := nonempty_taoSection7Prop78AbsolutePacket
  exact packet.to_prop71_character_decay

/-- Primitive-frequency Proposition 1.17 in the current natural-exponent
surface.  Imprimitive frequencies are intentionally left to conductor descent
in Section 6. -/
theorem taoProp117PrimitivePolynomialDecay :
    TaoProp117PrimitivePolynomialDecayStatement :=
  TaoProp117PrimitivePolynomialDecayStatement.of_section7_character
    TaoSection7CharacterBridgeStatement.source_law
    taoProp71CharacterDecay

end

end Tao
end Erdos1135
