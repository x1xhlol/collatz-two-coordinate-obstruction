import Erdos1135.ND.Fourier.FixedTotalAmbientCollision
import Erdos1135.Tao.Section6.HeadEntropyScalar

/-!
# Raw Fixed-Total Ambient Polynomial Decay

This leaf absorbs the head entropy factor in the checked squared raw-slice
estimate and produces the linear polynomial rate consumed by the later
two-parameter slice sum.  Feasible slices obtain the entropy bound from their
retained complete head gate; every other slice is the zero vector.

No fixed-ambient transport, aggregation, exceptional-event charge, or
endpoint normalization occurs here.
-/

namespace Erdos1135
namespace ND

open Tao

noncomputable section

/-- Every additive raw fixed-total ambient slice has an eventual linear
polynomial oscillation rate, uniformly in its head total and full total. -/
theorem exists_ndSection6FixedTotalAmbientOscillation_le
    (CA : ℝ) (hCA : 17 ≤ CA) (Q : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ N0 : ℕ, ∀ T k l L m : ℕ,
      N0 ≤ T + (k + 1) →
      m ≤ T + (k + 1) →
      9 * (T + (k + 1)) ≤ 10 * m →
      Tao.taoZModPowOscillation m (T + (k + 1))
          (ndSection6FixedTotalAmbientSubmass
            CA (T + (k + 1)) k l L) ≤
        D / ((T + (k + 1) : ℕ) : ℝ) ^ (Q + 3) := by
  let P := Tao.taoSection6HeadEntropyExponent CA
  let B := Q + P + 3
  have hB : 0 < B := by omega
  obtain ⟨C, hC, N0, hsq⟩ :=
    exists_ndSection6FixedTotalAmbientOscillation_sq_le B hB CA hCA
  let D := C * (20 : ℝ) ^ B
  have hD : 0 ≤ D := mul_nonneg hC (pow_nonneg (by norm_num) _)
  refine ⟨D, hD, N0, ?_⟩
  intro T k l L m hn hmn hm
  let n := T + (k + 1)
  change Tao.taoZModPowOscillation m n
      (ndSection6FixedTotalAmbientSubmass CA n k l L) ≤
    D / (n : ℝ) ^ (Q + 3)
  have hn_nat : 1 ≤ n := by
    dsimp [n]
    omega
  have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_nat
  have hn_pos : (0 : ℝ) < (n : ℝ) :=
    lt_of_lt_of_le zero_lt_one hn_real
  have hpowB :
      (n : ℝ) ^ B = (n : ℝ) ^ (Q + 3) * (n : ℝ) ^ P := by
    rw [show B = (Q + 3) + P by omega, pow_add]
  have hdelta :
      Tao.taoSection6TailDecayDelta C B n =
        (D / (n : ℝ) ^ (Q + 3)) / (n : ℝ) ^ P := by
    rw [Tao.taoSection6TailDecayDelta, hpowB]
    dsimp [D]
    field_simp
  have hP_one : (1 : ℝ) ≤ (n : ℝ) ^ P := one_le_pow₀ hn_real
  have hP_pos : (0 : ℝ) < (n : ℝ) ^ P := by positivity
  let R := D / (n : ℝ) ^ (Q + 3)
  have hR_nonneg : 0 ≤ R := by
    exact div_nonneg hD (pow_nonneg (by positivity) _)
  have hscalar :
      Tao.taoSection6TailDecayDelta C B n ^ 2 * (n : ℝ) ^ P ≤
        R ^ 2 := by
    rw [hdelta]
    change (R / (n : ℝ) ^ P) ^ 2 * (n : ℝ) ^ P ≤ R ^ 2
    rw [div_pow]
    field_simp
    nlinarith [sq_nonneg R]
  rcases
      ndSection6FixedTotalAmbientSubmass_add_eq_zero_or_exists_gate_fixedSplit
        CA T k l L with
    hzero | ⟨_full, hgate, _s, _hs, _hfiber, _heq⟩
  · simpa [n, R, hzero] using hR_nonneg
  · have hent :=
      Tao.taoSection6HeadGate_entropyFactor_lt_pow hn_nat hgate.1.2
    have hsq_entropy :
        Tao.taoZModPowOscillation m n
            (ndSection6FixedTotalAmbientSubmass CA n k l L) ^ 2 ≤
          Tao.taoSection6TailDecayDelta C B n ^ 2 * (n : ℝ) ^ P := by
      calc
        _ ≤ Tao.taoSection6TailDecayDelta C B n ^ 2 *
              (((3 ^ n : ℕ) : ℝ)) * (1 / 2 : ℝ) ^ l := by
          simpa [n] using hsq T k l L m hn hmn hm
        _ = Tao.taoSection6TailDecayDelta C B n ^ 2 *
              Tao.taoSection6HeadEntropyFactor n l := by
          simp only [Tao.taoSection6HeadEntropyFactor]
          ring
        _ ≤ Tao.taoSection6TailDecayDelta C B n ^ 2 * (n : ℝ) ^ P :=
          mul_le_mul_of_nonneg_left
            (by simpa [P] using le_of_lt hent) (sq_nonneg _)
    have hosc_nonneg :
        0 ≤ Tao.taoZModPowOscillation m n
          (ndSection6FixedTotalAmbientSubmass CA n k l L) := by
      simp only [Tao.taoZModPowOscillation]
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hosc_sq :
        Tao.taoZModPowOscillation m n
            (ndSection6FixedTotalAmbientSubmass CA n k l L) ^ 2 ≤
          R ^ 2 :=
      hsq_entropy.trans hscalar
    have hosc :
        Tao.taoZModPowOscillation m n
            (ndSection6FixedTotalAmbientSubmass CA n k l L) ≤ R := by
      nlinarith [sq_nonneg
        (Tao.taoZModPowOscillation m n
          (ndSection6FixedTotalAmbientSubmass CA n k l L) - R)]
    simpa [R] using hosc

end

end ND
end Erdos1135
