import Erdos1135.Tao.Section6.AmbientTailDecay
import Erdos1135.Tao.Section6.FiniteFourierCollision
import Erdos1135.Tao.Section6.GatedSourceConvolution
import Erdos1135.Tao.Section6.HeadSubmass

/-!
# Section 6 Fixed-Slice Collision

This leaf combines the exact gated source convolution, reduced-conductor tail
decay, and the fixed-head collision cap.  It proves the squared oscillation
bound for one fixed `k,l` slice and leaves concentration and slice summation
to later modules.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

/-- Exact fixed-slice Fourier collision bound from an explicit head L2 cap.
There is exactly one ambient factor `3^n`. -/
theorem taoSection6FixedSliceOscillation_sq_le
    {B : ℕ} {C : ℝ}
    (hdecay : syracPMFPrimitivePolynomialDecayAt B C)
    (hC : 0 ≤ C)
    {CA : ℝ} {T k l m : ℕ}
    (hmn : m ≤ T + (k + 1))
    (hhead : k + 1 ≤ m)
    (hm : 9 * (T + (k + 1)) ≤ 10 * m)
    (hk : 20 * k ≤ 17 * (T + (k + 1)))
    (hheadL2 :
      (∑ y : ZMod (3 ^ (T + (k + 1))),
        (taoSection6HeadSubmass CA (T + (k + 1)) k l y) ^ 2) ≤
          (1 / 2 : ℝ) ^ l) :
    taoZModPowOscillation m (T + (k + 1))
        (taoSection6GatedSourceSubmass CA T k l) ^ 2 ≤
      (taoSection6TailDecayDelta C B (T + (k + 1))) ^ 2 *
        (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) *
        (1 / 2 : ℝ) ^ l := by
  let tau : ZMod (3 ^ (T + (k + 1))) → ℝ := fun z =>
    (taoSection6AmbientTailPMF (k + 1) T l z).toReal
  have hsource :
      taoSection6GatedSourceSubmass CA T k l =
        taoZModRawConvolution
          (taoSection6HeadSubmass CA (T + (k + 1)) k l) tau := by
    funext x
    simpa [tau] using
      taoSection6GatedSourceSubmass_eq_rawConvolution CA T k l x
  rw [hsource]
  have htail : ∀ xi : ZMod (3 ^ (T + (k + 1))),
      ¬zmodThreePowMultiple
          (T + (k + 1)) (T + (k + 1) - m) xi →
        ‖ZMod.dft (fun x => ((tau x : ℝ) : ℂ)) xi‖ ≤
          taoSection6TailDecayDelta C B (T + (k + 1)) := by
    intro xi hxi
    simpa [tau, pmfComplexMass] using
      hdecay.dft_taoSection6AmbientTailPMF_le
        hC hhead hm hk xi hxi
  have hcollision :=
    taoZModPowOscillation_rawConvolution_sq_le
      hmn
      (taoSection6HeadSubmass CA (T + (k + 1)) k l)
      tau
      (taoSection6TailDecayDelta_nonneg hC B (T + (k + 1)))
      htail
  calc
    taoZModPowOscillation m (T + (k + 1))
        (taoZModRawConvolution
          (taoSection6HeadSubmass CA (T + (k + 1)) k l)
          tau) ^ 2 ≤
      (taoSection6TailDecayDelta C B (T + (k + 1))) ^ 2 *
        (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) *
        ∑ y : ZMod (3 ^ (T + (k + 1))),
          (taoSection6HeadSubmass CA (T + (k + 1)) k l y) ^ 2 :=
      hcollision
    _ ≤ (taoSection6TailDecayDelta C B (T + (k + 1))) ^ 2 *
        (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) *
        (1 / 2 : ℝ) ^ l := by
      exact mul_le_mul_of_nonneg_left hheadL2
        (mul_nonneg (sq_nonneg _) (by positivity))

/-- Eventual conditional fixed-slice collision bound.  The head L2 input is
discharged by repaired Corollary 6.3 and crossing localization, while the
conductor-geometry bounds remain explicit inputs. -/
theorem exists_taoSection6FixedSliceOscillation_sq_le_of_bounds
    {B : ℕ} {C : ℝ}
    (hdecay : syracPMFPrimitivePolynomialDecayAt B C)
    (hC : 0 ≤ C)
    (CA : ℝ) (hCA : 17 ≤ CA) :
    ∃ N0 : ℕ, ∀ T k l m : ℕ,
      N0 ≤ T + (k + 1) →
      m ≤ T + (k + 1) →
      k + 1 ≤ m →
      9 * (T + (k + 1)) ≤ 10 * m →
      20 * k ≤ 17 * (T + (k + 1)) →
      taoZModPowOscillation m (T + (k + 1))
          (taoSection6GatedSourceSubmass CA T k l) ^ 2 ≤
        (taoSection6TailDecayDelta C B (T + (k + 1))) ^ 2 *
          (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) *
          (1 / 2 : ℝ) ^ l := by
  obtain ⟨N0, hN0⟩ := exists_taoSection6HeadSubmass_sum_sq_le CA hCA
  refine ⟨N0, ?_⟩
  intro T k l m hn hmn hhead hm hk
  exact taoSection6FixedSliceOscillation_sq_le
    hdecay hC hmn hhead hm hk (hN0 (T + (k + 1)) hn k l)

end

end Tao
end Erdos1135
