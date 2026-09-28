import Erdos1135.ND.Fourier.FixedTotalConductorDecay
import Erdos1135.ND.Fourier.FixedSplitCollision
import Erdos1135.Tao.Section6.AmbientTailDecay

/-!
# Fixed-Total Ambient Tail Decay

This leaf factors every discarded ambient frequency at its exact power of
three, applies the fixed-total conductor-mixture estimate at the positive
primitive cofactor, and weakens the reduced level using the checked
comparison `n ≤ 20 * r`.  Its final corollary supplies the literal tail
hypothesis of the fixed-split Fourier collision theorem.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

open Tao

noncomputable section

private theorem
    norm_dft_ndSection6FixedSplitTailSubmass_le_of_natConductor
    {A : ℕ} {C : ℝ}
    (hnum : ∀ n : ℕ, 1 ≤ n →
      ∀ xi : ZMod (3 ^ n), Tao.zmodThreePrimitive n xi →
        ∀ L : ℕ,
          ‖ndSection7FiberNumerator n L xi‖ ≤
            C / (n : ℝ) ^ A)
    (q T r j l R : ℕ)
    (hT : r + j = T) (hr : 1 ≤ r) (hR : T ≤ R)
    (xi : ZMod (3 ^ (T + q)))
    (eta : ℕ) (heta : ¬3 ∣ eta)
    (hxi : Tao.taoSection6TailScaledFrequency
        (Nat.le_add_right T q) l xi =
      (3 : ZMod (3 ^ T)) ^ j * eta) :
    ‖ZMod.dft (fun z =>
      ((ndSection6FixedSplitTailSubmass q T l R z : ℝ) : ℂ)) xi‖ ≤
      C / (r : ℝ) ^ A := by
  subst T
  refine
    norm_dft_ndSection6FixedSplitTailSubmass_le_of_uniformNumerator
      q r j l R hR xi (eta : ZMod (3 ^ (r + j))) hxi ?_
  intro L
  simpa only [Tao.taoZModThreeProjection_natCast] using
    hnum r hr (eta : ZMod (3 ^ r))
      (Tao.zmodThreePrimitive_natCast_of_not_dvd hr heta) L

/-- Uniform primitive decay on every retained fixed-total numerator gives the
exact ambient decay scale required by the Section-6 collision theorem. -/
theorem norm_dft_ndSection6FixedSplitTailSubmass_le_tailDecayDelta
    {A : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hnum : ∀ n : ℕ, 1 ≤ n →
      ∀ xi : ZMod (3 ^ n), Tao.zmodThreePrimitive n xi →
        ∀ L : ℕ,
          ‖ndSection7FiberNumerator n L xi‖ ≤
            C / (n : ℝ) ^ A)
    {T k m l R : ℕ}
    (hR : T ≤ R)
    (hhead : k + 1 ≤ m)
    (hm : 9 * (T + (k + 1)) ≤ 10 * m)
    (hk : 20 * k ≤ 17 * (T + (k + 1)))
    (xi : ZMod (3 ^ (T + (k + 1))))
    (hxi : ¬Tao.zmodThreePowMultiple
      (T + (k + 1)) (T + (k + 1) - m) xi) :
    ‖ZMod.dft (fun z =>
      ((ndSection6FixedSplitTailSubmass
        (k + 1) T l R z : ℝ) : ℂ)) xi‖ ≤
      Tao.taoSection6TailDecayDelta C A (T + (k + 1)) := by
  have hqT : T + (k + 1) - m ≤ T := by omega
  have hTn : T ≤ T + (k + 1) := by omega
  have hscaled :
      ¬Tao.zmodThreePowMultiple T (T + (k + 1) - m)
        (Tao.taoSection6TailScaledFrequency hTn l xi) :=
    Tao.taoSection6TailScaledFrequency_not_pow_multiple
      hqT hTn hxi
  obtain ⟨j, eta, hj, heta, hfactor⟩ :=
    Tao.exists_three_pow_mul_not_dvd_of_not_pow_multiple hscaled
  have hjT : j < T := hj.trans_le hqT
  let r := T - j
  have hjr : j + r = T := by
    dsimp [r]
    omega
  obtain ⟨hrj, hr, _hmkr, _hnmk, hnr⟩ :=
    Tao.taoSection6_conductor_index_bounds
      (n := T + (k + 1)) (m := m) (k := k)
      (T := T) (j := j) (r := r)
      (by omega) hjr hhead hj hm hk
  have hraw :
      ‖ZMod.dft (fun z =>
        ((ndSection6FixedSplitTailSubmass
          (k + 1) T l R z : ℝ) : ℂ)) xi‖ ≤
        C / (r : ℝ) ^ A :=
    norm_dft_ndSection6FixedSplitTailSubmass_le_of_natConductor
      hnum (k + 1) T r j l R hrj hr hR xi eta heta hfactor
  have hn_pos : 0 < T + (k + 1) := by omega
  have hr_real_pos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hn_real_pos : 0 < ((T + (k + 1) : ℕ) : ℝ) := by
    exact_mod_cast hn_pos
  have hnr_real :
      ((T + (k + 1) : ℕ) : ℝ) ≤ (20 : ℝ) * (r : ℝ) := by
    exact_mod_cast hnr
  have hpow :
      (((T + (k + 1) : ℕ) : ℝ) ^ A) ≤
        (20 : ℝ) ^ A * (r : ℝ) ^ A := by
    calc
      (((T + (k + 1) : ℕ) : ℝ) ^ A) ≤
          ((20 : ℝ) * (r : ℝ)) ^ A := by gcongr
      _ = (20 : ℝ) ^ A * (r : ℝ) ^ A := by rw [mul_pow]
  have hr_pow_pos : 0 < (r : ℝ) ^ A := pow_pos hr_real_pos A
  have hn_pow_pos :
      0 < (((T + (k + 1) : ℕ) : ℝ) ^ A) :=
    pow_pos hn_real_pos A
  calc
    _ ≤ C / (r : ℝ) ^ A := hraw
    _ ≤ C * (20 : ℝ) ^ A /
        (((T + (k + 1) : ℕ) : ℝ) ^ A) := by
      apply (div_le_div_iff₀ hr_pow_pos hn_pow_pos).2
      calc
        C * (((T + (k + 1) : ℕ) : ℝ) ^ A)
            ≤ C * ((20 : ℝ) ^ A * (r : ℝ) ^ A) :=
          mul_le_mul_of_nonneg_left hpow hC
        _ = (C * (20 : ℝ) ^ A) * (r : ℝ) ^ A := by ring
    _ = Tao.taoSection6TailDecayDelta
          C A (T + (k + 1)) := rfl

/-- The ambient fixed-total tail bound closes the explicit tail premise of
the checked raw-convolution collision theorem.  The head L2 sum remains
visible for the next P2 unit. -/
theorem ndSection6FixedSplitOscillation_sq_le_of_numeratorDecay
    {A : ℕ} {C CA : ℝ}
    (hC : 0 ≤ C)
    (hnum : ∀ n : ℕ, 1 ≤ n →
      ∀ xi : ZMod (3 ^ n), Tao.zmodThreePrimitive n xi →
        ∀ R : ℕ,
          ‖ndSection7FiberNumerator n R xi‖ ≤
            C / (n : ℝ) ^ A)
    {T k L m : ℕ}
    {s : NDFixedTotalSplitIndex (k + 1) T L}
    (hmn : m ≤ T + (k + 1))
    (hhead : k + 1 ≤ m)
    (hm : 9 * (T + (k + 1)) ≤ 10 * m)
    (hk : 20 * k ≤ 17 * (T + (k + 1))) :
    Tao.taoZModPowOscillation m (T + (k + 1))
        (ndSection6FixedSplitSourceSubmass CA T k L s) ^ 2 ≤
      (Tao.taoSection6TailDecayDelta C A (T + (k + 1))) ^ 2 *
        (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) *
        ∑ y, (Tao.taoSection6HeadSubmass
          CA (T + (k + 1)) k s.headTotal y) ^ 2 := by
  apply ndSection6FixedSplitOscillation_sq_le
    hmn
    (Tao.taoSection6TailDecayDelta_nonneg
      hC A (T + (k + 1)))
  intro xi hxi
  exact norm_dft_ndSection6FixedSplitTailSubmass_le_tailDecayDelta
    hC hnum s.tailLength_le hhead hm hk xi hxi

/-- The repaired Section-6 head collision bound absorbs the remaining head
L2 sum, uniformly over every feasible fixed-total split. -/
theorem exists_ndSection6FixedSplitOscillation_sq_le_of_numeratorDecay
    {A : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hnum : ∀ n : ℕ, 1 ≤ n →
      ∀ xi : ZMod (3 ^ n), Tao.zmodThreePrimitive n xi →
        ∀ R : ℕ,
          ‖ndSection7FiberNumerator n R xi‖ ≤
            C / (n : ℝ) ^ A)
    (CA : ℝ) (hCA : 17 ≤ CA) :
    ∃ N0 : ℕ, ∀ {T k L m : ℕ},
      ∀ {s : NDFixedTotalSplitIndex (k + 1) T L},
      N0 ≤ T + (k + 1) →
      m ≤ T + (k + 1) →
      k + 1 ≤ m →
      9 * (T + (k + 1)) ≤ 10 * m →
      20 * k ≤ 17 * (T + (k + 1)) →
      Tao.taoZModPowOscillation m (T + (k + 1))
          (ndSection6FixedSplitSourceSubmass CA T k L s) ^ 2 ≤
        (Tao.taoSection6TailDecayDelta C A (T + (k + 1))) ^ 2 *
          (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) *
          (1 / 2 : ℝ) ^ s.headTotal := by
  obtain ⟨N0, hN0⟩ :=
    Tao.exists_taoSection6HeadSubmass_sum_sq_le CA hCA
  refine ⟨N0, ?_⟩
  intro T k L m s hn hmn hhead hm hk
  calc
    Tao.taoZModPowOscillation m (T + (k + 1))
        (ndSection6FixedSplitSourceSubmass CA T k L s) ^ 2 ≤
      (Tao.taoSection6TailDecayDelta C A (T + (k + 1))) ^ 2 *
        (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) *
        ∑ y, (Tao.taoSection6HeadSubmass
          CA (T + (k + 1)) k s.headTotal y) ^ 2 :=
      ndSection6FixedSplitOscillation_sq_le_of_numeratorDecay
        hC hnum hmn hhead hm hk
    _ ≤ (Tao.taoSection6TailDecayDelta C A (T + (k + 1))) ^ 2 *
        (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) *
        (1 / 2 : ℝ) ^ s.headTotal := by
      exact mul_le_mul_of_nonneg_left
        (hN0 (T + (k + 1)) hn k s.headTotal)
        (mul_nonneg (sq_nonneg _) (by positivity))

/-- The checked fixed-fiber numerator theorem supplies one eventual
polynomial fixed-split collision packet for every positive exponent. -/
theorem exists_ndSection6FixedSplitOscillation_sq_le
    (A : ℕ) (hA : 0 < A) (CA : ℝ) (hCA : 17 ≤ CA) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∃ N0 : ℕ, ∀ {T k L m : ℕ},
        ∀ {s : NDFixedTotalSplitIndex (k + 1) T L},
        N0 ≤ T + (k + 1) →
        m ≤ T + (k + 1) →
        k + 1 ≤ m →
        9 * (T + (k + 1)) ≤ 10 * m →
        20 * k ≤ 17 * (T + (k + 1)) →
        Tao.taoZModPowOscillation m (T + (k + 1))
            (ndSection6FixedSplitSourceSubmass CA T k L s) ^ 2 ≤
          (Tao.taoSection6TailDecayDelta C A (T + (k + 1))) ^ 2 *
            (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) *
            (1 / 2 : ℝ) ^ s.headTotal := by
  obtain ⟨C, hC, hnum⟩ :=
    exists_ndSection7FiberNumerator_polynomial_decay A hA
  obtain ⟨N0, hN0⟩ :=
    exists_ndSection6FixedSplitOscillation_sq_le_of_numeratorDecay
      hC hnum CA hCA
  exact ⟨C, hC, N0, hN0⟩

end

end ND
end Erdos1135
