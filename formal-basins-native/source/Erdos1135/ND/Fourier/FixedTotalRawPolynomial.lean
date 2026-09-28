import Erdos1135.ND.Fourier.FixedTotalRawEventAggregation
import Erdos1135.Tao.Section6.Geom2IntervalConcentration

/-!
# Raw Fixed-Total Polynomial Decay

This leaf combines the checked fixed-total local-union rate with the one-time
raw-event replacement and Tao's unconditional global-failure decay.  The
result remains unnormalized and uniform in the fixed total `L`.

No endpoint division, fiber window, or T3 estimate occurs here.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- The literal raw fixed-total residue vector has arbitrary polynomial decay
in the high regime, with one spare power for endpoint normalization. -/
theorem exists_ndSection6FixedTotalRawOscillation_le (Q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ n L m : ℕ, N0 ≤ n → m ≤ n → 9 * n ≤ 10 * m →
        Tao.taoZModPowOscillation m n
            (ndSection6FixedSplitTailSubmass 0 n 0 L) ≤
          C / (n : ℝ) ^ (Q + 1) := by
  let CA : ℝ := 8 * ((Q : ℝ) + 4)
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hCA : (17 : ℝ) ≤ CA := by
    dsimp [CA]
    nlinarith
  obtain ⟨D, hD, Nlocal, hNlocal, hlocal⟩ :=
    exists_ndSection6FixedTotalLocalUnionOscillation_le CA hCA Q
  obtain ⟨Nevent, hNevent, hevent⟩ :=
    exists_ndSection6FixedTotalRawOscillation_le_localUnion_add_globalFailure
      CA hCA
  refine ⟨2 * D + 2, by nlinarith, max Nlocal Nevent,
    hNevent.trans (le_max_right _ _), ?_⟩
  intro n L m hn hmn hhigh
  have hnLocal : Nlocal ≤ n := (le_max_left _ _).trans hn
  have hnEvent : Nevent ≤ n := (le_max_right _ _).trans hn
  have hnTwo : 2 ≤ n := hNevent.trans hnEvent
  have hfailure :
      2 * Tao.taoSection6GlobalFailureMass CA n ≤
        2 / (n : ℝ) ^ (Q + 1) := by
    have h := Tao.taoSection6GlobalFailureMass_le_inv_pow Q hnTwo
    dsimp [CA]
    calc
      2 * Tao.taoSection6GlobalFailureMass
            (8 * ((Q : ℝ) + 4)) n ≤
          2 * (1 / (n : ℝ) ^ (Q + 1)) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
      _ = 2 / (n : ℝ) ^ (Q + 1) := by ring
  calc
    Tao.taoZModPowOscillation m n
        (ndSection6FixedSplitTailSubmass 0 n 0 L) ≤
      Tao.taoZModPowOscillation m n
          (ndSection6FixedTotalLocalUnionSubmass CA n L) +
        2 * Tao.taoSection6GlobalFailureMass CA n :=
      hevent n hnEvent L m hmn
    _ ≤ (2 * D) / (n : ℝ) ^ (Q + 1) +
        2 / (n : ℝ) ^ (Q + 1) :=
      add_le_add (hlocal n L m hnLocal hmn hhigh) hfailure
    _ = (2 * D + 2) / (n : ℝ) ^ (Q + 1) := by ring

end

end ND
end Erdos1135
