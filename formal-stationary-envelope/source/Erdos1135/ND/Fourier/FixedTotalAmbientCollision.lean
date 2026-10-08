import Erdos1135.ND.Fourier.FixedTotalAmbientDecay
import Erdos1135.ND.Fourier.FixedTotalAmbientSlice

/-!
# Raw Fixed-Total Ambient Collision

This leaf transports the checked fixed-split Fourier collision packet to an
arbitrary raw fixed-total ambient slice.  Inhabited slices retain a complete
head-gate witness, which supplies the stopping-index geometry required by the
split theorem; all infeasible slices are the zero vector.

No endpoint mass, conditioned split weight, or aggregation occurs here.
-/

namespace Erdos1135
namespace ND

open Tao

noncomputable section

/-- Every raw fixed-total ambient slice has the squared oscillation decay of
its unique feasible fixed split.  The public interface exposes only the
ambient high-frequency hypotheses: the head-index and conductor premises are
derived from the retained complete source witness. -/
theorem exists_ndSection6FixedTotalAmbientOscillation_sq_le
    (A : ℕ) (hA : 0 < A) (CA : ℝ) (hCA : 17 ≤ CA) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∃ N0 : ℕ, ∀ T k l L m : ℕ,
        N0 ≤ T + (k + 1) →
        m ≤ T + (k + 1) →
        9 * (T + (k + 1)) ≤ 10 * m →
        Tao.taoZModPowOscillation m (T + (k + 1))
            (ndSection6FixedTotalAmbientSubmass
              CA (T + (k + 1)) k l L) ^ 2 ≤
          (Tao.taoSection6TailDecayDelta C A
            (T + (k + 1))) ^ 2 *
          (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) *
          (1 / 2 : ℝ) ^ l := by
  obtain ⟨C, hC, Ncollision, hcollision⟩ :=
    exists_ndSection6FixedSplitOscillation_sq_le A hA CA hCA
  obtain ⟨Nindex, hindex⟩ :=
    Tao.exists_taoSection6HeadGate_index_le CA hCA
  refine ⟨C, hC, max Ncollision Nindex, ?_⟩
  intro T k l L m hn hmn hm
  have hncollision : Ncollision ≤ T + (k + 1) :=
    (le_max_left _ _).trans hn
  have hnindex : Nindex ≤ T + (k + 1) :=
    (le_max_right _ _).trans hn
  rcases
      ndSection6FixedTotalAmbientSubmass_add_eq_zero_or_exists_gate_fixedSplit
        CA T k l L with
    hzero | ⟨full, hgate, s, hs, _hfiber, heq⟩
  · have hrhs :
        0 ≤ (Tao.taoSection6TailDecayDelta C A
            (T + (k + 1))) ^ 2 *
          (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) *
          (1 / 2 : ℝ) ^ l := by
      exact mul_nonneg
        (mul_nonneg (sq_nonneg _) (by positivity))
        (pow_nonneg (by norm_num) l)
    simpa [hzero] using hrhs
  · have hk : 20 * k ≤ 17 * (T + (k + 1)) :=
      hindex (T + (k + 1)) hnindex k l
        (full.take (k + 1)) hgate.1.2
    have hhead : k + 1 ≤ m :=
      Tao.taoSection6HeadIndex_le_m_of_bounds (by omega) hm hk
    rw [heq]
    simpa only [hs] using
      hcollision (s := s) hncollision hmn hhead hm hk

end

end ND
end Erdos1135
