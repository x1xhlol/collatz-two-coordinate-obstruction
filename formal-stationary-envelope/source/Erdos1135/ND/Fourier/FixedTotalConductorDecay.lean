import Erdos1135.ND.Fourier.FixedTotalConductor
import Erdos1135.ND.Fourier.FiberNumeratorDecay

/-!
# Fixed-Total Conductor Decay

The dropped suffix in the exact conductor mixture has total mass at most one.
Consequently any bound uniform in the retained fixed total passes directly to
the accepted-tail DFT, without a central-window split or endpoint
renormalization.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

open Tao

noncomputable section

/-- The iid Geom(2) endpoint mass is nonnegative. -/
theorem ndGeom2EndpointMass_nonneg (n L : ℕ) :
    0 ≤ ndGeom2EndpointMass n L := by
  unfold ndGeom2EndpointMass
  exact ENNReal.toReal_nonneg

private theorem ndGeom2EndpointMass_eq_weightMap_apply
    (n L : ℕ) :
    ndGeom2EndpointMass n L =
      (((Tao.geom2PNatListPMF n).map Tao.taoTupleWeight) L).toReal := by
  rw [ndGeom2EndpointMass_eq_weightSelector,
    Tao.taoPMF_map_apply_toReal_tsum]
  apply tsum_congr
  intro as
  by_cases h : Tao.taoTupleWeight as = L
  · rw [if_pos h, if_pos h.symm]
  · have h' : L ≠ Tao.taoTupleWeight as :=
      fun h' => h h'.symm
    rw [if_neg h, if_neg h']

/-- Any finite collection of endpoint masses has total at most one. -/
theorem sum_ndGeom2EndpointMass_le_one
    (n : ℕ) (S : Finset ℕ) :
    ∑ L ∈ S, ndGeom2EndpointMass n L ≤ 1 := by
  classical
  let p : PMF ℕ :=
    (Tao.geom2PNatListPMF n).map Tao.taoTupleWeight
  have hp : Summable fun L : ℕ => (p L).toReal :=
    Tao.taoPMF_summable_toReal p
  calc
    (∑ L ∈ S, ndGeom2EndpointMass n L) =
        ∑ L ∈ S, (p L).toReal := by
      apply Finset.sum_congr rfl
      intro L _hL
      simpa [p] using ndGeom2EndpointMass_eq_weightMap_apply n L
    _ ≤ ∑' L : ℕ, (p L).toReal :=
      hp.sum_le_tsum S (fun _ _ => ENNReal.toReal_nonneg)
    _ = 1 := by
      have hp_one := congrArg ENNReal.toReal (PMF.tsum_coe p)
      rw [ENNReal.tsum_toReal_eq (PMF.apply_ne_top p)] at hp_one
      simpa using hp_one

/-- A fixed-total numerator estimate that is uniform in the retained total
passes through the exact conductor mixture to the accepted-tail DFT. -/
theorem norm_dft_ndSection6FixedSplitTailSubmass_le_of_uniformNumerator
    {A : ℕ} {C : ℝ}
    (q r j l R : ℕ) (hR : r + j ≤ R)
    (xi : ZMod (3 ^ ((r + j) + q)))
    (eta : ZMod (3 ^ (r + j)))
    (hxi : Tao.taoSection6TailScaledFrequency
        (Nat.le_add_right (r + j) q) l xi =
      (3 : ZMod (3 ^ (r + j))) ^ j * eta)
    (hnum : ∀ L : ℕ,
      ‖ndSection7FiberNumerator r L
        (Tao.taoZModThreeProjection
          (Nat.le_add_right r j) eta)‖ ≤
        C / (r : ℝ) ^ A) :
    ‖ZMod.dft (fun z =>
      ((ndSection6FixedSplitTailSubmass
        q (r + j) l R z : ℝ) : ℂ)) xi‖ ≤
      C / (r : ℝ) ^ A := by
  rw [dft_ndSection6FixedSplitTailSubmass_eq_droppedTotalSum
    q r j l R hR xi eta hxi]
  have hbound_nonneg : 0 ≤ C / (r : ℝ) ^ A :=
    (norm_nonneg _).trans (hnum R)
  calc
    ‖∑ t ∈ Finset.Icc j (R - r),
        (ndGeom2EndpointMass j t : ℂ) *
          ndSection7FiberNumerator r (R - t)
            (Tao.taoZModThreeProjection
              (Nat.le_add_right r j) eta)‖
        ≤ ∑ t ∈ Finset.Icc j (R - r),
            ‖(ndGeom2EndpointMass j t : ℂ) *
              ndSection7FiberNumerator r (R - t)
                (Tao.taoZModThreeProjection
                  (Nat.le_add_right r j) eta)‖ :=
      norm_sum_le _ _
    _ = ∑ t ∈ Finset.Icc j (R - r),
          ndGeom2EndpointMass j t *
            ‖ndSection7FiberNumerator r (R - t)
              (Tao.taoZModThreeProjection
                (Nat.le_add_right r j) eta)‖ := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (ndGeom2EndpointMass_nonneg j t)]
    _ ≤ ∑ t ∈ Finset.Icc j (R - r),
          ndGeom2EndpointMass j t * (C / (r : ℝ) ^ A) := by
      apply Finset.sum_le_sum
      intro t _ht
      exact mul_le_mul_of_nonneg_left
        (hnum (R - t)) (ndGeom2EndpointMass_nonneg j t)
    _ = (∑ t ∈ Finset.Icc j (R - r),
          ndGeom2EndpointMass j t) * (C / (r : ℝ) ^ A) := by
      rw [Finset.sum_mul]
    _ ≤ 1 * (C / (r : ℝ) ^ A) :=
      mul_le_mul_of_nonneg_right
        (sum_ndGeom2EndpointMass_le_one
          j (Finset.Icc j (R - r)))
        hbound_nonneg
    _ = C / (r : ℝ) ^ A := one_mul _

end

end ND
end Erdos1135
