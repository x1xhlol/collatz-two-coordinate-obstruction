import Erdos1135.Tao.Section6.ConductorProjectivity

/-!
# Section 6 Conductor Descent For Syracuse Fourier Coefficients

This leaf combines Syracuse projectivity with compatibility of the standard
additive characters across powers of three.  A level-`r + j` coefficient at
frequency `3^j * eta` is exactly the level-`r` coefficient at the projected
cofactor.  The forward transforms are unnormalized, so no cardinality factor
appears.
-/

open scoped ZMod

namespace Erdos1135
namespace Tao

noncomputable section

private theorem taoForwardDFTKernel_three_pow_mul_natCast
    (r j x eta : ℕ) :
    taoForwardDFTKernel
        (x : ZMod (3 ^ (r + j)))
        ((3 : ZMod (3 ^ (r + j))) ^ j * eta) =
      taoForwardDFTKernel
        (x : ZMod (3 ^ r))
        (eta : ZMod (3 ^ r)) := by
  unfold taoForwardDFTKernel
  have hhigh :
      (x : ZMod (3 ^ (r + j))) *
          ((3 : ZMod (3 ^ (r + j))) ^ j * eta) =
        (x * (3 ^ j * eta) : ℕ) := by
    simp only [Nat.cast_mul, Nat.cast_pow]
    norm_num
  have hlow :
      (x : ZMod (3 ^ r)) * (eta : ZMod (3 ^ r)) =
        (x * eta : ℕ) := by
    simp only [Nat.cast_mul]
  rw [hhigh, hlow]
  rw [show -((x * (3 ^ j * eta) : ℕ) : ZMod (3 ^ (r + j))) =
      ((-(x * (3 ^ j * eta) : ℕ) : ℤ) : ZMod (3 ^ (r + j))) by norm_num]
  rw [show -((x * eta : ℕ) : ZMod (3 ^ r)) =
      ((-(x * eta : ℕ) : ℤ) : ZMod (3 ^ r)) by norm_num]
  change
    ZMod.stdAddChar
        (((-(x * (3 ^ j * eta) : ℕ) : ℤ) :
          ZMod (3 ^ (r + j)))) =
      ZMod.stdAddChar
        (((-(x * eta : ℕ) : ℤ) : ZMod (3 ^ r)))
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [pow_add]
  field_simp

/-- Multiplication by `3^j` lowers the additive character from level `r+j` to
level `r`.  The cofactor is projected; projecting the already multiplied
frequency would erase the conductor information. -/
theorem taoForwardDFTKernel_three_pow_mul_eq_projection
    (r j : ℕ) (x eta : ZMod (3 ^ (r + j))) :
    taoForwardDFTKernel x
        ((3 : ZMod (3 ^ (r + j))) ^ j * eta) =
      taoForwardDFTKernel
        (taoZModThreeProjection (Nat.le_add_right r j) x)
        (taoZModThreeProjection (Nat.le_add_right r j) eta) := by
  conv_lhs =>
    rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val eta]
  conv_rhs =>
    rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val eta]
  simp only [taoZModThreeProjection_natCast]
  exact taoForwardDFTKernel_three_pow_mul_natCast r j x.val eta.val

/-- Exact conductor descent for Syracuse Fourier coefficients.  There is no
normalization factor because the forward DFT is a character expectation. -/
theorem dft_syracPMF_three_pow_mul_eq_projection
    (r j : ℕ) (eta : ZMod (3 ^ (r + j))) :
    ZMod.dft (pmfComplexMass (syracPMF (r + j)))
        ((3 : ZMod (3 ^ (r + j))) ^ j * eta) =
      ZMod.dft (pmfComplexMass (syracPMF r))
        (taoZModThreeProjection (Nat.le_add_right r j) eta) := by
  let pi := taoZModThreeProjection (Nat.le_add_right r j)
  calc
    ZMod.dft (pmfComplexMass (syracPMF (r + j)))
        ((3 : ZMod (3 ^ (r + j))) ^ j * eta) =
      ∑' x : ZMod (3 ^ (r + j)),
        taoForwardDFTKernel x
            ((3 : ZMod (3 ^ (r + j))) ^ j * eta) *
          (((syracPMF (r + j) x).toReal : ℝ) : ℂ) := by
            have hsource :=
              tao_dft_pmfComplexMass_map_apply
                (syracPMF (r + j)) (fun x => x)
                ((3 : ZMod (3 ^ (r + j))) ^ j * eta)
            have hmap :
                (syracPMF (r + j)).map (fun x => x) =
                  syracPMF (r + j) := by
              simpa only [id_eq] using PMF.map_id (syracPMF (r + j))
            rw [hmap] at hsource
            exact hsource
    _ = ∑' x : ZMod (3 ^ (r + j)),
        taoForwardDFTKernel (pi x) (pi eta) *
          (((syracPMF (r + j) x).toReal : ℝ) : ℂ) := by
            apply tsum_congr
            intro x
            rw [taoForwardDFTKernel_three_pow_mul_eq_projection]
    _ = ZMod.dft (pmfComplexMass ((syracPMF (r + j)).map pi))
          (pi eta) := by
            exact
              (tao_dft_pmfComplexMass_map_apply
                (syracPMF (r + j)) pi (pi eta)).symm
    _ = ZMod.dft (pmfComplexMass (syracPMF r)) (pi eta) := by
            rw [syracPMF_map_taoZModThreeProjection_eq_of_le]

/-- Primitive decay at the positive reduced conductor controls the matching
imprimitive coefficient at every higher ambient level. -/
theorem syracPMFPrimitivePolynomialDecayAt.dft_three_pow_mul_le
    {A : ℕ} {C : ℝ} (hdecay : syracPMFPrimitivePolynomialDecayAt A C)
    {r j : ℕ} (hr : 1 ≤ r) {eta : ZMod (3 ^ (r + j))}
    (heta : zmodThreePrimitive r
      (taoZModThreeProjection (Nat.le_add_right r j) eta)) :
    ‖ZMod.dft (pmfComplexMass (syracPMF (r + j)))
        ((3 : ZMod (3 ^ (r + j))) ^ j * eta)‖ ≤
      C / (r : ℝ) ^ A := by
  rw [dft_syracPMF_three_pow_mul_eq_projection]
  exact hdecay.apply hr heta

end

end Tao
end Erdos1135
