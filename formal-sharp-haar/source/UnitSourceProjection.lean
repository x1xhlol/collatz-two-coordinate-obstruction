import UnitSourcePrimitiveFourier
import Erdos1135.Tao.Section6.AmbientOffsetAppend

/-!
# Seeded source projection and an unused final exponent

The affine law is the literal image of the native geometric list PMF. Below
the step count, the seed vanishes under reduction and the native Syracuse
law is recovered exactly. At ambient level n the same law can be presented
using n geometric exponents, with only the first n-1 used in the output.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Erdos1135.Tao

/-- Reduction below the number of affine steps erases the terminal seed. -/
theorem unitSourceAffineOffset_projection_eq_take
    {r N k : ℕ} (hrN : r ≤ N) (hrk : r ≤ k)
    (z : ZMod (3 ^ N)) (as : List ℕ+) :
    taoZModThreeProjection hrN (unitSourceAffineOffset N k z as) =
      taoSection7OffsetZMod r (as.take r) := by
  have hpow : (3 : ZMod (3 ^ r)) ^ k = 0 := by
    simpa only [Nat.cast_pow] using (ZMod.natCast_pow_eq_zero_of_le 3 hrk)
  unfold unitSourceAffineOffset
  rw [map_add, map_mul, map_mul, taoZModThreeProjection_three_pow, hpow]
  simp only [zero_mul, add_zero]
  rw [taoSection7OffsetZMod_eq_offsetPrefix]
  unfold taoSection7OffsetPrefix
  rw [map_sum]
  calc
    (∑ i ∈ Finset.range k,
        taoZModThreeProjection hrN (taoSection7OffsetSummand N as i)) =
      ∑ i ∈ Finset.range r,
        taoZModThreeProjection hrN (taoSection7OffsetSummand N as i) := by
      symm
      apply Finset.sum_subset (Finset.range_mono hrk)
      intro i _hik hir
      have hri : r ≤ i := Nat.le_of_not_gt
        (fun hi => hir (Finset.mem_range.mpr hi))
      unfold taoSection7OffsetSummand
      rw [map_mul, taoZModThreeProjection_three_pow]
      have hp : (3 : ZMod (3 ^ r)) ^ i = 0 := by
        simpa only [Nat.cast_pow] using (ZMod.natCast_pow_eq_zero_of_le 3 hri)
      rw [hp, zero_mul]
    _ = ∑ i ∈ Finset.range r, taoSection7OffsetSummand r (as.take r) i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i + 1 ≤ r := Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
      unfold taoSection7OffsetSummand
      rw [map_mul, taoZModThreeProjection_three_pow,
        taoZModThreeProjection_inv_two_pow]
      simp only [List.take_take, Nat.min_eq_left hir]

/-- The lower-conductor marginal of the literal seeded source is the native
Syracuse offset law once at least that many geometric steps have occurred. -/
theorem unitSourceAffinePMF_projection_eq_syracPMF
    {r N k : ℕ} (hrN : r ≤ N) (hrk : r ≤ k)
    (z : ZMod (3 ^ N)) :
    (unitSourceAffinePMF N k z).map (taoZModThreeProjection hrN) = syracPMF r := by
  unfold unitSourceAffinePMF
  rw [PMF.map_comp, syracPMF_eq_geom2PNatListPMF_map_taoSection7OffsetZMod]
  have hfun : taoZModThreeProjection hrN ∘ unitSourceAffineOffset N k z =
      taoSection7OffsetZMod r ∘ (fun as : List ℕ+ => as.take r) := by
    funext as
    exact unitSourceAffineOffset_projection_eq_take hrN hrk z as
  rw [hfun, ← PMF.map_comp, geom2PNatListPMF_map_take_eq_of_le hrk]

/-- Exact DFT descent when the reduced conductor lies below the step count. -/
theorem unitSourceAffinePMF_dft_three_pow_mul_eq_syracPMF
    (r j k : ℕ) (hrk : r ≤ k)
    (z eta : ZMod (3 ^ (r + j))) :
    ZMod.dft (pmfComplexMass (unitSourceAffinePMF (r + j) k z))
        ((3 : ZMod (3 ^ (r + j))) ^ j * eta) =
      ZMod.dft (pmfComplexMass (syracPMF r))
        (taoZModThreeProjection (Nat.le_add_right r j) eta) := by
  let pi := taoZModThreeProjection (Nat.le_add_right r j)
  let p := unitSourceAffinePMF (r + j) k z
  have hmap : p.map (fun x => x) = p := by simpa only [id_eq] using PMF.map_id p
  have hsource := tao_dft_pmfComplexMass_map_apply p (fun x => x)
    ((3 : ZMod (3 ^ (r + j))) ^ j * eta)
  rw [hmap] at hsource
  calc
    _ = ∑' x : ZMod (3 ^ (r + j)),
      taoForwardDFTKernel x ((3 : ZMod (3 ^ (r + j))) ^ j * eta) *
        (((p x).toReal : ℝ) : ℂ) := hsource
    _ = ∑' x : ZMod (3 ^ (r + j)),
      taoForwardDFTKernel (pi x) (pi eta) * (((p x).toReal : ℝ) : ℂ) := by
      apply tsum_congr
      intro x
      rw [taoForwardDFTKernel_three_pow_mul_eq_projection]
    _ = ZMod.dft (pmfComplexMass (p.map pi)) (pi eta) :=
      (tao_dft_pmfComplexMass_map_apply p pi (pi eta)).symm
    _ = _ := by
      rw [show p.map pi = syracPMF r from
        unitSourceAffinePMF_projection_eq_syracPMF (Nat.le_add_right r j) hrk z]

/-- A length-n source presentation with one unused final geometric exponent. -/
noncomputable def unitSourceLengthNMap
    (n : ℕ) (z : ZMod (3 ^ n)) (full : List ℕ+) : ZMod (3 ^ n) :=
  unitSourceAffineOffset n (n - 1) z (full.take (n - 1))

theorem unitSourceLengthNMap_pmf_eq (n : ℕ) (z : ZMod (3 ^ n)) :
    (geom2PNatListPMF n).map (unitSourceLengthNMap n z) =
      unitSourceAffinePMF n (n - 1) z := by
  change (geom2PNatListPMF n).map
      (unitSourceAffineOffset n (n - 1) z ∘ (fun full => full.take (n - 1))) = _
  rw [← PMF.map_comp, geom2PNatListPMF_map_take_eq_of_le (Nat.sub_le n 1)]
  rfl

end Erdos1135.Tao
