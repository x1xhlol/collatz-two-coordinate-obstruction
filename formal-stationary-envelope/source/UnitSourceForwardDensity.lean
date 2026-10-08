import UnitSourceAffineForward
import UnitSourceUniformSeed

/-!
# Independent finite branch density

The forward PMF starts with the uniform unit digit. Its density is defined
independently by the explicit geometric branch transfer, with the factor
three from the finite Haar Jacobian. Induction identifies these two
constructions and proves the full-Haar factor 3/2.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Erdos1135.Tao

/-- Forward geometric affine evolution, initialized with the uniform unit digit. -/
noncomputable def unitSourceForwardPMF : (j : ℕ) → PMF (ZMod (3 ^ (j + 1)))
  | 0 => unitSourceInitialPMF
  | j + 1 => (unitSourceForwardPMF j).bind
      (fun y => geom2PNat.map (fun a => syracStep (j + 1) y a))

/-- Explicit branch transfer, with the factor-three finite Haar Jacobian.
This density is defined independently of `unitSourceForwardPMF`. -/
noncomputable def unitSourceBranchDensity : (j : ℕ) → ZMod (3 ^ (j + 1)) → ℝ
  | 0, x => if x = 0 then 0 else 1
  | j + 1, x => 3 * ∑ y : ZMod (3 ^ (j + 1)),
      unitSourceBranchDensity j y *
        ((geom2PNat.map (fun a => syracStep (j + 1) y a)) x).toReal

/-- The branch kernel uses the literal geometric weights, with no
abstract transition probability or limiting-density hypothesis. -/
theorem unitSourceBranchDensity_succ_explicit
    (j : ℕ) (x : ZMod (3 ^ (j + 1 + 1))) :
    unitSourceBranchDensity (j + 1) x =
      3 * ∑ y : ZMod (3 ^ (j + 1)), unitSourceBranchDensity j y *
        ∑' a : ℕ+, if x = syracStep (j + 1) y a then
          (1 / 2 : ℝ) ^ (a : ℕ) else 0 := by
  simp only [unitSourceBranchDensity, pmf_map_apply_toReal_tsum,
    geom2PNat_apply_toReal]

theorem unitSource_bind_apply_toReal_sum
    {α β : Type*} [Fintype α] (p : PMF α) (q : α → PMF β) (y : β) :
    ((p.bind q) y).toReal = ∑ s, (p s).toReal * (q s y).toReal := by
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro s _hs
    exact ENNReal.mul_ne_top (p.apply_ne_top s) ((q s).apply_ne_top y)

/-- The independent forward recursion equals the two fixed-seed mixture. -/
theorem unitSourceForwardPMF_eq_seed_mixture (j : ℕ) :
    unitSourceForwardPMF j = (PMF.uniformOfFintype (Fin 2)).bind
      (fun b => unitSourceAffinePMF (j + 1) j ((b.val + 1 : ℕ) : ZMod (3 ^ (j + 1)))) := by
  induction j with
  | zero =>
      simp only [unitSourceForwardPMF, unitSourceAffinePMF_zero]
      rfl
  | succ j ih =>
      rw [unitSourceForwardPMF, ih, PMF.bind_bind]
      apply congrArg (PMF.bind (PMF.uniformOfFintype (Fin 2)))
      funext b
      rw [unitSourceAffinePMF_succ]
      congr 2
      simp

/-- Every lower marginal is exactly the native Syracuse marginal. -/
theorem unitSourceForwardPMF_projection_eq_syracPMF
    {r j : ℕ} (hrj : r ≤ j) :
    (unitSourceForwardPMF j).map
      (taoZModThreeProjection (by omega : r ≤ j + 1)) = syracPMF r := by
  rw [unitSourceForwardPMF_eq_seed_mixture, PMF.map_bind]
  simp only [unitSourceAffinePMF_projection_eq_syracPMF (by omega : r ≤ j + 1) hrj,
    PMF.bind_const]

/-- Finite unit-Haar density normalization, proved from the branch recursion. -/
theorem unitSourceBranchDensity_eq_mass (j : ℕ) (x : ZMod (3 ^ (j + 1))) :
    unitSourceBranchDensity j x =
      2 * (3 : ℝ) ^ j * (unitSourceForwardPMF j x).toReal := by
  induction j with
  | zero =>
      simp only [unitSourceBranchDensity, unitSourceForwardPMF, pow_zero, mul_one]
      rw [unitSourceInitialPMF_apply_toReal]
      split_ifs <;> norm_num
  | succ j ih =>
      simp only [unitSourceBranchDensity, unitSourceForwardPMF,
        unitSource_bind_apply_toReal_sum, ih, pow_succ]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _hy
      ring

/-- Full-Haar density equals three-halves the independently defined unit density. -/
theorem unitSourceForwardPMF_density_normalization
    (j : ℕ) (x : ZMod (3 ^ (j + 1))) :
    (3 : ℝ) ^ (j + 1) * (unitSourceForwardPMF j x).toReal =
      (3 / 2 : ℝ) * unitSourceBranchDensity j x := by
  rw [unitSourceBranchDensity_eq_mass, pow_succ]
  ring

#print axioms unitSourceBranchDensity_succ_explicit
#print axioms unitSourceForwardPMF_eq_seed_mixture
#print axioms unitSourceForwardPMF_density_normalization

end Erdos1135.Tao
