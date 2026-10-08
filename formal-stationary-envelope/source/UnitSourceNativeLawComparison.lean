import UnitSourceHighRegimeMixing
import Erdos1135.Tao.Section6.AdjacentOneStep

/-!
# Seed-uniform finite-law comparison

The seeded n-1-step law and the native level-n Syracuse law project to the
same level-(n-1) marginal. Their L1 distance is therefore bounded by the sum
of their adjacent oscillations. For n >= 10 both estimates lie in the checked
high regime; the finite remaining range uses the total PMF mass bound.
No infinite Haar-density interpretation is asserted in this module.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Erdos1135.Tao

theorem unitSourceAffinePMF_fiberSum_eq_syracProjection
    {r n : ℕ} (hrn : r ≤ n) (hrk : r ≤ n - 1)
    (z y : ZMod (3 ^ n)) :
    zmodPowFiberSum r n (fun x => (unitSourceAffinePMF n (n - 1) z x).toReal) y =
      syracPMFMassVector r (taoZModThreeProjection hrn y) := by
  classical
  have hmap :
      (∑ x : ZMod (3 ^ n),
        if taoZModThreeProjection hrn y = taoZModThreeProjection hrn x then
          (unitSourceAffinePMF n (n - 1) z x).toReal else 0) =
        syracPMFMassVector r (taoZModThreeProjection hrn y) := by
    calc
      _ = (((unitSourceAffinePMF n (n - 1) z).map (taoZModThreeProjection hrn))
          (taoZModThreeProjection hrn y)).toReal := by
        rw [pmf_map_apply_toReal_tsum, tsum_fintype]
      _ = _ := by
        rw [unitSourceAffinePMF_projection_eq_syracPMF hrn hrk]
        rfl
  unfold zmodPowFiberSum
  calc
    _ = ∑ x : ZMod (3 ^ n),
        if taoZModThreeProjection hrn y = taoZModThreeProjection hrn x then
          (unitSourceAffinePMF n (n - 1) z x).toReal else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [zmodSameResidueModPow_iff_projection_eq hrn]
      by_cases hxy : taoZModThreeProjection hrn x = taoZModThreeProjection hrn y
      · rw [if_pos hxy, if_pos hxy.symm]
      · have hyx : ¬taoZModThreeProjection hrn y = taoZModThreeProjection hrn x :=
          fun h => hxy h.symm
        rw [if_neg hxy, if_neg hyx]
    _ = _ := hmap

/-- The seeded and native fiber averages are literally the same function. -/
theorem unitSourceAffinePMF_fiberAverage_eq_syrac
    {r n : ℕ} (hrn : r ≤ n) (hrk : r ≤ n - 1) (z : ZMod (3 ^ n)) :
    zmodPowFiberAverage r n (fun x => (unitSourceAffinePMF n (n - 1) z x).toReal) =
      zmodPowFiberAverage r n (syracPMFMassVector n) := by
  funext y
  unfold zmodPowFiberAverage
  rw [unitSourceAffinePMF_fiberSum_eq_syracProjection hrn hrk z y,
    zmodPowFiberSum_syracPMFMassVector_eq_projection hrn y]

noncomputable def unitSourceNativeL1Distance (n : ℕ) (z : ZMod (3 ^ n)) : ℝ :=
  ∑ y : ZMod (3 ^ n),
    |(unitSourceAffinePMF n (n - 1) z y).toReal - (syracPMF n y).toReal|

theorem unitSourceNativeL1Distance_le_oscillations
    {m n : ℕ} (hmn : m ≤ n) (hmk : m ≤ n - 1) (z : ZMod (3 ^ n)) :
    unitSourceNativeL1Distance n z ≤
      unitSourceFineScaleOscillation m n z + syracFineScaleOscillation m n := by
  unfold unitSourceNativeL1Distance unitSourceFineScaleOscillation
  unfold syracFineScaleOscillation taoZModPowOscillation
  change _ ≤ (∑ y : ZMod (3 ^ n),
      |(unitSourceAffinePMF n (n - 1) z y).toReal -
        zmodPowFiberAverage m n
          (fun x => (unitSourceAffinePMF n (n - 1) z x).toReal) y|) +
    ∑ y : ZMod (3 ^ n), |syracPMFMassVector n y -
      zmodPowFiberAverage m n (syracPMFMassVector n) y|
  rw [unitSourceAffinePMF_fiberAverage_eq_syrac hmn hmk z]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _hy
  change |(unitSourceAffinePMF n (n - 1) z y).toReal - syracPMFMassVector n y| ≤ _
  calc
    _ ≤ |(unitSourceAffinePMF n (n - 1) z y).toReal -
          zmodPowFiberAverage m n (syracPMFMassVector n) y| +
        |zmodPowFiberAverage m n (syracPMFMassVector n) y - syracPMFMassVector n y| :=
      abs_sub_le _ _ _
    _ = _ := by rw [abs_sub_comm (zmodPowFiberAverage m n (syracPMFMassVector n) y)]

/-- The L1 distance between two probability mass vectors is at most two. -/
theorem unitSourceNativeL1Distance_le_two (n : ℕ) (z : ZMod (3 ^ n)) :
    unitSourceNativeL1Distance n z ≤ 2 := by
  unfold unitSourceNativeL1Distance
  calc
    _ ≤ ∑ y : ZMod (3 ^ n),
        ((unitSourceAffinePMF n (n - 1) z y).toReal + (syracPMF n y).toReal) := by
      apply Finset.sum_le_sum
      intro y _hy
      simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg]
        using abs_sub_le (unitSourceAffinePMF n (n - 1) z y).toReal 0 (syracPMF n y).toReal
    _ = 2 := by rw [Finset.sum_add_distrib, pmf_sum_toReal, pmf_sum_toReal]; norm_num

/-- Uniform finite-modulus L1 approximation of the native Syracuse law by the
literal affine n-1-step PMF, with every polynomial rate and every seed. -/
theorem exists_unitSourceNativeL1Distance_le_inv_pow (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ z : ZMod (3 ^ n),
      unitSourceNativeL1Distance n z ≤ C / (n : ℝ) ^ A := by
  obtain ⟨Dseed, hDseed, hseed⟩ := exists_unitSourceFineScaleOscillation_le_highRegime A
  obtain ⟨Dnative, hDnative, N0, _hN0, hnative⟩ :=
    taoProp117PrimitivePolynomialDecay.exists_syracFineScaleOscillation_le_highRegime A
  let N := max N0 10
  let C := Dseed + Dnative + 2 * (N : ℝ) ^ A
  have hC : 0 ≤ C := add_nonneg (add_nonneg hDseed hDnative) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro n hn z
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  by_cases hbig : N ≤ n
  · have hn0 : N0 ≤ n := (le_max_left _ _).trans hbig
    have hnten : 10 ≤ n := (le_max_right _ _).trans hbig
    have hmhigh : 9 * n ≤ 10 * (n - 1) := by omega
    have hnat : syracFineScaleOscillation (n - 1) n ≤ Dnative / (n : ℝ) ^ A := by
      calc
        _ ≤ Dnative / (n : ℝ) ^ (A + 1) :=
          hnative n (n - 1) hn0 (Nat.sub_le n 1) hmhigh
        _ ≤ _ := div_le_div_of_nonneg_left hDnative (by positivity)
          (pow_le_pow_right₀ hnR (by omega))
    calc
      _ ≤ unitSourceFineScaleOscillation (n - 1) n z + syracFineScaleOscillation (n - 1) n :=
        unitSourceNativeL1Distance_le_oscillations (Nat.sub_le n 1) (le_refl _) z
      _ ≤ Dseed / (n : ℝ) ^ A + Dnative / (n : ℝ) ^ A :=
        add_le_add (hseed n (n - 1) hn (Nat.sub_le n 1) hmhigh z) hnat
      _ = (Dseed + Dnative) / (n : ℝ) ^ A := by ring
      _ ≤ C / (n : ℝ) ^ A :=
        div_le_div_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
  · have hnN : (n : ℝ) ≤ N := by exact_mod_cast (le_of_not_ge hbig)
    have hpow : (n : ℝ) ^ A ≤ (N : ℝ) ^ A := by gcongr
    have hsmall : 2 ≤ C / (n : ℝ) ^ A := by
      apply (le_div_iff₀ (pow_pos hnpos A)).2
      dsimp [C]
      nlinarith
    exact (unitSourceNativeL1Distance_le_two n z).trans hsmall

#print axioms exists_unitSourceNativeL1Distance_le_inv_pow

end Erdos1135.Tao
