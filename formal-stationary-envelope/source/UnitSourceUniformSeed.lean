import Erdos1135.Tao.Section6.ConductorProjectivity
import Mathlib.Probability.Distributions.Uniform

/-!
# Explicit uniform unit seed

Independent uniform digits b in Fin 2 and t in Fin (3^j) give the unit
residue 3*t+b+1 modulo 3^(j+1). This leaf checks its atom probabilities and
its exact marginal modulo three.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Erdos1135.Tao

def unitSourceUnitDigit (b : Fin 2) : ZMod 3 := (b.val + 1 : ℕ)

noncomputable def unitSourceInitialPMF : PMF (ZMod 3) :=
  (PMF.uniformOfFintype (Fin 2)).map unitSourceUnitDigit

theorem unitSourceInitialPMF_apply_toReal (x : ZMod 3) :
    (unitSourceInitialPMF x).toReal = if x = 0 then 0 else 1 / 2 := by
  classical
  rw [unitSourceInitialPMF, pmf_map_apply_toReal_tsum, tsum_fintype]
  simp only [Fin.sum_univ_two, PMF.uniformOfFintype_apply, Fintype.card_fin]
  fin_cases x
  · rw [if_neg (by change (0 : Fin 3) ≠ 1; decide),
      if_neg (by change (0 : Fin 3) ≠ 2; decide),
      if_pos (by change (0 : Fin 3) = 0; rfl)]
    norm_num
  · rw [if_pos (by change (1 : Fin 3) = 1; rfl),
      if_neg (by change (1 : Fin 3) ≠ 2; decide),
      if_neg (by change (1 : Fin 3) ≠ 0; decide)]
    norm_num
  · rw [if_neg (by change (2 : Fin 3) ≠ 1; decide),
      if_pos (by change (2 : Fin 3) = 2; rfl),
      if_neg (by change (2 : Fin 3) ≠ 0; decide)]
    norm_num

def unitSourceSeedPoint (j : ℕ) (d : Fin 2 × Fin (3 ^ j)) : ZMod (3 ^ (j + 1)) :=
  (3 * d.2.val + d.1.val + 1 : ℕ)

noncomputable def unitSourceUniformSeed (j : ℕ) : PMF (ZMod (3 ^ (j + 1))) :=
  (PMF.uniformOfFintype (Fin 2 × Fin (3 ^ j))).map (unitSourceSeedPoint j)

theorem unitSourceSeedPoint_val (j : ℕ) (d : Fin 2 × Fin (3 ^ j)) :
    (unitSourceSeedPoint j d).val = 3 * d.2.val + d.1.val + 1 := by
  apply ZMod.val_natCast_of_lt
  have hb := d.1.isLt
  have ht := d.2.isLt
  rw [pow_succ]
  omega

theorem unitSourceSeedPoint_injective (j : ℕ) :
    Function.Injective (unitSourceSeedPoint j) := by
  intro d e h
  have hv := congrArg ZMod.val h
  rw [unitSourceSeedPoint_val, unitSourceSeedPoint_val] at hv
  have hd := d.1.isLt
  have he := e.1.isLt
  apply Prod.ext <;> apply Fin.ext <;> omega

theorem unitSourceSeedPoint_mod_three (j : ℕ) (d : Fin 2 × Fin (3 ^ j)) :
    (unitSourceSeedPoint j d).val % 3 = d.1.val + 1 := by
  rw [unitSourceSeedPoint_val]
  have hb := d.1.isLt
  omega

theorem unitSourceSeedPoint_range (j : ℕ) (x : ZMod (3 ^ (j + 1))) :
    (∃ d, unitSourceSeedPoint j d = x) ↔ x.val % 3 ≠ 0 := by
  constructor
  · rintro ⟨d, rfl⟩
    rw [unitSourceSeedPoint_mod_three]
    omega
  · intro hx
    have hv := ZMod.val_lt x
    have hm := Nat.mod_lt x.val (by omega : 0 < 3)
    have hd : x.val / 3 < 3 ^ j := by
      have hp : 3 ^ (j + 1) = 3 ^ j * 3 := pow_succ 3 j
      omega
    let b : Fin 2 := ⟨x.val % 3 - 1, by omega⟩
    let t : Fin (3 ^ j) := ⟨x.val / 3, hd⟩
    refine ⟨(b, t), ?_⟩
    apply ZMod.val_injective
    rw [unitSourceSeedPoint_val]
    dsimp [b, t]
    omega

theorem unitSourceUniformSeed_apply (j : ℕ) (x : ZMod (3 ^ (j + 1))) :
    unitSourceUniformSeed j x =
      if x.val % 3 = 0 then 0 else (2 * 3 ^ j : ENNReal)⁻¹ := by
  classical
  rw [unitSourceUniformSeed, PMF.map_apply, tsum_fintype]
  by_cases hx : x.val % 3 = 0
  · rw [if_pos hx]
    apply Finset.sum_eq_zero
    intro d _hd
    have hne : x ≠ unitSourceSeedPoint j d := by
      intro h
      rw [h, unitSourceSeedPoint_mod_three] at hx
      omega
    simp [hne]
  · rw [if_neg hx]
    obtain ⟨d, hd⟩ := (unitSourceSeedPoint_range j x).mpr hx
    rw [← hd]
    have hiff (e : Fin 2 × Fin (3 ^ j)) :
        unitSourceSeedPoint j d = unitSourceSeedPoint j e ↔ d = e :=
      (unitSourceSeedPoint_injective j).eq_iff
    simp [hiff, PMF.uniformOfFintype_apply, Fintype.card_prod]

theorem unitSourceUniformSeed_apply_toReal (j : ℕ) (x : ZMod (3 ^ (j + 1))) :
    (unitSourceUniformSeed j x).toReal =
      if x.val % 3 = 0 then 0 else 1 / (2 * 3 ^ j : ℝ) := by
  rw [unitSourceUniformSeed_apply]
  split_ifs <;> simp [ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_pow]

theorem unitSourceSeedPoint_projection (j : ℕ) (d : Fin 2 × Fin (3 ^ j)) :
    taoZModThreeProjection (show 1 ≤ j + 1 by omega) (unitSourceSeedPoint j d) =
      unitSourceUnitDigit d.1 := by
  unfold unitSourceSeedPoint
  rw [map_natCast]
  norm_num [unitSourceUnitDigit, Nat.cast_add, Nat.cast_mul]
  change (3 : ZMod 3) * _ = 0
  rw [show (3 : ZMod 3) = 0 by decide, zero_mul]

theorem unitSourceUniformSeed_projection_eq_initial (j : ℕ) :
    (unitSourceUniformSeed j).map
        (taoZModThreeProjection (show 1 ≤ j + 1 by omega)) =
      unitSourceInitialPMF := by
  classical
  rw [unitSourceUniformSeed, PMF.map_comp]
  have hf :
      (taoZModThreeProjection (show 1 ≤ j + 1 by omega)) ∘ unitSourceSeedPoint j =
        unitSourceUnitDigit ∘ Prod.fst := by
    funext d
    exact unitSourceSeedPoint_projection j d
  rw [hf, ← PMF.map_comp]
  apply congrArg (PMF.map unitSourceUnitDigit)
  ext b
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Fintype.card_fin]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_ite, mul_zero, Fintype.sum_ite_eq]
  rw [ENNReal.mul_inv (by simp) (by simp)]
  rw [mul_left_comm]
  simp [ENNReal.mul_inv_cancel]

#print axioms unitSourceUniformSeed_apply_toReal
#print axioms unitSourceUniformSeed_projection_eq_initial
#print axioms unitSourceInitialPMF_apply_toReal

end Erdos1135.Tao
