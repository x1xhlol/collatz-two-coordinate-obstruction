import UnitSourceProjection
import Erdos1135.Tao.Section6.AmbientTailDecay

/-!
# Seeded tail decay at the actual reduced conductor

The primitive-conductor branch uses the frozen seed-stable Fourier theorem.
Every lower-conductor branch is identified exactly with the native Syracuse
law. Native conductor geometry and the ambient tail embedding are retained.
-/

set_option autoImplicit false

namespace Erdos1135.Tao

/-- Uniform seeded Fourier decay indexed by the actual reduced conductor. -/
def UnitSourceReducedDecayAt (A : ℕ) (C : ℝ) : Prop :=
  ∀ r j : ℕ, 1 ≤ r → ∀ z : ZMod (3 ^ (r + j)),
    ∀ eta : ℕ, ¬3 ∣ eta →
      ‖ZMod.dft (pmfComplexMass
          (unitSourceAffinePMF (r + j) (r + j - 1) z))
          ((3 : ZMod (3 ^ (r + j))) ^ j * eta)‖ ≤ C / (r : ℝ) ^ A

/-- Primitive frequencies use the new seed-stable bound. At every lower
conductor the seed vanishes and the native Syracuse bound applies exactly. -/
theorem exists_unitSourceReducedDecayAt (A : ℕ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ UnitSourceReducedDecayAt A C := by
  obtain ⟨K, hK, hseed⟩ := unitSourceAffinePMF_primitive_polynomial_decay A hA
  obtain ⟨D, hD, hnative⟩ := taoProp117PrimitivePolynomialDecay.bound hA
  refine ⟨K + D, add_nonneg hK hD, ?_⟩
  intro r j hr z eta heta
  by_cases hj : j = 0
  · subst j
    have hprim := zmodThreePrimitive_natCast_of_not_dvd hr heta
    have hbound := hseed r hr (eta : ZMod (3 ^ r)) hprim z
    calc
      _ ≤ K / (r : ℝ) ^ A := by simpa using hbound
      _ ≤ (K + D) / (r : ℝ) ^ A :=
        div_le_div_of_nonneg_right (le_add_of_nonneg_right hD) (by positivity)
  · rw [unitSourceAffinePMF_dft_three_pow_mul_eq_syracPMF r j
      (r + j - 1) (by omega)]
    have hprim : zmodThreePrimitive r
        (taoZModThreeProjection (Nat.le_add_right r j)
          (eta : ZMod (3 ^ (r + j)))) := by
      simpa using zmodThreePrimitive_natCast_of_not_dvd hr heta
    calc
      _ ≤ D / (r : ℝ) ^ A := hnative.apply hr hprim
      _ ≤ (K + D) / (r : ℝ) ^ A :=
        div_le_div_of_nonneg_right (le_add_of_nonneg_left hK) (by positivity)

noncomputable def unitSourceAmbientTailPMF
    (q T l : ℕ) (z : ZMod (3 ^ T)) : PMF (ZMod (3 ^ (T + q))) :=
  (unitSourceAffinePMF T (T - 1) z).map (taoSection6AmbientTailEmbed q T l)

theorem unitSourceAmbientTailPMF_dft
    (q T l : ℕ) (z : ZMod (3 ^ T)) (xi : ZMod (3 ^ (T + q))) :
    ZMod.dft (pmfComplexMass (unitSourceAmbientTailPMF q T l z)) xi =
      ZMod.dft (pmfComplexMass (unitSourceAffinePMF T (T - 1) z))
        (taoSection6TailScaledFrequency (Nat.le_add_right T q) l xi) := by
  unfold unitSourceAmbientTailPMF
  rw [tao_dft_pmfComplexMass_map_apply]
  have htail := tao_dft_pmfComplexMass_map_apply
    (unitSourceAffinePMF T (T - 1) z) (fun x => x)
    (taoSection6TailScaledFrequency (Nat.le_add_right T q) l xi)
  have hid : (unitSourceAffinePMF T (T - 1) z).map (fun x => x) =
      unitSourceAffinePMF T (T - 1) z := by
    simpa only [id_eq] using PMF.map_id (unitSourceAffinePMF T (T - 1) z)
  rw [hid] at htail
  rw [htail]
  apply tsum_congr
  intro x
  rw [taoForwardDFTKernel_ambientTailEmbed]

theorem UnitSourceReducedDecayAt.tail_scaled_frequency_le
    {A : ℕ} {C : ℝ} (hdecay : UnitSourceReducedDecayAt A C)
    {n m k T l : ℕ}
    (htail : k + 1 + T = n) (hhead : k + 1 ≤ m)
    (hm : 9 * n ≤ 10 * m) (hk : 20 * k ≤ 17 * n)
    {xi : ZMod (3 ^ n)}
    (hxi : ¬zmodThreePowMultiple n (n - m) xi)
    (z : ZMod (3 ^ T)) :
    ∃ r j : ℕ,
      j < n - m ∧ r + j = T ∧ k + j + 1 + r = n ∧
      1 ≤ r ∧ m - k ≤ r ∧ n ≤ 20 * r ∧
      ‖ZMod.dft (pmfComplexMass (unitSourceAffinePMF T (T - 1) z))
          (taoSection6TailScaledFrequency (by omega : T ≤ n) l xi)‖ ≤
        C / (r : ℝ) ^ A := by
  have hqT : n - m ≤ T := by omega
  have hTn : T ≤ n := by omega
  have hscaled : ¬zmodThreePowMultiple T (n - m)
      (taoSection6TailScaledFrequency hTn l xi) :=
    taoSection6TailScaledFrequency_not_pow_multiple hqT hTn hxi
  obtain ⟨j, eta, hj, heta, hfactor⟩ :=
    exists_three_pow_mul_not_dvd_of_not_pow_multiple hscaled
  have hjT : j < T := hj.trans_le hqT
  let r := T - j
  have hjr : j + r = T := by dsimp [r]; omega
  obtain ⟨hrj, hr, hmkr, _hnmk, hnr⟩ :=
    taoSection6_conductor_index_bounds htail hjr hhead hj hm hk
  have hfull := taoSection6_head_add_frequency_add_conductor_eq htail hjr
  refine ⟨r, j, hj, hrj, hfull, hr, hmkr, hnr, ?_⟩
  rw [hfactor]
  clear_value r
  clear hjr
  subst T
  exact hdecay r j hr z eta heta

theorem UnitSourceReducedDecayAt.dft_ambientTail_le
    {B : ℕ} {C : ℝ} (hdecay : UnitSourceReducedDecayAt B C) (hC : 0 ≤ C)
    {T k l m : ℕ}
    (hhead : k + 1 ≤ m)
    (hm : 9 * (T + (k + 1)) ≤ 10 * m)
    (hk : 20 * k ≤ 17 * (T + (k + 1)))
    (xi : ZMod (3 ^ (T + (k + 1))))
    (hxi : ¬zmodThreePowMultiple
      (T + (k + 1)) (T + (k + 1) - m) xi)
    (z : ZMod (3 ^ T)) :
    ‖ZMod.dft (pmfComplexMass (unitSourceAmbientTailPMF (k + 1) T l z)) xi‖ ≤
      taoSection6TailDecayDelta C B (T + (k + 1)) := by
  rw [unitSourceAmbientTailPMF_dft]
  obtain ⟨r, j, _hj, _hrj, _hfull, hr, _hmkr, hnr, hbound⟩ :=
    hdecay.tail_scaled_frequency_le (n := T + (k + 1)) (m := m)
      (k := k) (T := T) (l := l) (by omega) hhead hm hk hxi z
  have hn_pos : 0 < T + (k + 1) := by omega
  have hr_real_pos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hn_real_pos : 0 < ((T + (k + 1) : ℕ) : ℝ) := by exact_mod_cast hn_pos
  have hnr_real : ((T + (k + 1) : ℕ) : ℝ) ≤ (20 : ℝ) * (r : ℝ) := by
    exact_mod_cast hnr
  have hpow : (((T + (k + 1) : ℕ) : ℝ) ^ B) ≤ (20 : ℝ) ^ B * (r : ℝ) ^ B := by
    calc
      _ ≤ ((20 : ℝ) * (r : ℝ)) ^ B := by gcongr
      _ = _ := by rw [mul_pow]
  have hr_pow_pos : 0 < (r : ℝ) ^ B := pow_pos hr_real_pos B
  have hn_pow_pos : 0 < (((T + (k + 1) : ℕ) : ℝ) ^ B) := pow_pos hn_real_pos B
  calc
    _ ≤ C / (r : ℝ) ^ B := hbound
    _ ≤ C * (20 : ℝ) ^ B / (((T + (k + 1) : ℕ) : ℝ) ^ B) := by
      apply (div_le_div_iff₀ hr_pow_pos hn_pow_pos).2
      calc
        C * (((T + (k + 1) : ℕ) : ℝ) ^ B) ≤
            C * ((20 : ℝ) ^ B * (r : ℝ) ^ B) := mul_le_mul_of_nonneg_left hpow hC
        _ = _ := by ring
    _ = _ := rfl

end Erdos1135.Tao
