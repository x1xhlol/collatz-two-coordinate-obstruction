import UnitSourceGatedConvolution
import Erdos1135.Tao.Section6.FixedSlicePolynomial
import Erdos1135.Tao.Section6.HeadGateIndex

/-!
# Seed-uniform Section 6 fixed-slice estimates

The native Corollary 6.3 head collision cap, head gate localization, and
entropy bound are unchanged. A nonempty gate at n >= 7 leaves at least one
tail coordinate. The seeded tail Fourier bound then feeds the existing
generic Fourier convolution collision estimate.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Erdos1135.Tao

theorem unitSourceFixedSliceOscillation_sq_le
    {B : ℕ} {C : ℝ} (hdecay : UnitSourceReducedDecayAt B C) (hC : 0 ≤ C)
    {CA : ℝ} {T k l m : ℕ} (hT : 1 ≤ T)
    (hmn : m ≤ T + (k + 1)) (hhead : k + 1 ≤ m)
    (hm : 9 * (T + (k + 1)) ≤ 10 * m)
    (hk : 20 * k ≤ 17 * (T + (k + 1)))
    (hheadL2 : (∑ y : ZMod (3 ^ (T + (k + 1))),
      (taoSection6HeadSubmass CA (T + (k + 1)) k l y) ^ 2) ≤ (1 / 2 : ℝ) ^ l)
    (z : ZMod (3 ^ (T + (k + 1)))) :
    taoZModPowOscillation m (T + (k + 1)) (unitSourceGatedSubmass CA T k l z) ^ 2 ≤
      (taoSection6TailDecayDelta C B (T + (k + 1))) ^ 2 *
        (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) * (1 / 2 : ℝ) ^ l := by
  let tau : ZMod (3 ^ (T + (k + 1))) → ℝ := fun y =>
    (unitSourceAmbientTailPMF (k + 1) T l
      (taoZModThreeProjection (Nat.le_add_right T (k + 1)) z) y).toReal
  have hsource : unitSourceGatedSubmass CA T k l z =
      taoZModRawConvolution (taoSection6HeadSubmass CA (T + (k + 1)) k l) tau := by
    funext x
    exact unitSourceGatedSubmass_eq_rawConvolution CA T k l hT z x
  rw [hsource]
  have htail : ∀ xi : ZMod (3 ^ (T + (k + 1))),
      ¬zmodThreePowMultiple (T + (k + 1)) (T + (k + 1) - m) xi →
      ‖ZMod.dft (fun x => ((tau x : ℝ) : ℂ)) xi‖ ≤
        taoSection6TailDecayDelta C B (T + (k + 1)) := by
    intro xi hxi
    exact hdecay.dft_ambientTail_le hC hhead hm hk xi hxi
      (taoZModThreeProjection (Nat.le_add_right T (k + 1)) z)
  have hcollision := taoZModPowOscillation_rawConvolution_sq_le hmn
    (taoSection6HeadSubmass CA (T + (k + 1)) k l) tau
    (taoSection6TailDecayDelta_nonneg hC B (T + (k + 1))) htail
  exact hcollision.trans (mul_le_mul_of_nonneg_left hheadL2
    (mul_nonneg (sq_nonneg _) (by positivity)))

/-- Every nonempty sufficiently large native head gate leaves a positive
seeded tail. Empty gates, including T=0, are discharged directly. -/
theorem exists_unitSourceFixedSliceOscillation_sq_le
    {B : ℕ} {C : ℝ} (hdecay : UnitSourceReducedDecayAt B C) (hC : 0 ≤ C)
    (CA : ℝ) (hCA : 17 ≤ CA) :
    ∃ N0 : ℕ, ∀ T k l m : ℕ, ∀ z : ZMod (3 ^ (T + (k + 1))),
      N0 ≤ T + (k + 1) → m ≤ T + (k + 1) → 9 * (T + (k + 1)) ≤ 10 * m →
      taoZModPowOscillation m (T + (k + 1)) (unitSourceGatedSubmass CA T k l z) ^ 2 ≤
        (taoSection6TailDecayDelta C B (T + (k + 1))) ^ 2 *
          (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) * (1 / 2 : ℝ) ^ l := by
  obtain ⟨Ncollision, hcollision⟩ := exists_taoSection6HeadSubmass_sum_sq_le CA hCA
  obtain ⟨Nindex, hindex⟩ := exists_taoSection6HeadGate_index_le CA hCA
  refine ⟨max (max Ncollision Nindex) 7, ?_⟩
  intro T k l m z hn hmn hm
  have hncollision : Ncollision ≤ T + (k + 1) :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hnindex : Nindex ≤ T + (k + 1) :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnseven : 7 ≤ T + (k + 1) := (le_max_right _ _).trans hn
  by_cases hgate : ∃ head : List ℕ+, taoSection6HeadGate CA (T + (k + 1)) k l head
  · obtain ⟨head, hheadGate⟩ := hgate
    have hk : 20 * k ≤ 17 * (T + (k + 1)) :=
      hindex (T + (k + 1)) hnindex k l head hheadGate
    have hhead : k + 1 ≤ m := taoSection6HeadIndex_le_m_of_bounds (by omega) hm hk
    have hT : 1 ≤ T := by omega
    exact unitSourceFixedSliceOscillation_sq_le hdecay hC hT hmn hhead hm hk
      (hcollision (T + (k + 1)) hncollision k l) z
  · have hzero := unitSourceGatedOscillation_eq_zero_of_headGate_empty
      (m := m) hgate z
    rw [hzero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    positivity

theorem exists_unitSourceFixedSliceOscillation_sq_le_headEntropy
    {B : ℕ} {C : ℝ} (hdecay : UnitSourceReducedDecayAt B C) (hC : 0 ≤ C)
    (CA : ℝ) (hCA : 17 ≤ CA) :
    ∃ N0 : ℕ, ∀ T k l m : ℕ, ∀ z : ZMod (3 ^ (T + (k + 1))),
      N0 ≤ T + (k + 1) → m ≤ T + (k + 1) → 9 * (T + (k + 1)) ≤ 10 * m →
      taoZModPowOscillation m (T + (k + 1)) (unitSourceGatedSubmass CA T k l z) ^ 2 ≤
        taoSection6TailDecayDelta C B (T + (k + 1)) ^ 2 *
          ((T + (k + 1) : ℕ) : ℝ) ^ taoSection6HeadEntropyExponent CA := by
  obtain ⟨N0, hsource⟩ := exists_unitSourceFixedSliceOscillation_sq_le hdecay hC CA hCA
  refine ⟨N0, ?_⟩
  intro T k l m z hn hmn hm
  let n := T + (k + 1)
  have hn_pos : 1 ≤ n := by omega
  by_cases hl : taoCor63StarQ CA n < (l : ℝ)
  · have hraw := hsource T k l m z hn hmn hm
    have hent := taoSection6HeadEntropyFactor_lt_pow hn_pos hl
    calc
      _ ≤ taoSection6TailDecayDelta C B n ^ 2 *
          (((3 ^ n : ℕ) : ℝ)) * (1 / 2 : ℝ) ^ l := hraw
      _ = taoSection6TailDecayDelta C B n ^ 2 * taoSection6HeadEntropyFactor n l := by
        simp only [taoSection6HeadEntropyFactor]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_of_lt hent) (sq_nonneg _)
  · have hgate : ¬ ∃ head : List ℕ+, taoSection6HeadGate CA n k l head := by
      rintro ⟨head, hhead⟩
      apply hl
      simpa [taoSection6HeadGate_weight hhead] using (taoSection6HeadGate_crossing hhead).2
    have hzero := unitSourceGatedOscillation_eq_zero_of_headGate_empty
      (m := m) hgate z
    rw [hzero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    positivity

/-- Polynomial fixed-slice oscillation, uniform over every ambient seed. -/
theorem exists_unitSourceFixedSliceOscillation_le
    (CA : ℝ) (hCA : 17 ≤ CA) (A : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ N0 : ℕ, ∀ T k l m : ℕ,
      ∀ z : ZMod (3 ^ (T + (k + 1))), N0 ≤ T + (k + 1) →
      m ≤ T + (k + 1) → 9 * (T + (k + 1)) ≤ 10 * m →
      taoZModPowOscillation m (T + (k + 1)) (unitSourceGatedSubmass CA T k l z) ≤
        D / ((T + (k + 1) : ℕ) : ℝ) ^ (A + 3) := by
  let P := taoSection6HeadEntropyExponent CA
  let B := A + P + 3
  have hB : 0 < B := by omega
  obtain ⟨C, hC, hdecay⟩ := exists_unitSourceReducedDecayAt B hB
  let D := C * (20 : ℝ) ^ B
  have hD : 0 ≤ D := mul_nonneg hC (pow_nonneg (by norm_num) _)
  obtain ⟨N0, hsq⟩ :=
    exists_unitSourceFixedSliceOscillation_sq_le_headEntropy hdecay hC CA hCA
  refine ⟨D, hD, N0, ?_⟩
  intro T k l m z hn hmn hm
  let n := T + (k + 1)
  have hn_nat : 1 ≤ n := by omega
  have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_nat
  have hn_pos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn_real
  have hsq' := hsq T k l m z hn hmn hm
  have hpowB : (n : ℝ) ^ B = (n : ℝ) ^ (A + 3) * (n : ℝ) ^ P := by
    rw [show B = (A + 3) + P by omega, pow_add]
  have hdelta : taoSection6TailDecayDelta C B n =
      (D / (n : ℝ) ^ (A + 3)) / (n : ℝ) ^ P := by
    rw [taoSection6TailDecayDelta, hpowB]
    dsimp [D]
    field_simp
  have hP_one : (1 : ℝ) ≤ (n : ℝ) ^ P := one_le_pow₀ hn_real
  have hP_pos : (0 : ℝ) < (n : ℝ) ^ P := by positivity
  let R := D / (n : ℝ) ^ (A + 3)
  have hscalar : (taoSection6TailDecayDelta C B n) ^ 2 * (n : ℝ) ^ P ≤ R ^ 2 := by
    rw [hdelta]
    change (R / (n : ℝ) ^ P) ^ 2 * (n : ℝ) ^ P ≤ R ^ 2
    rw [div_pow]
    field_simp
    nlinarith [sq_nonneg R]
  have hosc_sq : taoZModPowOscillation m n (unitSourceGatedSubmass CA T k l z) ^ 2 ≤ R ^ 2 :=
    hsq'.trans hscalar
  have hosc_nonneg : 0 ≤ taoZModPowOscillation m n (unitSourceGatedSubmass CA T k l z) := by
    simp only [taoZModPowOscillation]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hR_nonneg : 0 ≤ R := div_nonneg hD (pow_nonneg (by positivity) _)
  have hosc : taoZModPowOscillation m n (unitSourceGatedSubmass CA T k l z) ≤ R := by
    nlinarith [sq_nonneg
      (taoZModPowOscillation m n (unitSourceGatedSubmass CA T k l z) - R)]
  exact hosc

end Erdos1135.Tao
