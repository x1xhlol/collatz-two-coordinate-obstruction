/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Fourier.Basic
import Mathlib.Analysis.Complex.Norm

/-!
# Finite Fourier To Full-L1 TV Bridge

This module packages deterministic finite Fourier-inversion and triangle
inequality bridges to the project-local full-L1 `taoTV` convention.  It consumes
future coefficient bounds, but proves no Fourier decay estimate.
-/

open scoped BigOperators
open scoped ZMod

namespace Erdos1135SecondScale
namespace Tao

theorem taoTV_eq_sum_norm_pmfComplexMass_sub {α : Type*} [Fintype α]
    (p q : PMF α) :
    taoTV p q = ∑ a, ‖pmfComplexMass p a - pmfComplexMass q a‖ := by
  simp [taoTV, pmfComplexMass, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem dft_pmfComplexMass_sub {N : ℕ} [NeZero N]
    (p q : PMF (ZMod N)) :
    ZMod.dft (fun x => pmfComplexMass p x - pmfComplexMass q x) =
      fun k => ZMod.dft (pmfComplexMass p) k - ZMod.dft (pmfComplexMass q) k := by
  ext k
  change (ZMod.dft ((pmfComplexMass p) - (pmfComplexMass q))) k =
    (ZMod.dft (pmfComplexMass p) - ZMod.dft (pmfComplexMass q)) k
  rw [map_sub]

theorem pmfComplexMass_sub_apply_eq_invDFT_dft_sub {N : ℕ} [NeZero N]
    (p q : PMF (ZMod N)) (x : ZMod N) :
    pmfComplexMass p x - pmfComplexMass q x =
      (N : ℂ)⁻¹ •
        ∑ k : ZMod N, ZMod.stdAddChar (k * x) •
          (ZMod.dft (pmfComplexMass p) k - ZMod.dft (pmfComplexMass q) k) := by
  let Φ : ZMod N → ℂ := fun y => pmfComplexMass p y - pmfComplexMass q y
  have hdft :
      ZMod.dft Φ =
        fun k => ZMod.dft (pmfComplexMass p) k - ZMod.dft (pmfComplexMass q) k := by
    simpa [Φ] using dft_pmfComplexMass_sub (N := N) p q
  calc
    pmfComplexMass p x - pmfComplexMass q x = Φ x := rfl
    _ = (ZMod.dft (N := N) (E := ℂ)).symm (ZMod.dft Φ) x := by
      rw [LinearEquiv.symm_apply_apply]
    _ = (ZMod.dft (N := N) (E := ℂ)).symm
          (fun k => ZMod.dft (pmfComplexMass p) k - ZMod.dft (pmfComplexMass q) k) x := by
      rw [hdft]
    _ = (N : ℂ)⁻¹ •
        ∑ k : ZMod N, ZMod.stdAddChar (k * x) •
          (ZMod.dft (pmfComplexMass p) k - ZMod.dft (pmfComplexMass q) k) := by
      rw [ZMod.invDFT_apply]

theorem norm_pmfComplexMass_sub_apply_le_inv_norm_sum_dft_sub {N : ℕ} [NeZero N]
    (p q : PMF (ZMod N)) (x : ZMod N) :
    ‖pmfComplexMass p x - pmfComplexMass q x‖ ≤
      ‖(N : ℂ)⁻¹‖ *
        ∑ k : ZMod N,
          ‖ZMod.dft (pmfComplexMass p) k - ZMod.dft (pmfComplexMass q) k‖ := by
  rw [pmfComplexMass_sub_apply_eq_invDFT_dft_sub (N := N) p q x]
  calc
    ‖(N : ℂ)⁻¹ •
        ∑ k : ZMod N, ZMod.stdAddChar (k * x) •
          (ZMod.dft (pmfComplexMass p) k - ZMod.dft (pmfComplexMass q) k)‖
        = ‖(N : ℂ)⁻¹‖ *
          ‖∑ k : ZMod N, ZMod.stdAddChar (k * x) •
            (ZMod.dft (pmfComplexMass p) k - ZMod.dft (pmfComplexMass q) k)‖ := by
            rw [norm_smul]
    _ ≤ ‖(N : ℂ)⁻¹‖ *
        ∑ k : ZMod N,
          ‖ZMod.stdAddChar (k * x) •
            (ZMod.dft (pmfComplexMass p) k - ZMod.dft (pmfComplexMass q) k)‖ := by
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ‖(N : ℂ)⁻¹‖ *
        ∑ k : ZMod N,
          ‖ZMod.dft (pmfComplexMass p) k - ZMod.dft (pmfComplexMass q) k‖ := by
          congr 1
          apply Finset.sum_congr rfl
          intro k _hk
          simp [ZMod.stdAddChar_apply]

theorem taoTV_le_sum_inv_norm_sum_dft_sub {N : ℕ} [NeZero N]
    (p q : PMF (ZMod N)) :
    taoTV p q ≤
      ∑ _x : ZMod N,
        ‖(N : ℂ)⁻¹‖ *
          ∑ k : ZMod N,
            ‖ZMod.dft (pmfComplexMass p) k - ZMod.dft (pmfComplexMass q) k‖ := by
  rw [taoTV_eq_sum_norm_pmfComplexMass_sub]
  exact Finset.sum_le_sum fun x _hx =>
    norm_pmfComplexMass_sub_apply_le_inv_norm_sum_dft_sub (N := N) p q x

theorem taoTV_le_card_mul_inv_norm_sum_dft_sub {N : ℕ} [NeZero N]
    (p q : PMF (ZMod N)) :
    taoTV p q ≤
      (N : ℝ) *
        (‖(N : ℂ)⁻¹‖ *
          ∑ k : ZMod N,
            ‖ZMod.dft (pmfComplexMass p) k - ZMod.dft (pmfComplexMass q) k‖) := by
  calc
    taoTV p q ≤
      ∑ _x : ZMod N,
        ‖(N : ℂ)⁻¹‖ *
          ∑ k : ZMod N,
            ‖ZMod.dft (pmfComplexMass p) k - ZMod.dft (pmfComplexMass q) k‖ := by
        exact taoTV_le_sum_inv_norm_sum_dft_sub (N := N) p q
    _ = (N : ℝ) *
        (‖(N : ℂ)⁻¹‖ *
          ∑ k : ZMod N,
            ‖ZMod.dft (pmfComplexMass p) k - ZMod.dft (pmfComplexMass q) k‖) := by
        simp [ZMod.card, nsmul_eq_mul]

theorem natCast_mul_norm_inv_natCast_complex (N : ℕ) [NeZero N] :
    (N : ℝ) * ‖(N : ℂ)⁻¹‖ = 1 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [norm_inv]
  simp [mul_inv_cancel₀ hNpos.ne']

theorem taoTV_le_sum_dft_sub {N : ℕ} [NeZero N]
    (p q : PMF (ZMod N)) :
    taoTV p q ≤
      ∑ k : ZMod N,
        ‖ZMod.dft (pmfComplexMass p) k - ZMod.dft (pmfComplexMass q) k‖ := by
  calc
    taoTV p q ≤
      (N : ℝ) *
        (‖(N : ℂ)⁻¹‖ *
          ∑ k : ZMod N,
            ‖ZMod.dft (pmfComplexMass p) k - ZMod.dft (pmfComplexMass q) k‖) := by
        exact taoTV_le_card_mul_inv_norm_sum_dft_sub (N := N) p q
    _ = ∑ k : ZMod N,
          ‖ZMod.dft (pmfComplexMass p) k - ZMod.dft (pmfComplexMass q) k‖ := by
        rw [← mul_assoc, natCast_mul_norm_inv_natCast_complex N, one_mul]

theorem pmfComplexMass_uniformOfFintype_zmod {N : ℕ} [NeZero N] (x : ZMod N) :
    pmfComplexMass (PMF.uniformOfFintype (ZMod N)) x = (N : ℂ)⁻¹ := by
  simp [pmfComplexMass, PMF.uniformOfFintype_apply, ZMod.card]

theorem sum_stdAddChar_neg_mul_eq_zero {N : ℕ} [NeZero N] {k : ZMod N}
    (hk : k ≠ 0) :
    (∑ j : ZMod N, ZMod.stdAddChar (-(j * k))) = 0 := by
  have hnontriv :
      AddChar.mulShift (ZMod.stdAddChar (N := N)) (-k) ≠ 0 := by
    have hkneg : (-k) ≠ 0 := by simpa using neg_ne_zero.mpr hk
    simpa using (ZMod.isPrimitive_stdAddChar N hkneg)
  have hsum :
      (∑ j : ZMod N, AddChar.mulShift (ZMod.stdAddChar (N := N)) (-k) j) = 0 :=
    AddChar.sum_eq_zero_iff_ne_zero.mpr hnontriv
  simpa [AddChar.mulShift_apply, mul_comm, neg_mul] using hsum

theorem dft_uniformOfFintype_apply {N : ℕ} [NeZero N] (k : ZMod N) :
    ZMod.dft (pmfComplexMass (PMF.uniformOfFintype (ZMod N))) k =
      if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · rw [if_pos hk]
    simpa [hk] using
      dft_pmfComplexMass_apply_zero (N := N) (PMF.uniformOfFintype (ZMod N))
  · rw [if_neg hk]
    rw [ZMod.dft_apply]
    simp_rw [pmfComplexMass_uniformOfFintype_zmod]
    simp_rw [smul_eq_mul]
    rw [← Finset.sum_mul]
    rw [sum_stdAddChar_neg_mul_eq_zero (N := N) hk]
    simp

theorem taoTV_le_sum_nonzero_dft_uniform {N : ℕ} [NeZero N]
    (p : PMF (ZMod N)) :
    taoTV p (PMF.uniformOfFintype (ZMod N)) ≤
      ∑ k : ZMod N, if k = 0 then 0 else ‖ZMod.dft (pmfComplexMass p) k‖ := by
  calc
    taoTV p (PMF.uniformOfFintype (ZMod N)) ≤
      ∑ k : ZMod N,
        ‖ZMod.dft (pmfComplexMass p) k -
          ZMod.dft (pmfComplexMass (PMF.uniformOfFintype (ZMod N))) k‖ := by
        exact taoTV_le_sum_dft_sub (N := N) p (PMF.uniformOfFintype (ZMod N))
    _ = ∑ k : ZMod N, if k = 0 then 0 else ‖ZMod.dft (pmfComplexMass p) k‖ := by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [dft_uniformOfFintype_apply]
        by_cases hk0 : k = 0
        · rw [if_pos hk0, if_pos hk0]
          rw [hk0, dft_pmfComplexMass_apply_zero]
          simp
        · rw [if_neg hk0, if_neg hk0]
          simp

theorem sum_if_ne_zero_eq_sum_erase_zero {N : ℕ} [NeZero N] (f : ZMod N → ℝ) :
    (∑ k : ZMod N, if k = 0 then 0 else f k) =
      ∑ k ∈ Finset.univ.erase (0 : ZMod N), f k := by
  classical
  have hfilter :
      (Finset.univ.filter fun k : ZMod N => k ≠ 0) =
        Finset.univ.erase (0 : ZMod N) := by
    ext k
    simp
  calc
    (∑ k : ZMod N, if k = 0 then 0 else f k)
        = ∑ k ∈ Finset.univ.filter (fun k : ZMod N => k ≠ 0), f k := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro k _hk
          by_cases hk0 : k = 0 <;> simp [hk0]
    _ = ∑ k ∈ Finset.univ.erase (0 : ZMod N), f k := by
          rw [hfilter]

theorem taoTV_le_sum_erase_zero_dft_uniform {N : ℕ} [NeZero N]
    (p : PMF (ZMod N)) :
    taoTV p (PMF.uniformOfFintype (ZMod N)) ≤
      ∑ k ∈ Finset.univ.erase (0 : ZMod N), ‖ZMod.dft (pmfComplexMass p) k‖ := by
  calc
    taoTV p (PMF.uniformOfFintype (ZMod N)) ≤
      ∑ k : ZMod N, if k = 0 then 0 else ‖ZMod.dft (pmfComplexMass p) k‖ := by
        exact taoTV_le_sum_nonzero_dft_uniform (N := N) p
    _ = ∑ k ∈ Finset.univ.erase (0 : ZMod N), ‖ZMod.dft (pmfComplexMass p) k‖ := by
        exact sum_if_ne_zero_eq_sum_erase_zero
          (N := N) (f := fun k => ‖ZMod.dft (pmfComplexMass p) k‖)

theorem taoTV_uniform_le_erase_card_mul_of_nonzero_dft_le {N : ℕ} [NeZero N]
    (p : PMF (ZMod N)) {B : ℝ}
    (hB : ∀ k : ZMod N, k ≠ 0 → ‖ZMod.dft (pmfComplexMass p) k‖ ≤ B) :
    taoTV p (PMF.uniformOfFintype (ZMod N)) ≤
      ((Finset.univ.erase (0 : ZMod N)).card : ℝ) * B := by
  calc
    taoTV p (PMF.uniformOfFintype (ZMod N)) ≤
      ∑ k ∈ Finset.univ.erase (0 : ZMod N), ‖ZMod.dft (pmfComplexMass p) k‖ := by
        exact taoTV_le_sum_erase_zero_dft_uniform (N := N) p
    _ ≤ ∑ _k ∈ Finset.univ.erase (0 : ZMod N), B := by
        apply Finset.sum_le_sum
        intro k hk
        exact hB k (Finset.mem_erase.mp hk).1
    _ = ((Finset.univ.erase (0 : ZMod N)).card : ℝ) * B := by
        simp [nsmul_eq_mul]

theorem taoTV_uniform_le_nonzero_card_mul_of_nonzero_dft_le {N : ℕ} [NeZero N]
    (p : PMF (ZMod N)) {B : ℝ}
    (hB : ∀ k : ZMod N, k ≠ 0 → ‖ZMod.dft (pmfComplexMass p) k‖ ≤ B) :
    taoTV p (PMF.uniformOfFintype (ZMod N)) ≤ ((N - 1 : ℕ) : ℝ) * B := by
  calc
    taoTV p (PMF.uniformOfFintype (ZMod N)) ≤
      ((Finset.univ.erase (0 : ZMod N)).card : ℝ) * B := by
        exact taoTV_uniform_le_erase_card_mul_of_nonzero_dft_le (N := N) p hB
    _ = ((N - 1 : ℕ) : ℝ) * B := by
        simp [Finset.card_erase_of_mem, ZMod.card]

theorem taoTV_uniform_le_of_nonzero_dft_le_div_nonzero_card {N : ℕ} [NeZero N]
    (p : PMF (ZMod N)) (hN : 1 < N) {ε : ℝ}
    (hB : ∀ k : ZMod N, k ≠ 0 →
      ‖ZMod.dft (pmfComplexMass p) k‖ ≤ ε / ((N - 1 : ℕ) : ℝ)) :
    taoTV p (PMF.uniformOfFintype (ZMod N)) ≤ ε := by
  have hcount_pos : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hN
  calc
    taoTV p (PMF.uniformOfFintype (ZMod N)) ≤
        ((N - 1 : ℕ) : ℝ) * (ε / ((N - 1 : ℕ) : ℝ)) := by
      exact taoTV_uniform_le_nonzero_card_mul_of_nonzero_dft_le (N := N) p hB
    _ = ε := by
      rw [mul_comm, div_mul_cancel₀ ε hcount_pos.ne']

theorem taoTV_uniform_le_card_mul_of_nonzero_dft_le {N : ℕ} [NeZero N]
    (p : PMF (ZMod N)) {B : ℝ} (hB_nonneg : 0 ≤ B)
    (hB : ∀ k : ZMod N, k ≠ 0 → ‖ZMod.dft (pmfComplexMass p) k‖ ≤ B) :
    taoTV p (PMF.uniformOfFintype (ZMod N)) ≤ (N : ℝ) * B := by
  calc
    taoTV p (PMF.uniformOfFintype (ZMod N)) ≤
      ∑ k : ZMod N, if k = 0 then 0 else ‖ZMod.dft (pmfComplexMass p) k‖ := by
        exact taoTV_le_sum_nonzero_dft_uniform (N := N) p
    _ ≤ ∑ _k : ZMod N, B := by
        apply Finset.sum_le_sum
        intro k _hk
        by_cases hk0 : k = 0
        · simp [hk0, hB_nonneg]
        · simpa [hk0] using hB k hk0
    _ = (N : ℝ) * B := by
        simp [ZMod.card, nsmul_eq_mul]

theorem taoTV_uniform_le_of_nonzero_dft_le_div_natCast {N : ℕ} [NeZero N]
    (p : PMF (ZMod N)) {ε : ℝ} (hε : 0 ≤ ε)
    (hB : ∀ k : ZMod N, k ≠ 0 →
      ‖ZMod.dft (pmfComplexMass p) k‖ ≤ ε / (N : ℝ)) :
    taoTV p (PMF.uniformOfFintype (ZMod N)) ≤ ε := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  calc
    taoTV p (PMF.uniformOfFintype (ZMod N)) ≤
        (N : ℝ) * (ε / (N : ℝ)) := by
      exact taoTV_uniform_le_card_mul_of_nonzero_dft_le (N := N) p
        (div_nonneg hε hNpos.le) hB
    _ = ε := by
      rw [mul_comm, div_mul_cancel₀ ε hNpos.ne']

theorem taoTV_syracPMF_uniform_le_nonzero_card_mul_of_dft_le (n : ℕ) {B : ℝ}
    (hB : ∀ k : ZMod (3 ^ n), k ≠ 0 →
      ‖ZMod.dft (pmfComplexMass (syracPMF n)) k‖ ≤ B) :
    taoTV (syracPMF n) (PMF.uniformOfFintype (ZMod (3 ^ n))) ≤
      (((3 ^ n) - 1 : ℕ) : ℝ) * B := by
  exact taoTV_uniform_le_nonzero_card_mul_of_nonzero_dft_le
    (N := 3 ^ n) (syracPMF n) hB

/-- Statement-level hypothesis for nonzero Fourier coefficients of `syracPMF n`. -/
def syracPMFNonzeroDFTBound (n : ℕ) (B : ℝ) : Prop :=
  ∀ k : ZMod (3 ^ n), k ≠ 0 →
    ‖ZMod.dft (pmfComplexMass (syracPMF n)) k‖ ≤ B

theorem syracPMFNonzeroDFTBound_taoTV_uniform_le
    (n : ℕ) {B : ℝ} (hB : syracPMFNonzeroDFTBound n B) :
    taoTV (syracPMF n) (PMF.uniformOfFintype (ZMod (3 ^ n))) ≤
      (((3 ^ n) - 1 : ℕ) : ℝ) * B := by
  exact taoTV_syracPMF_uniform_le_nonzero_card_mul_of_dft_le n hB

theorem taoTV_syracPMF_uniform_le_of_nonzero_dft_le_div_nonzero_card
    (n : ℕ) (hn : 0 < n) {ε : ℝ}
    (hB : ∀ k : ZMod (3 ^ n), k ≠ 0 →
      ‖ZMod.dft (pmfComplexMass (syracPMF n)) k‖ ≤
        ε / (((3 ^ n) - 1 : ℕ) : ℝ)) :
    taoTV (syracPMF n) (PMF.uniformOfFintype (ZMod (3 ^ n))) ≤ ε := by
  have hpow : 1 < 3 ^ n := by
    exact Nat.one_lt_pow (Nat.ne_of_gt hn) (by norm_num)
  exact taoTV_uniform_le_of_nonzero_dft_le_div_nonzero_card
    (N := 3 ^ n) (syracPMF n) hpow hB

theorem taoTV_syracPMF_uniform_le_of_nonzero_dft_le_div_natCast
    (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hB : ∀ k : ZMod (3 ^ n), k ≠ 0 →
      ‖ZMod.dft (pmfComplexMass (syracPMF n)) k‖ ≤ ε / ((3 ^ n : ℕ) : ℝ)) :
    taoTV (syracPMF n) (PMF.uniformOfFintype (ZMod (3 ^ n))) ≤ ε := by
  exact taoTV_uniform_le_of_nonzero_dft_le_div_natCast
    (N := 3 ^ n) (syracPMF n) hε hB

end Tao
end Erdos1135SecondScale
