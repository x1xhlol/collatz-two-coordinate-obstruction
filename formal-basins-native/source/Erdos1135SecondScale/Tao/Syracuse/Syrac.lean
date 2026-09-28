/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Syracuse.ValuationDistribution
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Finite Syrac PMF Skeleton

This module starts Tao's finite `Syrac(Z/3^nZ)` surface.  The first checked layer only fixes the
step orientation and recursive PMF shape.  The inverse of `2^a` multiplies the entire lifted
`3 * y + 1` term; table proofs, Fourier transforms, Proposition 1.9 estimates, and renewal
machinery are intentionally left to later modules.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable def syracStep (n : ℕ)
    (y : ZMod (3 ^ n)) (a : ℕ+) : ZMod (3 ^ (n + 1)) :=
  (((2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ))⁻¹) *
    ((3 : ZMod (3 ^ (n + 1))) * (y.val : ZMod (3 ^ (n + 1))) + 1)

noncomputable def syracPMF : (n : ℕ) → PMF (ZMod (3 ^ n))
  | 0 => PMF.pure 0
  | n + 1 =>
      (syracPMF n).bind fun y =>
        geom2PNat.map fun a => syracStep n y a

theorem syracPMF_zero_apply_zero :
    syracPMF 0 (0 : ZMod (3 ^ 0)) = 1 := by
  simp [syracPMF]

theorem syracStep_zero_even (k : ℕ) :
    syracStep 0 (0 : ZMod (3 ^ 0)) ⟨2 * k + 2, by omega⟩ =
      (1 : ZMod (3 ^ (0 + 1))) := by
  simp [syracStep]
  rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul]
  change (4 : ZMod 3) ^ (k + 1) = 1
  rw [show (4 : ZMod 3) = 1 by decide]
  simp

theorem syracStep_zero_odd (k : ℕ) :
    syracStep 0 (0 : ZMod (3 ^ 0)) ⟨2 * k + 1, by omega⟩ =
      (2 : ZMod (3 ^ (0 + 1))) := by
  simp [syracStep]
  have heven : (2 : ZMod (3 ^ (0 + 1))) ^ (2 * k) = 1 := by
    rw [pow_mul]
    change (4 : ZMod 3) ^ k = 1
    rw [show (4 : ZMod 3) = 1 by decide]
    simp
  have hpow : (2 : ZMod (3 ^ (0 + 1))) ^ (2 * k + 1) = 2 := by
    calc
      (2 : ZMod (3 ^ (0 + 1))) ^ (2 * k + 1)
          = (2 : ZMod (3 ^ (0 + 1))) ^ (2 * k) * 2 := by
            exact pow_succ (2 : ZMod (3 ^ (0 + 1))) (2 * k)
      _ = 1 * 2 := by rw [heven]
      _ = 2 := by norm_num
  rw [hpow]
  change ((2 : ZMod 3)⁻¹ = 2)
  exact inv_eq_of_mul_eq_one_right (by decide : (2 : ZMod 3) * 2 = 1)

theorem syracPMF_one_eq_map :
    syracPMF 1 =
      geom2PNat.map fun a => syracStep 0 (0 : ZMod (3 ^ 0)) a := by
  ext x
  simp [syracPMF]

private def syracEvenExp (k : ℕ) : ℕ+ :=
  ⟨2 * k + 2, by omega⟩

private def syracOddExp (k : ℕ) : ℕ+ :=
  ⟨2 * k + 1, by omega⟩

private theorem syracStep_zero_even_exp (k : ℕ) :
    syracStep 0 (0 : ZMod (3 ^ 0)) (syracEvenExp k) =
      (1 : ZMod (3 ^ (0 + 1))) := by
  simpa [syracEvenExp] using syracStep_zero_even k

private theorem syracStep_zero_odd_exp (k : ℕ) :
    syracStep 0 (0 : ZMod (3 ^ 0)) (syracOddExp k) =
      (2 : ZMod (3 ^ (0 + 1))) := by
  simpa [syracOddExp] using syracStep_zero_odd k

private theorem syracStep_zero_ne_zero (a : ℕ+) :
    syracStep 0 (0 : ZMod (3 ^ 0)) a ≠ (0 : ZMod (3 ^ (0 + 1))) := by
  rcases Nat.even_or_odd' (a : ℕ) with ⟨k, hk | hk⟩
  · cases k with
    | zero =>
        exfalso
        have : (a : ℕ) = 0 := by simpa only [Nat.mul_zero] using hk
        exact (Nat.ne_of_gt a.2) this
    | succ k =>
        have ha : a = syracEvenExp k := by
          apply Subtype.ext
          change (a : ℕ) = 2 * k + 2
          omega
        rw [ha, syracStep_zero_even_exp]
        decide
  · have ha : a = syracOddExp k := by
      apply Subtype.ext
      change (a : ℕ) = 2 * k + 1
      omega
    rw [ha, syracStep_zero_odd_exp]
    decide

private theorem syracStep_zero_eq_one_iff (a : ℕ+) :
    syracStep 0 (0 : ZMod (3 ^ 0)) a = (1 : ZMod (3 ^ (0 + 1))) ↔
      ∃ k : ℕ, a = syracEvenExp k := by
  constructor
  · intro h
    rcases Nat.even_or_odd' (a : ℕ) with ⟨k, hk | hk⟩
    · cases k with
      | zero =>
          exfalso
          have : (a : ℕ) = 0 := by simpa only [Nat.mul_zero] using hk
          exact (Nat.ne_of_gt a.2) this
      | succ k =>
          refine ⟨k, ?_⟩
          apply Subtype.ext
          change (a : ℕ) = 2 * k + 2
          omega
    · have ha : a = syracOddExp k := by
        apply Subtype.ext
        change (a : ℕ) = 2 * k + 1
        omega
      rw [ha, syracStep_zero_odd_exp] at h
      exfalso
      exact (by decide : ¬((2 : ZMod (3 ^ (0 + 1))) = 1)) h
  · rintro ⟨k, rfl⟩
    exact syracStep_zero_even_exp k

private theorem syracStep_zero_eq_two_iff (a : ℕ+) :
    syracStep 0 (0 : ZMod (3 ^ 0)) a = (2 : ZMod (3 ^ (0 + 1))) ↔
      ∃ k : ℕ, a = syracOddExp k := by
  constructor
  · intro h
    rcases Nat.even_or_odd' (a : ℕ) with ⟨k, hk | hk⟩
    · cases k with
      | zero =>
          exfalso
          have : (a : ℕ) = 0 := by simpa only [Nat.mul_zero] using hk
          exact (Nat.ne_of_gt a.2) this
      | succ k =>
          have ha : a = syracEvenExp k := by
            apply Subtype.ext
            change (a : ℕ) = 2 * k + 2
            omega
          rw [ha, syracStep_zero_even_exp] at h
          exfalso
          exact (by decide : ¬((1 : ZMod (3 ^ (0 + 1))) = 2)) h
    · refine ⟨k, ?_⟩
      apply Subtype.ext
      change (a : ℕ) = 2 * k + 1
      omega
  · rintro ⟨k, rfl⟩
    exact syracStep_zero_odd_exp k

theorem syracPMF_one_apply_zero :
    syracPMF 1 (0 : ZMod (3 ^ 1)) = 0 := by
  rw [syracPMF_one_eq_map, PMF.map_apply]
  rw [ENNReal.tsum_eq_zero]
  intro a
  by_cases hz : (0 : ZMod (3 ^ 1)) = syracStep 0 (0 : ZMod (3 ^ 0)) a
  · exact (syracStep_zero_ne_zero a hz.symm).elim
  · simp [hz]

private theorem tsum_indicator_range_eq_of_injective (e : ℕ → ℕ+)
    (hinj : Function.Injective e) (g : ℕ+ → ℝ) :
    (∑' a : ℕ+, (Set.range e).indicator g a) = ∑' k : ℕ, g (e k) := by
  calc
    (∑' a : ℕ+, (Set.range e).indicator g a)
        = ∑' a : Set.range e, g a := by
          exact (tsum_subtype (Set.range e) g).symm
    _ = ∑' k : ℕ, g (e k) := by
          simpa using ((Equiv.ofInjective e hinj).tsum_eq
            (fun a : Set.range e => g a)).symm

private theorem syracEvenExp_injective : Function.Injective syracEvenExp := by
  intro i j h
  have hval : 2 * i + 2 = 2 * j + 2 := congrArg Subtype.val h
  omega

private theorem syracOddExp_injective : Function.Injective syracOddExp := by
  intro i j h
  have hval : 2 * i + 1 = 2 * j + 1 := congrArg Subtype.val h
  omega

private theorem syracPMF_one_apply_one_toReal_eq_fiber :
    (syracPMF 1 (1 : ZMod (3 ^ 1))).toReal =
      ∑' a : ℕ+,
        (if (1 : ZMod (3 ^ 1)) = syracStep 0 (0 : ZMod (3 ^ 0)) a
          then geom2PNat a else 0).toReal := by
  rw [syracPMF_one_eq_map, PMF.map_apply]
  rw [ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro a
    by_cases h : (1 : ZMod (3 ^ 1)) = syracStep 0 (0 : ZMod (3 ^ 0)) a <;> simp [h]
  · intro a
    by_cases h : (1 : ZMod (3 ^ 1)) = syracStep 0 (0 : ZMod (3 ^ 0)) a
    · simp [h, PMF.apply_ne_top]
    · simp [h]

private theorem syracPMF_one_apply_two_toReal_eq_fiber :
    (syracPMF 1 (2 : ZMod (3 ^ 1))).toReal =
      ∑' a : ℕ+,
        (if (2 : ZMod (3 ^ 1)) = syracStep 0 (0 : ZMod (3 ^ 0)) a
          then geom2PNat a else 0).toReal := by
  rw [syracPMF_one_eq_map, PMF.map_apply]
  rw [ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro a
    by_cases h : (2 : ZMod (3 ^ 1)) = syracStep 0 (0 : ZMod (3 ^ 0)) a <;> simp [h]
  · intro a
    by_cases h : (2 : ZMod (3 ^ 1)) = syracStep 0 (0 : ZMod (3 ^ 0)) a
    · simp [h, PMF.apply_ne_top]
    · simp [h]

private theorem tsum_syrac_one_fiber_eq_even_mass :
    (∑' a : ℕ+,
        (if (1 : ZMod (3 ^ 1)) = syracStep 0 (0 : ZMod (3 ^ 0)) a
          then geom2PNat a else 0).toReal) =
      ∑' k : ℕ, (geom2PNat (syracEvenExp k)).toReal := by
  calc
    (∑' a : ℕ+,
        (if (1 : ZMod (3 ^ 1)) = syracStep 0 (0 : ZMod (3 ^ 0)) a
          then geom2PNat a else 0).toReal)
        = ∑' a : ℕ+,
            (Set.range syracEvenExp).indicator
              (fun a : ℕ+ => (geom2PNat a).toReal) a := by
          apply tsum_congr
          intro a
          have hcond :
              ((1 : ZMod (3 ^ 1)) = syracStep 0 (0 : ZMod (3 ^ 0)) a) ↔
                ∃ k : ℕ, a = syracEvenExp k := by
            rw [eq_comm, syracStep_zero_eq_one_iff]
          by_cases h : ∃ k : ℕ, a = syracEvenExp k
          · have hstep :
                (1 : ZMod (3 ^ 1)) = syracStep 0 (0 : ZMod (3 ^ 0)) a :=
              hcond.mpr h
            have hrange : a ∈ Set.range syracEvenExp := by
              rcases h with ⟨k, hk⟩
              exact ⟨k, hk.symm⟩
            simp [hstep, hrange]
          · have hstep :
                ¬ (1 : ZMod (3 ^ 1)) = syracStep 0 (0 : ZMod (3 ^ 0)) a := by
              intro hs
              exact h (hcond.mp hs)
            have hrange : a ∉ Set.range syracEvenExp := by
              rintro ⟨k, hk⟩
              exact h ⟨k, hk.symm⟩
            simp [hstep, hrange]
    _ = ∑' k : ℕ, (geom2PNat (syracEvenExp k)).toReal := by
          exact tsum_indicator_range_eq_of_injective syracEvenExp syracEvenExp_injective
            (fun a : ℕ+ => (geom2PNat a).toReal)

private theorem tsum_syrac_two_fiber_eq_odd_mass :
    (∑' a : ℕ+,
        (if (2 : ZMod (3 ^ 1)) = syracStep 0 (0 : ZMod (3 ^ 0)) a
          then geom2PNat a else 0).toReal) =
      ∑' k : ℕ, (geom2PNat (syracOddExp k)).toReal := by
  calc
    (∑' a : ℕ+,
        (if (2 : ZMod (3 ^ 1)) = syracStep 0 (0 : ZMod (3 ^ 0)) a
          then geom2PNat a else 0).toReal)
        = ∑' a : ℕ+,
            (Set.range syracOddExp).indicator
              (fun a : ℕ+ => (geom2PNat a).toReal) a := by
          apply tsum_congr
          intro a
          have hcond :
              ((2 : ZMod (3 ^ 1)) = syracStep 0 (0 : ZMod (3 ^ 0)) a) ↔
                ∃ k : ℕ, a = syracOddExp k := by
            rw [eq_comm, syracStep_zero_eq_two_iff]
          by_cases h : ∃ k : ℕ, a = syracOddExp k
          · have hstep :
                (2 : ZMod (3 ^ 1)) = syracStep 0 (0 : ZMod (3 ^ 0)) a :=
              hcond.mpr h
            have hrange : a ∈ Set.range syracOddExp := by
              rcases h with ⟨k, hk⟩
              exact ⟨k, hk.symm⟩
            simp [hstep, hrange]
          · have hstep :
                ¬ (2 : ZMod (3 ^ 1)) = syracStep 0 (0 : ZMod (3 ^ 0)) a := by
              intro hs
              exact h (hcond.mp hs)
            have hrange : a ∉ Set.range syracOddExp := by
              rintro ⟨k, hk⟩
              exact h ⟨k, hk.symm⟩
            simp [hstep, hrange]
    _ = ∑' k : ℕ, (geom2PNat (syracOddExp k)).toReal := by
          exact tsum_indicator_range_eq_of_injective syracOddExp syracOddExp_injective
            (fun a : ℕ+ => (geom2PNat a).toReal)

private theorem syracPMF_one_apply_one_toReal :
    (syracPMF 1 (1 : ZMod (3 ^ 1))).toReal = 1 / 3 := by
  rw [syracPMF_one_apply_one_toReal_eq_fiber, tsum_syrac_one_fiber_eq_even_mass]
  simpa [syracEvenExp] using tsum_geom2PNat_even_param_toReal

private theorem syracPMF_one_apply_two_toReal :
    (syracPMF 1 (2 : ZMod (3 ^ 1))).toReal = 2 / 3 := by
  rw [syracPMF_one_apply_two_toReal_eq_fiber, tsum_syrac_two_fiber_eq_odd_mass]
  simpa [syracOddExp] using tsum_geom2PNat_odd_param_toReal

theorem syracPMF_one_apply_one :
    syracPMF 1 (1 : ZMod (3 ^ 1)) = ENNReal.ofReal (1 / 3 : ℝ) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top (syracPMF 1) (1 : ZMod (3 ^ 1)))
    ENNReal.ofReal_ne_top).mp
  rw [syracPMF_one_apply_one_toReal]
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1 / 3 : ℝ))]

theorem syracPMF_one_apply_two :
    syracPMF 1 (2 : ZMod (3 ^ 1)) = ENNReal.ofReal (2 / 3 : ℝ) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top (syracPMF 1) (2 : ZMod (3 ^ 1)))
    ENNReal.ofReal_ne_top).mp
  rw [syracPMF_one_apply_two_toReal]
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (2 / 3 : ℝ))]

theorem syracPMF_one_apply (x : ZMod (3 ^ 1)) :
    syracPMF 1 x =
      if x = 0 then 0
      else if x = 1 then ENNReal.ofReal (1 / 3 : ℝ)
      else ENNReal.ofReal (2 / 3 : ℝ) := by
  fin_cases x
  · change syracPMF 1 (0 : ZMod (3 ^ 1)) =
      if (0 : ZMod (3 ^ 1)) = 0 then 0
      else if (0 : ZMod (3 ^ 1)) = 1 then ENNReal.ofReal (1 / 3 : ℝ)
      else ENNReal.ofReal (2 / 3 : ℝ)
    rw [syracPMF_one_apply_zero]
    simp
  · change syracPMF 1 (1 : ZMod (3 ^ 1)) =
      if (1 : ZMod (3 ^ 1)) = 0 then 0
      else if (1 : ZMod (3 ^ 1)) = 1 then ENNReal.ofReal (1 / 3 : ℝ)
      else ENNReal.ofReal (2 / 3 : ℝ)
    rw [syracPMF_one_apply_one]
    simp [show ¬((1 : ZMod (3 ^ 1)) = 0) by decide]
  · change syracPMF 1 (2 : ZMod (3 ^ 1)) =
      if (2 : ZMod (3 ^ 1)) = 0 then 0
      else if (2 : ZMod (3 ^ 1)) = 1 then ENNReal.ofReal (1 / 3 : ℝ)
      else ENNReal.ofReal (2 / 3 : ℝ)
    rw [syracPMF_one_apply_two]
    simp [show ¬((2 : ZMod (3 ^ 1)) = 0) by decide,
      show ¬((2 : ZMod (3 ^ 1)) = 1) by decide]

private def syracMod6Exp1 (k : ℕ) : ℕ+ :=
  ⟨6 * k + 1, by omega⟩

private def syracMod6Exp2 (k : ℕ) : ℕ+ :=
  ⟨6 * k + 2, by omega⟩

private def syracMod6Exp3 (k : ℕ) : ℕ+ :=
  ⟨6 * k + 3, by omega⟩

private def syracMod6Exp4 (k : ℕ) : ℕ+ :=
  ⟨6 * k + 4, by omega⟩

private def syracMod6Exp5 (k : ℕ) : ℕ+ :=
  ⟨6 * k + 5, by omega⟩

private def syracMod6Exp6 (k : ℕ) : ℕ+ :=
  ⟨6 * k + 6, by omega⟩

private theorem pnat_mod6_cases (a : ℕ+) :
    (∃ k : ℕ, a = syracMod6Exp1 k) ∨
    (∃ k : ℕ, a = syracMod6Exp2 k) ∨
    (∃ k : ℕ, a = syracMod6Exp3 k) ∨
    (∃ k : ℕ, a = syracMod6Exp4 k) ∨
    (∃ k : ℕ, a = syracMod6Exp5 k) ∨
    (∃ k : ℕ, a = syracMod6Exp6 k) := by
  let r := (a : ℕ) % 6
  have hr : (a : ℕ) % 6 = r := rfl
  have hrlt : r < 6 := Nat.mod_lt _ (by decide)
  have hdiv : 6 * ((a : ℕ) / 6) + (a : ℕ) % 6 = (a : ℕ) := Nat.div_add_mod (a : ℕ) 6
  interval_cases r
  · right; right; right; right; right
    refine ⟨(a : ℕ) / 6 - 1, ?_⟩
    apply Subtype.ext
    change (a : ℕ) = 6 * (((a : ℕ) / 6 - 1)) + 6
    have hqpos : 0 < (a : ℕ) / 6 := by
      by_contra hq
      have hq0 : (a : ℕ) / 6 = 0 := by omega
      have : (a : ℕ) = 0 := by omega
      exact (Nat.ne_of_gt a.2) this
    omega
  · left
    refine ⟨(a : ℕ) / 6, ?_⟩
    apply Subtype.ext
    change (a : ℕ) = 6 * ((a : ℕ) / 6) + 1
    omega
  · right; left
    refine ⟨(a : ℕ) / 6, ?_⟩
    apply Subtype.ext
    change (a : ℕ) = 6 * ((a : ℕ) / 6) + 2
    omega
  · right; right; left
    refine ⟨(a : ℕ) / 6, ?_⟩
    apply Subtype.ext
    change (a : ℕ) = 6 * ((a : ℕ) / 6) + 3
    omega
  · right; right; right; left
    refine ⟨(a : ℕ) / 6, ?_⟩
    apply Subtype.ext
    change (a : ℕ) = 6 * ((a : ℕ) / 6) + 4
    omega
  · right; right; right; right; left
    refine ⟨(a : ℕ) / 6, ?_⟩
    apply Subtype.ext
    change (a : ℕ) = 6 * ((a : ℕ) / 6) + 5
    omega

private theorem two_pow_mod9_mod6 (k r : ℕ) :
    (2 : ZMod 9) ^ (6 * k + r) = (2 : ZMod 9) ^ r := by
  rw [pow_add, pow_mul]
  rw [show (2 : ZMod 9) ^ 6 = 1 by decide]
  simp

private theorem syracStep_one_zero_mod6_one (k : ℕ) :
    syracStep 1 (0 : ZMod (3 ^ 1)) (syracMod6Exp1 k) =
      (5 : ZMod (3 ^ (1 + 1))) := by
  simp [syracStep, syracMod6Exp1]
  change (((2 : ZMod 9) ^ (6 * k + 1))⁻¹) = 5
  rw [two_pow_mod9_mod6]
  decide

private theorem syracStep_one_zero_mod6_two (k : ℕ) :
    syracStep 1 (0 : ZMod (3 ^ 1)) (syracMod6Exp2 k) =
      (7 : ZMod (3 ^ (1 + 1))) := by
  simp [syracStep, syracMod6Exp2]
  change (((2 : ZMod 9) ^ (6 * k + 2))⁻¹) = 7
  rw [two_pow_mod9_mod6]
  decide

private theorem syracStep_one_zero_mod6_three (k : ℕ) :
    syracStep 1 (0 : ZMod (3 ^ 1)) (syracMod6Exp3 k) =
      (8 : ZMod (3 ^ (1 + 1))) := by
  simp [syracStep, syracMod6Exp3]
  change (((2 : ZMod 9) ^ (6 * k + 3))⁻¹) = 8
  rw [two_pow_mod9_mod6]
  decide

private theorem syracStep_one_zero_mod6_four (k : ℕ) :
    syracStep 1 (0 : ZMod (3 ^ 1)) (syracMod6Exp4 k) =
      (4 : ZMod (3 ^ (1 + 1))) := by
  simp [syracStep, syracMod6Exp4]
  change (((2 : ZMod 9) ^ (6 * k + 4))⁻¹) = 4
  rw [two_pow_mod9_mod6]
  decide

private theorem syracStep_one_zero_mod6_five (k : ℕ) :
    syracStep 1 (0 : ZMod (3 ^ 1)) (syracMod6Exp5 k) =
      (2 : ZMod (3 ^ (1 + 1))) := by
  simp [syracStep, syracMod6Exp5]
  change (((2 : ZMod 9) ^ (6 * k + 5))⁻¹) = 2
  rw [two_pow_mod9_mod6]
  decide

private theorem syracStep_one_zero_mod6_six (k : ℕ) :
    syracStep 1 (0 : ZMod (3 ^ 1)) (syracMod6Exp6 k) =
      (1 : ZMod (3 ^ (1 + 1))) := by
  simp [syracStep, syracMod6Exp6]
  change (((2 : ZMod 9) ^ (6 * k + 6))⁻¹) = 1
  rw [two_pow_mod9_mod6]
  decide

private theorem syracStep_one_one_mod6_one (k : ℕ) :
    syracStep 1 (1 : ZMod (3 ^ 1)) (syracMod6Exp1 k) =
      (2 : ZMod (3 ^ (1 + 1))) := by
  simp [syracStep, syracMod6Exp1]
  change (((2 : ZMod 9) ^ (6 * k + 1))⁻¹) * 4 = 2
  rw [two_pow_mod9_mod6]
  decide

private theorem syracStep_one_one_mod6_two (k : ℕ) :
    syracStep 1 (1 : ZMod (3 ^ 1)) (syracMod6Exp2 k) =
      (1 : ZMod (3 ^ (1 + 1))) := by
  simp [syracStep, syracMod6Exp2]
  change (((2 : ZMod 9) ^ (6 * k + 2))⁻¹) * 4 = 1
  rw [two_pow_mod9_mod6]
  decide

private theorem syracStep_one_one_mod6_three (k : ℕ) :
    syracStep 1 (1 : ZMod (3 ^ 1)) (syracMod6Exp3 k) =
      (5 : ZMod (3 ^ (1 + 1))) := by
  simp [syracStep, syracMod6Exp3]
  change (((2 : ZMod 9) ^ (6 * k + 3))⁻¹) * 4 = 5
  rw [two_pow_mod9_mod6]
  decide

private theorem syracStep_one_one_mod6_four (k : ℕ) :
    syracStep 1 (1 : ZMod (3 ^ 1)) (syracMod6Exp4 k) =
      (7 : ZMod (3 ^ (1 + 1))) := by
  simp [syracStep, syracMod6Exp4]
  change (((2 : ZMod 9) ^ (6 * k + 4))⁻¹) * 4 = 7
  rw [two_pow_mod9_mod6]
  decide

private theorem syracStep_one_one_mod6_five (k : ℕ) :
    syracStep 1 (1 : ZMod (3 ^ 1)) (syracMod6Exp5 k) =
      (8 : ZMod (3 ^ (1 + 1))) := by
  simp [syracStep, syracMod6Exp5]
  change (((2 : ZMod 9) ^ (6 * k + 5))⁻¹) * 4 = 8
  rw [two_pow_mod9_mod6]
  decide

private theorem syracStep_one_one_mod6_six (k : ℕ) :
    syracStep 1 (1 : ZMod (3 ^ 1)) (syracMod6Exp6 k) =
      (4 : ZMod (3 ^ (1 + 1))) := by
  simp [syracStep, syracMod6Exp6]
  change (((2 : ZMod 9) ^ (6 * k + 6))⁻¹) * 4 = 4
  rw [two_pow_mod9_mod6]
  decide

private theorem syracStep_one_two_mod6_one (k : ℕ) :
    syracStep 1 (2 : ZMod (3 ^ 1)) (syracMod6Exp1 k) =
      (8 : ZMod (3 ^ (1 + 1))) := by
  simp [syracStep, syracMod6Exp1]
  change (((2 : ZMod 9) ^ (6 * k + 1))⁻¹) * 7 = 8
  rw [two_pow_mod9_mod6]
  decide

private theorem syracStep_one_two_mod6_two (k : ℕ) :
    syracStep 1 (2 : ZMod (3 ^ 1)) (syracMod6Exp2 k) =
      (4 : ZMod (3 ^ (1 + 1))) := by
  simp [syracStep, syracMod6Exp2]
  change (((2 : ZMod 9) ^ (6 * k + 2))⁻¹) * 7 = 4
  rw [two_pow_mod9_mod6]
  decide

private theorem syracStep_one_two_mod6_three (k : ℕ) :
    syracStep 1 (2 : ZMod (3 ^ 1)) (syracMod6Exp3 k) =
      (2 : ZMod (3 ^ (1 + 1))) := by
  simp [syracStep, syracMod6Exp3]
  change (((2 : ZMod 9) ^ (6 * k + 3))⁻¹) * 7 = 2
  rw [two_pow_mod9_mod6]
  decide

private theorem syracStep_one_two_mod6_four (k : ℕ) :
    syracStep 1 (2 : ZMod (3 ^ 1)) (syracMod6Exp4 k) =
      (1 : ZMod (3 ^ (1 + 1))) := by
  simp [syracStep, syracMod6Exp4]
  change (((2 : ZMod 9) ^ (6 * k + 4))⁻¹) * 7 = 1
  rw [two_pow_mod9_mod6]
  decide

private theorem syracStep_one_two_mod6_five (k : ℕ) :
    syracStep 1 (2 : ZMod (3 ^ 1)) (syracMod6Exp5 k) =
      (5 : ZMod (3 ^ (1 + 1))) := by
  simp [syracStep, syracMod6Exp5]
  change (((2 : ZMod 9) ^ (6 * k + 5))⁻¹) * 7 = 5
  rw [two_pow_mod9_mod6]
  decide

private theorem syracStep_one_two_mod6_six (k : ℕ) :
    syracStep 1 (2 : ZMod (3 ^ 1)) (syracMod6Exp6 k) =
      (7 : ZMod (3 ^ (1 + 1))) := by
  simp [syracStep, syracMod6Exp6]
  change (((2 : ZMod 9) ^ (6 * k + 6))⁻¹) * 7 = 7
  rw [two_pow_mod9_mod6]
  decide

private theorem syracStep_one_ne_zero_mod9 (y : ZMod (3 ^ 1)) (a : ℕ+) :
    syracStep 1 y a ≠ (0 : ZMod (3 ^ (1 + 1))) := by
  rcases pnat_mod6_cases a with h | h | h | h | h | h
  all_goals
    rcases h with ⟨k, rfl⟩
    fin_cases y <;>
      simp [syracStep, syracMod6Exp1, syracMod6Exp2, syracMod6Exp3, syracMod6Exp4,
        syracMod6Exp5, syracMod6Exp6, two_pow_mod9_mod6] <;>
      decide

private theorem syracStep_one_ne_three_mod9 (y : ZMod (3 ^ 1)) (a : ℕ+) :
    syracStep 1 y a ≠ (3 : ZMod (3 ^ (1 + 1))) := by
  rcases pnat_mod6_cases a with h | h | h | h | h | h
  all_goals
    rcases h with ⟨k, rfl⟩
    fin_cases y <;>
      simp [syracStep, syracMod6Exp1, syracMod6Exp2, syracMod6Exp3, syracMod6Exp4,
        syracMod6Exp5, syracMod6Exp6, two_pow_mod9_mod6] <;>
      decide

private theorem syracStep_one_ne_six_mod9 (y : ZMod (3 ^ 1)) (a : ℕ+) :
    syracStep 1 y a ≠ (6 : ZMod (3 ^ (1 + 1))) := by
  rcases pnat_mod6_cases a with h | h | h | h | h | h
  all_goals
    rcases h with ⟨k, rfl⟩
    fin_cases y <;>
      simp [syracStep, syracMod6Exp1, syracMod6Exp2, syracMod6Exp3, syracMod6Exp4,
        syracMod6Exp5, syracMod6Exp6, two_pow_mod9_mod6] <;>
      decide

private theorem map_syracStep_one_apply_zero
    (y : ZMod (3 ^ 1)) :
    (PMF.map (fun a => syracStep 1 y a) geom2PNat)
      (0 : ZMod (3 ^ (1 + 1))) = 0 := by
  rw [PMF.map_apply, ENNReal.tsum_eq_zero]
  intro a
  by_cases h : (0 : ZMod (3 ^ (1 + 1))) = syracStep 1 y a
  · exact (syracStep_one_ne_zero_mod9 y a h.symm).elim
  · simp [h]

private theorem map_syracStep_one_apply_three
    (y : ZMod (3 ^ 1)) :
    (PMF.map (fun a => syracStep 1 y a) geom2PNat)
      (3 : ZMod (3 ^ (1 + 1))) = 0 := by
  rw [PMF.map_apply, ENNReal.tsum_eq_zero]
  intro a
  by_cases h : (3 : ZMod (3 ^ (1 + 1))) = syracStep 1 y a
  · exact (syracStep_one_ne_three_mod9 y a h.symm).elim
  · simp [h]

private theorem map_syracStep_one_apply_six
    (y : ZMod (3 ^ 1)) :
    (PMF.map (fun a => syracStep 1 y a) geom2PNat)
      (6 : ZMod (3 ^ (1 + 1))) = 0 := by
  rw [PMF.map_apply, ENNReal.tsum_eq_zero]
  intro a
  by_cases h : (6 : ZMod (3 ^ (1 + 1))) = syracStep 1 y a
  · exact (syracStep_one_ne_six_mod9 y a h.symm).elim
  · simp [h]

theorem syracPMF_two_apply_zero :
    syracPMF 2 (0 : ZMod (3 ^ 2)) = 0 := by
  change syracPMF (1 + 1) (0 : ZMod (3 ^ (1 + 1))) = 0
  rw [syracPMF, PMF.bind_apply, ENNReal.tsum_eq_zero]
  intro y
  rw [map_syracStep_one_apply_zero y, mul_zero]

theorem syracPMF_two_apply_three :
    syracPMF 2 (3 : ZMod (3 ^ 2)) = 0 := by
  change syracPMF (1 + 1) (3 : ZMod (3 ^ (1 + 1))) = 0
  rw [syracPMF, PMF.bind_apply, ENNReal.tsum_eq_zero]
  intro y
  rw [map_syracStep_one_apply_three y, mul_zero]

theorem syracPMF_two_apply_six :
    syracPMF 2 (6 : ZMod (3 ^ 2)) = 0 := by
  change syracPMF (1 + 1) (6 : ZMod (3 ^ (1 + 1))) = 0
  rw [syracPMF, PMF.bind_apply, ENNReal.tsum_eq_zero]
  intro y
  rw [map_syracStep_one_apply_six y, mul_zero]

private theorem syracStep_one_one_eq_two_iff (a : ℕ+) :
    (2 : ZMod (3 ^ (1 + 1))) = syracStep 1 (1 : ZMod (3 ^ 1)) a ↔
      ∃ k : ℕ, a = syracMod6Exp1 k := by
  rcases pnat_mod6_cases a with h | h | h | h | h | h
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro _
      exact ⟨k, rfl⟩
    · intro _
      rw [syracStep_one_one_mod6_one]
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_two] at hstep
      exact (by decide : ¬((2 : ZMod (3 ^ (1 + 1))) = 1)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 2 = 6 * j + 1 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_three] at hstep
      exact (by decide : ¬((2 : ZMod (3 ^ (1 + 1))) = 5)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 3 = 6 * j + 1 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_four] at hstep
      exact (by decide : ¬((2 : ZMod (3 ^ (1 + 1))) = 7)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 4 = 6 * j + 1 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_five] at hstep
      exact (by decide : ¬((2 : ZMod (3 ^ (1 + 1))) = 8)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 5 = 6 * j + 1 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_six] at hstep
      exact (by decide : ¬((2 : ZMod (3 ^ (1 + 1))) = 4)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 6 = 6 * j + 1 := congrArg Subtype.val hj
      omega

private theorem syracMod6Exp1_injective : Function.Injective syracMod6Exp1 := by
  intro i j h
  have hval : 6 * i + 1 = 6 * j + 1 := congrArg Subtype.val h
  omega

private theorem syracMod6Exp3_injective : Function.Injective syracMod6Exp3 := by
  intro i j h
  have hval : 6 * i + 3 = 6 * j + 3 := congrArg Subtype.val h
  omega

private theorem syracMod6Exp2_injective : Function.Injective syracMod6Exp2 := by
  intro i j h
  have hval : 6 * i + 2 = 6 * j + 2 := congrArg Subtype.val h
  omega

private theorem syracMod6Exp4_injective : Function.Injective syracMod6Exp4 := by
  intro i j h
  have hval : 6 * i + 4 = 6 * j + 4 := congrArg Subtype.val h
  omega

private theorem syracMod6Exp5_injective : Function.Injective syracMod6Exp5 := by
  intro i j h
  have hval : 6 * i + 5 = 6 * j + 5 := congrArg Subtype.val h
  omega

private theorem syracMod6Exp6_injective : Function.Injective syracMod6Exp6 := by
  intro i j h
  have hval : 6 * i + 6 = 6 * j + 6 := congrArg Subtype.val h
  omega

private theorem syracStep_one_two_eq_two_iff (a : ℕ+) :
    (2 : ZMod (3 ^ (1 + 1))) = syracStep 1 (2 : ZMod (3 ^ 1)) a ↔
      ∃ k : ℕ, a = syracMod6Exp3 k := by
  rcases pnat_mod6_cases a with h | h | h | h | h | h
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_one] at hstep
      exact (by decide : ¬((2 : ZMod (3 ^ (1 + 1))) = 8)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 1 = 6 * j + 3 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_two] at hstep
      exact (by decide : ¬((2 : ZMod (3 ^ (1 + 1))) = 4)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 2 = 6 * j + 3 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro _
      exact ⟨k, rfl⟩
    · intro _
      rw [syracStep_one_two_mod6_three]
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_four] at hstep
      exact (by decide : ¬((2 : ZMod (3 ^ (1 + 1))) = 1)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 4 = 6 * j + 3 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_five] at hstep
      exact (by decide : ¬((2 : ZMod (3 ^ (1 + 1))) = 5)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 5 = 6 * j + 3 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_six] at hstep
      exact (by decide : ¬((2 : ZMod (3 ^ (1 + 1))) = 7)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 6 = 6 * j + 3 := congrArg Subtype.val hj
      omega

private theorem syracStep_one_one_eq_one_iff (a : ℕ+) :
    (1 : ZMod (3 ^ (1 + 1))) = syracStep 1 (1 : ZMod (3 ^ 1)) a ↔
      ∃ k : ℕ, a = syracMod6Exp2 k := by
  rcases pnat_mod6_cases a with h | h | h | h | h | h
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_one] at hstep
      exact (by decide : ¬((1 : ZMod (3 ^ (1 + 1))) = 2)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 1 = 6 * j + 2 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro _
      exact ⟨k, rfl⟩
    · intro _
      rw [syracStep_one_one_mod6_two]
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_three] at hstep
      exact (by decide : ¬((1 : ZMod (3 ^ (1 + 1))) = 5)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 3 = 6 * j + 2 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_four] at hstep
      exact (by decide : ¬((1 : ZMod (3 ^ (1 + 1))) = 7)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 4 = 6 * j + 2 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_five] at hstep
      exact (by decide : ¬((1 : ZMod (3 ^ (1 + 1))) = 8)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 5 = 6 * j + 2 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_six] at hstep
      exact (by decide : ¬((1 : ZMod (3 ^ (1 + 1))) = 4)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 6 = 6 * j + 2 := congrArg Subtype.val hj
      omega

private theorem syracStep_one_two_eq_one_iff (a : ℕ+) :
    (1 : ZMod (3 ^ (1 + 1))) = syracStep 1 (2 : ZMod (3 ^ 1)) a ↔
      ∃ k : ℕ, a = syracMod6Exp4 k := by
  rcases pnat_mod6_cases a with h | h | h | h | h | h
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_one] at hstep
      exact (by decide : ¬((1 : ZMod (3 ^ (1 + 1))) = 8)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 1 = 6 * j + 4 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_two] at hstep
      exact (by decide : ¬((1 : ZMod (3 ^ (1 + 1))) = 4)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 2 = 6 * j + 4 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_three] at hstep
      exact (by decide : ¬((1 : ZMod (3 ^ (1 + 1))) = 2)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 3 = 6 * j + 4 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro _
      exact ⟨k, rfl⟩
    · intro _
      rw [syracStep_one_two_mod6_four]
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_five] at hstep
      exact (by decide : ¬((1 : ZMod (3 ^ (1 + 1))) = 5)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 5 = 6 * j + 4 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_six] at hstep
      exact (by decide : ¬((1 : ZMod (3 ^ (1 + 1))) = 7)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 6 = 6 * j + 4 := congrArg Subtype.val hj
      omega

private theorem syracStep_one_one_eq_four_iff (a : ℕ+) :
    (4 : ZMod (3 ^ (1 + 1))) = syracStep 1 (1 : ZMod (3 ^ 1)) a ↔
      ∃ k : ℕ, a = syracMod6Exp6 k := by
  rcases pnat_mod6_cases a with h | h | h | h | h | h
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_one] at hstep
      exact (by decide : ¬((4 : ZMod (3 ^ (1 + 1))) = 2)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 1 = 6 * j + 6 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_two] at hstep
      exact (by decide : ¬((4 : ZMod (3 ^ (1 + 1))) = 1)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 2 = 6 * j + 6 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_three] at hstep
      exact (by decide : ¬((4 : ZMod (3 ^ (1 + 1))) = 5)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 3 = 6 * j + 6 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_four] at hstep
      exact (by decide : ¬((4 : ZMod (3 ^ (1 + 1))) = 7)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 4 = 6 * j + 6 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_five] at hstep
      exact (by decide : ¬((4 : ZMod (3 ^ (1 + 1))) = 8)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 5 = 6 * j + 6 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro _
      exact ⟨k, rfl⟩
    · intro _
      rw [syracStep_one_one_mod6_six]

private theorem syracStep_one_two_eq_four_iff (a : ℕ+) :
    (4 : ZMod (3 ^ (1 + 1))) = syracStep 1 (2 : ZMod (3 ^ 1)) a ↔
      ∃ k : ℕ, a = syracMod6Exp2 k := by
  rcases pnat_mod6_cases a with h | h | h | h | h | h
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_one] at hstep
      exact (by decide : ¬((4 : ZMod (3 ^ (1 + 1))) = 8)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 1 = 6 * j + 2 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro _
      exact ⟨k, rfl⟩
    · intro _
      rw [syracStep_one_two_mod6_two]
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_three] at hstep
      exact (by decide : ¬((4 : ZMod (3 ^ (1 + 1))) = 2)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 3 = 6 * j + 2 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_four] at hstep
      exact (by decide : ¬((4 : ZMod (3 ^ (1 + 1))) = 1)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 4 = 6 * j + 2 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_five] at hstep
      exact (by decide : ¬((4 : ZMod (3 ^ (1 + 1))) = 5)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 5 = 6 * j + 2 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_six] at hstep
      exact (by decide : ¬((4 : ZMod (3 ^ (1 + 1))) = 7)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 6 = 6 * j + 2 := congrArg Subtype.val hj
      omega

private theorem syracStep_one_one_eq_five_iff (a : ℕ+) :
    (5 : ZMod (3 ^ (1 + 1))) = syracStep 1 (1 : ZMod (3 ^ 1)) a ↔
      ∃ k : ℕ, a = syracMod6Exp3 k := by
  rcases pnat_mod6_cases a with h | h | h | h | h | h
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_one] at hstep
      exact (by decide : ¬((5 : ZMod (3 ^ (1 + 1))) = 2)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 1 = 6 * j + 3 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_two] at hstep
      exact (by decide : ¬((5 : ZMod (3 ^ (1 + 1))) = 1)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 2 = 6 * j + 3 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro _
      exact ⟨k, rfl⟩
    · intro _
      rw [syracStep_one_one_mod6_three]
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_four] at hstep
      exact (by decide : ¬((5 : ZMod (3 ^ (1 + 1))) = 7)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 4 = 6 * j + 3 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_five] at hstep
      exact (by decide : ¬((5 : ZMod (3 ^ (1 + 1))) = 8)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 5 = 6 * j + 3 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_six] at hstep
      exact (by decide : ¬((5 : ZMod (3 ^ (1 + 1))) = 4)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 6 = 6 * j + 3 := congrArg Subtype.val hj
      omega

private theorem syracStep_one_two_eq_five_iff (a : ℕ+) :
    (5 : ZMod (3 ^ (1 + 1))) = syracStep 1 (2 : ZMod (3 ^ 1)) a ↔
      ∃ k : ℕ, a = syracMod6Exp5 k := by
  rcases pnat_mod6_cases a with h | h | h | h | h | h
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_one] at hstep
      exact (by decide : ¬((5 : ZMod (3 ^ (1 + 1))) = 8)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 1 = 6 * j + 5 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_two] at hstep
      exact (by decide : ¬((5 : ZMod (3 ^ (1 + 1))) = 4)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 2 = 6 * j + 5 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_three] at hstep
      exact (by decide : ¬((5 : ZMod (3 ^ (1 + 1))) = 2)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 3 = 6 * j + 5 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_four] at hstep
      exact (by decide : ¬((5 : ZMod (3 ^ (1 + 1))) = 1)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 4 = 6 * j + 5 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro _
      exact ⟨k, rfl⟩
    · intro _
      rw [syracStep_one_two_mod6_five]
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_six] at hstep
      exact (by decide : ¬((5 : ZMod (3 ^ (1 + 1))) = 7)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 6 = 6 * j + 5 := congrArg Subtype.val hj
      omega

private theorem syracStep_one_one_eq_seven_iff (a : ℕ+) :
    (7 : ZMod (3 ^ (1 + 1))) = syracStep 1 (1 : ZMod (3 ^ 1)) a ↔
      ∃ k : ℕ, a = syracMod6Exp4 k := by
  rcases pnat_mod6_cases a with h | h | h | h | h | h
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_one] at hstep
      exact (by decide : ¬((7 : ZMod (3 ^ (1 + 1))) = 2)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 1 = 6 * j + 4 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_two] at hstep
      exact (by decide : ¬((7 : ZMod (3 ^ (1 + 1))) = 1)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 2 = 6 * j + 4 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_three] at hstep
      exact (by decide : ¬((7 : ZMod (3 ^ (1 + 1))) = 5)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 3 = 6 * j + 4 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro _
      exact ⟨k, rfl⟩
    · intro _
      rw [syracStep_one_one_mod6_four]
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_five] at hstep
      exact (by decide : ¬((7 : ZMod (3 ^ (1 + 1))) = 8)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 5 = 6 * j + 4 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_six] at hstep
      exact (by decide : ¬((7 : ZMod (3 ^ (1 + 1))) = 4)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 6 = 6 * j + 4 := congrArg Subtype.val hj
      omega

private theorem syracStep_one_two_eq_seven_iff (a : ℕ+) :
    (7 : ZMod (3 ^ (1 + 1))) = syracStep 1 (2 : ZMod (3 ^ 1)) a ↔
      ∃ k : ℕ, a = syracMod6Exp6 k := by
  rcases pnat_mod6_cases a with h | h | h | h | h | h
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_one] at hstep
      exact (by decide : ¬((7 : ZMod (3 ^ (1 + 1))) = 8)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 1 = 6 * j + 6 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_two] at hstep
      exact (by decide : ¬((7 : ZMod (3 ^ (1 + 1))) = 4)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 2 = 6 * j + 6 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_three] at hstep
      exact (by decide : ¬((7 : ZMod (3 ^ (1 + 1))) = 2)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 3 = 6 * j + 6 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_four] at hstep
      exact (by decide : ¬((7 : ZMod (3 ^ (1 + 1))) = 1)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 4 = 6 * j + 6 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_five] at hstep
      exact (by decide : ¬((7 : ZMod (3 ^ (1 + 1))) = 5)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 5 = 6 * j + 6 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro _
      exact ⟨k, rfl⟩
    · intro _
      rw [syracStep_one_two_mod6_six]

private theorem syracStep_one_one_eq_eight_iff (a : ℕ+) :
    (8 : ZMod (3 ^ (1 + 1))) = syracStep 1 (1 : ZMod (3 ^ 1)) a ↔
      ∃ k : ℕ, a = syracMod6Exp5 k := by
  rcases pnat_mod6_cases a with h | h | h | h | h | h
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_one] at hstep
      exact (by decide : ¬((8 : ZMod (3 ^ (1 + 1))) = 2)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 1 = 6 * j + 5 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_two] at hstep
      exact (by decide : ¬((8 : ZMod (3 ^ (1 + 1))) = 1)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 2 = 6 * j + 5 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_three] at hstep
      exact (by decide : ¬((8 : ZMod (3 ^ (1 + 1))) = 5)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 3 = 6 * j + 5 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_four] at hstep
      exact (by decide : ¬((8 : ZMod (3 ^ (1 + 1))) = 7)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 4 = 6 * j + 5 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro _
      exact ⟨k, rfl⟩
    · intro _
      rw [syracStep_one_one_mod6_five]
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_one_mod6_six] at hstep
      exact (by decide : ¬((8 : ZMod (3 ^ (1 + 1))) = 4)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 6 = 6 * j + 5 := congrArg Subtype.val hj
      omega

private theorem syracStep_one_two_eq_eight_iff (a : ℕ+) :
    (8 : ZMod (3 ^ (1 + 1))) = syracStep 1 (2 : ZMod (3 ^ 1)) a ↔
      ∃ k : ℕ, a = syracMod6Exp1 k := by
  rcases pnat_mod6_cases a with h | h | h | h | h | h
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro _
      exact ⟨k, rfl⟩
    · intro _
      rw [syracStep_one_two_mod6_one]
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_two] at hstep
      exact (by decide : ¬((8 : ZMod (3 ^ (1 + 1))) = 4)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 2 = 6 * j + 1 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_three] at hstep
      exact (by decide : ¬((8 : ZMod (3 ^ (1 + 1))) = 2)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 3 = 6 * j + 1 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_four] at hstep
      exact (by decide : ¬((8 : ZMod (3 ^ (1 + 1))) = 1)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 4 = 6 * j + 1 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_five] at hstep
      exact (by decide : ¬((8 : ZMod (3 ^ (1 + 1))) = 5)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 5 = 6 * j + 1 := congrArg Subtype.val hj
      omega
  · rcases h with ⟨k, rfl⟩
    constructor
    · intro hstep
      exfalso
      rw [syracStep_one_two_mod6_six] at hstep
      exact (by decide : ¬((8 : ZMod (3 ^ (1 + 1))) = 7)) hstep
    · rintro ⟨j, hj⟩
      exfalso
      have hval : 6 * k + 6 = 6 * j + 1 := congrArg Subtype.val hj
      omega

private theorem map_syracStep_one_apply_toReal_of_fiber
    (y : ZMod (3 ^ 1)) (x : ZMod (3 ^ (1 + 1))) (e : ℕ → ℕ+)
    (hinj : Function.Injective e)
    (hiff : ∀ a : ℕ+, x = syracStep 1 y a ↔ ∃ k : ℕ, a = e k) :
    ((PMF.map (fun a => syracStep 1 y a) geom2PNat) x).toReal =
      ∑' k : ℕ, (geom2PNat (e k)).toReal := by
  rw [PMF.map_apply]
  rw [ENNReal.tsum_toReal_eq]
  · trans ∑' a : ℕ+,
        (Set.range e).indicator
          (fun a : ℕ+ => (geom2PNat a).toReal) a
    · apply tsum_congr
      intro a
      have hcond := hiff a
      by_cases h : ∃ k : ℕ, a = e k
      · have hstep : x = syracStep 1 y a := hcond.mpr h
        have hrange : a ∈ Set.range e := by
          rcases h with ⟨k, hk⟩
          exact ⟨k, hk.symm⟩
        simp [hstep, hrange]
      · have hstep : ¬ x = syracStep 1 y a := by
          intro hs
          exact h (hcond.mp hs)
        have hrange : a ∉ Set.range e := by
          rintro ⟨k, hk⟩
          exact h ⟨k, hk.symm⟩
        simp [hstep, hrange]
    · exact tsum_indicator_range_eq_of_injective e hinj
        (fun a : ℕ+ => (geom2PNat a).toReal)
  · intro a
    by_cases h : x = syracStep 1 y a
    · simp [h, PMF.apply_ne_top]
    · simp [h]

private theorem map_syracStep_one_one_apply_two_toReal :
    ((PMF.map (fun a => syracStep 1 (1 : ZMod (3 ^ 1)) a) geom2PNat)
      (2 : ZMod (3 ^ (1 + 1)))).toReal = 32 / 63 := by
  rw [map_syracStep_one_apply_toReal_of_fiber
    (1 : ZMod (3 ^ 1)) (2 : ZMod (3 ^ (1 + 1))) syracMod6Exp1
    syracMod6Exp1_injective syracStep_one_one_eq_two_iff]
  simpa [syracMod6Exp1] using tsum_geom2PNat_mod6_one_toReal

private theorem map_syracStep_one_one_apply_two :
    (PMF.map (fun a => syracStep 1 (1 : ZMod (3 ^ 1)) a) geom2PNat)
      (2 : ZMod (3 ^ (1 + 1))) = ENNReal.ofReal (32 / 63 : ℝ) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top
      (PMF.map (fun a => syracStep 1 (1 : ZMod (3 ^ 1)) a) geom2PNat)
      (2 : ZMod (3 ^ (1 + 1))))
    ENNReal.ofReal_ne_top).mp
  rw [map_syracStep_one_one_apply_two_toReal]
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (32 / 63 : ℝ))]

private theorem map_syracStep_one_two_apply_two_toReal :
    ((PMF.map (fun a => syracStep 1 (2 : ZMod (3 ^ 1)) a) geom2PNat)
      (2 : ZMod (3 ^ (1 + 1)))).toReal = 8 / 63 := by
  rw [map_syracStep_one_apply_toReal_of_fiber
    (2 : ZMod (3 ^ 1)) (2 : ZMod (3 ^ (1 + 1))) syracMod6Exp3
    syracMod6Exp3_injective syracStep_one_two_eq_two_iff]
  simpa [syracMod6Exp3] using tsum_geom2PNat_mod6_three_toReal

private theorem map_syracStep_one_two_apply_two :
    (PMF.map (fun a => syracStep 1 (2 : ZMod (3 ^ 1)) a) geom2PNat)
      (2 : ZMod (3 ^ (1 + 1))) = ENNReal.ofReal (8 / 63 : ℝ) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top
      (PMF.map (fun a => syracStep 1 (2 : ZMod (3 ^ 1)) a) geom2PNat)
      (2 : ZMod (3 ^ (1 + 1))))
    ENNReal.ofReal_ne_top).mp
  rw [map_syracStep_one_two_apply_two_toReal]
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (8 / 63 : ℝ))]

private theorem map_syracStep_one_one_apply_one_toReal :
    ((PMF.map (fun a => syracStep 1 (1 : ZMod (3 ^ 1)) a) geom2PNat)
      (1 : ZMod (3 ^ (1 + 1)))).toReal = 16 / 63 := by
  rw [map_syracStep_one_apply_toReal_of_fiber
    (1 : ZMod (3 ^ 1)) (1 : ZMod (3 ^ (1 + 1))) syracMod6Exp2
    syracMod6Exp2_injective syracStep_one_one_eq_one_iff]
  simpa [syracMod6Exp2] using tsum_geom2PNat_mod6_two_toReal

private theorem map_syracStep_one_one_apply_one :
    (PMF.map (fun a => syracStep 1 (1 : ZMod (3 ^ 1)) a) geom2PNat)
      (1 : ZMod (3 ^ (1 + 1))) = ENNReal.ofReal (16 / 63 : ℝ) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top
      (PMF.map (fun a => syracStep 1 (1 : ZMod (3 ^ 1)) a) geom2PNat)
      (1 : ZMod (3 ^ (1 + 1))))
    ENNReal.ofReal_ne_top).mp
  rw [map_syracStep_one_one_apply_one_toReal]
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (16 / 63 : ℝ))]

private theorem map_syracStep_one_two_apply_one_toReal :
    ((PMF.map (fun a => syracStep 1 (2 : ZMod (3 ^ 1)) a) geom2PNat)
      (1 : ZMod (3 ^ (1 + 1)))).toReal = 4 / 63 := by
  rw [map_syracStep_one_apply_toReal_of_fiber
    (2 : ZMod (3 ^ 1)) (1 : ZMod (3 ^ (1 + 1))) syracMod6Exp4
    syracMod6Exp4_injective syracStep_one_two_eq_one_iff]
  simpa [syracMod6Exp4] using tsum_geom2PNat_mod6_four_toReal

private theorem map_syracStep_one_two_apply_one :
    (PMF.map (fun a => syracStep 1 (2 : ZMod (3 ^ 1)) a) geom2PNat)
      (1 : ZMod (3 ^ (1 + 1))) = ENNReal.ofReal (4 / 63 : ℝ) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top
      (PMF.map (fun a => syracStep 1 (2 : ZMod (3 ^ 1)) a) geom2PNat)
      (1 : ZMod (3 ^ (1 + 1))))
    ENNReal.ofReal_ne_top).mp
  rw [map_syracStep_one_two_apply_one_toReal]
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (4 / 63 : ℝ))]

private theorem map_syracStep_one_one_apply_four_toReal :
    ((PMF.map (fun a => syracStep 1 (1 : ZMod (3 ^ 1)) a) geom2PNat)
      (4 : ZMod (3 ^ (1 + 1)))).toReal = 1 / 63 := by
  rw [map_syracStep_one_apply_toReal_of_fiber
    (1 : ZMod (3 ^ 1)) (4 : ZMod (3 ^ (1 + 1))) syracMod6Exp6
    syracMod6Exp6_injective syracStep_one_one_eq_four_iff]
  simpa [syracMod6Exp6] using tsum_geom2PNat_mod6_six_toReal

private theorem map_syracStep_one_one_apply_four :
    (PMF.map (fun a => syracStep 1 (1 : ZMod (3 ^ 1)) a) geom2PNat)
      (4 : ZMod (3 ^ (1 + 1))) = ENNReal.ofReal (1 / 63 : ℝ) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top
      (PMF.map (fun a => syracStep 1 (1 : ZMod (3 ^ 1)) a) geom2PNat)
      (4 : ZMod (3 ^ (1 + 1))))
    ENNReal.ofReal_ne_top).mp
  rw [map_syracStep_one_one_apply_four_toReal]
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1 / 63 : ℝ))]

private theorem map_syracStep_one_two_apply_four_toReal :
    ((PMF.map (fun a => syracStep 1 (2 : ZMod (3 ^ 1)) a) geom2PNat)
      (4 : ZMod (3 ^ (1 + 1)))).toReal = 16 / 63 := by
  rw [map_syracStep_one_apply_toReal_of_fiber
    (2 : ZMod (3 ^ 1)) (4 : ZMod (3 ^ (1 + 1))) syracMod6Exp2
    syracMod6Exp2_injective syracStep_one_two_eq_four_iff]
  simpa [syracMod6Exp2] using tsum_geom2PNat_mod6_two_toReal

private theorem map_syracStep_one_two_apply_four :
    (PMF.map (fun a => syracStep 1 (2 : ZMod (3 ^ 1)) a) geom2PNat)
      (4 : ZMod (3 ^ (1 + 1))) = ENNReal.ofReal (16 / 63 : ℝ) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top
      (PMF.map (fun a => syracStep 1 (2 : ZMod (3 ^ 1)) a) geom2PNat)
      (4 : ZMod (3 ^ (1 + 1))))
    ENNReal.ofReal_ne_top).mp
  rw [map_syracStep_one_two_apply_four_toReal]
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (16 / 63 : ℝ))]

private theorem map_syracStep_one_one_apply_five_toReal :
    ((PMF.map (fun a => syracStep 1 (1 : ZMod (3 ^ 1)) a) geom2PNat)
      (5 : ZMod (3 ^ (1 + 1)))).toReal = 8 / 63 := by
  rw [map_syracStep_one_apply_toReal_of_fiber
    (1 : ZMod (3 ^ 1)) (5 : ZMod (3 ^ (1 + 1))) syracMod6Exp3
    syracMod6Exp3_injective syracStep_one_one_eq_five_iff]
  simpa [syracMod6Exp3] using tsum_geom2PNat_mod6_three_toReal

private theorem map_syracStep_one_one_apply_five :
    (PMF.map (fun a => syracStep 1 (1 : ZMod (3 ^ 1)) a) geom2PNat)
      (5 : ZMod (3 ^ (1 + 1))) = ENNReal.ofReal (8 / 63 : ℝ) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top
      (PMF.map (fun a => syracStep 1 (1 : ZMod (3 ^ 1)) a) geom2PNat)
      (5 : ZMod (3 ^ (1 + 1))))
    ENNReal.ofReal_ne_top).mp
  rw [map_syracStep_one_one_apply_five_toReal]
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (8 / 63 : ℝ))]

private theorem map_syracStep_one_two_apply_five_toReal :
    ((PMF.map (fun a => syracStep 1 (2 : ZMod (3 ^ 1)) a) geom2PNat)
      (5 : ZMod (3 ^ (1 + 1)))).toReal = 2 / 63 := by
  rw [map_syracStep_one_apply_toReal_of_fiber
    (2 : ZMod (3 ^ 1)) (5 : ZMod (3 ^ (1 + 1))) syracMod6Exp5
    syracMod6Exp5_injective syracStep_one_two_eq_five_iff]
  simpa [syracMod6Exp5] using tsum_geom2PNat_mod6_five_toReal

private theorem map_syracStep_one_two_apply_five :
    (PMF.map (fun a => syracStep 1 (2 : ZMod (3 ^ 1)) a) geom2PNat)
      (5 : ZMod (3 ^ (1 + 1))) = ENNReal.ofReal (2 / 63 : ℝ) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top
      (PMF.map (fun a => syracStep 1 (2 : ZMod (3 ^ 1)) a) geom2PNat)
      (5 : ZMod (3 ^ (1 + 1))))
    ENNReal.ofReal_ne_top).mp
  rw [map_syracStep_one_two_apply_five_toReal]
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (2 / 63 : ℝ))]

private theorem map_syracStep_one_one_apply_seven_toReal :
    ((PMF.map (fun a => syracStep 1 (1 : ZMod (3 ^ 1)) a) geom2PNat)
      (7 : ZMod (3 ^ (1 + 1)))).toReal = 4 / 63 := by
  rw [map_syracStep_one_apply_toReal_of_fiber
    (1 : ZMod (3 ^ 1)) (7 : ZMod (3 ^ (1 + 1))) syracMod6Exp4
    syracMod6Exp4_injective syracStep_one_one_eq_seven_iff]
  simpa [syracMod6Exp4] using tsum_geom2PNat_mod6_four_toReal

private theorem map_syracStep_one_one_apply_seven :
    (PMF.map (fun a => syracStep 1 (1 : ZMod (3 ^ 1)) a) geom2PNat)
      (7 : ZMod (3 ^ (1 + 1))) = ENNReal.ofReal (4 / 63 : ℝ) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top
      (PMF.map (fun a => syracStep 1 (1 : ZMod (3 ^ 1)) a) geom2PNat)
      (7 : ZMod (3 ^ (1 + 1))))
    ENNReal.ofReal_ne_top).mp
  rw [map_syracStep_one_one_apply_seven_toReal]
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (4 / 63 : ℝ))]

private theorem map_syracStep_one_two_apply_seven_toReal :
    ((PMF.map (fun a => syracStep 1 (2 : ZMod (3 ^ 1)) a) geom2PNat)
      (7 : ZMod (3 ^ (1 + 1)))).toReal = 1 / 63 := by
  rw [map_syracStep_one_apply_toReal_of_fiber
    (2 : ZMod (3 ^ 1)) (7 : ZMod (3 ^ (1 + 1))) syracMod6Exp6
    syracMod6Exp6_injective syracStep_one_two_eq_seven_iff]
  simpa [syracMod6Exp6] using tsum_geom2PNat_mod6_six_toReal

private theorem map_syracStep_one_two_apply_seven :
    (PMF.map (fun a => syracStep 1 (2 : ZMod (3 ^ 1)) a) geom2PNat)
      (7 : ZMod (3 ^ (1 + 1))) = ENNReal.ofReal (1 / 63 : ℝ) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top
      (PMF.map (fun a => syracStep 1 (2 : ZMod (3 ^ 1)) a) geom2PNat)
      (7 : ZMod (3 ^ (1 + 1))))
    ENNReal.ofReal_ne_top).mp
  rw [map_syracStep_one_two_apply_seven_toReal]
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1 / 63 : ℝ))]

private theorem map_syracStep_one_one_apply_eight_toReal :
    ((PMF.map (fun a => syracStep 1 (1 : ZMod (3 ^ 1)) a) geom2PNat)
      (8 : ZMod (3 ^ (1 + 1)))).toReal = 2 / 63 := by
  rw [map_syracStep_one_apply_toReal_of_fiber
    (1 : ZMod (3 ^ 1)) (8 : ZMod (3 ^ (1 + 1))) syracMod6Exp5
    syracMod6Exp5_injective syracStep_one_one_eq_eight_iff]
  simpa [syracMod6Exp5] using tsum_geom2PNat_mod6_five_toReal

private theorem map_syracStep_one_one_apply_eight :
    (PMF.map (fun a => syracStep 1 (1 : ZMod (3 ^ 1)) a) geom2PNat)
      (8 : ZMod (3 ^ (1 + 1))) = ENNReal.ofReal (2 / 63 : ℝ) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top
      (PMF.map (fun a => syracStep 1 (1 : ZMod (3 ^ 1)) a) geom2PNat)
      (8 : ZMod (3 ^ (1 + 1))))
    ENNReal.ofReal_ne_top).mp
  rw [map_syracStep_one_one_apply_eight_toReal]
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (2 / 63 : ℝ))]

private theorem map_syracStep_one_two_apply_eight_toReal :
    ((PMF.map (fun a => syracStep 1 (2 : ZMod (3 ^ 1)) a) geom2PNat)
      (8 : ZMod (3 ^ (1 + 1)))).toReal = 32 / 63 := by
  rw [map_syracStep_one_apply_toReal_of_fiber
    (2 : ZMod (3 ^ 1)) (8 : ZMod (3 ^ (1 + 1))) syracMod6Exp1
    syracMod6Exp1_injective syracStep_one_two_eq_eight_iff]
  simpa [syracMod6Exp1] using tsum_geom2PNat_mod6_one_toReal

private theorem map_syracStep_one_two_apply_eight :
    (PMF.map (fun a => syracStep 1 (2 : ZMod (3 ^ 1)) a) geom2PNat)
      (8 : ZMod (3 ^ (1 + 1))) = ENNReal.ofReal (32 / 63 : ℝ) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top
      (PMF.map (fun a => syracStep 1 (2 : ZMod (3 ^ 1)) a) geom2PNat)
      (8 : ZMod (3 ^ (1 + 1))))
    ENNReal.ofReal_ne_top).mp
  rw [map_syracStep_one_two_apply_eight_toReal]
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (32 / 63 : ℝ))]

private theorem zmod3_univ :
    (Finset.univ : Finset (ZMod (3 ^ 1))) = {0, 1, 2} := by
  ext x
  fin_cases x
  · constructor
    · intro _
      decide
    · intro _
      simp
  · constructor
    · intro _
      decide
    · intro _
      simp
  · constructor
    · intro _
      decide
    · intro _
      simp

private theorem zmod3_tsum_eq_sum_three (f : ZMod (3 ^ 1) → ENNReal) :
    (∑' x : ZMod (3 ^ 1), f x) = f 0 + f 1 + f 2 := by
  rw [tsum_fintype]
  rw [zmod3_univ]
  have h01 : (0 : ZMod (3 ^ 1)) ≠ 1 := by decide
  have h02 : (0 : ZMod (3 ^ 1)) ≠ 2 := by decide
  have h12 : (1 : ZMod (3 ^ 1)) ≠ 2 := by decide
  simp [h01, h02, h12]
  rw [add_assoc]

private theorem weighted_geom_sum_eq_ofReal (m1 m2 total : ℝ)
    (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (htotal : 0 ≤ total)
    (hcalc : (1 / 3 : ℝ) * m1 + (2 / 3 : ℝ) * m2 = total) :
    (3 : ENNReal)⁻¹ * ENNReal.ofReal m1 +
        ENNReal.ofReal (2 / 3 : ℝ) * ENNReal.ofReal m2 =
      ENNReal.ofReal total := by
  apply (ENNReal.toReal_eq_toReal_iff' ?_ ENNReal.ofReal_ne_top).mp
  · rw [ENNReal.toReal_add]
    · rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
      rw [ENNReal.toReal_ofReal hm1, ENNReal.toReal_ofReal hm2,
        ENNReal.toReal_ofReal (by norm_num : 0 ≤ (2 / 3 : ℝ)),
        ENNReal.toReal_ofReal htotal]
      norm_num
      exact hcalc
    · exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩

private theorem ennreal_inv_nat63_eq :
    (63 : ENNReal)⁻¹ = ENNReal.ofReal (1 / 63 : ℝ) := by
  apply (ENNReal.toReal_eq_toReal_iff' ?_ ENNReal.ofReal_ne_top).mp
  · rw [ENNReal.toReal_inv]
    rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1 / 63 : ℝ))]
    norm_num
  · simp

theorem syracPMF_two_apply_one :
    syracPMF 2 (1 : ZMod (3 ^ 2)) = ENNReal.ofReal (8 / 63 : ℝ) := by
  change syracPMF (1 + 1) (1 : ZMod (3 ^ (1 + 1))) =
    ENNReal.ofReal (8 / 63 : ℝ)
  rw [syracPMF, PMF.bind_apply]
  rw [zmod3_tsum_eq_sum_three]
  rw [syracPMF_one_apply_zero, syracPMF_one_apply_one, syracPMF_one_apply_two]
  rw [map_syracStep_one_one_apply_one, map_syracStep_one_two_apply_one]
  simp
  exact weighted_geom_sum_eq_ofReal (16 / 63) (4 / 63) (8 / 63)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem syracPMF_two_apply_two :
    syracPMF 2 (2 : ZMod (3 ^ 2)) = ENNReal.ofReal (16 / 63 : ℝ) := by
  change syracPMF (1 + 1) (2 : ZMod (3 ^ (1 + 1))) =
    ENNReal.ofReal (16 / 63 : ℝ)
  rw [syracPMF, PMF.bind_apply]
  rw [zmod3_tsum_eq_sum_three]
  rw [syracPMF_one_apply_zero, syracPMF_one_apply_one, syracPMF_one_apply_two]
  rw [map_syracStep_one_one_apply_two, map_syracStep_one_two_apply_two]
  simp
  apply (ENNReal.toReal_eq_toReal_iff' ?_ ENNReal.ofReal_ne_top).mp
  · rw [ENNReal.toReal_add]
    · rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
      rw [ENNReal.toReal_ofReal, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
      norm_num
      all_goals norm_num
    · exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩

theorem syracPMF_two_apply_four :
    syracPMF 2 (4 : ZMod (3 ^ 2)) = ENNReal.ofReal (11 / 63 : ℝ) := by
  change syracPMF (1 + 1) (4 : ZMod (3 ^ (1 + 1))) =
    ENNReal.ofReal (11 / 63 : ℝ)
  rw [syracPMF, PMF.bind_apply]
  rw [zmod3_tsum_eq_sum_three]
  rw [syracPMF_one_apply_zero, syracPMF_one_apply_one, syracPMF_one_apply_two]
  rw [map_syracStep_one_one_apply_four, map_syracStep_one_two_apply_four]
  simp
  rw [ennreal_inv_nat63_eq]
  exact weighted_geom_sum_eq_ofReal (1 / 63) (16 / 63) (11 / 63)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem syracPMF_two_apply_five :
    syracPMF 2 (5 : ZMod (3 ^ 2)) = ENNReal.ofReal (4 / 63 : ℝ) := by
  change syracPMF (1 + 1) (5 : ZMod (3 ^ (1 + 1))) =
    ENNReal.ofReal (4 / 63 : ℝ)
  rw [syracPMF, PMF.bind_apply]
  rw [zmod3_tsum_eq_sum_three]
  rw [syracPMF_one_apply_zero, syracPMF_one_apply_one, syracPMF_one_apply_two]
  rw [map_syracStep_one_one_apply_five, map_syracStep_one_two_apply_five]
  simp
  exact weighted_geom_sum_eq_ofReal (8 / 63) (2 / 63) (4 / 63)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem syracPMF_two_apply_seven :
    syracPMF 2 (7 : ZMod (3 ^ 2)) = ENNReal.ofReal (2 / 63 : ℝ) := by
  change syracPMF (1 + 1) (7 : ZMod (3 ^ (1 + 1))) =
    ENNReal.ofReal (2 / 63 : ℝ)
  rw [syracPMF, PMF.bind_apply]
  rw [zmod3_tsum_eq_sum_three]
  rw [syracPMF_one_apply_zero, syracPMF_one_apply_one, syracPMF_one_apply_two]
  rw [map_syracStep_one_one_apply_seven, map_syracStep_one_two_apply_seven]
  simp
  rw [ennreal_inv_nat63_eq]
  exact weighted_geom_sum_eq_ofReal (4 / 63) (1 / 63) (2 / 63)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem syracPMF_two_apply_eight :
    syracPMF 2 (8 : ZMod (3 ^ 2)) = ENNReal.ofReal (22 / 63 : ℝ) := by
  change syracPMF (1 + 1) (8 : ZMod (3 ^ (1 + 1))) =
    ENNReal.ofReal (22 / 63 : ℝ)
  rw [syracPMF, PMF.bind_apply]
  rw [zmod3_tsum_eq_sum_three]
  rw [syracPMF_one_apply_zero, syracPMF_one_apply_one, syracPMF_one_apply_two]
  rw [map_syracStep_one_one_apply_eight, map_syracStep_one_two_apply_eight]
  simp
  exact weighted_geom_sum_eq_ofReal (2 / 63) (32 / 63) (22 / 63)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem syracPMF_two_apply (x : ZMod (3 ^ 2)) :
    syracPMF 2 x =
      if x = 0 then 0
      else if x = 1 then ENNReal.ofReal (8 / 63 : ℝ)
      else if x = 2 then ENNReal.ofReal (16 / 63 : ℝ)
      else if x = 3 then 0
      else if x = 4 then ENNReal.ofReal (11 / 63 : ℝ)
      else if x = 5 then ENNReal.ofReal (4 / 63 : ℝ)
      else if x = 6 then 0
      else if x = 7 then ENNReal.ofReal (2 / 63 : ℝ)
      else ENNReal.ofReal (22 / 63 : ℝ) := by
  fin_cases x
  · change syracPMF 2 (0 : ZMod (3 ^ 2)) =
      if (0 : ZMod (3 ^ 2)) = 0 then 0
      else if (0 : ZMod (3 ^ 2)) = 1 then ENNReal.ofReal (8 / 63 : ℝ)
      else if (0 : ZMod (3 ^ 2)) = 2 then ENNReal.ofReal (16 / 63 : ℝ)
      else if (0 : ZMod (3 ^ 2)) = 3 then 0
      else if (0 : ZMod (3 ^ 2)) = 4 then ENNReal.ofReal (11 / 63 : ℝ)
      else if (0 : ZMod (3 ^ 2)) = 5 then ENNReal.ofReal (4 / 63 : ℝ)
      else if (0 : ZMod (3 ^ 2)) = 6 then 0
      else if (0 : ZMod (3 ^ 2)) = 7 then ENNReal.ofReal (2 / 63 : ℝ)
      else ENNReal.ofReal (22 / 63 : ℝ)
    rw [syracPMF_two_apply_zero]
    rw [if_pos rfl]
  · change syracPMF 2 (1 : ZMod (3 ^ 2)) =
      if (1 : ZMod (3 ^ 2)) = 0 then 0
      else if (1 : ZMod (3 ^ 2)) = 1 then ENNReal.ofReal (8 / 63 : ℝ)
      else if (1 : ZMod (3 ^ 2)) = 2 then ENNReal.ofReal (16 / 63 : ℝ)
      else if (1 : ZMod (3 ^ 2)) = 3 then 0
      else if (1 : ZMod (3 ^ 2)) = 4 then ENNReal.ofReal (11 / 63 : ℝ)
      else if (1 : ZMod (3 ^ 2)) = 5 then ENNReal.ofReal (4 / 63 : ℝ)
      else if (1 : ZMod (3 ^ 2)) = 6 then 0
      else if (1 : ZMod (3 ^ 2)) = 7 then ENNReal.ofReal (2 / 63 : ℝ)
      else ENNReal.ofReal (22 / 63 : ℝ)
    rw [syracPMF_two_apply_one]
    rw [if_neg (by decide : ¬((1 : ZMod (3 ^ 2)) = 0))]
    rw [if_pos rfl]
  · change syracPMF 2 (2 : ZMod (3 ^ 2)) =
      if (2 : ZMod (3 ^ 2)) = 0 then 0
      else if (2 : ZMod (3 ^ 2)) = 1 then ENNReal.ofReal (8 / 63 : ℝ)
      else if (2 : ZMod (3 ^ 2)) = 2 then ENNReal.ofReal (16 / 63 : ℝ)
      else if (2 : ZMod (3 ^ 2)) = 3 then 0
      else if (2 : ZMod (3 ^ 2)) = 4 then ENNReal.ofReal (11 / 63 : ℝ)
      else if (2 : ZMod (3 ^ 2)) = 5 then ENNReal.ofReal (4 / 63 : ℝ)
      else if (2 : ZMod (3 ^ 2)) = 6 then 0
      else if (2 : ZMod (3 ^ 2)) = 7 then ENNReal.ofReal (2 / 63 : ℝ)
      else ENNReal.ofReal (22 / 63 : ℝ)
    rw [syracPMF_two_apply_two]
    rw [if_neg (by decide : ¬((2 : ZMod (3 ^ 2)) = 0))]
    rw [if_neg (by decide : ¬((2 : ZMod (3 ^ 2)) = 1))]
    rw [if_pos rfl]
  · change syracPMF 2 (3 : ZMod (3 ^ 2)) =
      if (3 : ZMod (3 ^ 2)) = 0 then 0
      else if (3 : ZMod (3 ^ 2)) = 1 then ENNReal.ofReal (8 / 63 : ℝ)
      else if (3 : ZMod (3 ^ 2)) = 2 then ENNReal.ofReal (16 / 63 : ℝ)
      else if (3 : ZMod (3 ^ 2)) = 3 then 0
      else if (3 : ZMod (3 ^ 2)) = 4 then ENNReal.ofReal (11 / 63 : ℝ)
      else if (3 : ZMod (3 ^ 2)) = 5 then ENNReal.ofReal (4 / 63 : ℝ)
      else if (3 : ZMod (3 ^ 2)) = 6 then 0
      else if (3 : ZMod (3 ^ 2)) = 7 then ENNReal.ofReal (2 / 63 : ℝ)
      else ENNReal.ofReal (22 / 63 : ℝ)
    rw [syracPMF_two_apply_three]
    rw [if_neg (by decide : ¬((3 : ZMod (3 ^ 2)) = 0))]
    rw [if_neg (by decide : ¬((3 : ZMod (3 ^ 2)) = 1))]
    rw [if_neg (by decide : ¬((3 : ZMod (3 ^ 2)) = 2))]
    rw [if_pos rfl]
  · change syracPMF 2 (4 : ZMod (3 ^ 2)) =
      if (4 : ZMod (3 ^ 2)) = 0 then 0
      else if (4 : ZMod (3 ^ 2)) = 1 then ENNReal.ofReal (8 / 63 : ℝ)
      else if (4 : ZMod (3 ^ 2)) = 2 then ENNReal.ofReal (16 / 63 : ℝ)
      else if (4 : ZMod (3 ^ 2)) = 3 then 0
      else if (4 : ZMod (3 ^ 2)) = 4 then ENNReal.ofReal (11 / 63 : ℝ)
      else if (4 : ZMod (3 ^ 2)) = 5 then ENNReal.ofReal (4 / 63 : ℝ)
      else if (4 : ZMod (3 ^ 2)) = 6 then 0
      else if (4 : ZMod (3 ^ 2)) = 7 then ENNReal.ofReal (2 / 63 : ℝ)
      else ENNReal.ofReal (22 / 63 : ℝ)
    rw [syracPMF_two_apply_four]
    rw [if_neg (by decide : ¬((4 : ZMod (3 ^ 2)) = 0))]
    rw [if_neg (by decide : ¬((4 : ZMod (3 ^ 2)) = 1))]
    rw [if_neg (by decide : ¬((4 : ZMod (3 ^ 2)) = 2))]
    rw [if_neg (by decide : ¬((4 : ZMod (3 ^ 2)) = 3))]
    rw [if_pos rfl]
  · change syracPMF 2 (5 : ZMod (3 ^ 2)) =
      if (5 : ZMod (3 ^ 2)) = 0 then 0
      else if (5 : ZMod (3 ^ 2)) = 1 then ENNReal.ofReal (8 / 63 : ℝ)
      else if (5 : ZMod (3 ^ 2)) = 2 then ENNReal.ofReal (16 / 63 : ℝ)
      else if (5 : ZMod (3 ^ 2)) = 3 then 0
      else if (5 : ZMod (3 ^ 2)) = 4 then ENNReal.ofReal (11 / 63 : ℝ)
      else if (5 : ZMod (3 ^ 2)) = 5 then ENNReal.ofReal (4 / 63 : ℝ)
      else if (5 : ZMod (3 ^ 2)) = 6 then 0
      else if (5 : ZMod (3 ^ 2)) = 7 then ENNReal.ofReal (2 / 63 : ℝ)
      else ENNReal.ofReal (22 / 63 : ℝ)
    rw [syracPMF_two_apply_five]
    rw [if_neg (by decide : ¬((5 : ZMod (3 ^ 2)) = 0))]
    rw [if_neg (by decide : ¬((5 : ZMod (3 ^ 2)) = 1))]
    rw [if_neg (by decide : ¬((5 : ZMod (3 ^ 2)) = 2))]
    rw [if_neg (by decide : ¬((5 : ZMod (3 ^ 2)) = 3))]
    rw [if_neg (by decide : ¬((5 : ZMod (3 ^ 2)) = 4))]
    rw [if_pos rfl]
  · change syracPMF 2 (6 : ZMod (3 ^ 2)) =
      if (6 : ZMod (3 ^ 2)) = 0 then 0
      else if (6 : ZMod (3 ^ 2)) = 1 then ENNReal.ofReal (8 / 63 : ℝ)
      else if (6 : ZMod (3 ^ 2)) = 2 then ENNReal.ofReal (16 / 63 : ℝ)
      else if (6 : ZMod (3 ^ 2)) = 3 then 0
      else if (6 : ZMod (3 ^ 2)) = 4 then ENNReal.ofReal (11 / 63 : ℝ)
      else if (6 : ZMod (3 ^ 2)) = 5 then ENNReal.ofReal (4 / 63 : ℝ)
      else if (6 : ZMod (3 ^ 2)) = 6 then 0
      else if (6 : ZMod (3 ^ 2)) = 7 then ENNReal.ofReal (2 / 63 : ℝ)
      else ENNReal.ofReal (22 / 63 : ℝ)
    rw [syracPMF_two_apply_six]
    rw [if_neg (by decide : ¬((6 : ZMod (3 ^ 2)) = 0))]
    rw [if_neg (by decide : ¬((6 : ZMod (3 ^ 2)) = 1))]
    rw [if_neg (by decide : ¬((6 : ZMod (3 ^ 2)) = 2))]
    rw [if_neg (by decide : ¬((6 : ZMod (3 ^ 2)) = 3))]
    rw [if_neg (by decide : ¬((6 : ZMod (3 ^ 2)) = 4))]
    rw [if_neg (by decide : ¬((6 : ZMod (3 ^ 2)) = 5))]
    rw [if_pos rfl]
  · change syracPMF 2 (7 : ZMod (3 ^ 2)) =
      if (7 : ZMod (3 ^ 2)) = 0 then 0
      else if (7 : ZMod (3 ^ 2)) = 1 then ENNReal.ofReal (8 / 63 : ℝ)
      else if (7 : ZMod (3 ^ 2)) = 2 then ENNReal.ofReal (16 / 63 : ℝ)
      else if (7 : ZMod (3 ^ 2)) = 3 then 0
      else if (7 : ZMod (3 ^ 2)) = 4 then ENNReal.ofReal (11 / 63 : ℝ)
      else if (7 : ZMod (3 ^ 2)) = 5 then ENNReal.ofReal (4 / 63 : ℝ)
      else if (7 : ZMod (3 ^ 2)) = 6 then 0
      else if (7 : ZMod (3 ^ 2)) = 7 then ENNReal.ofReal (2 / 63 : ℝ)
      else ENNReal.ofReal (22 / 63 : ℝ)
    rw [syracPMF_two_apply_seven]
    rw [if_neg (by decide : ¬((7 : ZMod (3 ^ 2)) = 0))]
    rw [if_neg (by decide : ¬((7 : ZMod (3 ^ 2)) = 1))]
    rw [if_neg (by decide : ¬((7 : ZMod (3 ^ 2)) = 2))]
    rw [if_neg (by decide : ¬((7 : ZMod (3 ^ 2)) = 3))]
    rw [if_neg (by decide : ¬((7 : ZMod (3 ^ 2)) = 4))]
    rw [if_neg (by decide : ¬((7 : ZMod (3 ^ 2)) = 5))]
    rw [if_neg (by decide : ¬((7 : ZMod (3 ^ 2)) = 6))]
    rw [if_pos rfl]
  · change syracPMF 2 (8 : ZMod (3 ^ 2)) =
      if (8 : ZMod (3 ^ 2)) = 0 then 0
      else if (8 : ZMod (3 ^ 2)) = 1 then ENNReal.ofReal (8 / 63 : ℝ)
      else if (8 : ZMod (3 ^ 2)) = 2 then ENNReal.ofReal (16 / 63 : ℝ)
      else if (8 : ZMod (3 ^ 2)) = 3 then 0
      else if (8 : ZMod (3 ^ 2)) = 4 then ENNReal.ofReal (11 / 63 : ℝ)
      else if (8 : ZMod (3 ^ 2)) = 5 then ENNReal.ofReal (4 / 63 : ℝ)
      else if (8 : ZMod (3 ^ 2)) = 6 then 0
      else if (8 : ZMod (3 ^ 2)) = 7 then ENNReal.ofReal (2 / 63 : ℝ)
      else ENNReal.ofReal (22 / 63 : ℝ)
    rw [syracPMF_two_apply_eight]
    rw [if_neg (by decide : ¬((8 : ZMod (3 ^ 2)) = 0))]
    rw [if_neg (by decide : ¬((8 : ZMod (3 ^ 2)) = 1))]
    rw [if_neg (by decide : ¬((8 : ZMod (3 ^ 2)) = 2))]
    rw [if_neg (by decide : ¬((8 : ZMod (3 ^ 2)) = 3))]
    rw [if_neg (by decide : ¬((8 : ZMod (3 ^ 2)) = 4))]
    rw [if_neg (by decide : ¬((8 : ZMod (3 ^ 2)) = 5))]
    rw [if_neg (by decide : ¬((8 : ZMod (3 ^ 2)) = 6))]
    rw [if_neg (by decide : ¬((8 : ZMod (3 ^ 2)) = 7))]

end Tao
end Erdos1135SecondScale
