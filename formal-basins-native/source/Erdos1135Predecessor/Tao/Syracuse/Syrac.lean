/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Syracuse.ValuationDistribution
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases

namespace Erdos1135Predecessor

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

end Tao

end Erdos1135Predecessor
