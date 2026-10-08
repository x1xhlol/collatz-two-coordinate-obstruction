/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma77PascalFormula
import Mathlib.Data.Nat.Choose.Central

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Lemma77

def lemma77FairBinomialMass (N k : ℕ) : ℝ :=
  (Nat.choose N k : ℝ) * (1 / 2 : ℝ) ^ N

def lemma77CentralFairBinomialMass (m : ℕ) : ℝ :=
  lemma77FairBinomialMass (2 * m) m

theorem lemma77FairBinomialMass_nonneg (N k : ℕ) :
    0 ≤ lemma77FairBinomialMass N k := by
  unfold lemma77FairBinomialMass
  positivity

theorem lemma77FairBinomialMass_succ_right (N k : ℕ) :
    lemma77FairBinomialMass N (k + 1) =
      ((N - k : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
        lemma77FairBinomialMass N k := by
  have h := congrArg (fun x : ℕ => (x : ℝ))
    (Nat.choose_succ_right_eq N k)
  push_cast at h
  simp only [lemma77FairBinomialMass]
  field_simp
  simpa [Nat.cast_add, mul_comm] using h

theorem lemma77CentralFairBinomialMass_nonneg (m : ℕ) :
    0 ≤ lemma77CentralFairBinomialMass m := by
  exact lemma77FairBinomialMass_nonneg _ _

theorem lemma77CentralFairBinomialMass_succ (m : ℕ) :
    lemma77CentralFairBinomialMass (m + 1) =
      ((2 * m + 1 : ℕ) : ℝ) / ((2 * m + 2 : ℕ) : ℝ) *
        lemma77CentralFairBinomialMass m := by
  have h := congrArg (fun x : ℕ => (x : ℝ))
    (Nat.succ_mul_centralBinom_succ m)
  push_cast at h
  simp only [Nat.centralBinom] at h
  have htwo : 2 * (m + 1) = 2 * m + 2 := by omega
  rw [htwo] at h
  unfold lemma77CentralFairBinomialMass lemma77FairBinomialMass
  push_cast
  rw [htwo, pow_add]
  norm_num
  field_simp
  nlinarith

theorem lemma77CentralFairBinomialMass_square_bound (m : ℕ) :
    (((2 * m + 1 : ℕ) : ℝ) *
      lemma77CentralFairBinomialMass m ^ 2) ≤ 1 := by
  induction m with
  | zero =>
      norm_num [lemma77CentralFairBinomialMass, lemma77FairBinomialMass]
  | succ m ih =>
      rw [show m + 1 = m + 1 by rfl,
        lemma77CentralFairBinomialMass_succ]
      push_cast
      have hden : 0 < (2 : ℝ) * m + 2 := by positivity
      have hden_sq : 0 < ((2 : ℝ) * m + 2) ^ 2 := sq_pos_of_pos hden
      have hfrac :
          ((2 : ℝ) * m + 3) *
              (((2 : ℝ) * m + 1) / ((2 : ℝ) * m + 2)) ^ 2 ≤
            (2 : ℝ) * m + 1 := by
        rw [div_pow, ← mul_div_assoc]
        apply (div_le_iff₀ hden_sq).2
        nlinarith
      calc
        ((2 : ℝ) * (m + 1) + 1) *
              ((((2 : ℝ) * m + 1) / ((2 : ℝ) * m + 2)) *
                lemma77CentralFairBinomialMass m) ^ 2 =
            (((2 : ℝ) * m + 3) *
              (((2 : ℝ) * m + 1) / ((2 : ℝ) * m + 2)) ^ 2) *
                lemma77CentralFairBinomialMass m ^ 2 := by ring
        _ ≤ ((2 : ℝ) * m + 1) *
              lemma77CentralFairBinomialMass m ^ 2 := by
          gcongr
        _ ≤ 1 := by simpa using ih

theorem lemma77CentralFairBinomialMass_le_rpow (m : ℕ) :
    lemma77CentralFairBinomialMass m ≤
      (((2 * m + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
  let A : ℝ := ((2 * m + 1 : ℕ) : ℝ)
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hsqrtpos : 0 < Real.sqrt A := Real.sqrt_pos.2 hApos
  have hsq :
      (lemma77CentralFairBinomialMass m * Real.sqrt A) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt hApos.le]
    simpa [A, mul_comm] using
      lemma77CentralFairBinomialMass_square_bound m
  have hprod_nonneg :
      0 ≤ lemma77CentralFairBinomialMass m * Real.sqrt A :=
    mul_nonneg (lemma77CentralFairBinomialMass_nonneg m)
      (Real.sqrt_nonneg A)
  have hprod :
      lemma77CentralFairBinomialMass m * Real.sqrt A ≤ 1 := by
    nlinarith
  have hdiv :
      lemma77CentralFairBinomialMass m ≤ 1 / Real.sqrt A :=
    (le_div_iff₀ hsqrtpos).2 (by simpa [mul_comm] using hprod)
  rw [Real.rpow_neg hApos.le, ← Real.sqrt_eq_rpow]
  simpa [A, one_div] using hdiv

theorem lemma77FairBinomialMass_even_le_central (m k : ℕ) :
    lemma77FairBinomialMass (2 * m) k ≤
      lemma77CentralFairBinomialMass m := by
  simp only [lemma77CentralFairBinomialMass, lemma77FairBinomialMass]
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast Nat.choose_le_centralBinom k m
  · positivity

theorem lemma77FairBinomialMass_odd_mode (m : ℕ) :
    lemma77FairBinomialMass (2 * m + 1) (m + 1) =
      lemma77CentralFairBinomialMass (m + 1) := by
  have hchoose :
      Nat.choose (2 * m + 2) (m + 1) =
        2 * Nat.choose (2 * m + 1) (m + 1) := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega,
      Nat.choose_succ_succ']
    rw [← Nat.choose_symm_half m]
    omega
  have h := congrArg (fun x : ℕ => (x : ℝ)) hchoose
  push_cast at h
  have htwo : 2 * (m + 1) = 2 * m + 2 := by omega
  have hpow :
      (1 / 2 : ℝ) ^ (2 * m + 2) =
        (1 / 2 : ℝ) ^ (2 * m + 1) * (1 / 2 : ℝ) := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, pow_succ]
  simp only [lemma77CentralFairBinomialMass, lemma77FairBinomialMass]
  rw [htwo, hpow, h]
  ring

theorem lemma77FairBinomialMass_odd_le_central (m k : ℕ) :
    lemma77FairBinomialMass (2 * m + 1) k ≤
      lemma77CentralFairBinomialMass (m + 1) := by
  calc
    lemma77FairBinomialMass (2 * m + 1) k ≤
        lemma77FairBinomialMass (2 * m + 1) m := by
      simp only [lemma77FairBinomialMass]
      apply mul_le_mul_of_nonneg_right
      · have h := Nat.choose_le_middle k (2 * m + 1)
        have hhalf : (2 * m + 1) / 2 = m := by omega
        simpa [hhalf] using h
      · positivity
    _ = lemma77FairBinomialMass (2 * m + 1) (m + 1) := by
      simp only [lemma77FairBinomialMass]
      rw [Nat.choose_symm_half]
    _ = lemma77CentralFairBinomialMass (m + 1) :=
      lemma77FairBinomialMass_odd_mode m

theorem lemma77FairBinomialMass_le_rpow (N k : ℕ) :
    lemma77FairBinomialMass N k ≤
      (((N + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
  rcases Nat.even_or_odd' N with ⟨m, hN | hN⟩
  · subst N
    exact (lemma77FairBinomialMass_even_le_central m k).trans
      (lemma77CentralFairBinomialMass_le_rpow m)
  · subst N
    calc
      lemma77FairBinomialMass (2 * m + 1) k ≤
          lemma77CentralFairBinomialMass (m + 1) :=
        lemma77FairBinomialMass_odd_le_central m k
      _ ≤ (((2 * (m + 1) + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) :=
        lemma77CentralFairBinomialMass_le_rpow (m + 1)
      _ ≤ (((2 * m + 1 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
        apply Real.rpow_le_rpow_of_nonpos
        · positivity
        · exact_mod_cast (show 2 * m + 1 + 1 ≤ 2 * (m + 1) + 1 by omega)
        · norm_num

theorem lemma77FairBinomialMass_even_step_factor_le_exp
    (m r : ℕ) (hm : 0 < m) (hr : r < m) :
    ((m - r : ℕ) : ℝ) / ((m + r + 1 : ℕ) : ℝ) ≤
      Real.exp
        (-(((2 * r + 1 : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ))) := by
  have hratio :
      ((m - r : ℕ) : ℝ) / ((m + r + 1 : ℕ) : ℝ) =
        1 - (((2 * r + 1 : ℕ) : ℝ) /
          ((m + r + 1 : ℕ) : ℝ)) := by
    rw [Nat.cast_sub (by omega : r ≤ m)]
    push_cast
    field_simp
    ring
  rw [hratio]
  calc
    1 - (((2 * r + 1 : ℕ) : ℝ) /
          ((m + r + 1 : ℕ) : ℝ)) ≤
        Real.exp
          (-(((2 * r + 1 : ℕ) : ℝ) /
            ((m + r + 1 : ℕ) : ℝ))) :=
      Real.one_sub_le_exp_neg _
    _ ≤ Real.exp
        (-(((2 * r + 1 : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ))) := by
      apply Real.exp_monotone
      have hnum : 0 ≤ ((2 * r + 1 : ℕ) : ℝ) := by positivity
      have hden_le :
          ((m + r + 1 : ℕ) : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
        exact_mod_cast (show m + r + 1 ≤ 2 * m by omega)
      have hdiv := div_le_div_of_nonneg_left hnum (by positivity) hden_le
      linarith

theorem lemma77FairBinomialMass_odd_step_factor_le_exp
    (m r : ℕ) (hr : r < m) :
    ((m - r : ℕ) : ℝ) / ((m + r + 2 : ℕ) : ℝ) ≤
      Real.exp
        (-(((2 * r + 2 : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ))) := by
  have hratio :
      ((m - r : ℕ) : ℝ) / ((m + r + 2 : ℕ) : ℝ) =
        1 - (((2 * r + 2 : ℕ) : ℝ) /
          ((m + r + 2 : ℕ) : ℝ)) := by
    rw [Nat.cast_sub (by omega : r ≤ m)]
    push_cast
    field_simp
    ring
  rw [hratio]
  calc
    1 - (((2 * r + 2 : ℕ) : ℝ) /
          ((m + r + 2 : ℕ) : ℝ)) ≤
        Real.exp
          (-(((2 * r + 2 : ℕ) : ℝ) /
            ((m + r + 2 : ℕ) : ℝ))) :=
      Real.one_sub_le_exp_neg _
    _ ≤ Real.exp
        (-(((2 * r + 2 : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ))) := by
      apply Real.exp_monotone
      have hnum : 0 ≤ ((2 * r + 2 : ℕ) : ℝ) := by positivity
      have hden_le :
          ((m + r + 2 : ℕ) : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show m + r + 2 ≤ 2 * m + 1 by omega)
      have hdiv := div_le_div_of_nonneg_left hnum (by positivity) hden_le
      linarith

theorem lemma77FairBinomialMass_even_right_tail
    (m r : ℕ) (hm : 0 < m) (hr : r ≤ m) :
    lemma77FairBinomialMass (2 * m) (m + r) ≤
      lemma77CentralFairBinomialMass m *
        Real.exp (-((r : ℝ) ^ 2 / ((2 * m : ℕ) : ℝ))) := by
  induction r with
  | zero =>
      simp [lemma77CentralFairBinomialMass]
  | succ r ih =>
      have hrm : r < m := by omega
      have hsub : 2 * m - (m + r) = m - r := by omega
      have hindex : m + (r + 1) = (m + r) + 1 := by omega
      rw [hindex, lemma77FairBinomialMass_succ_right, hsub]
      have hstep :=
        lemma77FairBinomialMass_even_step_factor_le_exp m r hm hrm
      calc
        ((m - r : ℕ) : ℝ) / ((m + r + 1 : ℕ) : ℝ) *
              lemma77FairBinomialMass (2 * m) (m + r) ≤
            ((m - r : ℕ) : ℝ) / ((m + r + 1 : ℕ) : ℝ) *
              (lemma77CentralFairBinomialMass m *
                Real.exp (-((r : ℝ) ^ 2 / ((2 * m : ℕ) : ℝ)))) := by
          apply mul_le_mul_of_nonneg_left (ih (by omega))
          positivity
        _ ≤ Real.exp
              (-(((2 * r + 1 : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ))) *
              (lemma77CentralFairBinomialMass m *
                Real.exp (-((r : ℝ) ^ 2 / ((2 * m : ℕ) : ℝ)))) := by
          apply mul_le_mul_of_nonneg_right hstep
          exact mul_nonneg (lemma77CentralFairBinomialMass_nonneg m)
            (Real.exp_nonneg _)
        _ = lemma77CentralFairBinomialMass m *
              Real.exp
                (-(((r + 1 : ℕ) : ℝ) ^ 2 / ((2 * m : ℕ) : ℝ))) := by
          calc
            _ = lemma77CentralFairBinomialMass m *
                  (Real.exp
                    (-(((2 * r + 1 : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ))) *
                    Real.exp
                      (-((r : ℝ) ^ 2 / ((2 * m : ℕ) : ℝ)))) := by ring
            _ = lemma77CentralFairBinomialMass m *
                  Real.exp
                    (-(((r + 1 : ℕ) : ℝ) ^ 2 /
                      ((2 * m : ℕ) : ℝ))) := by
              rw [← Real.exp_add]
              congr 2
              field_simp
              push_cast
              ring

theorem lemma77FairBinomialMass_odd_right_tail
    (m r : ℕ) (hr : r ≤ m) :
    lemma77FairBinomialMass (2 * m + 1) (m + 1 + r) ≤
      lemma77CentralFairBinomialMass (m + 1) *
        Real.exp
          (-((r : ℝ) * ((r : ℝ) + 1) / ((2 * m + 1 : ℕ) : ℝ))) := by
  induction r with
  | zero =>
      simpa using (lemma77FairBinomialMass_odd_mode m).le
  | succ r ih =>
      have hrm : r < m := by omega
      have hsub : 2 * m + 1 - (m + 1 + r) = m - r := by omega
      have hindex : m + 1 + (r + 1) = (m + 1 + r) + 1 := by omega
      rw [hindex, lemma77FairBinomialMass_succ_right, hsub]
      have hstep := lemma77FairBinomialMass_odd_step_factor_le_exp m r hrm
      calc
        ((m - r : ℕ) : ℝ) / ((m + 1 + r + 1 : ℕ) : ℝ) *
              lemma77FairBinomialMass (2 * m + 1) (m + 1 + r) ≤
            ((m - r : ℕ) : ℝ) / ((m + r + 2 : ℕ) : ℝ) *
              (lemma77CentralFairBinomialMass (m + 1) *
                Real.exp
                  (-((r : ℝ) * ((r : ℝ) + 1) /
                    ((2 * m + 1 : ℕ) : ℝ)))) := by
          rw [show m + 1 + r + 1 = m + r + 2 by omega]
          apply mul_le_mul_of_nonneg_left (ih (by omega))
          positivity
        _ ≤ Real.exp
              (-(((2 * r + 2 : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ))) *
              (lemma77CentralFairBinomialMass (m + 1) *
                Real.exp
                  (-((r : ℝ) * ((r : ℝ) + 1) /
                    ((2 * m + 1 : ℕ) : ℝ)))) := by
          apply mul_le_mul_of_nonneg_right hstep
          exact mul_nonneg (lemma77CentralFairBinomialMass_nonneg (m + 1))
            (Real.exp_nonneg _)
        _ = lemma77CentralFairBinomialMass (m + 1) *
              Real.exp
                (-((((r + 1 : ℕ) : ℝ) * (((r + 1 : ℕ) : ℝ) + 1)) /
                  ((2 * m + 1 : ℕ) : ℝ))) := by
          calc
            _ = lemma77CentralFairBinomialMass (m + 1) *
                  (Real.exp
                    (-(((2 * r + 2 : ℕ) : ℝ) /
                      ((2 * m + 1 : ℕ) : ℝ))) *
                    Real.exp
                      (-((r : ℝ) * ((r : ℝ) + 1) /
                        ((2 * m + 1 : ℕ) : ℝ)))) := by ring
            _ = lemma77CentralFairBinomialMass (m + 1) *
                  Real.exp
                    (-((((r + 1 : ℕ) : ℝ) *
                        (((r + 1 : ℕ) : ℝ) + 1)) /
                      ((2 * m + 1 : ℕ) : ℝ))) := by
              rw [← Real.exp_add]
              congr 2
              field_simp
              push_cast
              ring

theorem lemma77FairBinomialMass_even_left_eq_right
    (m r : ℕ) (hr : r ≤ m) :
    lemma77FairBinomialMass (2 * m) (m - r) =
      lemma77FairBinomialMass (2 * m) (m + r) := by
  simp only [lemma77FairBinomialMass]
  rw [Nat.choose_symm_of_eq_add
    (show 2 * m = (m - r) + (m + r) by omega)]

theorem lemma77FairBinomialMass_even_left_tail
    (m r : ℕ) (hm : 0 < m) (hr : r ≤ m) :
    lemma77FairBinomialMass (2 * m) (m - r) ≤
      lemma77CentralFairBinomialMass m *
        Real.exp (-((r : ℝ) ^ 2 / ((2 * m : ℕ) : ℝ))) := by
  rw [lemma77FairBinomialMass_even_left_eq_right m r hr]
  exact lemma77FairBinomialMass_even_right_tail m r hm hr

theorem lemma77FairBinomialMass_odd_left_eq_right
    (m r : ℕ) (hr : r ≤ m) :
    lemma77FairBinomialMass (2 * m + 1) (m - r) =
      lemma77FairBinomialMass (2 * m + 1) (m + 1 + r) := by
  simp only [lemma77FairBinomialMass]
  rw [Nat.choose_symm_of_eq_add
    (show 2 * m + 1 = (m - r) + (m + 1 + r) by omega)]

theorem lemma77FairBinomialMass_odd_left_tail
    (m r : ℕ) (hr : r ≤ m) :
    lemma77FairBinomialMass (2 * m + 1) (m - r) ≤
      lemma77CentralFairBinomialMass (m + 1) *
        Real.exp
          (-((r : ℝ) * ((r : ℝ) + 1) / ((2 * m + 1 : ℕ) : ℝ))) := by
  rw [lemma77FairBinomialMass_odd_left_eq_right m r hr]
  exact lemma77FairBinomialMass_odd_right_tail m r hr

theorem lemma77FairBinomialMass_even_centered_gaussian
    (m k : ℕ) (hm : 0 < m) (hk : k ≤ 2 * m) :
    lemma77FairBinomialMass (2 * m) k ≤
      (((2 * m + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
        Real.exp
          (1 / (4 * ((2 * m : ℕ) : ℝ)) -
            (((k : ℝ) - ((2 * m : ℕ) : ℝ) / 2) ^ 2 /
              ((2 * m : ℕ) : ℝ))) := by
  rcases le_total k m with hkm | hmk
  · let r := m - k
    have hrm : r ≤ m := by
      dsimp [r]
      omega
    have hkindex : m - r = k := by
      dsimp [r]
      omega
    have hcenter :
        ((k : ℝ) - ((2 * m : ℕ) : ℝ) / 2) ^ 2 = (r : ℝ) ^ 2 := by
      dsimp [r]
      rw [Nat.cast_sub hkm]
      push_cast
      ring
    calc
      lemma77FairBinomialMass (2 * m) k =
          lemma77FairBinomialMass (2 * m) (m - r) := by rw [hkindex]
      _ ≤ lemma77CentralFairBinomialMass m *
            Real.exp (-((r : ℝ) ^ 2 / ((2 * m : ℕ) : ℝ))) :=
        lemma77FairBinomialMass_even_left_tail m r hm hrm
      _ ≤ (((2 * m + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
            Real.exp (-((r : ℝ) ^ 2 / ((2 * m : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right
          (lemma77CentralFairBinomialMass_le_rpow m) (Real.exp_nonneg _)
      _ ≤ (((2 * m + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
            Real.exp
              (1 / (4 * ((2 * m : ℕ) : ℝ)) -
                (((k : ℝ) - ((2 * m : ℕ) : ℝ) / 2) ^ 2 /
                  ((2 * m : ℕ) : ℝ))) := by
        apply mul_le_mul_of_nonneg_left
        · apply Real.exp_monotone
          rw [hcenter]
          have hcorr :
              0 ≤ (1 / (4 * ((2 * m : ℕ) : ℝ)) : ℝ) := by positivity
          linarith
        · positivity
  · let r := k - m
    have hrm : r ≤ m := by
      dsimp [r]
      omega
    have hkindex : m + r = k := by
      dsimp [r]
      omega
    have hcenter :
        ((k : ℝ) - ((2 * m : ℕ) : ℝ) / 2) ^ 2 = (r : ℝ) ^ 2 := by
      dsimp [r]
      rw [Nat.cast_sub hmk]
      push_cast
      ring
    calc
      lemma77FairBinomialMass (2 * m) k =
          lemma77FairBinomialMass (2 * m) (m + r) := by rw [hkindex]
      _ ≤ lemma77CentralFairBinomialMass m *
            Real.exp (-((r : ℝ) ^ 2 / ((2 * m : ℕ) : ℝ))) :=
        lemma77FairBinomialMass_even_right_tail m r hm hrm
      _ ≤ (((2 * m + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
            Real.exp (-((r : ℝ) ^ 2 / ((2 * m : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right
          (lemma77CentralFairBinomialMass_le_rpow m) (Real.exp_nonneg _)
      _ ≤ (((2 * m + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
            Real.exp
              (1 / (4 * ((2 * m : ℕ) : ℝ)) -
                (((k : ℝ) - ((2 * m : ℕ) : ℝ) / 2) ^ 2 /
                  ((2 * m : ℕ) : ℝ))) := by
        apply mul_le_mul_of_nonneg_left
        · apply Real.exp_monotone
          rw [hcenter]
          have hcorr :
              0 ≤ (1 / (4 * ((2 * m : ℕ) : ℝ)) : ℝ) := by positivity
          linarith
        · positivity

theorem lemma77FairBinomialMass_odd_centered_gaussian
    (m k : ℕ) (hk : k ≤ 2 * m + 1) :
    lemma77FairBinomialMass (2 * m + 1) k ≤
      (((2 * m + 1 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
        Real.exp
          (1 / (4 * ((2 * m + 1 : ℕ) : ℝ)) -
            (((k : ℝ) - ((2 * m + 1 : ℕ) : ℝ) / 2) ^ 2 /
              ((2 * m + 1 : ℕ) : ℝ))) := by
  have hmode :
      lemma77CentralFairBinomialMass (m + 1) ≤
        (((2 * m + 1 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
    rw [← lemma77FairBinomialMass_odd_mode m]
    exact lemma77FairBinomialMass_le_rpow (2 * m + 1) (m + 1)
  by_cases hleft : k ≤ m
  · have htail := lemma77FairBinomialMass_odd_left_tail m (m - k) (by omega)
    rw [show m - (m - k) = k by omega] at htail
    have hexp :
        -(((m - k : ℕ) : ℝ) * (((m - k : ℕ) : ℝ) + 1) /
            ((2 * m + 1 : ℕ) : ℝ)) =
          1 / (4 * ((2 * m + 1 : ℕ) : ℝ)) -
            (((k : ℝ) - ((2 * m + 1 : ℕ) : ℝ) / 2) ^ 2 /
              ((2 * m + 1 : ℕ) : ℝ)) := by
      rw [Nat.cast_sub hleft]
      push_cast
      field_simp
      ring
    exact htail.trans <| by
      calc
        _ ≤ (((2 * m + 1 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
              Real.exp
                (-(((m - k : ℕ) : ℝ) * (((m - k : ℕ) : ℝ) + 1) /
                  ((2 * m + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right hmode (Real.exp_nonneg _)
        _ = _ := by rw [hexp]
  · have hright : m + 1 ≤ k := by omega
    have htail :=
      lemma77FairBinomialMass_odd_right_tail m (k - (m + 1)) (by omega)
    rw [show m + 1 + (k - (m + 1)) = k by omega] at htail
    have hexp :
        -(((k - (m + 1) : ℕ) : ℝ) *
            (((k - (m + 1) : ℕ) : ℝ) + 1) /
            ((2 * m + 1 : ℕ) : ℝ)) =
          1 / (4 * ((2 * m + 1 : ℕ) : ℝ)) -
            (((k : ℝ) - ((2 * m + 1 : ℕ) : ℝ) / 2) ^ 2 /
              ((2 * m + 1 : ℕ) : ℝ)) := by
      rw [Nat.cast_sub hright]
      push_cast
      field_simp
      ring
    exact htail.trans <| by
      calc
        _ ≤ (((2 * m + 1 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
              Real.exp
                (-(((k - (m + 1) : ℕ) : ℝ) *
                  (((k - (m + 1) : ℕ) : ℝ) + 1) /
                  ((2 * m + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right hmode (Real.exp_nonneg _)
        _ = _ := by rw [hexp]

theorem lemma77FairBinomialMass_centered_gaussian
    (N k : ℕ) (hN : 0 < N) (hk : k ≤ N) :
    lemma77FairBinomialMass N k ≤
      (((N + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
        Real.exp
          (1 / (4 * (N : ℝ)) -
            (((k : ℝ) - (N : ℝ) / 2) ^ 2 / (N : ℝ))) := by
  rcases Nat.even_or_odd' N with ⟨m, hN | hN⟩
  · subst N
    exact lemma77FairBinomialMass_even_centered_gaussian m k (by omega) hk
  · subst N
    exact lemma77FairBinomialMass_odd_centered_gaussian m k hk

theorem lemma77HeightPotentialMass_eq_eighth_fairBinomialMass_of_support
    (start : TaoSection7RenewalPoint) {j s : ℕ}
    (hj : 2 ≤ j) (hs : 2 * j + 1 ≤ s) :
    lemma77HeightPotentialMass start (j : ℤ) s =
      (1 / 8 : ℝ) * lemma77FairBinomialMass (s - 4) (2 * j - 3) := by
  rw [lemma77HeightPotentialMass_eq_choose_of_support start hj hs]
  simp only [lemma77FairBinomialMass]
  have hexp : s - 1 = (s - 4) + 3 := by omega
  rw [hexp, pow_add]
  norm_num
  ring

theorem lemma77Pascal_prefactor_shift (N : ℕ) (hN : 0 < N) :
    (((N + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      2 * (((N + 5 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
  let A : ℝ := ((N + 1 : ℕ) : ℝ)
  let B : ℝ := ((N + 5 : ℕ) : ℝ)
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hsqrtA : 0 < Real.sqrt A := Real.sqrt_pos.2 hApos
  have hsqrtB : 0 < Real.sqrt B := Real.sqrt_pos.2 hBpos
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsq : Real.sqrt B ≤ 2 * Real.sqrt A := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt hApos.le]
      dsimp [A, B]
      push_cast
      nlinarith
  have hquot : Real.sqrt B / Real.sqrt A ≤ 2 :=
    (div_le_iff₀ hsqrtA).2 (by simpa [mul_comm] using hsq)
  rw [Real.rpow_neg hApos.le, ← Real.sqrt_eq_rpow,
    Real.rpow_neg hBpos.le, ← Real.sqrt_eq_rpow]
  apply (le_div_iff₀ hsqrtB).2
  simpa [div_eq_mul_inv, mul_comm] using hquot

theorem lemma77Pascal_exponent_transfer (N : ℕ) (hN : 0 < N) (x : ℝ) :
    1 / (4 * (N : ℝ)) - (2 * x - 1) ^ 2 / (N : ℝ) ≤
      1 / 3 - x ^ 2 / ((N + 5 : ℕ) : ℝ) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  let R : ℝ :=
    (7 * (N : ℝ) + 20) / (4 * (N : ℝ) * (3 * (N : ℝ) + 20))
  let C : ℝ :=
    (3 * (N : ℝ) + 20) / ((N : ℝ) * ((N + 5 : ℕ) : ℝ))
  let a : ℝ :=
    2 * ((N + 5 : ℕ) : ℝ) / (3 * (N : ℝ) + 20)
  have hid :
      1 / (4 * (N : ℝ)) - (2 * x - 1) ^ 2 / (N : ℝ) +
          x ^ 2 / ((N + 5 : ℕ) : ℝ) =
        R - C * (x - a) ^ 2 := by
    dsimp [R, C, a]
    push_cast
    field_simp
    ring
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hR : R ≤ 1 / 3 := by
    dsimp [R]
    apply (div_le_iff₀
      (by positivity : 0 < 4 * (N : ℝ) * (3 * (N : ℝ) + 20))).2
    nlinarith
  calc
    1 / (4 * (N : ℝ)) - (2 * x - 1) ^ 2 / (N : ℝ) =
        (1 / (4 * (N : ℝ)) - (2 * x - 1) ^ 2 / (N : ℝ) +
          x ^ 2 / ((N + 5 : ℕ) : ℝ)) -
            x ^ 2 / ((N + 5 : ℕ) : ℝ) := by ring
    _ = (R - C * (x - a) ^ 2) - x ^ 2 / ((N + 5 : ℕ) : ℝ) := by
      rw [hid]
    _ ≤ R - x ^ 2 / ((N + 5 : ℕ) : ℝ) :=
      sub_le_sub_right (sub_le_self R (mul_nonneg hC (sq_nonneg _))) _
    _ ≤ 1 / 3 - x ^ 2 / ((N + 5 : ℕ) : ℝ) :=
      sub_le_sub_right hR _

theorem lemma77_exp_one_third_le_three_halves :
    Real.exp (1 / 3 : ℝ) ≤ 3 / 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem lemma77HeightPotentialMass_le_three_eighths_gaussian_of_support
    (start : TaoSection7RenewalPoint) {j s : ℕ}
    (hj : 2 ≤ j) (hs : 2 * j + 1 ≤ s) :
    lemma77HeightPotentialMass start (j : ℤ) s ≤
      (3 / 8 : ℝ) * (((s + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
        Real.exp
          (-(((j : ℝ) - (s : ℝ) / 4) ^ 2 /
            ((s + 1 : ℕ) : ℝ))) := by
  let N := s - 4
  let k := 2 * j - 3
  let x : ℝ := (j : ℝ) - (s : ℝ) / 4
  have hN : 0 < N := by
    dsimp [N]
    omega
  have hk : k ≤ N := by
    dsimp [k, N]
    omega
  have hN5 : N + 5 = s + 1 := by
    dsimp [N]
    omega
  have hcenter : ((k : ℝ) - (N : ℝ) / 2) = 2 * x - 1 := by
    dsimp [k, N, x]
    rw [Nat.cast_sub (by omega : 3 ≤ 2 * j),
      Nat.cast_sub (by omega : 4 ≤ s)]
    push_cast
    ring
  let prefN : ℝ := (((N + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))
  let prefB : ℝ := (((N + 5 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))
  let expN : ℝ :=
    Real.exp
      (1 / (4 * (N : ℝ)) -
        (((k : ℝ) - (N : ℝ) / 2) ^ 2 / (N : ℝ)))
  let expB : ℝ := Real.exp (-(x ^ 2 / ((N + 5 : ℕ) : ℝ)))
  have hp : lemma77FairBinomialMass N k ≤ prefN * expN :=
    lemma77FairBinomialMass_centered_gaussian N k hN hk
  have hpre : prefN ≤ 2 * prefB := lemma77Pascal_prefactor_shift N hN
  have hE :
      1 / (4 * (N : ℝ)) -
          (((k : ℝ) - (N : ℝ) / 2) ^ 2 / (N : ℝ)) ≤
        1 / 3 - x ^ 2 / ((N + 5 : ℕ) : ℝ) := by
    rw [hcenter]
    exact lemma77Pascal_exponent_transfer N hN x
  have hExp : expN ≤ (3 / 2 : ℝ) * expB := by
    dsimp [expN, expB]
    calc
      Real.exp
          (1 / (4 * (N : ℝ)) -
            (((k : ℝ) - (N : ℝ) / 2) ^ 2 / (N : ℝ))) ≤
          Real.exp (1 / 3 - x ^ 2 / ((N + 5 : ℕ) : ℝ)) :=
        Real.exp_monotone hE
      _ = Real.exp (1 / 3) *
            Real.exp (-(x ^ 2 / ((N + 5 : ℕ) : ℝ))) := by
        rw [show (1 / 3 : ℝ) - x ^ 2 / ((N + 5 : ℕ) : ℝ) =
          1 / 3 + (-(x ^ 2 / ((N + 5 : ℕ) : ℝ))) by ring,
          Real.exp_add]
      _ ≤ (3 / 2 : ℝ) *
            Real.exp (-(x ^ 2 / ((N + 5 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right lemma77_exp_one_third_le_three_halves
          (Real.exp_nonneg _)
  rw [lemma77HeightPotentialMass_eq_eighth_fairBinomialMass_of_support
    start hj hs]
  change (1 / 8 : ℝ) * lemma77FairBinomialMass N k ≤ _
  calc
    (1 / 8 : ℝ) * lemma77FairBinomialMass N k ≤
        (1 / 8 : ℝ) * (prefN * expN) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ (1 / 8 : ℝ) * ((2 * prefB) * expN) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpre (by dsimp [expN]; positivity))
        (by norm_num)
    _ ≤ (1 / 8 : ℝ) * ((2 * prefB) * ((3 / 2 : ℝ) * expB)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hExp (by dsimp [prefB]; positivity))
        (by norm_num)
    _ = (3 / 8 : ℝ) * prefB * expB := by ring
    _ = (3 / 8 : ℝ) * (((s + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
          Real.exp
            (-(((j : ℝ) - (s : ℝ) / 4) ^ 2 /
              ((s + 1 : ℕ) : ℝ))) := by
      dsimp [prefB, expB, x]
      rw [hN5]

theorem lemma77ThreeEighthsGaussian_le_heightPotentialKernel_nat
    (j s : ℕ) :
    (3 / 8 : ℝ) * (((s + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
          Real.exp
            (-(((j : ℝ) - (s : ℝ) / 4) ^ 2 /
              ((s + 1 : ℕ) : ℝ))) ≤
      lemma77HeightPotentialKernel (1 / 2) 1 (j : ℤ) s := by
  let H : ℝ := (((s + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))
  let x : ℝ := (j : ℝ) - (s : ℝ) / 4
  let Q : ℝ := Real.exp (-(x ^ 2 / ((s + 1 : ℕ) : ℝ)))
  let L : ℝ := Real.exp (-|x|)
  have hH : 0 ≤ H := by
    dsimp [H]
    exact Real.rpow_nonneg (by positivity) _
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact Real.exp_nonneg _
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.exp_nonneg _
  change (3 / 8 : ℝ) * H * Q ≤ _
  calc
    (3 / 8 : ℝ) * H * Q ≤ (1 / 2 : ℝ) * H * Q :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (by norm_num : (3 / 8 : ℝ) ≤ 1 / 2) hH) hQ
    _ ≤ (1 / 2 : ℝ) * H * (Q + L) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hL)
        (mul_nonneg (by norm_num) hH)
    _ = lemma77HeightPotentialKernel (1 / 2) 1 (j : ℤ) s := by
      simp [lemma77HeightPotentialKernel, taoLemma22GaussianWeight,
        H, Q, L, x, Nat.cast_add, Nat.cast_one, add_comm]

theorem lemma77HeightPotentialMass_le_kernel_of_support
    (start : TaoSection7RenewalPoint) {j s : ℕ}
    (hj : 2 ≤ j) (hs : 2 * j + 1 ≤ s) :
    lemma77HeightPotentialMass start (j : ℤ) s ≤
      lemma77HeightPotentialKernel (1 / 2) 1 (j : ℤ) s :=
  (lemma77HeightPotentialMass_le_three_eighths_gaussian_of_support
      start hj hs).trans
    (lemma77ThreeEighthsGaussian_le_heightPotentialKernel_nat j s)

theorem lemma77HeightPotentialMass_one_three_le_kernel
    (start : TaoSection7RenewalPoint) :
    lemma77HeightPotentialMass start (1 : ℤ) 3 ≤
      lemma77HeightPotentialKernel (1 / 2) 1 (1 : ℤ) 3 := by
  have hpref : (4 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num : 0 ≤ (4 : ℝ)), ← Real.sqrt_eq_rpow]
    norm_num
  have hquad : (63 / 64 : ℝ) ≤ Real.exp (-(1 / 64 : ℝ)) := by
    have h := Real.one_sub_le_exp_neg (1 / 64 : ℝ)
    norm_num at h ⊢
    exact h
  have hlinear : (3 / 4 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ)) := by
    have h := Real.one_sub_le_exp_neg (1 / 4 : ℝ)
    norm_num at h ⊢
    exact h
  have hsum :
      (1 : ℝ) ≤
        Real.exp (-(1 / 64 : ℝ)) + Real.exp (-(1 / 4 : ℝ)) := by
    calc
      (1 : ℝ) ≤ 63 / 64 + 3 / 4 := by norm_num
      _ ≤ Real.exp (-(1 / 64 : ℝ)) + Real.exp (-(1 / 4 : ℝ)) :=
        add_le_add hquad hlinear
  have hkernel :
      lemma77HeightPotentialKernel (1 / 2) 1 (1 : ℤ) 3 =
        (1 / 4 : ℝ) *
          (Real.exp (-(1 / 64 : ℝ)) + Real.exp (-(1 / 4 : ℝ))) := by
    unfold lemma77HeightPotentialKernel taoLemma22GaussianWeight
    norm_num [hpref]
  rw [lemma77HeightPotentialMass_one_three]
  calc
    (1 / 4 : ℝ) = (1 / 4 : ℝ) * 1 := by ring
    _ ≤ (1 / 4 : ℝ) *
          (Real.exp (-(1 / 64 : ℝ)) + Real.exp (-(1 / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = lemma77HeightPotentialKernel (1 / 2) 1 (1 : ℤ) 3 := hkernel.symm

theorem lemma77HeightPotentialMass_le_oneHalf_one_nat
    (start : TaoSection7RenewalPoint) (j s : ℕ) :
    lemma77HeightPotentialMass start (j : ℤ) s ≤
      lemma77HeightPotentialKernel (1 / 2) 1 (j : ℤ) s := by
  have hpiece := lemma77HeightPotentialMass_eq_piecewise start j s
  by_cases h00 : j = 0 ∧ s = 0
  · rcases h00 with ⟨rfl, rfl⟩
    rw [if_pos (show (0 : ℕ) = 0 ∧ (0 : ℕ) = 0 by simp)] at hpiece
    rw [hpiece]
    norm_num [lemma77HeightPotentialKernel, taoLemma22GaussianWeight]
  · by_cases h13 : j = 1 ∧ s = 3
    · rcases h13 with ⟨rfl, rfl⟩
      exact lemma77HeightPotentialMass_one_three_le_kernel start
    · by_cases hsupp : 2 ≤ j ∧ 2 * j + 1 ≤ s
      · exact lemma77HeightPotentialMass_le_kernel_of_support
          start hsupp.1 hsupp.2
      · have hzero : lemma77HeightPotentialMass start (j : ℤ) s = 0 := by
          simp only [if_neg h00, if_neg h13, if_neg hsupp] at hpiece
          exact hpiece
        rw [hzero]
        exact lemma77HeightPotentialKernel_nonneg (by norm_num) (j : ℤ) s

theorem lemma77HeightPotentialMass_le_oneHalf_one
    (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) :
    lemma77HeightPotentialMass start j s ≤
      lemma77HeightPotentialKernel (1 / 2) 1 j s := by
  by_cases hj : j < 0
  · calc
      lemma77HeightPotentialMass start j s = 0 :=
        lemma77HeightPotentialMass_eq_zero_of_j_neg start hj s
      _ ≤ lemma77HeightPotentialKernel (1 / 2) 1 j s :=
        lemma77HeightPotentialKernel_nonneg (by norm_num) j s
  · have hj_nonneg : 0 ≤ j := le_of_not_gt hj
    have hj_cast : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj_nonneg
    simpa only [hj_cast] using
      lemma77HeightPotentialMass_le_oneHalf_one_nat start j.toNat s

theorem lemma77HeightPotentialInput_oneHalf_one :
    Lemma77HeightPotentialInput (1 / 2) 1 where
  constants := by norm_num
  height_potential := by
    intro start j s
    exact lemma77HeightPotentialMass_le_oneHalf_one start j s

end TaoSection7Lemma77

end

end Tao

end Erdos1135Predecessor
