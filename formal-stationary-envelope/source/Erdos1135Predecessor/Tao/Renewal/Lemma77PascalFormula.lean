/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma77PascalComposition

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Lemma77

theorem lemma77_two_mul_length_le_sum_of_allGeTwo
    (bs : List ℕ) (h2 : taoSection7AllGeTwo bs) :
    2 * bs.length ≤ bs.sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      have hb : 2 ≤ b := h2 b (by simp)
      have htail : taoSection7AllGeTwo bs := by
        intro x hx
        exact h2 x (by simp [hx])
      have hih := ih htail
      simp only [List.length_cons, List.sum_cons]
      omega

theorem lemma77RawTerminalFiber_sum_lower_bound
    {j s : ℕ} (bs : Lemma77RawTerminalFiber j s) :
    2 * j + 1 ≤ s := by
  have hflat : bs.1.dropLast ++ [3] = bs.1 := by
    apply List.dropLast_append_getLast?
    simp [bs.2.2.2.2]
  have hdrop : taoSection7AllGeTwo bs.1.dropLast := by
    intro b hb
    exact bs.2.2.2.1 b (List.mem_of_mem_dropLast hb)
  have hlower :=
    lemma77_two_mul_length_le_sum_of_allGeTwo bs.1.dropLast hdrop
  have hlen : bs.1.dropLast.length + 1 = bs.1.length := by
    simpa using congrArg List.length hflat
  have hsum : bs.1.dropLast.sum + 3 = bs.1.sum := by
    simpa using congrArg List.sum hflat
  have hj := bs.2.1
  have hs := bs.2.2.1
  omega

theorem lemma77HeightPotentialMass_eq_zero_of_pos_of_lt_support
    (start : TaoSection7RenewalPoint) {j s : ℕ}
    (hj : 0 < j) (hs : s < 2 * j + 1) :
    lemma77HeightPotentialMass start (j : ℤ) s = 0 := by
  rw [lemma77HeightPotentialMass_eq_rawTerminalMass start hj]
  letI : IsEmpty (Lemma77RawTerminalFiber j s) :=
    ⟨fun bs => (Nat.not_le_of_lt hs)
      (lemma77RawTerminalFiber_sum_lower_bound bs)⟩
  simp

@[simp]
theorem lemma77HeightPotentialMass_zero_nat
    (start : TaoSection7RenewalPoint) (s : ℕ) :
    lemma77HeightPotentialMass start (0 : ℤ) s =
      if s = 0 then 1 else 0 := by
  simpa using lemma77HeightPotentialMass_eq_sum_range start 0 s

theorem lemma77HeightPotentialMass_eq_multichoose_of_support
    (start : TaoSection7RenewalPoint) {j s : ℕ}
    (hj : 0 < j) (hs : 2 * j + 1 ≤ s) :
    lemma77HeightPotentialMass start (j : ℤ) s =
      (Nat.multichoose (2 * (j - 1)) (s - (2 * j + 1)) : ℝ) *
        (1 / 2 : ℝ) ^ (s - 1) := by
  have h := lemma77HeightPotentialMass_eq_multichoose
    start (j - 1) (s - (2 * j + 1))
  have hjcoord : j - 1 + 1 = j := by omega
  have hscoord : 2 * (j - 1) + (s - (2 * j + 1)) + 3 = s := by
    omega
  have hexp : 2 * (j - 1) + (s - (2 * j + 1)) + 2 = s - 1 := by
    omega
  simpa only [hjcoord, hscoord, hexp] using h

theorem lemma77HeightPotentialMass_eq_choose_asymm_of_support
    (start : TaoSection7RenewalPoint) {j s : ℕ}
    (hj : 0 < j) (hs : 2 * j + 1 ≤ s) :
    lemma77HeightPotentialMass start (j : ℤ) s =
      (Nat.choose (s - 4) (s - (2 * j + 1)) : ℝ) *
        (1 / 2 : ℝ) ^ (s - 1) := by
  rw [lemma77HeightPotentialMass_eq_multichoose_of_support start hj hs,
    Nat.multichoose_eq]
  have htop :
      2 * (j - 1) + (s - (2 * j + 1)) - 1 = s - 4 := by
    omega
  rw [htop]

theorem lemma77HeightPotentialMass_eq_choose_of_support
    (start : TaoSection7RenewalPoint) {j s : ℕ}
    (hj : 2 ≤ j) (hs : 2 * j + 1 ≤ s) :
    lemma77HeightPotentialMass start (j : ℤ) s =
      (Nat.choose (s - 4) (2 * j - 3) : ℝ) *
        (1 / 2 : ℝ) ^ (s - 1) := by
  rw [lemma77HeightPotentialMass_eq_choose_asymm_of_support start
    (by omega) hs]
  have htop : s - 4 = (s - (2 * j + 1)) + (2 * j - 3) := by
    omega
  rw [Nat.choose_symm_of_eq_add htop]

@[simp]
theorem lemma77HeightPotentialMass_one_three
    (start : TaoSection7RenewalPoint) :
    lemma77HeightPotentialMass start (1 : ℤ) 3 = (1 / 4 : ℝ) := by
  have h := lemma77HeightPotentialMass_eq_multichoose start 0 0
  norm_num at h
  exact h

theorem lemma77HeightPotentialMass_one_eq_zero_of_ne_three
    (start : TaoSection7RenewalPoint) {s : ℕ} (hs : s ≠ 3) :
    lemma77HeightPotentialMass start (1 : ℤ) s = 0 := by
  by_cases hbelow : s < 3
  · exact lemma77HeightPotentialMass_eq_zero_of_pos_of_lt_support
      (j := 1) (s := s) start (by norm_num) (by omega)
  · have hsge : 3 ≤ s := by omega
    have hsub : 0 < s - 3 := by omega
    have hmulti : Nat.multichoose 0 (s - 3) = 0 := by
      cases hu : s - 3 with
      | zero => omega
      | succ u => simp
    have h := lemma77HeightPotentialMass_eq_multichoose start 0 (s - 3)
    simpa [hmulti, Nat.sub_add_cancel hsge] using h

theorem lemma77HeightPotentialMass_eq_piecewise
    (start : TaoSection7RenewalPoint) (j s : ℕ) :
    lemma77HeightPotentialMass start (j : ℤ) s =
      if j = 0 ∧ s = 0 then 1
      else if j = 1 ∧ s = 3 then (1 / 4 : ℝ)
      else if 2 ≤ j ∧ 2 * j + 1 ≤ s then
        (Nat.choose (s - 4) (2 * j - 3) : ℝ) *
          (1 / 2 : ℝ) ^ (s - 1)
      else 0 := by
  by_cases hj0 : j = 0
  · subst j
    by_cases hs0 : s = 0
    · subst s
      simp
    · simp [hs0]
  · have hjpos : 0 < j := by omega
    by_cases hj1 : j = 1
    · subst j
      by_cases hs3 : s = 3
      · subst s
        simp
      · simpa [hs3] using
          lemma77HeightPotentialMass_one_eq_zero_of_ne_three start hs3
    · have hj2 : 2 ≤ j := by omega
      by_cases hsupp : 2 * j + 1 ≤ s
      · rw [lemma77HeightPotentialMass_eq_choose_of_support start hj2 hsupp]
        simp [hj0, hj1, hj2, hsupp]
      · rw [lemma77HeightPotentialMass_eq_zero_of_pos_of_lt_support
          start hjpos (by omega)]
        simp [hj0, hj1, hj2, hsupp]

end TaoSection7Lemma77

end

end Tao

end Erdos1135Predecessor
