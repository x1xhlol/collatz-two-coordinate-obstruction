/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Section 7 Product Penalty

This module isolates the deterministic finite product estimate used between
Tao's Lemma 7.2 and Proposition 7.3: if each factor is at most
`exp(-epsilon^3)` on white `b_j = 3` hits and at most `1` otherwise, then the
product is bounded by `exp(-epsilon^3 * hit_count)`.
-/

namespace Erdos1135SecondScale
namespace Tao

/--
Recursive finite count behind Tao equation (7.10), starting at source index
`j` with current prefix sum `s = b_[1,j-1]`.
-/
noncomputable def taoSection7WhiteHitCountFrom
    (W : ℕ → ℤ → Prop) : ℕ → ℕ → List ℕ → ℕ
  | _j, _s, [] => 0
  | j, s, b :: bs =>
      letI := Classical.propDecidable (b = 3 ∧ W j (Int.ofNat (s + b)))
      (if b = 3 ∧ W j (Int.ofNat (s + b)) then 1 else 0) +
        taoSection7WhiteHitCountFrom W (j + 1) (s + b) bs

/--
Finite version of the count in Tao equation (7.10):
`#{j : b_j = 3, (j, b_[1,j]) in W}`.
-/
noncomputable def taoSection7WhiteHitCount
    (W : ℕ → ℤ → Prop) (bs : List ℕ) : ℕ :=
  taoSection7WhiteHitCountFrom W 1 0 bs

/-- The exponential penalty appearing in Tao equation (7.10). -/
noncomputable def taoSection7WhiteHitPenaltyFrom
    (epsilon : ℝ) (W : ℕ → ℤ → Prop) (j s : ℕ) (bs : List ℕ) : ℝ :=
  Real.exp (-(epsilon ^ 3) * (taoSection7WhiteHitCountFrom W j s bs : ℝ))

/-- Top-level finite penalty from equation (7.10). -/
noncomputable def taoSection7WhiteHitPenalty
    (epsilon : ℝ) (W : ℕ → ℤ → Prop) (bs : List ℕ) : ℝ :=
  taoSection7WhiteHitPenaltyFrom epsilon W 1 0 bs

theorem taoSection7WhiteHitCountFrom_eq_zero_of_forall_not
    (W : ℕ → ℤ → Prop) :
    ∀ (j s : ℕ) (bs : List ℕ),
      (∀ k l, j ≤ k → ¬ W k l) →
        taoSection7WhiteHitCountFrom W j s bs = 0 := by
  intro j s bs
  induction bs generalizing j s with
  | nil =>
      intro _hW
      simp [taoSection7WhiteHitCountFrom]
  | cons b bs ih =>
      intro hW
      classical
      have hhere : ¬(b = 3 ∧ W j (Int.ofNat (s + b))) := by
        rintro ⟨_hb, hw⟩
        exact hW j _ (by omega) hw
      rw [taoSection7WhiteHitCountFrom, if_neg hhere]
      simpa using ih (j + 1) (s + b) (by
        intro k l hk
        exact hW k l (by omega))

theorem taoSection7WhiteHitCountFrom_take_eq_of_false_after
    (W : ℕ → ℤ → Prop) :
    ∀ (j s K : ℕ) (bs : List ℕ),
      (∀ k l, j + K ≤ k → ¬ W k l) →
        taoSection7WhiteHitCountFrom W j s (bs.take K) =
          taoSection7WhiteHitCountFrom W j s bs := by
  intro j s K bs
  induction K generalizing j s bs with
  | zero =>
      intro hW
      have hz := taoSection7WhiteHitCountFrom_eq_zero_of_forall_not
        W j s bs (by
          intro k l hk
          exact hW k l (by omega))
      simpa [taoSection7WhiteHitCountFrom] using hz.symm
  | succ K ih =>
      intro hW
      cases bs with
      | nil => simp [taoSection7WhiteHitCountFrom]
      | cons b bs =>
          classical
          simp only [List.take_succ_cons, taoSection7WhiteHitCountFrom]
          apply congrArg
          exact ih (j + 1) (s + b) bs (by
            intro k l hk
            exact hW k l (by omega))

theorem taoSection7WhiteHitCount_take_eq_of_false_after
    (W : ℕ → ℤ → Prop) (J : ℕ) (bs : List ℕ)
    (hW : ∀ j l, J < j → ¬ W j l) :
    taoSection7WhiteHitCount W (bs.take J) =
      taoSection7WhiteHitCount W bs := by
  unfold taoSection7WhiteHitCount
  exact taoSection7WhiteHitCountFrom_take_eq_of_false_after
    W 1 0 J bs (by
      intro k l hk
      exact hW k l (by omega))

theorem taoSection7WhiteHitPenalty_take_eq_of_false_after
    (epsilon : ℝ) (W : ℕ → ℤ → Prop) (J : ℕ) (bs : List ℕ)
    (hW : ∀ j l, J < j → ¬ W j l) :
    taoSection7WhiteHitPenalty epsilon W (bs.take J) =
      taoSection7WhiteHitPenalty epsilon W bs := by
  unfold taoSection7WhiteHitPenalty taoSection7WhiteHitPenaltyFrom
  rw [show
    taoSection7WhiteHitCountFrom W 1 0 (bs.take J) =
      taoSection7WhiteHitCountFrom W 1 0 bs by
        simpa [taoSection7WhiteHitCount] using
          taoSection7WhiteHitCount_take_eq_of_false_after W J bs hW]

/-- Recursive product of local Section 7 factor bounds along a finite `b` path. -/
noncomputable def taoSection7FactorProductFrom
    (F : ℕ → ℕ → ℕ → ℝ) : ℕ → ℕ → List ℕ → ℝ
  | _j, _s, [] => 1
  | j, s, b :: bs =>
      F j s b * taoSection7FactorProductFrom F (j + 1) (s + b) bs

/-- Top-level product of local Section 7 factor bounds. -/
noncomputable def taoSection7FactorProduct
    (F : ℕ → ℕ → ℕ → ℝ) (bs : List ℕ) : ℝ :=
  taoSection7FactorProductFrom F 1 0 bs

theorem taoSection7FactorProductFrom_nonneg
    {F : ℕ → ℕ → ℕ → ℝ}
    (hFnonneg : ∀ j s b, 0 ≤ F j s b) :
    ∀ j s bs, 0 ≤ taoSection7FactorProductFrom F j s bs := by
  intro j s bs
  induction bs generalizing j s with
  | nil =>
      simp [taoSection7FactorProductFrom]
  | cons b bs ih =>
      simp [taoSection7FactorProductFrom, mul_nonneg (hFnonneg j s b) (ih (j + 1) (s + b))]

theorem taoSection7FactorProductFrom_le_one
    {F : ℕ → ℕ → ℕ → ℝ}
    (hFnonneg : ∀ j s b, 0 ≤ F j s b)
    (hFle : ∀ j s b, F j s b ≤ 1) :
    ∀ j s bs, taoSection7FactorProductFrom F j s bs ≤ 1 := by
  intro j s bs
  induction bs generalizing j s with
  | nil =>
      simp [taoSection7FactorProductFrom]
  | cons b bs ih =>
      rw [taoSection7FactorProductFrom]
      calc
        F j s b * taoSection7FactorProductFrom F (j + 1) (s + b) bs
            ≤ 1 * 1 := by
              exact mul_le_mul (hFle j s b) (ih (j + 1) (s + b))
                (taoSection7FactorProductFrom_nonneg hFnonneg (j + 1) (s + b) bs)
                (by norm_num)
        _ = 1 := by norm_num

theorem taoSection7FactorProduct_le_one
    {F : ℕ → ℕ → ℕ → ℝ}
    (hFnonneg : ∀ j s b, 0 ≤ F j s b)
    (hFle : ∀ j s b, F j s b ≤ 1)
    (bs : List ℕ) :
    taoSection7FactorProduct F bs ≤ 1 :=
  taoSection7FactorProductFrom_le_one hFnonneg hFle 1 0 bs

private theorem exp_penalty_step
    (epsilon : ℝ) (count : ℕ) :
    Real.exp (-(epsilon ^ 3)) *
        Real.exp (-(epsilon ^ 3) * (count : ℝ)) =
      Real.exp (-(epsilon ^ 3) * ((1 + count : ℕ) : ℝ)) := by
  rw [← Real.exp_add]
  congr 1
  norm_num
  ring

/--
Deterministic product-to-count penalty.

This is the finite algebraic step turning pointwise Lemma 7.2 bounds and the
trivial `|f(x,b)| <= 1` bound into the exponential white-hit penalty.
-/
theorem taoSection7FactorProductFrom_le_penalty
    {epsilon : ℝ} {W : ℕ → ℤ → Prop} {F : ℕ → ℕ → ℕ → ℝ}
    (hFnonneg : ∀ j s b, 0 ≤ F j s b)
    (hFhit :
      ∀ j s b, b = 3 ∧ W j (Int.ofNat (s + b)) →
        F j s b ≤ Real.exp (-(epsilon ^ 3)))
    (hFmiss :
      ∀ j s b, ¬ (b = 3 ∧ W j (Int.ofNat (s + b))) →
        F j s b ≤ 1) :
    ∀ j s bs,
      taoSection7FactorProductFrom F j s bs ≤
        taoSection7WhiteHitPenaltyFrom epsilon W j s bs := by
  intro j s bs
  induction bs generalizing j s with
  | nil =>
      simp [taoSection7FactorProductFrom, taoSection7WhiteHitPenaltyFrom,
        taoSection7WhiteHitCountFrom]
  | cons b bs ih =>
      classical
      by_cases hhit : b = 3 ∧ W j (Int.ofNat (s + b))
      · rw [taoSection7FactorProductFrom, taoSection7WhiteHitPenaltyFrom,
          taoSection7WhiteHitCountFrom]
        rw [if_pos hhit]
        have htail_nonneg :
            0 ≤ taoSection7FactorProductFrom F (j + 1) (s + b) bs :=
          taoSection7FactorProductFrom_nonneg hFnonneg (j + 1) (s + b) bs
        have htail_bound := ih (j + 1) (s + b)
        calc
          F j s b * taoSection7FactorProductFrom F (j + 1) (s + b) bs
              ≤ Real.exp (-(epsilon ^ 3)) *
                    taoSection7WhiteHitPenaltyFrom epsilon W (j + 1) (s + b) bs := by
                exact mul_le_mul (hFhit j s b hhit) htail_bound htail_nonneg
                  (Real.exp_pos _).le
          _ = Real.exp (-(epsilon ^ 3)) *
                Real.exp (-(epsilon ^ 3) *
                  (taoSection7WhiteHitCountFrom W (j + 1) (s + b) bs : ℝ)) := by
                rfl
          _ = Real.exp (-(epsilon ^ 3) *
                ((1 + taoSection7WhiteHitCountFrom W (j + 1) (s + b) bs : ℕ) : ℝ)) := by
                rw [exp_penalty_step]
      · rw [taoSection7FactorProductFrom, taoSection7WhiteHitPenaltyFrom,
          taoSection7WhiteHitCountFrom]
        rw [if_neg hhit]
        have htail_bound := ih (j + 1) (s + b)
        calc
          F j s b * taoSection7FactorProductFrom F (j + 1) (s + b) bs
              ≤ 1 * taoSection7WhiteHitPenaltyFrom epsilon W (j + 1) (s + b) bs := by
                exact mul_le_mul (hFmiss j s b hhit) htail_bound
                  (taoSection7FactorProductFrom_nonneg hFnonneg (j + 1) (s + b) bs)
                  (by norm_num)
          _ = Real.exp (-(epsilon ^ 3) *
                ((0 + taoSection7WhiteHitCountFrom W (j + 1) (s + b) bs : ℕ) : ℝ)) := by
                simp [taoSection7WhiteHitPenaltyFrom]

/-- Top-level product-to-count penalty, starting at source index `1` and prefix `0`. -/
theorem taoSection7FactorProduct_le_penalty
    {epsilon : ℝ} {W : ℕ → ℤ → Prop} {F : ℕ → ℕ → ℕ → ℝ}
    (hFnonneg : ∀ j s b, 0 ≤ F j s b)
    (hFhit :
      ∀ j s b, b = 3 ∧ W j (Int.ofNat (s + b)) →
        F j s b ≤ Real.exp (-(epsilon ^ 3)))
    (hFmiss :
      ∀ j s b, ¬ (b = 3 ∧ W j (Int.ofNat (s + b))) →
        F j s b ≤ 1)
    (bs : List ℕ) :
    taoSection7FactorProduct F bs ≤
      taoSection7WhiteHitPenalty epsilon W bs :=
  taoSection7FactorProductFrom_le_penalty hFnonneg hFhit hFmiss 1 0 bs

end Tao
end Erdos1135SecondScale
