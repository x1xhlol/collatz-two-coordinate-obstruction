/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Terras.Core.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
# Terras/Everett Parity Words

This module introduces the length-indexed parity words used for the accelerated map.  Here `true`
means the odd branch, matching the usual Terras parity-vector convention for the accelerated map.
-/

open Function

namespace Erdos1135SecondScale
namespace Terras

/-- A parity word of length `k`; `true` means the odd branch. -/
abbrev ParityWord (k : ℕ) : Type :=
  Fin k → Bool

/-- The number of odd branch bits in a parity word. -/
def numOdd {k : ℕ} (w : ParityWord k) : ℕ :=
  (Finset.univ.filter fun i : Fin k => w i).card

/-- The parity bit of a natural number, with `true` meaning odd. -/
def parityBit (n : ℕ) : Bool :=
  decide (¬ Even n)

/-- The length-`k` parity prefix of the accelerated orbit of `n`. -/
def parityPrefix (k n : ℕ) : ParityWord k :=
  fun i => parityBit (accelerated^[i.val] n)

/-- A recursive list version of `parityPrefix`, useful for induction over prefixes. -/
def parityPrefixList : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, n => parityBit n :: parityPrefixList k (accelerated n)

/-- The branch condition represented by a Terras parity bit. -/
def FollowsParityBit (isOdd : Bool) (n : ℕ) : Prop :=
  if isOdd then ¬ Even n else Even n

/-- The explicit accelerated branch selected by a Terras parity bit. -/
def acceleratedBranchStep (isOdd : Bool) (n : ℕ) : ℕ :=
  if isOdd then (3 * n + 1) / 2 else n / 2

/-- The accelerated orbit starting at `n` follows a list of Terras parity bits. -/
def FollowsParityList : List Bool → ℕ → Prop
  | [], _ => True
  | isOdd :: ps, n => FollowsParityBit isOdd n ∧ FollowsParityList ps (accelerated n)

/-- The cleared scale of one accelerated branch. -/
def branchScale (isOdd : Bool) : ℤ :=
  if isOdd then 3 else 1

/-- The cleared offset of one accelerated branch. -/
def branchOffset (isOdd : Bool) : ℤ :=
  if isOdd then 1 else 0

lemma branchScale_nonneg (isOdd : Bool) : 0 ≤ branchScale isOdd := by
  cases isOdd <;> simp [branchScale]

lemma branchOffset_nonneg (isOdd : Bool) : 0 ≤ branchOffset isOdd := by
  cases isOdd <;> simp [branchOffset]

/-- The list form of a parity word, used for recursive affine data. -/
def parityWordToList {k : ℕ} (w : ParityWord k) : List Bool :=
  List.ofFn w

/-- Cleared affine scale for an accelerated parity word represented as a list. -/
def branchScaleList : List Bool → ℤ
  | [] => 1
  | isOdd :: ps => branchScaleList ps * branchScale isOdd

/-- Cleared affine constant for an accelerated parity word represented as a list. -/
def branchConstList : List Bool → ℤ
  | [] => 0
  | isOdd :: ps => branchScaleList ps * branchOffset isOdd + 2 * branchConstList ps

/-- Cleared affine scale for a parity word. -/
def wordScale {k : ℕ} (w : ParityWord k) : ℤ :=
  branchScaleList (parityWordToList w)

/-- Cleared affine constant for a parity word. -/
def branchConst {k : ℕ} (w : ParityWord k) : ℤ :=
  branchConstList (parityWordToList w)

lemma branchScaleList_nonneg : ∀ ps : List Bool, 0 ≤ branchScaleList ps
  | [] => by simp [branchScaleList]
  | isOdd :: ps => by
      have hs := branchScaleList_nonneg ps
      have hb := branchScale_nonneg isOdd
      simp [branchScaleList]
      nlinarith

lemma branchConstList_nonneg : ∀ ps : List Bool, 0 ≤ branchConstList ps
  | [] => by simp [branchConstList]
  | isOdd :: ps => by
      have hs := branchScaleList_nonneg ps
      have ho := branchOffset_nonneg isOdd
      have hc := branchConstList_nonneg ps
      simp [branchConstList]
      nlinarith

theorem branchConst_nonneg {k : ℕ} (w : ParityWord k) : 0 ≤ branchConst w :=
  branchConstList_nonneg (parityWordToList w)

lemma branchScaleList_eq_list_prod : ∀ ps : List Bool,
    branchScaleList ps = (ps.map branchScale).prod
  | [] => by
      simp [branchScaleList]
  | isOdd :: ps => by
      simp [branchScaleList, branchScaleList_eq_list_prod ps, mul_comm]

lemma wordScale_eq_three_pow_numOdd {k : ℕ} (w : ParityWord k) :
    wordScale w = (3 : ℤ) ^ numOdd w := by
  rw [wordScale, parityWordToList, branchScaleList_eq_list_prod]
  rw [List.map_ofFn, List.prod_ofFn]
  rw [numOdd]
  change (∏ i : Fin k, branchScale (w i)) = (3 : ℤ) ^ (Finset.univ.filter fun i => w i).card
  simp only [branchScale]
  rw [← Finset.prod_filter]
  simp

lemma parityWordToList_length {k : ℕ} (w : ParityWord k) :
    (parityWordToList w).length = k := by
  simp [parityWordToList]

lemma parityWordToList_parityPrefix_eq_parityPrefixList :
    ∀ (k n : ℕ), parityWordToList (parityPrefix k n) = parityPrefixList k n
  | 0, _ => by
      rfl
  | k + 1, n => by
      change List.ofFn (fun i : Fin (k + 1) => parityBit (accelerated^[i.val] n)) =
        parityBit n :: parityPrefixList k (accelerated n)
      rw [List.ofFn_succ]
      congr
      have hfun :
          (fun i : Fin k => parityBit (accelerated^[i.succ.val] n)) =
            parityPrefix k (accelerated n) := by
        funext i
        simp [parityPrefix, iterate_succ_apply]
      rw [hfun]
      exact parityWordToList_parityPrefix_eq_parityPrefixList k (accelerated n)

lemma parityPrefix_apply {k n : ℕ} (i : Fin k) :
    parityPrefix k n i = parityBit (accelerated^[i.val] n) :=
  rfl

lemma parityPrefixList_length :
    ∀ (k n : ℕ), (parityPrefixList k n).length = k
  | 0, _ => rfl
  | k + 1, n => by
      simp [parityPrefixList, parityPrefixList_length k (accelerated n)]

lemma parityBit_eq_true_iff_not_even (n : ℕ) :
    parityBit n = true ↔ ¬ Even n := by
  simp [parityBit]

lemma parityBit_eq_false_iff_even (n : ℕ) :
    parityBit n = false ↔ Even n := by
  by_cases hn : Even n
  · simp [parityBit, hn]
  · simp [parityBit, hn]

lemma followsParityBit_parityBit (n : ℕ) :
    FollowsParityBit (parityBit n) n := by
  by_cases hn : Even n
  · simp [FollowsParityBit, parityBit, hn]
  · simp [FollowsParityBit, parityBit, hn]

lemma followsParityBit_parityPrefix {k n : ℕ} (i : Fin k) :
    FollowsParityBit (parityPrefix k n i) (accelerated^[i.val] n) := by
  simpa [parityPrefix_apply] using followsParityBit_parityBit (accelerated^[i.val] n)

lemma followsParityList_parityPrefixList :
    ∀ (k n : ℕ), FollowsParityList (parityPrefixList k n) n
  | 0, _ => by
      simp [parityPrefixList, FollowsParityList]
  | k + 1, n => by
      simp [parityPrefixList, FollowsParityList, followsParityBit_parityBit,
        followsParityList_parityPrefixList k (accelerated n)]

lemma accelerated_eq_branchStep_of_follows {isOdd : Bool} {n : ℕ}
    (h : FollowsParityBit isOdd n) :
    accelerated n = acceleratedBranchStep isOdd n := by
  cases isOdd <;> simp [FollowsParityBit, acceleratedBranchStep] at h ⊢
  · exact accelerated_eq_div_two_of_even h
  · exact accelerated_eq_three_mul_add_one_div_two_of_not_even (Nat.not_even_iff_odd.mpr h)

lemma two_mul_accelerated_eq_branch_of_follows {isOdd : Bool} {n : ℕ}
    (h : FollowsParityBit isOdd n) :
    2 * accelerated n = if isOdd then 3 * n + 1 else n := by
  cases isOdd <;> simp [FollowsParityBit] at h ⊢
  · exact two_mul_accelerated_eq_of_even h
  · exact two_mul_accelerated_eq_of_not_even (Nat.not_even_iff_odd.mpr h)

lemma two_mul_accelerated_eq_branch_int_of_follows {isOdd : Bool} {n : ℕ}
    (h : FollowsParityBit isOdd n) :
    (2 : ℤ) * (accelerated n : ℤ) =
      branchScale isOdd * (n : ℤ) + branchOffset isOdd := by
  have hnat := two_mul_accelerated_eq_branch_of_follows h
  cases isOdd
  · simp [branchScale, branchOffset] at hnat ⊢
    exact_mod_cast hnat
  · simp [branchScale, branchOffset] at hnat ⊢
    exact_mod_cast hnat

theorem affine_normal_form_list :
    ∀ (ps : List Bool) (n : ℕ), FollowsParityList ps n →
      (2 ^ ps.length : ℤ) * (accelerated^[ps.length] n : ℤ) =
        branchScaleList ps * (n : ℤ) + branchConstList ps
  | [], n, _ => by
      simp [branchScaleList, branchConstList]
  | isOdd :: ps, n, h => by
      rcases h with ⟨hfirst, htail⟩
      have ih := affine_normal_form_list ps (accelerated n) htail
      have hbranch := two_mul_accelerated_eq_branch_int_of_follows hfirst
      calc
        (2 ^ (isOdd :: ps).length : ℤ) *
            (accelerated^[(isOdd :: ps).length] n : ℤ)
            = 2 * ((2 ^ ps.length : ℤ) *
                (accelerated^[ps.length] (accelerated n) : ℤ)) := by
              rw [List.length_cons, iterate_succ_apply]
              ring_nf
        _ = 2 * (branchScaleList ps * (accelerated n : ℤ) + branchConstList ps) := by
              rw [ih]
        _ = branchScaleList ps * ((2 : ℤ) * (accelerated n : ℤ)) +
              2 * branchConstList ps := by
              ring
        _ = branchScaleList ps *
              (branchScale isOdd * (n : ℤ) + branchOffset isOdd) +
              2 * branchConstList ps := by
              rw [hbranch]
        _ = branchScaleList (isOdd :: ps) * (n : ℤ) +
              branchConstList (isOdd :: ps) := by
              simp [branchScaleList, branchConstList]
              ring

theorem affine_normal_form_parityPrefixList (k n : ℕ) :
    (2 ^ k : ℤ) * (accelerated^[k] n : ℤ) =
      branchScaleList (parityPrefixList k n) * (n : ℤ) +
        branchConstList (parityPrefixList k n) := by
  have h :=
    affine_normal_form_list (parityPrefixList k n) n
      (followsParityList_parityPrefixList k n)
  simpa [parityPrefixList_length k n] using h

theorem affine_normal_form_parityPrefix (k n : ℕ) :
    (2 ^ k : ℤ) * (accelerated^[k] n : ℤ) =
      wordScale (parityPrefix k n) * (n : ℤ) + branchConst (parityPrefix k n) := by
  simpa [wordScale, branchConst, parityWordToList_parityPrefix_eq_parityPrefixList k n] using
    affine_normal_form_parityPrefixList k n

theorem affine_normal_form {k n : ℕ} (w : ParityWord k)
    (h : parityPrefix k n = w) :
    (2 ^ k : ℤ) * (accelerated^[k] n : ℤ) =
      ((3 : ℤ) ^ numOdd w) * (n : ℤ) + branchConst w := by
  calc
    (2 ^ k : ℤ) * (accelerated^[k] n : ℤ)
        = wordScale (parityPrefix k n) * (n : ℤ) + branchConst (parityPrefix k n) :=
          affine_normal_form_parityPrefix k n
    _ = wordScale w * (n : ℤ) + branchConst w := by
          rw [h]
    _ = ((3 : ℤ) ^ numOdd w) * (n : ℤ) + branchConst w := by
          rw [wordScale_eq_three_pow_numOdd]

theorem iterate_affine_of_parityPrefix {k n : ℕ} {w : ParityWord k}
    (h : parityPrefix k n = w) :
    (2 ^ k : ℤ) * (accelerated^[k] n : ℤ) =
      ((3 : ℤ) ^ numOdd w) * (n : ℤ) + branchConst w :=
  affine_normal_form w h

lemma card_parityWord (k : ℕ) :
    Fintype.card (ParityWord k) = 2 ^ k := by
  unfold ParityWord
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

end Terras
end Erdos1135SecondScale
