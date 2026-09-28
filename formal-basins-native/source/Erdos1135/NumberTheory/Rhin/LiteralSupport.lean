import Erdos1135.NumberTheory.Rhin.LiteralPolynomial
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Central support of Rhin's literal square

This file proves the alternating signs of the three central coefficients of
the square of Rhin's literal p. 162 polynomial.  The proof is table-free: after
the substitution `X ↦ -X`, every printed factor has nonnegative natural
coefficients and coefficientwise dominates `1 + X`.  The resulting product
therefore has dense positive support throughout the range needed below.
-/

namespace Erdos1135
namespace NumberTheory
namespace Rhin

noncomputable section

open Polynomial
open scoped BigOperators

private abbrev NPoly := ℕ[X]

private def CoeffLE (P Q : NPoly) : Prop :=
  ∀ k : ℕ, P.coeff k ≤ Q.coeff k

private theorem CoeffLE.refl (P : NPoly) : CoeffLE P P :=
  fun _ ↦ le_rfl

private theorem CoeffLE.mul {P Q R S : NPoly}
    (hPR : CoeffLE P R) (hQS : CoeffLE Q S) :
    CoeffLE (P * Q) (R * S) := by
  intro k
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_le_sum
  intro ij hij
  exact Nat.mul_le_mul (hPR ij.1) (hQS ij.2)

private theorem CoeffLE.pow {P Q : NPoly} (hPQ : CoeffLE P Q) (n : ℕ) :
    CoeffLE (P ^ n) (Q ^ n) := by
  induction n with
  | zero => exact CoeffLE.refl 1
  | succ n ih =>
      simpa only [pow_succ] using ih.mul hPQ

private theorem CoeffLE.prod
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P Q : ι → NPoly)
    (h : ∀ i ∈ s, CoeffLE (P i) (Q i)) :
    CoeffLE (∏ i ∈ s, P i) (∏ i ∈ s, Q i) := by
  induction s using Finset.induction_on with
  | empty => simp [CoeffLE.refl]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih (fun i hi ↦ h i (Finset.mem_insert_of_mem hi)))

/-- The six positive-coefficient companions obtained from the printed factors
by substituting `-X` and discarding their harmless global signs. -/
private def positiveRhinFactor : Fin 6 → NPoly :=
  ![X + C 3,
    X + C 2,
    X + C 4,
    C 5 * X + C 12,
    C 17 * X ^ 2 + C 102 * X + C 144,
    C 19 * X ^ 2 + C 108 * X + C 144]

private theorem one_add_X_coeffLE_of_coeff
    (Q : NPoly) (h0 : 1 ≤ Q.coeff 0) (h1 : 1 ≤ Q.coeff 1) :
    CoeffLE (1 + X) Q := by
  intro k
  rcases k with _ | k
  · simpa [Polynomial.coeff_one, Polynomial.coeff_X] using h0
  rcases k with _ | k
  · simpa [Polynomial.coeff_one, Polynomial.coeff_X] using h1
  · simp [Polynomial.coeff_one, Polynomial.coeff_X]

private theorem one_add_X_coeffLE_positiveRhinFactor (i : Fin 6) :
    CoeffLE (1 + X) (positiveRhinFactor i) := by
  fin_cases i
  · change CoeffLE (1 + X) (X + C 3)
    apply one_add_X_coeffLE_of_coeff <;> norm_num
  · change CoeffLE (1 + X) (X + C 2)
    apply one_add_X_coeffLE_of_coeff <;> norm_num
  · change CoeffLE (1 + X) (X + C 4)
    apply one_add_X_coeffLE_of_coeff <;> norm_num
  · change CoeffLE (1 + X) (C 5 * X + C 12)
    apply one_add_X_coeffLE_of_coeff <;> norm_num
  · change CoeffLE (1 + X) (C 17 * X ^ 2 + C 102 * X + C 144)
    apply one_add_X_coeffLE_of_coeff <;> norm_num
  · change CoeffLE (1 + X) (C 19 * X ^ 2 + C 108 * X + C 144)
    apply one_add_X_coeffLE_of_coeff <;> norm_num

private def literalRhinCopyCount (n : ℕ) : ℕ :=
  ∑ i : Fin 6, literalRhinMultiplicity i n

private def positiveRhinProduct (n : ℕ) : NPoly :=
  ∏ i : Fin 6, positiveRhinFactor i ^ literalRhinMultiplicity i n

/-- Product of the six positive-companion coefficient sums.  This is a
derived exact evaluation-at-one coefficient majorant for the literal p. 162
polynomial, not a quantity printed by Rhin. -/
def literalRhinCoefficientProduct (n : ℕ) : ℕ :=
  ∏ i : Fin 6,
    ![4, 3, 5, 17, 263, 271] i ^ literalRhinMultiplicity i n

private theorem positiveRhinProduct_eval_one (n : ℕ) :
    (positiveRhinProduct n).eval 1 = literalRhinCoefficientProduct n := by
  unfold positiveRhinProduct literalRhinCoefficientProduct
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval_pow]
  fin_cases i <;> norm_num [positiveRhinFactor]

private theorem natPolynomial_coeff_le_eval_one (P : ℕ[X]) (k : ℕ) :
    P.coeff k ≤ P.eval 1 := by
  rw [Polynomial.eval_eq_sum]
  simp only [one_pow, mul_one]
  by_cases hk : k ∈ P.support
  · exact Finset.single_le_sum (fun i hi ↦ Nat.zero_le _) hk
  · rw [Polynomial.mem_support_iff, not_ne_iff] at hk
    rw [hk]
    exact Nat.zero_le _

private theorem one_add_X_pow_copyCount_coeffLE (n : ℕ) :
    CoeffLE ((1 + X) ^ literalRhinCopyCount n) (positiveRhinProduct n) := by
  have hProd := CoeffLE.prod (Finset.univ : Finset (Fin 6))
    (fun i ↦ (1 + X) ^ literalRhinMultiplicity i n)
    (fun i ↦ positiveRhinFactor i ^ literalRhinMultiplicity i n)
    (by
      intro i hi
      exact (one_add_X_coeffLE_positiveRhinFactor i).pow _)
  simpa only [positiveRhinProduct, literalRhinCopyCount,
    Finset.prod_pow_eq_pow_sum] using hProd

private theorem positiveRhinProduct_sq_coeff_pos
    (n k : ℕ) (hk : k ≤ 2 * literalRhinCopyCount n) :
    0 < (positiveRhinProduct n ^ 2).coeff k := by
  have hCoeff := (one_add_X_pow_copyCount_coeffLE n).pow 2 k
  have hPower :
      (((1 + X : NPoly) ^ literalRhinCopyCount n) ^ 2) =
        (1 + X) ^ (2 * literalRhinCopyCount n) := by
    calc
      (((1 + X : NPoly) ^ literalRhinCopyCount n) ^ 2) =
          (1 + X) ^ (literalRhinCopyCount n * 2) :=
        (pow_mul _ _ _).symm
      _ = (1 + X) ^ (2 * literalRhinCopyCount n) := by
        rw [Nat.mul_comm]
  rw [hPower, Polynomial.coeff_one_add_X_pow] at hCoeff
  exact (Nat.choose_pos hk).trans_le hCoeff

private theorem literalRhinCopyCount_ge_succ
    (n : ℕ) (hn : 8 ≤ n) : n + 1 ≤ literalRhinCopyCount n := by
  have h1 := Nat.mod_add_div (704324 * n) 1000000
  have h2 := Nat.mod_add_div (552418 * n) 1000000
  have h3 := Nat.mod_add_div (447582 * n) 1000000
  have h4 := Nat.mod_add_div (109072 * n) 1000000
  have h5 := Nat.mod_add_div (38934 * n) 1000000
  have h6 := Nat.mod_add_div (54368 * n) 1000000
  have hr1 := Nat.mod_lt (704324 * n) (by norm_num : 0 < (1000000 : ℕ))
  have hr2 := Nat.mod_lt (552418 * n) (by norm_num : 0 < (1000000 : ℕ))
  have hr3 := Nat.mod_lt (447582 * n) (by norm_num : 0 < (1000000 : ℕ))
  have hr4 := Nat.mod_lt (109072 * n) (by norm_num : 0 < (1000000 : ℕ))
  have hr5 := Nat.mod_lt (38934 * n) (by norm_num : 0 < (1000000 : ℕ))
  have hr6 := Nat.mod_lt (54368 * n) (by norm_num : 0 < (1000000 : ℕ))
  simp [literalRhinCopyCount, literalRhinMultiplicity,
    literalRhinWeightNumerator, Fin.sum_univ_succ]
  omega

private def positiveRhinFactorInt (i : Fin 6) : ℤ[X] :=
  (positiveRhinFactor i).map (Nat.castRingHom ℤ)

private def positiveRhinSquareInt (n : ℕ) : ℤ[X] :=
  C ((12 : ℤ) ^ 14) *
    ((positiveRhinProduct n).map (Nat.castRingHom ℤ)) ^ 2

private theorem literal_factor_comp_neg_X_sq (i : Fin 6) :
    ((literalRhinFactor i).comp (-X)) ^ 2 =
      (positiveRhinFactorInt i) ^ 2 := by
  fin_cases i <;>
    simp [literalRhinFactor, literalRhinFactor1, literalRhinFactor2,
      literalRhinFactor3, literalRhinFactor4, literalRhinFactor5,
      literalRhinFactor6, positiveRhinFactorInt, positiveRhinFactor,
      Polynomial.sub_comp, Polynomial.add_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
    ring

private theorem pow_sq_eq_sq_pow {R : Type*} [CommMonoid R]
    (a : R) (m : ℕ) : (a ^ m) ^ 2 = (a ^ 2) ^ m := by
  calc
    (a ^ m) ^ 2 = a ^ (m * 2) := (pow_mul _ _ _).symm
    _ = a ^ (2 * m) := by rw [Nat.mul_comm]
    _ = (a ^ 2) ^ m := pow_mul _ _ _

private theorem literal_product_comp_neg_X_sq (n : ℕ) :
    ((∏ i : Fin 6,
        literalRhinFactor i ^ literalRhinMultiplicity i n).comp (-X)) ^ 2 =
      ((positiveRhinProduct n).map (Nat.castRingHom ℤ)) ^ 2 := by
  rw [Polynomial.prod_comp]
  simp only [Polynomial.pow_comp]
  rw [show (positiveRhinProduct n).map (Nat.castRingHom ℤ) =
      ∏ i : Fin 6,
        positiveRhinFactorInt i ^ literalRhinMultiplicity i n by
    unfold positiveRhinProduct
    rw [Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    simp [positiveRhinFactorInt]]
  rw [← Finset.prod_pow (Finset.univ : Finset (Fin 6)) 2,
    ← Finset.prod_pow (Finset.univ : Finset (Fin 6)) 2]
  apply Finset.prod_congr rfl
  intro i hi
  calc
    (((literalRhinFactor i).comp (-X)) ^ literalRhinMultiplicity i n) ^ 2 =
        (((literalRhinFactor i).comp (-X)) ^ 2) ^
          literalRhinMultiplicity i n := pow_sq_eq_sq_pow _ _
    _ = ((positiveRhinFactorInt i) ^ 2) ^ literalRhinMultiplicity i n := by
      rw [literal_factor_comp_neg_X_sq]
    _ = ((positiveRhinFactorInt i) ^ literalRhinMultiplicity i n) ^ 2 :=
      (pow_sq_eq_sq_pow _ _).symm

private theorem literalRhinPolynomial_sq_comp_neg_X (n : ℕ) :
    (literalRhinPolynomial n ^ 2).comp (-X) = positiveRhinSquareInt n := by
  rw [Polynomial.pow_comp]
  unfold literalRhinPolynomial positiveRhinSquareInt
  rw [Polynomial.mul_comp, Polynomial.C_comp]
  rw [mul_pow]
  rw [literal_product_comp_neg_X_sq]
  congr 1
  simp only [← C_pow, ← pow_mul]

private theorem positiveRhinSquareInt_coeff_pos
    (n k : ℕ) (hk : k ≤ 2 * literalRhinCopyCount n) :
    0 < (positiveRhinSquareInt n).coeff k := by
  have hNat := positiveRhinProduct_sq_coeff_pos n k hk
  unfold positiveRhinSquareInt
  rw [Polynomial.coeff_C_mul]
  have hMap :
      (((positiveRhinProduct n).map (Nat.castRingHom ℤ)) ^ 2).coeff k =
        ((positiveRhinProduct n ^ 2).coeff k : ℤ) := by
    rw [← Polynomial.map_pow, Polynomial.coeff_map]
    rfl
  rw [hMap]
  exact mul_pos (by positivity) (by exact_mod_cast hNat)

private theorem coeff_comp_neg_X (P : ℤ[X]) (k : ℕ) :
    (P.comp (-X)).coeff k = P.coeff k * (-1 : ℤ) ^ k := by
  have h := Polynomial.comp_C_mul_X_coeff (p := P) (r := (-1 : ℤ)) (n := k)
  simpa only [C_neg, C_1, one_mul, neg_mul, one_mul] using h

/-- Every coefficient of the literal square is bounded by the square of the
fixed scalar times the exact product of the six positive-companion
coefficient sums. -/
theorem literalRhinSquare_coeff_natAbs_le_raw (n k : ℕ) :
    Int.natAbs ((literalRhinPolynomial n ^ 2).coeff k) ≤
      (((12 : ℕ) ^ 7 * literalRhinCoefficientProduct n) ^ 2) := by
  have hCoeff := natPolynomial_coeff_le_eval_one
    (positiveRhinProduct n ^ 2) k
  calc
    Int.natAbs ((literalRhinPolynomial n ^ 2).coeff k) =
        Int.natAbs
          (((literalRhinPolynomial n ^ 2).comp (-X)).coeff k) := by
      rw [coeff_comp_neg_X, Int.natAbs_mul, Int.natAbs_pow,
        Int.natAbs_neg, Int.natAbs_one, one_pow, mul_one]
    _ = Int.natAbs ((positiveRhinSquareInt n).coeff k) := by
      rw [literalRhinPolynomial_sq_comp_neg_X]
    _ = (12 : ℕ) ^ 14 * (positiveRhinProduct n ^ 2).coeff k := by
      unfold positiveRhinSquareInt
      rw [Polynomial.coeff_C_mul]
      rw [← Polynomial.map_pow, Polynomial.coeff_map]
      simp [Int.natAbs_mul, Int.natAbs_pow]
    _ ≤ (12 : ℕ) ^ 14 * (positiveRhinProduct n ^ 2).eval 1 :=
      Nat.mul_le_mul_left _ hCoeff
    _ = (((12 : ℕ) ^ 7 * literalRhinCoefficientProduct n) ^ 2) := by
      rw [Polynomial.eval_pow, positiveRhinProduct_eval_one]
      ring

private theorem literalRhinSquare_transformed_coeff_pos
    (n k : ℕ) (hk : k ≤ 2 * literalRhinCopyCount n) :
    0 < ((literalRhinPolynomial n ^ 2).comp (-X)).coeff k := by
  rw [literalRhinPolynomial_sq_comp_neg_X]
  exact positiveRhinSquareInt_coeff_pos n k hk

/-- The leading member of the three central p. 159 square coefficients is
strictly positive once the exact floor ledger has dense enough support. -/
theorem literalRhinSquare_coeff_N_pos
    (n : ℕ) (hn : 8 ≤ n) :
    0 < (literalRhinPolynomial n ^ 2).coeff (2 * n + 2) := by
  have hCopies := literalRhinCopyCount_ge_succ n hn
  have hRange : 2 * n + 2 ≤ 2 * literalRhinCopyCount n := by omega
  have hPos := literalRhinSquare_transformed_coeff_pos n (2 * n + 2) hRange
  rw [coeff_comp_neg_X] at hPos
  have hEven : Even (2 * n + 2) := ⟨n + 1, by omega⟩
  rw [hEven.neg_one_pow, mul_one] at hPos
  exact hPos

/-- The middle member of the three central p. 159 square coefficients is
strictly negative once the exact floor ledger has dense enough support. -/
theorem literalRhinSquare_coeff_N_sub_one_neg
    (n : ℕ) (hn : 8 ≤ n) :
    (literalRhinPolynomial n ^ 2).coeff (2 * n + 1) < 0 := by
  have hCopies := literalRhinCopyCount_ge_succ n hn
  have hRange : 2 * n + 1 ≤ 2 * literalRhinCopyCount n := by omega
  have hPos := literalRhinSquare_transformed_coeff_pos n (2 * n + 1) hRange
  rw [coeff_comp_neg_X] at hPos
  have hOdd : Odd (2 * n + 1) := ⟨n, by omega⟩
  rw [hOdd.neg_one_pow, mul_neg, mul_one] at hPos
  exact neg_pos.mp hPos

/-- The trailing member of the three central p. 159 square coefficients is
strictly positive once the exact floor ledger has dense enough support. -/
theorem literalRhinSquare_coeff_N_sub_two_pos
    (n : ℕ) (hn : 8 ≤ n) :
    0 < (literalRhinPolynomial n ^ 2).coeff (2 * n) := by
  have hCopies := literalRhinCopyCount_ge_succ n hn
  have hRange : 2 * n ≤ 2 * literalRhinCopyCount n := by omega
  have hPos := literalRhinSquare_transformed_coeff_pos n (2 * n) hRange
  rw [coeff_comp_neg_X] at hPos
  have hEven : Even (2 * n) := ⟨n, by omega⟩
  rw [hEven.neg_one_pow, mul_one] at hPos
  exact hPos

end

end Rhin
end NumberTheory
end Erdos1135
