import FullTwoMatrixBasic
import Mathlib.Tactic.LinearCombination

namespace CollatzCertificate.FullTwoMatrix

open Matrix

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem common_positive_left_product_fixed (A B : M2) (w u : Fin 2 → ℝ) (α : ℝ)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B)
    (hA00 : 0 < A 0 0) (hB00 : 0 < B 0 0)
    (hw : ∀ i, 0 < w i) (hα : 0 < α)
    (hwA : ∀ j, ∑ i, w i * A i j = α*w j)
    (hwB : ∀ j, ∑ i, w i * B i j = α*w j)
    (hAB : (A*B).mulVec u = α^2 • u)
    (hBA : (B*A).mulVec u = α^2 • u) :
    A.mulVec u = α • u ∧ B.mulVec u = α • u := by
  have wa0 := hwA 0
  have wa1 := hwA 1
  have wb0 := hwB 0
  have wb1 := hwB 1
  simp only [Fin.sum_univ_two] at wa0 wa1 wb0 wb1
  have a00 : 0 ≤ A 0 0 := hA 0 0
  have a01 : 0 ≤ A 0 1 := hA 0 1
  have a10 : 0 ≤ A 1 0 := hA 1 0
  have a11 : 0 ≤ A 1 1 := hA 1 1
  have b00 : 0 ≤ B 0 0 := hB 0 0
  have b01 : 0 ≤ B 0 1 := hB 0 1
  have b10 : 0 ≤ B 1 0 := hB 1 0
  have b11 : 0 ≤ B 1 1 := hB 1 1
  have a00le : A 0 0 ≤ α := by
    have hh : w 0*(A 0 0) ≤ w 0*α := by
      nlinarith only [wa0,mul_nonneg (le_of_lt (hw 1)) a10]
    exact le_of_mul_le_mul_left hh (hw 0)
  have a11le : A 1 1 ≤ α := by
    have hh : w 1*(A 1 1) ≤ w 1*α := by
      nlinarith only [wa1,mul_nonneg (le_of_lt (hw 0)) a01]
    exact le_of_mul_le_mul_left hh (hw 1)
  have b00le : B 0 0 ≤ α := by
    have hh : w 0*(B 0 0) ≤ w 0*α := by
      nlinarith only [wb0,mul_nonneg (le_of_lt (hw 1)) b10]
    exact le_of_mul_le_mul_left hh (hw 0)
  have b11le : B 1 1 ≤ α := by
    have hh : w 1*(B 1 1) ≤ w 1*α := by
      nlinarith only [wb1,mul_nonneg (le_of_lt (hw 0)) b01]
    exact le_of_mul_le_mul_left hh (hw 1)
  let κA := A 0 0 + A 1 1 - α
  let κB := B 0 0 + B 1 1 - α
  have kal : -α < κA := by dsimp [κA]; linarith only [hA00,a11]
  have kau : κA ≤ α := by dsimp [κA]; linarith only [a00le,a11le]
  have kbl : -α < κB := by dsimp [κB]; linarith only [hB00,b11]
  have kbu : κB ≤ α := by dsimp [κB]; linarith only [b00le,b11le]
  let x : Fin 2 → ℝ := fun i => (A.mulVec u) i - α*u i
  let y : Fin 2 → ℝ := fun i => (B.mulVec u) i - α*u i
  have hx : w 0*x 0+w 1*x 1=0 := by
    dsimp [x]
    simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    linear_combination u 0*wa0 + u 1*wa1
  have hy : w 0*y 0+w 1*y 1=0 := by
    dsimp [y]
    simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    linear_combination u 0*wb0 + u 1*wb1
  have ab0 := congrArg (fun v : Fin 2 → ℝ => v 0) hAB
  have ba0 := congrArg (fun v : Fin 2 → ℝ => v 0) hBA
  simp only [Matrix.mulVec,Matrix.mul_apply,dotProduct,Fin.sum_univ_two,
    Pi.smul_apply,smul_eq_mul] at ab0 ba0
  have r1 : α*x 0+A 0 0*y 0+A 0 1*y 1=0 := by
    dsimp [x,y]
    simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    nlinarith only [ab0]
  have r2 : α*y 0+B 0 0*x 0+B 0 1*x 1=0 := by
    dsimp [x,y]
    simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    nlinarith only [ba0]
  have e1 : α*x 0+κA*y 0=0 := by
    have hm : w 1*(α*x 0+κA*y 0)=0 := by
      dsimp [κA]
      linear_combination w 1*r1 - A 0 1*hy + y 0*wa1
    exact (mul_eq_zero.mp hm).resolve_left (ne_of_gt (hw 1))
  have e2 : α*y 0+κB*x 0=0 := by
    have hm : w 1*(α*y 0+κB*x 0)=0 := by
      dsimp [κB]
      linear_combination w 1*r2 - B 0 1*hx + x 0*wb1
    exact (mul_eq_zero.mp hm).resolve_left (ne_of_gt (hw 1))
  have xz : x 0=0 := by
    by_cases kat : κA < α
    · have hp : κA*κB < α^2 := by
        by_cases ka0 : 0 ≤ κA
        · calc
            κA*κB ≤ κA*α := mul_le_mul_of_nonneg_left kbu ka0
            _ < α*α := mul_lt_mul_of_pos_right kat hα
            _ = α^2 := by ring
        · have kan : κA < 0 := lt_of_not_ge ka0
          calc
            κA*κB < κA*(-α) := mul_lt_mul_of_neg_left kbl kan
            _ < (-α)*(-α) := mul_lt_mul_of_neg_right kal (neg_neg_of_pos hα)
            _ = α^2 := by ring
      have hm : (α^2-κA*κB)*x 0=0 := by
        linear_combination α*e1 - κA*e2
      exact (mul_eq_zero.mp hm).resolve_left (ne_of_gt (sub_pos.mpr hp))
    · have kaeq : κA=α := le_antisymm kau (le_of_not_gt kat)
      have ad : A 0 0=α := by dsimp [κA] at kaeq; linarith only [kaeq,a00le,a11le]
      have dd : A 1 1=α := by dsimp [κA] at kaeq; linarith only [kaeq,a00le,a11le]
      have bd : A 0 1=0 := by
        rw [dd] at wa1
        have hz : w 0*A 0 1=0 := by nlinarith only [wa1]
        exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (hw 0))
      dsimp [x]
      simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,ad,bd,zero_mul,add_zero]
      ring
  have yz : y 0=0 := by
    rw [xz,mul_zero,add_zero] at e2
    exact (mul_eq_zero.mp e2).resolve_left (ne_of_gt hα)
  have xz1 : x 1=0 := by
    rw [xz,mul_zero,zero_add] at hx
    exact (mul_eq_zero.mp hx).resolve_left (ne_of_gt (hw 1))
  have yz1 : y 1=0 := by
    rw [yz,mul_zero,zero_add] at hy
    exact (mul_eq_zero.mp hy).resolve_left (ne_of_gt (hw 1))
  constructor
  · funext i
    fin_cases i
    · simpa only [x,Pi.smul_apply,smul_eq_mul,sub_eq_zero] using xz
    · simpa only [x,Pi.smul_apply,smul_eq_mul,sub_eq_zero] using xz1
  · funext i
    fin_cases i
    · simpa only [y,Pi.smul_apply,smul_eq_mul,sub_eq_zero] using yz
    · simpa only [y,Pi.smul_apply,smul_eq_mul,sub_eq_zero] using yz1

#print axioms common_positive_left_product_fixed

end CollatzCertificate.FullTwoMatrix
