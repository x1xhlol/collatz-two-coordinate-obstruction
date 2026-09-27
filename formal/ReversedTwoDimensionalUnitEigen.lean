import ReversedTwoDimensionalNonsingularEigenShape

namespace CollatzCertificate.TwoDimensionalUnitEigen

open Matrix FullTwoMatrix TwoDimensionalMiddleRank TwoDimensionalInvertibleMiddle
open TwoDimensionalSwapAlgebra (tr)

set_option maxHeartbeats 1000000

theorem nonsingular_shape_positive_left_aggregate (A B E F G : M2) (μ t : ℝ)
    (hμ : 0 < μ)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B)
    (htrA : tr A=3*μ) (htrB : tr B=3*μ)
    (hdetA : A.det=2*μ^2) (hdetB : B.det=2*μ^2)
    (hAN : A*(B-A)=(2*μ) • (B-A))
    (hNA : (B-A)*A=μ • (B-A))
    (hE : E=t • (2 • A-μ • (1 : M2)))
    (hF : F=t • (A+B-μ • (1 : M2)))
    (hG : G=t • (2 • B-μ • (1 : M2)))
    (h01 : 0 < ((A+B)+(E+F+G)) 0 1)
    (h10 : 0 < ((A+B)+(E+F+G)) 1 0) :
    ∃ w : Vec (Fin 2), (∀ i, 0 < w i) ∧
      w ᵥ* (A+B)=(4*μ) • w ∧ w ᵥ* (E+F+G)=(9*t*μ) • w := by
  let U := A-μ • (1 : M2)
  let V := B-μ • (1 : M2)
  let S := U+V
  have hU := shifted_matrix_nonnegative A μ hμ hA htrA hdetA
  have hV := shifted_matrix_nonnegative B μ hμ hB htrB hdetB
  have hS : EntrywiseLE 0 S := fun i j => add_nonneg (hU i j) (hV i j)
  have ha : A=U+μ • (1 : M2) := by dsimp [U]; module
  have hb : B=V+μ • (1 : M2) := by dsimp [V]; module
  have haa : A*A=(3*μ) • A-(2*μ^2) • (1 : M2) := by
    rw [square_trace_identity,htrA,hdetA]
  have hbb : B*B=(3*μ) • B-(2*μ^2) • (1 : M2) := by
    rw [square_trace_identity,htrB,hdetB]
  have hab : A*B=μ • A+(2*μ) • B-(2*μ^2) • (1 : M2) := by
    rw [Matrix.mul_sub,haa,smul_sub] at hAN
    ext i j
    have hh := congrFun (congrFun hAN i) j
    simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] at hh ⊢
    linear_combination hh
  have hba : B*A=(2*μ) • A+μ • B-(2*μ^2) • (1 : M2) := by
    rw [Matrix.sub_mul,haa,smul_sub] at hNA
    ext i j
    have hh := congrFun (congrFun hNA i) j
    simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] at hh ⊢
    linear_combination hh
  have huu : U*U=μ • U := by
    dsimp [U]
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.one_mul,Matrix.mul_one,haa]
    module
  have huv : U*V=μ • V := by
    dsimp [U,V]
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.one_mul,Matrix.mul_one,hab]
    module
  have hvu : V*U=μ • U := by
    dsimp [U,V]
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.one_mul,Matrix.mul_one,hba]
    module
  have hvv : V*V=μ • V := by
    dsimp [V]
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.one_mul,Matrix.mul_one,hbb]
    module
  have hSS : S*S=(2*μ) • S := by
    dsimp [S]
    rw [Matrix.add_mul,Matrix.mul_add,Matrix.mul_add,huu,huv,hvu,hvv]
    module
  have hspos (i j : Fin 2) (hne : i ≠ j)
      (hij : 0 < ((A+B)+(E+F+G)) i j) : 0 < S i j := by
    have hn : 0 ≤ A i j+B i j := add_nonneg (hA i j) (hB i j)
    rw [hE,hF,hG] at hij
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply_ne hne,mul_zero,sub_zero] at hij
    have hp : 0 < A i j+B i j := by
      by_contra hh
      have hz : A i j+B i j=0 := by linarith only [hn,hh]
      simp only [two_smul] at hij
      have hz' := congrArg (fun x : ℝ => (1+3*t)*x) hz
      nlinarith only [hij,hz']
    simpa only [S,U,V,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply_ne hne,mul_zero,sub_zero] using hp
  let w : Vec (Fin 2) := (fun _ => 1) ᵥ* S
  have hw : ∀ i, 0 < w i := by
    intro i
    fin_cases i
    · change 0 < w 0
      dsimp [w]
      simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two,one_mul]
      exact add_pos_of_nonneg_of_pos (hS 0 0) (hspos 1 0 (by decide) h10)
    · change 0 < w 1
      dsimp [w]
      simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two,one_mul]
      exact add_pos_of_pos_of_nonneg (hspos 0 1 (by decide) h01) (hS 1 1)
  have hwS : w ᵥ* S=(2*μ) • w := by
    dsimp [w]
    rw [vecMul_vecMul,hSS,vecMul_smul]
  have hP : A+B=S+(2*μ) • (1 : M2) := by rw [ha,hb]; dsimp [S]; module
  have hT : E+F+G=(3*t) • (S+μ • (1 : M2)) := by
    rw [hE,hF,hG,ha,hb]
    dsimp [S]
    module
  refine ⟨w,hw,?_,?_⟩
  · rw [hP,vecMul_add,vecMul_smul,vecMul_one,hwS]
    module
  · rw [hT,vecMul_smul,vecMul_add,vecMul_smul,vecMul_one,hwS]
    module

theorem ordered_rows_equal_of_positive_dot (p q u : Vec (Fin 2))
    (hpq : p ≤ q) (hu : ∀ i, 0 < u i) (he : p ⬝ᵥ u=q ⬝ᵥ u) : p=q := by
  have hz : (q-p) ⬝ᵥ u=0 := by rw [sub_dotProduct,he,sub_self]
  have hn (i : Fin 2) : 0 ≤ (q i-p i)*u i :=
    mul_nonneg (sub_nonneg.mpr (hpq i)) (hu i).le
  have hi (i : Fin 2) : (q i-p i)*u i=0 :=
    congrFun ((Fintype.sum_eq_zero_iff_of_nonneg hn).mp hz) i
  funext i
  exact (sub_eq_zero.mp ((mul_eq_zero.mp (hi i)).resolve_right (ne_of_gt (hu i)))).symm

end CollatzCertificate.TwoDimensionalUnitEigen

#print axioms CollatzCertificate.TwoDimensionalUnitEigen.nonsingular_shape_positive_left_aggregate
#print axioms CollatzCertificate.TwoDimensionalUnitEigen.ordered_rows_equal_of_positive_dot
