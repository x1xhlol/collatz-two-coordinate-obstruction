import ReversedTwoDimensionalNonsingularEigenBasic
import FullTwoMatrixNonsingularBoundary

namespace CollatzCertificate.TwoDimensionalNonsingularEigen

open Matrix FullTwoMatrix TwoDimensionalMiddleRank TwoDimensionalInvertibleMiddle
open TwoDimensionalSwapAlgebra (tr)

set_option maxHeartbeats 1000000

theorem positive_offdiagonal_of_return (H : M2) (hH : EntrywiseLE 0 H)
    (i j : Fin 2) (hne : i ≠ j) (hreturn : ∃ k : ℕ, 0 < (H^k) i j) :
    0 < H i j := by
  have hn : 0 ≤ H i j := hH i j
  by_contra hp
  have hz : H i j=0 := le_antisymm (le_of_not_gt hp) hn
  have hpow (n : ℕ) : (H^n) i j=0 := by
    induction n with
    | zero => rw [pow_zero,Matrix.one_apply_ne hne]
    | succ n ih =>
      rw [pow_succ]
      fin_cases i <;> fin_cases j
      · exact False.elim (hne rfl)
      · change H 0 1=0 at hz
        change (H^n) 0 1=0 at ih
        change ((H^n)*H) 0 1=0
        simp only [Matrix.mul_apply,Fin.sum_univ_two,hz,ih,mul_zero,zero_mul,add_zero]
      · change H 1 0=0 at hz
        change (H^n) 1 0=0 at ih
        change ((H^n)*H) 1 0=0
        simp only [Matrix.mul_apply,Fin.sum_univ_two,hz,ih,mul_zero,zero_mul,add_zero]
      · exact False.elim (hne rfl)
  obtain ⟨k,hk⟩ := hreturn
  rw [hpow k] at hk
  exact (lt_irrefl 0) hk

theorem nonsingular_shape_positive_eigenvector (A B E F G : M2) (μ t : ℝ)
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
    ∃ u : Vec (Fin 2), (∀ i, 0 < u i) ∧
      A *ᵥ u=(2*μ) • u ∧ B *ᵥ u=(2*μ) • u ∧
      E *ᵥ u=(3*t*μ) • u ∧ F *ᵥ u=(3*t*μ) • u ∧ G *ᵥ u=(3*t*μ) • u := by
  let U := A-μ • (1 : M2)
  let V := B-μ • (1 : M2)
  let S := U+V
  have hU := shifted_matrix_nonnegative A μ hμ hA htrA hdetA
  have hV := shifted_matrix_nonnegative B μ hμ hB htrB hdetB
  have hS : EntrywiseLE 0 S := fun i j => add_nonneg (hU i j) (hV i j)
  have ha : A=U+μ • (1 : M2) := by dsimp [U]; module
  have hb : B=V+μ • (1 : M2) := by dsimp [V]; module
  have he : E=t • (2 • U+μ • (1 : M2)) := by rw [hE,ha]; module
  have hf : F=t • (U+V+μ • (1 : M2)) := by rw [hF,ha,hb]; module
  have hg : G=t • (2 • V+μ • (1 : M2)) := by rw [hG,hb]; module
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
  have hUS : U*S=μ • S := by dsimp [S]; rw [Matrix.mul_add,huu,huv,smul_add]
  have hVS : V*S=μ • S := by dsimp [S]; rw [Matrix.mul_add,hvu,hvv,smul_add]
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
  let u : Vec (Fin 2) := S *ᵥ (fun _ => 1)
  have hu : ∀ i, 0 < u i := by
    intro i
    fin_cases i
    · change 0 < u 0
      dsimp [u]
      simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,mul_one]
      exact add_pos_of_nonneg_of_pos (hS 0 0) (hspos 0 1 (by decide) h01)
    · change 0 < u 1
      dsimp [u]
      simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,mul_one]
      exact add_pos_of_pos_of_nonneg (hspos 1 0 (by decide) h10) (hS 1 1)
  have hUu : U *ᵥ u=μ • u := by dsimp [u]; rw [mulVec_mulVec,hUS,smul_mulVec]
  have hVu : V *ᵥ u=μ • u := by dsimp [u]; rw [mulVec_mulVec,hVS,smul_mulVec]
  refine ⟨u,hu,?_,?_,?_,?_,?_⟩
  · rw [ha,add_mulVec,smul_mulVec,one_mulVec,hUu]
    module
  · rw [hb,add_mulVec,smul_mulVec,one_mulVec,hVu]
    module
  · rw [he,smul_mulVec,add_mulVec,smul_mulVec,smul_mulVec,one_mulVec,hUu]
    module
  · rw [hf,smul_mulVec,add_mulVec,add_mulVec,smul_mulVec,one_mulVec,hUu,hVu]
    module
  · rw [hg,smul_mulVec,add_mulVec,smul_mulVec,smul_mulVec,one_mulVec,hVu]
    module

theorem nonsingular_common_positive_eigenvector (A B E F G : M2)
    (h : ReversedExactSwaps A B E F G)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B)
    (hE : EntrywiseLE 0 E) (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (ha : A.det ≠ 0) (hf : F.det ≠ 0) (hne : A*B ≠ B*A)
    (hreturn : ∀ i j : Fin 2, ∃ k : ℕ, 0 < (((A+B)+(E+F+G))^k) j i) :
    ∃ μ κ : ℝ, ∃ u : Vec (Fin 2), 0 < μ ∧ 0 < κ ∧ (∀ i, 0 < u i) ∧
      A *ᵥ u=(2*μ) • u ∧ B *ᵥ u=(2*μ) • u ∧
      E *ᵥ u=(3*κ) • u ∧ F *ᵥ u=(3*κ) • u ∧ G *ᵥ u=(3*κ) • u := by
  obtain ⟨μ,t,hμ,ht,htrA,htrB,hdetA,hdetB,hAN,hNA,he,hfshape,hg⟩ :=
    reversed_nonsingular_unequal_shape A B E F G h hA hB hE hF hG ha hf hne
  have hH : EntrywiseLE 0 ((A+B)+(E+F+G)) := fun i j =>
    add_nonneg (add_nonneg (hA i j) (hB i j))
      (add_nonneg (add_nonneg (hE i j) (hF i j)) (hG i j))
  have h01 := positive_offdiagonal_of_return _ hH 0 1 (by decide) (hreturn 1 0)
  have h10 := positive_offdiagonal_of_return _ hH 1 0 (by decide) (hreturn 0 1)
  obtain ⟨u,hu,hAu,hBu,hEu,hFu,hGu⟩ := nonsingular_shape_positive_eigenvector A B E F G
    μ t hμ hA hB htrA htrB hdetA hdetB hAN hNA he hfshape hg h01 h10
  refine ⟨μ,t*μ,u,hμ,mul_pos ht hμ,hu,hAu,hBu,?_,?_,?_⟩
  · simpa only [mul_assoc] using hEu
  · simpa only [mul_assoc] using hFu
  · simpa only [mul_assoc] using hGu

end CollatzCertificate.TwoDimensionalNonsingularEigen

#print axioms CollatzCertificate.TwoDimensionalNonsingularEigen.positive_offdiagonal_of_return
#print axioms CollatzCertificate.TwoDimensionalNonsingularEigen.nonsingular_shape_positive_eigenvector
#print axioms CollatzCertificate.TwoDimensionalNonsingularEigen.nonsingular_common_positive_eigenvector
