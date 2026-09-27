import FullTwoMatrixAggregate
import ReversedTwoDimensionalMiddleRank

namespace CollatzCertificate.FullTwoMatrix

open Matrix TwoDimensionalSwapAlgebra TwoDimensionalMiddleRank

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

theorem matrix_unit_of_det (A : M2) (h : A.det ≠ 0) : IsUnit A :=
  A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr h)

theorem tr_eq_trace (A : M2) : tr A = Matrix.trace A := by
  simp [tr, Matrix.trace, Fin.sum_univ_two]

theorem trace_of_intertwining (X Y Q : M2) (hq : Q.det ≠ 0) (h : X * Q = Q * Y) :
    tr X = tr Y := by
  have hi := Q.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hq)
  have hxy : X = Q * Y * Q⁻¹ := by
    calc
      X = (X * Q) * Q⁻¹ := by rw [Matrix.mul_assoc, hi, Matrix.mul_one]
      _ = (Q * Y) * Q⁻¹ := by rw [h]
  rw [tr_eq_trace, tr_eq_trace, hxy, Matrix.trace_mul_cycle]
  rw [Q.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hq), Matrix.one_mul]

theorem tr_square (A : M2) : tr (A * A) = (tr A)^2 - 2*A.det := by
  simp [tr, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem det_sub_identity (A B : M2) :
    (B-A).det = A.det+B.det+tr (A*B)-tr A*tr B := by
  simp [tr, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem nonsingular_binary_invariants (A B E F G : M2)
    (h : ExactSwaps A B E F G)
    (hB : B.det ≠ 0) (hE : E.det ≠ 0) (hG : G.det ≠ 0)
    (htrA : 0 < tr A) (htrB : 0 < tr B) :
    A.det = B.det ∧ tr A = tr B ∧ tr (A*B) = tr (A*A) ∧
      tr (B-A) = 0 ∧ (B-A).det = 0 ∧ tr (A*(B-A)) = 0 := by
  rcases h with ⟨hae,haf,hag,hbe,hbf,hbg⟩
  have hef : E.det = F.det := by
    have hh := congrArg Matrix.det hbe
    simp only [Matrix.det_mul] at hh
    exact mul_left_cancel₀ hB (by simpa only [mul_comm] using hh)
  have hab : A.det = B.det := by
    have hh := congrArg Matrix.det haf
    simp only [Matrix.det_mul, ← hef] at hh
    exact mul_right_cancel₀ hE (by simpa only [mul_comm] using hh)
  have hEBB : (A*B)*E = E*(B*B) := by
    calc
      (A*B)*E = A*(B*E) := Matrix.mul_assoc _ _ _
      _ = A*(F*B) := by rw [hbe]
      _ = (A*F)*B := (Matrix.mul_assoc _ _ _).symm
      _ = (E*B)*B := by rw [haf]
      _ = E*(B*B) := Matrix.mul_assoc _ _ _
  have hGAA : (B*A)*G = G*(A*A) := by
    calc
      (B*A)*G = B*(A*G) := Matrix.mul_assoc _ _ _
      _ = B*(F*A) := by rw [hag]
      _ = (B*F)*A := (Matrix.mul_assoc _ _ _).symm
      _ = (G*A)*A := by rw [hbf]
      _ = G*(A*A) := Matrix.mul_assoc _ _ _
  have htB := trace_of_intertwining (A*B) (B*B) E hE hEBB
  have htA := trace_of_intertwining (B*A) (A*A) G hG hGAA
  rw [trace_product_commutes B A] at htA
  have habtr : tr A = tr B := by
    have hh : (tr A)^2 = (tr B)^2 := by
      rw [tr_square] at htA htB
      nlinarith only [htA,htB,hab]
    nlinarith only [hh,htrA,htrB]
  refine ⟨hab,habtr,htA,?_,?_,?_⟩
  · simp only [tr, Matrix.sub_apply]
    simp only [tr] at habtr
    linarith only [habtr]
  · rw [det_sub_identity, htA, tr_square, hab, habtr]
    ring
  · simp only [Matrix.mul_sub, tr, Matrix.sub_apply]
    simp only [tr] at htA
    linarith only [htA]

theorem centralizer_scalar_or_span (A E : M2) (h : A*E=E*A) :
    (∃ a : ℝ, A=a • (1 : M2)) ∨ ∃ x y : ℝ, E=x • (1 : M2)+y • A := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  by_cases ha01 : A 0 1 = 0
  · simp only [ha01,zero_mul,mul_zero,zero_add,add_zero] at h00 h01 h10 h11
    by_cases ha10 : A 1 0 = 0
    · simp only [ha10,zero_mul,mul_zero,zero_add,add_zero] at h00 h01 h10 h11
      by_cases hd : A 0 0 = A 1 1
      · left
        refine ⟨A 0 0, ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;> simp [ha01,ha10,hd]
      · right
        refine ⟨E 0 0-(E 0 0-E 1 1)/(A 0 0-A 1 1)*A 0 0,
          (E 0 0-E 1 1)/(A 0 0-A 1 1), ?_⟩
        have hn : A 0 0-A 1 1 ≠ 0 := sub_ne_zero.mpr hd
        have he01 : E 0 1=0 := by
          apply (mul_eq_zero.mp (show (A 0 0-A 1 1)*E 0 1=0 by nlinarith only [h01,ha01])).resolve_left hn
        have he10 : E 1 0=0 := by
          apply (mul_eq_zero.mp (show (A 0 0-A 1 1)*E 1 0=0 by nlinarith only [h10,ha10])).resolve_left hn
        ext i j
        fin_cases i <;> fin_cases j <;> simp [ha01,ha10,he01,he10] <;>
          (try field_simp) <;> nlinarith only [h00,h01,h10,h11,ha01,ha10]
    · right
      refine ⟨E 0 0-E 1 0/A 1 0*A 0 0, E 1 0/A 1 0, ?_⟩
      have he01 : E 0 1=0 := by
        apply (mul_eq_zero.mp (show E 0 1*A 1 0=0 by nlinarith only [h00,ha01])).resolve_right ha10
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha01,he01] <;>
        (try field_simp) <;> nlinarith only [h00,h01,h10,h11,ha01]
  · right
    refine ⟨E 0 0-E 0 1/A 0 1*A 0 0, E 0 1/A 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;>
      (try field_simp) <;> nlinarith only [h00,h01,h10,h11]

theorem nilpotent_invariant_image (A N : M2)
    (hN : N ≠ 0) (ht : tr N=0) (hd : N.det=0) (hat : tr (A*N)=0) :
    ∃ a : ℝ, A*N=a • N := by
  have hn2 : N*N=0 := by simp only [square_trace_identity, ht,hd,zero_smul,sub_self]
  have hnAn : N*A*N=0 := by
    rw [sandwich_trace_identity,trace_product_commutes N A,hat,hd]
    simp
  have hc : N*(A*N)=(A*N)*N := by
    rw [← Matrix.mul_assoc,hnAn,Matrix.mul_assoc,hn2,Matrix.mul_zero]
  rcases centralizer_scalar_or_span N (A*N) hc with ⟨n,hn⟩ | ⟨x,a,ha⟩
  · have hn0 : n=0 := by simp [hn,tr] at ht; linarith only [ht]
    exact False.elim (hN (by simpa only [hn0,zero_smul] using hn))
  · have hx : x=0 := by
      have hh := congrArg tr ha
      simp [tr, ht, hat] at hh
      simp only [tr] at ht hat
      linear_combination (hat-hh-a*ht)/2
    exact ⟨a,by simpa only [hx,zero_smul,zero_add] using ha⟩

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.matrix_unit_of_det
#print axioms CollatzCertificate.FullTwoMatrix.tr_eq_trace
#print axioms CollatzCertificate.FullTwoMatrix.trace_of_intertwining
#print axioms CollatzCertificate.FullTwoMatrix.tr_square
#print axioms CollatzCertificate.FullTwoMatrix.det_sub_identity
#print axioms CollatzCertificate.FullTwoMatrix.nonsingular_binary_invariants
#print axioms CollatzCertificate.FullTwoMatrix.centralizer_scalar_or_span
#print axioms CollatzCertificate.FullTwoMatrix.nilpotent_invariant_image
