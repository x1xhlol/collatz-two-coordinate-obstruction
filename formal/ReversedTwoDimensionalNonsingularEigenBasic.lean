import ReversedTwoDimensionalInvertibleMiddleBasic
import FullTwoMatrixDeterminants
import FullTwoMatrixNonsingularShape

namespace CollatzCertificate.TwoDimensionalNonsingularEigen

open Matrix FullTwoMatrix TwoDimensionalMiddleRank TwoDimensionalInvertibleMiddle
open TwoDimensionalSwapAlgebra (tr)

set_option maxHeartbeats 800000

theorem nonnegative_zero_trace_diagonals (M : M2)
    (hM : EntrywiseLE 0 M) (ht : tr M=0) : M 0 0=0 ∧ M 1 1=0 := by
  have h0 : 0 ≤ M 0 0 := hM 0 0
  have h1 : 0 ≤ M 1 1 := hM 1 1
  simp only [tr] at ht
  constructor <;> linarith only [ht,h0,h1]

theorem commuting_zero_diagonal_forces_equal_diagonals (A E : M2)
    (he0 : E 0 0=0) (he1 : E 1 1=0) (he : E.det ≠ 0)
    (h : A*E=E*A) : A 0 0=A 1 1 := by
  have he01 : E 0 1 ≠ 0 := by
    intro hz
    apply he
    simp only [Matrix.det_fin_two,he0,he1,hz,zero_mul,sub_self]
  have hh := congrFun (congrFun h 0) 1
  simp only [Matrix.mul_apply,Fin.sum_univ_two,he0,he1,mul_zero,zero_mul,
    add_zero,zero_add] at hh
  exact mul_right_cancel₀ he01 (by simpa only [mul_comm] using hh)

theorem equal_diagonals_intertwining_zero_diagonals (B E F : M2)
    (hb : B 0 0=B 1 1) (hb0 : B 0 0 ≠ 0)
    (he0 : E 0 0=0) (he1 : E 1 1=0)
    (hf0 : F 0 0=0) (hf1 : F 1 1=0)
    (h : B*E=F*B) : E=F := by
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply,Fin.sum_univ_two,he0,he1,hf0,hf1,
    mul_zero,zero_mul,add_zero,zero_add,← hb] at h01 h10
  have e01 : E 0 1=F 0 1 :=
    mul_left_cancel₀ hb0 (by simpa only [mul_comm] using h01)
  have e10 : E 1 0=F 1 0 :=
    mul_left_cancel₀ hb0 (by simpa only [mul_comm] using h10)
  ext i j
  fin_cases i <;> fin_cases j
  · exact he0.trans hf0.symm
  · exact e01
  · exact e10
  · exact he1.trans hf1.symm

theorem forward_positive_ternary_trace (A B E F G : M2)
    (h : ExactSwaps A B E F G)
    (ha : A.det ≠ 0) (hb : B.det ≠ 0)
    (hf : F.det ≠ 0) (hg : G.det ≠ 0)
    (hE : EntrywiseLE 0 E) (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (htB : 0 < tr B) (hne : A ≠ B) : 0 < tr E := by
  have htFE := trace_of_intertwining F E B hb h.2.2.2.1.symm
  have htFG := trace_of_intertwining F G A ha h.2.2.1.symm
  by_contra hn
  have htE : tr E=0 := le_antisymm (le_of_not_gt hn)
    (add_nonneg (hE 0 0) (hE 1 1))
  have htF : tr F=0 := htFE.trans htE
  have htG : tr G=0 := htFG.symm.trans htF
  obtain ⟨he0,he1⟩ := nonnegative_zero_trace_diagonals E hE htE
  obtain ⟨hf0,hf1⟩ := nonnegative_zero_trace_diagonals F hF htF
  obtain ⟨hg0,hg1⟩ := nonnegative_zero_trace_diagonals G hG htG
  have hBdiag := commuting_zero_diagonal_forces_equal_diagonals B G hg0 hg1 hg h.2.2.2.2.2
  have hB0 : B 0 0 ≠ 0 := by
    intro hz
    simp only [tr,← hBdiag,hz,add_zero,lt_self_iff_false] at htB
  have hef := equal_diagonals_intertwining_zero_diagonals B E F hBdiag hB0
    he0 he1 hf0 hf1 h.2.2.2.1
  apply hne
  apply (matrix_unit_of_det F hf).mul_left_cancel
  calc
    F*A = A*F := by simpa only [hef] using h.1.symm
    _ = F*B := by simpa only [hef] using h.2.1

theorem reversed_nonsingular_unequal_shape (A B E F G : M2)
    (h : ReversedExactSwaps A B E F G)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B)
    (hE : EntrywiseLE 0 E) (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (ha : A.det ≠ 0) (hf : F.det ≠ 0) (hne : A*B ≠ B*A) :
    ∃ μ t : ℝ, 0 < μ ∧ 0 < t ∧ tr A=3*μ ∧ tr B=3*μ ∧
      A.det=2*μ^2 ∧ B.det=2*μ^2 ∧
      A*(B-A)=(2*μ) • (B-A) ∧ (B-A)*A=μ • (B-A) ∧
      E=t • (2 • A-μ • (1 : M2)) ∧
      F=t • (A+B-μ • (1 : M2)) ∧ G=t • (2 • B-μ • (1 : M2)) := by
  have hs := reversed_exact_swaps_transpose A B E F G h
  have ha' : Aᵀ.det ≠ 0 := by simpa only [Matrix.det_transpose] using ha
  have hf' : Fᵀ.det ≠ 0 := by simpa only [Matrix.det_transpose] using hf
  have hA' : EntrywiseLE 0 Aᵀ := fun i j => hA j i
  have hB' : EntrywiseLE 0 Bᵀ := fun i j => hB j i
  obtain ⟨htA,htB⟩ := positive_binary_traces_of_noncommuting A B E F G h hf hA hB hne
  have hneq : Aᵀ ≠ Bᵀ := by
    intro heq
    have hh : A=B := by simpa only [transpose_transpose] using congrArg Matrix.transpose heq
    exact hne (by rw [hh])
  obtain ⟨_,hb',he',hg'⟩ := (invertible_middle_determinant_cases Aᵀ Bᵀ Eᵀ Fᵀ Gᵀ hs hf').resolve_left
    (fun hz => ha' hz.1)
  have htE := forward_positive_ternary_trace Aᵀ Bᵀ Eᵀ Fᵀ Gᵀ hs ha' hb' hf' hg'
    (fun i j => hE j i) (fun i j => hF j i) (fun i j => hG j i) htB hneq
  obtain ⟨hd,ht,_,_⟩ := forward_binary_invariants Aᵀ Bᵀ Eᵀ Fᵀ Gᵀ hs hf' hA' hB'
  obtain ⟨μ,t,hμ,htt,htr,hdet,hAN,hNA,hes,hfs,hgs⟩ :=
    nonsingular_unequal_shape Aᵀ Bᵀ Eᵀ Fᵀ Gᵀ hs ha' hb' he' hg' htA htB htE hneq
  refine ⟨μ,t,hμ,htt,htr,ht.symm.trans htr,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Matrix.det_transpose] using hdet
  · simpa only [Matrix.det_transpose] using hd.symm.trans hdet
  · simpa only [transpose_mul,transpose_sub,transpose_smul,transpose_transpose] using
      congrArg Matrix.transpose hNA
  · simpa only [transpose_mul,transpose_sub,transpose_smul,transpose_transpose] using
      congrArg Matrix.transpose hAN
  · simpa only [transpose_sub,transpose_smul,transpose_transpose,transpose_one] using
      congrArg Matrix.transpose hes
  · simpa only [transpose_sub,transpose_add,transpose_smul,transpose_transpose,transpose_one] using
      congrArg Matrix.transpose hfs
  · simpa only [transpose_sub,transpose_smul,transpose_transpose,transpose_one] using
      congrArg Matrix.transpose hgs

end CollatzCertificate.TwoDimensionalNonsingularEigen

#print axioms CollatzCertificate.TwoDimensionalNonsingularEigen.nonnegative_zero_trace_diagonals
#print axioms CollatzCertificate.TwoDimensionalNonsingularEigen.commuting_zero_diagonal_forces_equal_diagonals
#print axioms CollatzCertificate.TwoDimensionalNonsingularEigen.equal_diagonals_intertwining_zero_diagonals
#print axioms CollatzCertificate.TwoDimensionalNonsingularEigen.forward_positive_ternary_trace
#print axioms CollatzCertificate.TwoDimensionalNonsingularEigen.reversed_nonsingular_unequal_shape
