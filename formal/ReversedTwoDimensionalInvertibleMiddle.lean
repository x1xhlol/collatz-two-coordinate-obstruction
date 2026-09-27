import ReversedTwoDimensionalInvertibleMiddleSingular

namespace CollatzCertificate.TwoDimensionalInvertibleMiddle

open Matrix TwoDimensionalMiddleRank FullTwoMatrix
open TwoDimensionalSwapAlgebra (tr)

set_option maxHeartbeats 800000

theorem singular_binary_dichotomy (A B E F G : M2)
    (h : ReversedExactSwaps A B E F G)
    (ha : A.det=0) (hb : B.det=0) (hf : F.det ≠ 0)
    (htA : 0 < tr A) (htB : 0 < tr B) (hF : EntrywiseLE 0 F) (hne : A ≠ B) :
    ∃ α : ℝ, 0 < α ∧ tr A=α ∧ tr B=α ∧
      ((B*A=α • B ∧ A*B=α • A) ∨
        ∃ β : ℝ, 0 < β ∧ A*A=α • A ∧ A*B=α • B ∧
          B*A=α • A ∧ B*B=α • B ∧
          F=β • (1 : M2) ∧ E=(β/α) • A ∧ G=(β/α) • B) := by
  have hs := reversed_exact_swaps_transpose A B E F G h
  have ha' : Aᵀ.det=0 := by simpa only [Matrix.det_transpose] using ha
  have hb' : Bᵀ.det=0 := by simpa only [Matrix.det_transpose] using hb
  have hf' : Fᵀ.det ≠ 0 := by simpa only [Matrix.det_transpose] using hf
  have hne' : Aᵀ ≠ Bᵀ := by
    intro he
    apply hne
    simpa only [transpose_transpose] using congrArg Matrix.transpose he
  obtain ⟨α,hα,htα,htβ,heither⟩ := forward_singular_binary_dichotomy
    Aᵀ Bᵀ Eᵀ Fᵀ Gᵀ hs ha' hb' hf' htA htB (fun i j => hF j i) hne'
  have htα' : tr A=α := htα
  have htβ' : tr B=α := htβ
  refine ⟨α,hα,htα',htβ',?_⟩
  rcases heither with ⟨hab,hba⟩ | ⟨β,hβ,hab,hba,hfshape,heshape,hgshape⟩
  · left
    constructor
    · simpa only [transpose_mul,transpose_smul,transpose_transpose] using
        congrArg Matrix.transpose hab
    · simpa only [transpose_mul,transpose_smul,transpose_transpose] using
        congrArg Matrix.transpose hba
  · right
    refine ⟨β,hβ,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [square_trace_identity,ha,htα',zero_smul,sub_zero]
    · simpa only [transpose_mul,transpose_smul,transpose_transpose] using
        congrArg Matrix.transpose hba
    · simpa only [transpose_mul,transpose_smul,transpose_transpose] using
        congrArg Matrix.transpose hab
    · rw [square_trace_identity,hb,htβ',zero_smul,sub_zero]
    · simpa only [transpose_smul,transpose_transpose,transpose_one] using
        congrArg Matrix.transpose hfshape
    · simpa only [transpose_smul,transpose_transpose] using
        congrArg Matrix.transpose heshape
    · simpa only [transpose_smul,transpose_transpose] using
        congrArg Matrix.transpose hgshape

theorem shared_row_eigenvector (A B : M2) (r : Fin 2 → ℝ) (α : ℝ)
    (h : B*A=α • B) : (r ᵥ* B) ᵥ* A=α • (r ᵥ* B) := by
  rw [vecMul_vecMul,h,vecMul_smul]

theorem singular_binary_projection_of_no_shared_row (A B E F G : M2)
    (r : Fin 2 → ℝ)
    (h : ReversedExactSwaps A B E F G)
    (ha : A.det=0) (hb : B.det=0) (hf : F.det ≠ 0)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hF : EntrywiseLE 0 F)
    (hne : A*B ≠ B*A)
    (hrow : ∀ α : ℝ, 0 ≤ α → (r ᵥ* B) ᵥ* A ≠ α • (r ᵥ* B)) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ tr A=α ∧ tr B=α ∧
      A*A=α • A ∧ A*B=α • B ∧ B*A=α • A ∧ B*B=α • B ∧
      F=β • (1 : M2) ∧ E=(β/α) • A ∧ G=(β/α) • B := by
  obtain ⟨htA,htB⟩ := positive_binary_traces_of_noncommuting A B E F G h hf hA hB hne
  have hAB : A ≠ B := by intro he; exact hne (by rw [he])
  obtain ⟨α,hα,htα,htβ,heither⟩ := singular_binary_dichotomy A B E F G
    h ha hb hf htA htB hF hAB
  rcases heither with ⟨hba,_⟩ | ⟨β,hβ,haa,hab,hba,hbb,hfshape,heshape,hgshape⟩
  · exact False.elim (hrow α hα.le (shared_row_eigenvector A B r α hba))
  · exact ⟨α,β,hα,hβ,htα,htβ,haa,hab,hba,hbb,hfshape,heshape,hgshape⟩

end CollatzCertificate.TwoDimensionalInvertibleMiddle

#print axioms CollatzCertificate.TwoDimensionalInvertibleMiddle.singular_binary_dichotomy
#print axioms CollatzCertificate.TwoDimensionalInvertibleMiddle.shared_row_eigenvector
#print axioms CollatzCertificate.TwoDimensionalInvertibleMiddle.singular_binary_projection_of_no_shared_row
