import FullTwoMatrixSingularBinaryShape

namespace CollatzCertificate.TwoDimensionalInvertibleMiddle

open Matrix TwoDimensionalMiddleRank FullTwoMatrix
open TwoDimensionalSwapAlgebra (tr)

set_option maxHeartbeats 800000

def ReversedExactSwaps (A B E F G : M2) : Prop :=
  E*A=A*E ∧ F*A=B*E ∧ G*A=A*F ∧
  E*B=B*F ∧ F*B=A*G ∧ G*B=B*G

theorem reversed_exact_swaps_transpose (A B E F G : M2)
    (h : ReversedExactSwaps A B E F G) : ExactSwaps Aᵀ Bᵀ Eᵀ Fᵀ Gᵀ := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
  exact ⟨by simpa only [transpose_mul] using congrArg Matrix.transpose h1,
    by simpa only [transpose_mul] using congrArg Matrix.transpose h2,
    by simpa only [transpose_mul] using congrArg Matrix.transpose h3,
    by simpa only [transpose_mul] using congrArg Matrix.transpose h4,
    by simpa only [transpose_mul] using congrArg Matrix.transpose h5,
    by simpa only [transpose_mul] using congrArg Matrix.transpose h6⟩

theorem forward_binary_invariants (A B E F G : M2)
    (h : ExactSwaps A B E F G) (hf : F.det ≠ 0)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) :
    A.det=B.det ∧ tr A=tr B ∧
      (A*B)*F=F*(A*A) ∧ (B*A)*F=F*(B*B) := by
  have haf := congrArg Matrix.det h.2.1
  have hbe := congrArg Matrix.det h.2.2.2.1
  simp only [Matrix.det_mul] at haf hbe
  have hd : A.det=B.det := by
    apply mul_right_cancel₀ hf
    nlinarith only [haf,hbe]
  have hABF : (A*B)*F=F*(A*A) := by
    rw [Matrix.mul_assoc,h.2.2.2.2.1,← Matrix.mul_assoc,h.2.2.1,Matrix.mul_assoc]
  have hBAF : (B*A)*F=F*(B*B) := by
    rw [Matrix.mul_assoc,h.2.1,← Matrix.mul_assoc,h.2.2.2.1,Matrix.mul_assoc]
  have ht1 := trace_of_intertwining (A*B) (A*A) F hf hABF
  have ht2 := trace_of_intertwining (B*A) (B*B) F hf hBAF
  rw [trace_product_commutes B A] at ht2
  rw [tr_square] at ht1 ht2
  have htA : 0 ≤ tr A := add_nonneg (hA 0 0) (hA 1 1)
  have htB : 0 ≤ tr B := add_nonneg (hB 0 0) (hB 1 1)
  have ht : tr A=tr B := by nlinarith only [ht1,ht2,hd,htA,htB]
  exact ⟨hd,ht,hABF,hBAF⟩

theorem forward_positive_binary_traces_or_commute (A B E F G : M2)
    (h : ExactSwaps A B E F G) (hf : F.det ≠ 0)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) :
    (0 < tr A ∧ 0 < tr B) ∨ A*B=B*A := by
  obtain ⟨hd,ht,hABF,hBAF⟩ := forward_binary_invariants A B E F G h hf hA hB
  by_cases hp : 0 < tr A
  · exact Or.inl ⟨hp,ht ▸ hp⟩
  · right
    have htA : tr A=0 := le_antisymm (le_of_not_gt hp) (add_nonneg (hA 0 0) (hA 1 1))
    have htB : tr B=0 := ht ▸ htA
    have haa : A*A=-(A.det • (1 : M2)) := by
      rw [square_trace_identity,htA,zero_smul,zero_sub]
    have hbb : B*B=-(A.det • (1 : M2)) := by
      rw [square_trace_identity,htB,zero_smul,zero_sub,← hd]
    apply (matrix_unit_of_det F hf).mul_right_cancel
    rw [hABF,hBAF,haa,hbb]

theorem positive_binary_traces_or_commute (A B E F G : M2)
    (h : ReversedExactSwaps A B E F G) (hf : F.det ≠ 0)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) :
    (0 < tr A ∧ 0 < tr B) ∨ A*B=B*A := by
  have hs := reversed_exact_swaps_transpose A B E F G h
  have hf' : Fᵀ.det ≠ 0 := by simpa only [Matrix.det_transpose] using hf
  rcases forward_positive_binary_traces_or_commute Aᵀ Bᵀ Eᵀ Fᵀ Gᵀ hs hf'
      (fun i j => hA j i) (fun i j => hB j i) with hp | hc
  · exact Or.inl hp
  · right
    simpa only [transpose_mul,transpose_transpose] using congrArg Matrix.transpose hc.symm

theorem positive_binary_traces_of_noncommuting (A B E F G : M2)
    (h : ReversedExactSwaps A B E F G) (hf : F.det ≠ 0)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hne : A*B ≠ B*A) :
    0 < tr A ∧ 0 < tr B :=
  (positive_binary_traces_or_commute A B E F G h hf hA hB).resolve_right hne

end CollatzCertificate.TwoDimensionalInvertibleMiddle

#print axioms CollatzCertificate.TwoDimensionalInvertibleMiddle.reversed_exact_swaps_transpose
#print axioms CollatzCertificate.TwoDimensionalInvertibleMiddle.forward_binary_invariants
#print axioms CollatzCertificate.TwoDimensionalInvertibleMiddle.forward_positive_binary_traces_or_commute
#print axioms CollatzCertificate.TwoDimensionalInvertibleMiddle.positive_binary_traces_or_commute
#print axioms CollatzCertificate.TwoDimensionalInvertibleMiddle.positive_binary_traces_of_noncommuting
