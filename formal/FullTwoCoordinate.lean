import FullTwoTriangular
import FullTwoMatrixReduction

namespace CollatzResearch.FullTwo

open CollatzCertificate

theorem forward_all_gaps_zero (A B C D E F G : Aff2)
    (hA : Admissible A) (hB : Admissible B) (hC : Admissible C) (hD : Admissible D)
    (hE : Admissible E) (hF : Admissible F) (hG : Admissible G)
    (h : ForwardWeak A B C D E F G) : ForwardGapsZero A B C D E F G := by
  have hm := forward_matrix_rules A B C D E F G h
  have ht := FullTwoMatrix.forward_common_orientation
    A.matrix B.matrix C.matrix D.matrix E.matrix F.matrix G.matrix
    hA.1.1 hB.1.1 hC.1.1 hD.1.1 hE.1.1 hF.1.1 hG.1.1
    hA.2 hB.2 hC.2 hD.2 hE.2 hF.2 hG.2 hm
  exact forward_gaps_zero_of_triangular A B C D E F G hA hB hC hD hE hF hG h ht

theorem reversed_all_gaps_zero (A B C D E F G : Aff2)
    (hA : Admissible A) (hB : Admissible B) (hC : Admissible C) (hD : Admissible D)
    (hE : Admissible E) (hF : Admissible F) (hG : Admissible G)
    (h : ReversedRealWeak A B C D E F G) : ReversedGapsZero A B C D E F G := by
  have hm := reversed_matrix_rules A B C D E F G h
  have ht := FullTwoMatrix.reversed_common_orientation_and_first_diagonals
    A.matrix B.matrix C.matrix D.matrix E.matrix F.matrix G.matrix
    hA.1.1 hB.1.1 hC.1.1 hD.1.1 hE.1.1 hF.1.1 hG.1.1
    hA.2 hB.2 hC.2 hD.2 hE.2 hF.2 hG.2 hm
  exact reversed_gaps_zero_of_triangular A B C D E F G hA hB hC hD hE hF hG h ht.1

theorem full_two_coordinate_obstruction (A B C D E F G : Aff2)
    (hA : Admissible A) (hB : Admissible B) (hC : Admissible C) (hD : Admissible D)
    (hE : Admissible E) (hF : Admissible F) (hG : Admissible G) :
    (ForwardWeak A B C D E F G → ForwardGapsZero A B C D E F G) ∧
    (ReversedRealWeak A B C D E F G → ReversedGapsZero A B C D E F G) :=
  ⟨forward_all_gaps_zero A B C D E F G hA hB hC hD hE hF hG,
   reversed_all_gaps_zero A B C D E F G hA hB hC hD hE hF hG⟩

end CollatzResearch.FullTwo

#print axioms CollatzResearch.FullTwo.forward_all_gaps_zero
#print axioms CollatzResearch.FullTwo.reversed_all_gaps_zero
#print axioms CollatzResearch.FullTwo.full_two_coordinate_obstruction
