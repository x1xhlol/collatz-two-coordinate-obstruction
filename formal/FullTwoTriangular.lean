import FullTwoUpperAffine
import FullTwoLowerForward
import FullTwoLowerReversed
import FullTwoMatrixTranspose

namespace CollatzResearch.FullTwo

open CollatzCertificate

theorem forward_matrix_rules (A B C D E F G : Aff2)
    (h : ForwardWeak A B C D E F G) :
    FullTwoMatrix.WeakRules A.matrix B.matrix C.matrix D.matrix E.matrix F.matrix G.matrix :=
  ⟨h.ad.1,h.bd.1,h.ae.1,h.af.1,h.ag.1,h.be.1,h.bf.1,h.bg.1,h.ce.1,h.cf.1,h.cg.1⟩

theorem reversed_matrix_rules (A B C D E F G : Aff2)
    (h : ReversedRealWeak A B C D E F G) :
    FullTwoMatrix.ReversedWeakRules A.matrix B.matrix C.matrix D.matrix E.matrix F.matrix G.matrix := by
  refine ⟨h.da.1,h.db.1,h.ea.1,h.fa.1,h.ga.1,h.eb.1,h.fb.1,h.gb.1,h.ec.1,?_,?_⟩
  · simpa only [Affine.comp,Matrix.mul_assoc] using h.fc.1
  · simpa only [Affine.comp,Matrix.mul_assoc] using h.gc.1

theorem forward_gaps_zero_of_triangular (A B C D E F G : Aff2)
    (hA : Admissible A) (hB : Admissible B) (hC : Admissible C) (hD : Admissible D)
    (hE : Admissible E) (hF : Admissible F) (hG : Admissible G)
    (w : ForwardWeak A B C D E F G)
    (ht : FullTwoMatrix.Upper A.matrix B.matrix E.matrix F.matrix G.matrix ∨
      FullTwoMatrix.Lower A.matrix B.matrix E.matrix F.matrix G.matrix) :
    ForwardGapsZero A B C D E F G := by
  have wm := forward_matrix_rules A B C D E F G w
  rcases ht with hu | hl
  · obtain ⟨a,b,e,f,g⟩ := FullTwoMatrix.upper_first_diagonals_one
      A.matrix B.matrix C.matrix D.matrix E.matrix F.matrix G.matrix
      hA.1.1 hB.1.1 hC.1.1 hD.1.1 hE.1.1 hF.1.1 hG.1.1 hA.2 hB.2 hC.2 hD.2 hF.2 wm hu
    exact upper_forward_gaps_zero A B C D E F G hA hB hC hD hE hF hG
      ⟨a,hu.1⟩ ⟨b,hu.2.1⟩ ⟨e,hu.2.2.1⟩ ⟨f,hu.2.2.2.1⟩ ⟨g,hu.2.2.2.2⟩ w
  · obtain ⟨a,b,e,f,g⟩ := FullTwoMatrix.lower_first_diagonals_one
      A.matrix B.matrix C.matrix D.matrix E.matrix F.matrix G.matrix
      hA.1.1 hB.1.1 hC.1.1 hD.1.1 hE.1.1 hF.1.1 hG.1.1 hA.2 hB.2 hC.2 hD.2 hF.2 wm hl
    exact FullTwoLower.lower_forward_gaps_zero A B C D E F G hA hB hC hD hE hF hG
      ⟨a,hl.1⟩ ⟨b,hl.2.1⟩ ⟨e,hl.2.2.1⟩ ⟨f,hl.2.2.2.1⟩ ⟨g,hl.2.2.2.2⟩ w

theorem reversed_gaps_zero_of_triangular (A B C D E F G : Aff2)
    (hA : Admissible A) (hB : Admissible B) (hC : Admissible C) (hD : Admissible D)
    (hE : Admissible E) (hF : Admissible F) (hG : Admissible G)
    (w : ReversedRealWeak A B C D E F G)
    (ht : FullTwoMatrix.Upper A.matrix B.matrix E.matrix F.matrix G.matrix ∨
      FullTwoMatrix.Lower A.matrix B.matrix E.matrix F.matrix G.matrix) :
    ReversedGapsZero A B C D E F G := by
  have wm := reversed_matrix_rules A B C D E F G w
  obtain ⟨a,b,e,f,g⟩ := FullTwoMatrix.reversed_triangular_first_diagonals_one
    A.matrix B.matrix C.matrix D.matrix E.matrix F.matrix G.matrix
    hA.1.1 hB.1.1 hC.1.1 hD.1.1 hE.1.1 hF.1.1 hG.1.1 hA.2 hB.2 hC.2 hD.2 hF.2 wm ht
  rcases ht with hu | hl
  · exact upper_reversed_gaps_zero A B C D E F G hA hB hC hD hE hF hG
      ⟨a,hu.1⟩ ⟨b,hu.2.1⟩ ⟨e,hu.2.2.1⟩ ⟨f,hu.2.2.2.1⟩ ⟨g,hu.2.2.2.2⟩ w
  · exact FullTwoLower.lower_reversed_gaps_zero A B C D E F G hA hB hC hD hE hF hG
      ⟨a,hl.1⟩ ⟨b,hl.2.1⟩ ⟨e,hl.2.2.1⟩ ⟨f,hl.2.2.2.1⟩ ⟨g,hl.2.2.2.2⟩ w

end CollatzResearch.FullTwo

#print axioms CollatzResearch.FullTwo.forward_matrix_rules
#print axioms CollatzResearch.FullTwo.reversed_matrix_rules
#print axioms CollatzResearch.FullTwo.forward_gaps_zero_of_triangular
#print axioms CollatzResearch.FullTwo.reversed_gaps_zero_of_triangular
