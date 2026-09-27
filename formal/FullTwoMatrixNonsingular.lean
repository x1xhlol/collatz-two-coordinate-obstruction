import FullTwoMatrixNonsingularShape
import FullTwoMatrixNonsingularBoundary
import FullTwoMatrixRepeated

namespace CollatzCertificate.FullTwoMatrix

open Matrix TwoDimensionalSwapAlgebra

theorem nonsingular_digits_contradiction (A B C D E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hC : EntrywiseLE 0 C)
    (hD : EntrywiseLE 0 D) (hE : EntrywiseLE 0 E)
    (_hF : EntrywiseLE 0 F) (_hG : EntrywiseLE 0 G)
    (hA00 : 1 ≤ A 0 0) (hB00 : 1 ≤ B 0 0) (hC00 : 1 ≤ C 0 0)
    (hD00 : 1 ≤ D 0 0) (hE00 : 1 ≤ E 0 0)
    (_hF00 : 1 ≤ F 0 0) (_hG00 : 1 ≤ G 0 0)
    (w : WeakRules A B C D E F G) (s : ExactSwaps A B E F G)
    (dA : A.det ≠ 0) (dB : B.det ≠ 0) (dE : E.det ≠ 0)
    (_dF : F.det ≠ 0) (dG : G.det ≠ 0)
    (h01 : 0 < ((A+B)+(E+F+G)) 0 1)
    (h10 : 0 < ((A+B)+(E+F+G)) 1 0) : False := by
  by_cases hab : A=B
  · subst B
    have hef : E=F := (matrix_unit_of_det A dA).mul_left_cancel (s.1.trans s.2.1.symm)
    subst F
    have hge : G=E := (matrix_unit_of_det A dA).mul_left_cancel (s.2.2.1.trans s.1.symm)
    subst G
    exact repeated_digits_contradiction A C D E hA hC hD hE hA00 hC00 hD00 hE00
      w.ad w.bd w.cf s.1 h01 h10
  · have htA : 0 < tr A := by have hn : 0 ≤ A 1 1 := hA 1 1; dsimp [tr]; linarith only [hA00,hn]
    have htB : 0 < tr B := by have hn : 0 ≤ B 1 1 := hB 1 1; dsimp [tr]; linarith only [hB00,hn]
    have htE : 0 < tr E := by have hn : 0 ≤ E 1 1 := hE 1 1; dsimp [tr]; linarith only [hE00,hn]
    obtain ⟨hd,ht,_,_,_,_⟩ := nonsingular_binary_invariants A B E F G s dB dE dG htA htB
    obtain ⟨μ,t,hμ,htt,htr,hdμ,hAN,hNA,he,hf,hg⟩ :=
      nonsingular_unequal_shape A B E F G s dA dB dE dG htA htB htE hab
    exact nonsingular_shape_boundary_impossible A B C D E F G μ t hμ htt
      hA hB hC hD hA00 hB00 hC00 hD00 w htr (ht.symm.trans htr)
      hdμ (hd.symm.trans hdμ) hAN hNA he hf hg h01 h10

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.nonsingular_digits_contradiction
