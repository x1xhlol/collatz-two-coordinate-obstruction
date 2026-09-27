import FullTwoMatrixSingularBinaryShape
import FullTwoMatrixSingularEqual
import FullTwoMatrixBinaryProjectionBoundary

namespace CollatzCertificate.FullTwoMatrix

open Matrix TwoDimensionalSwapAlgebra

theorem singular_binary_invertible_middle_contradiction (A B C D E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hC : EntrywiseLE 0 C)
    (hD : EntrywiseLE 0 D) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (hA00 : 1 ≤ A 0 0) (hB00 : 1 ≤ B 0 0) (hC00 : 1 ≤ C 0 0)
    (hD00 : 1 ≤ D 0 0) (hE00 : 1 ≤ E 0 0)
    (hF00 : 1 ≤ F 0 0) (hG00 : 1 ≤ G 0 0)
    (w : WeakRules A B C D E F G) (s : ExactSwaps A B E F G)
    (dA : A.det=0) (dB : B.det=0) (dF : F.det ≠ 0)
    (h01 : 0 < ((A+B)+(E+F+G)) 0 1)
    (h10 : 0 < ((A+B)+(E+F+G)) 1 0) : False := by
  by_cases hab : A=B
  · subst B
    exact equal_singular_boundary_contradiction A C D E F G hA hC hD hE hF hG
      hA00 hC00 hD00 hE00 hF00 hG00 w s dA h01 h10
  · have htA : 0 < tr A := by have hn : 0 ≤ A 1 1 := hA 1 1; dsimp [tr]; linarith only [hA00,hn]
    have htB : 0 < tr B := by have hn : 0 ≤ B 1 1 := hB 1 1; dsimp [tr]; linarith only [hB00,hn]
    have htF : 0 < tr F := by have hn : 0 ≤ F 1 1 := hF 1 1; dsimp [tr]; linarith only [hF00,hn]
    obtain ⟨α,β,hα,hβ,hta,htb,hab',hba,hf,he,hg⟩ :=
      singular_binary_unequal_shape A B E F G s dA dB dF htA htB htF hab
    exact binary_projection_boundary_impossible A B C D E F G α β hα hβ
      hA hB hC hD hA00 hB00 hC00 hD00 w hta htb dA dB hab' hba he hf hg h01 h10

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.singular_binary_invertible_middle_contradiction
