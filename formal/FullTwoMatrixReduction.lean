import FullTwoMatrixOrientation
import FullTwoMatrixFirstDiagonal
import FullTwoMatrixTranspose
import FullTwoMatrixDeterminants
import FullTwoMatrixSingular
import FullTwoMatrixNonsingular
import FullTwoMatrixSingularBinary

namespace CollatzCertificate.FullTwoMatrix

open Matrix

theorem forward_common_orientation (A B C D E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hC : EntrywiseLE 0 C)
    (hD : EntrywiseLE 0 D) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (hA₀ : 1 ≤ A 0 0) (hB₀ : 1 ≤ B 0 0) (hC₀ : 1 ≤ C 0 0)
    (hD₀ : 1 ≤ D 0 0) (hE₀ : 1 ≤ E 0 0) (hF₀ : 1 ≤ F 0 0) (hG₀ : 1 ≤ G 0 0)
    (h : WeakRules A B C D E F G) : Upper A B E F G ∨ Lower A B E F G := by
  apply orientation_of_not_positive_offdiagonals A B E F G hA hB hE hF hG
  rintro ⟨h01,h10⟩
  have hs := exact_swaps_of_total_offdiagonal_positive A B C D E F G hA hB hE hF hG h h01 h10
  by_cases hf : F.det=0
  · exact singular_middle_contradiction A B C D E F G hA hB hC hD hE hF hG
      hA₀ hB₀ hC₀ hD₀ hE₀ hF₀ hG₀ h hs hf h01 h10
  rcases invertible_middle_determinant_cases A B E F G hs hf with ⟨ha,hb⟩ | ⟨ha,hb,he,hg⟩
  · exact singular_binary_invertible_middle_contradiction A B C D E F G hA hB hC hD hE hF hG
      hA₀ hB₀ hC₀ hD₀ hE₀ hF₀ hG₀ h hs ha hb hf h01 h10
  · exact nonsingular_digits_contradiction A B C D E F G hA hB hC hD hE hF hG
      hA₀ hB₀ hC₀ hD₀ hE₀ hF₀ hG₀ h hs ha hb he hf hg h01 h10

theorem forward_common_orientation_and_first_diagonals (A B C D E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hC : EntrywiseLE 0 C)
    (hD : EntrywiseLE 0 D) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (hA₀ : 1 ≤ A 0 0) (hB₀ : 1 ≤ B 0 0) (hC₀ : 1 ≤ C 0 0)
    (hD₀ : 1 ≤ D 0 0) (hE₀ : 1 ≤ E 0 0) (hF₀ : 1 ≤ F 0 0) (hG₀ : 1 ≤ G 0 0)
    (h : WeakRules A B C D E F G) :
    (Upper A B E F G ∨ Lower A B E F G) ∧
      (A 0 0=1 ∧ B 0 0=1 ∧ E 0 0=1 ∧ F 0 0=1 ∧ G 0 0=1) := by
  have ho := forward_common_orientation A B C D E F G hA hB hC hD hE hF hG
    hA₀ hB₀ hC₀ hD₀ hE₀ hF₀ hG₀ h
  refine ⟨ho, ?_⟩
  rcases ho with hu | hl
  · exact upper_first_diagonals_one A B C D E F G hA hB hC hD hE hF hG
      hA₀ hB₀ hC₀ hD₀ hF₀ h hu
  · exact lower_first_diagonals_one A B C D E F G hA hB hC hD hE hF hG
      hA₀ hB₀ hC₀ hD₀ hF₀ h hl

theorem reversed_common_orientation_and_first_diagonals (A B C D E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hC : EntrywiseLE 0 C)
    (hD : EntrywiseLE 0 D) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (hA₀ : 1 ≤ A 0 0) (hB₀ : 1 ≤ B 0 0) (hC₀ : 1 ≤ C 0 0)
    (hD₀ : 1 ≤ D 0 0) (hE₀ : 1 ≤ E 0 0) (hF₀ : 1 ≤ F 0 0) (hG₀ : 1 ≤ G 0 0)
    (h : ReversedWeakRules A B C D E F G) :
    (Upper A B E F G ∨ Lower A B E F G) ∧
      (A 0 0=1 ∧ B 0 0=1 ∧ E 0 0=1 ∧ F 0 0=1 ∧ G 0 0=1) := by
  have ht := forward_common_orientation_and_first_diagonals Aᵀ Bᵀ Cᵀ Dᵀ Eᵀ Fᵀ Gᵀ
    (nonnegative_transpose A hA) (nonnegative_transpose B hB) (nonnegative_transpose C hC)
    (nonnegative_transpose D hD) (nonnegative_transpose E hE)
    (nonnegative_transpose F hF) (nonnegative_transpose G hG)
    hA₀ hB₀ hC₀ hD₀ hE₀ hF₀ hG₀ (reversed_rules_transpose A B C D E F G h)
  refine ⟨?_, ht.2⟩
  rcases ht.1 with hu | hl
  · exact Or.inr hu
  · exact Or.inl hl

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.forward_common_orientation
#print axioms CollatzCertificate.FullTwoMatrix.forward_common_orientation_and_first_diagonals
#print axioms CollatzCertificate.FullTwoMatrix.reversed_common_orientation_and_first_diagonals
