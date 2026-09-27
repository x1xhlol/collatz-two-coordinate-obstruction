import CollatzReversedRealTriangular
import CollatzReversedRealCoordinateSwap

namespace CollatzResearch.RealTwoCoordinate

open Matrix CollatzCertificate RealAffine RealCoordinateSwap

theorem strict_reversed_two_coordinate_contradiction
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) : False := by
  rcases RealTriangularNecessity.strict_reversed_common_triangular_orientation
    A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict with
    ⟨ha,hb,he,hf,hg,_hlt⟩ | ⟨ha,hb,he,hf,hg,_hlt⟩
  · exact RealTriangular.strict_upper_triangular_contradiction A B C D E F G i₀
      hA hB hC hD hE hF hG h hstrict ha hb he hf hg
  · obtain ⟨ha',hb',he',hf',hg'⟩ := lower_digits_swap_upper A B E F G ha hb he hf hg
    exact RealTriangular.strict_upper_triangular_contradiction
      (swapCoordinates A) (swapCoordinates B) (swapCoordinates C) (swapInput D)
      (swapCoordinates E) (swapCoordinates F) (swapCoordinates G) i₀
      (swap_coordinates_nonnegative A hA) (swap_coordinates_nonnegative B hB)
      (swap_coordinates_nonnegative C hC) (swap_input_nonnegative D hD)
      (swap_coordinates_nonnegative E hE) (swap_coordinates_nonnegative F hF)
      (swap_coordinates_nonnegative G hG) (swap_coordinates_reversed_weak A B C D E F G h)
      (swap_coordinates_strict A B D G i₀ hstrict) ha' hb' he' hf' hg'

theorem reversed_eligible_offsets_equal
    (A B C D E F G : Affine (Fin 2))
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G) :
    (D.comp A).offset = D.offset ∧ (D.comp B).offset = (D.comp G).offset := by
  constructor
  · funext i
    apply le_antisymm _ (h.da.2 i)
    by_contra hn
    exact strict_reversed_two_coordinate_contradiction A B C D E F G i
      hA hB hC hD hE hF hG h (Or.inl (lt_of_not_ge hn))
  · funext i
    apply le_antisymm _ (h.db.2 i)
    by_contra hn
    exact strict_reversed_two_coordinate_contradiction A B C D E F G i
      hA hB hC hD hE hF hG h (Or.inr (lt_of_not_ge hn))

theorem no_positive_eligible_offset_gap
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2) (δ : ℝ)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G) (hδ : 0 < δ) :
    ¬ (D.offset i₀ + δ ≤ (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ + δ ≤ (D.comp B).offset i₀) := by
  intro hgap
  apply strict_reversed_two_coordinate_contradiction A B C D E F G i₀
    hA hB hC hD hE hF hG h
  rcases hgap with ha | hb
  · exact Or.inl (lt_of_lt_of_le (lt_add_of_pos_right _ hδ) ha)
  · exact Or.inr (lt_of_lt_of_le (lt_add_of_pos_right _ hδ) hb)

end CollatzResearch.RealTwoCoordinate

#print axioms CollatzResearch.RealTwoCoordinate.strict_reversed_two_coordinate_contradiction
#print axioms CollatzResearch.RealTwoCoordinate.reversed_eligible_offsets_equal
#print axioms CollatzResearch.RealTwoCoordinate.no_positive_eligible_offset_gap
