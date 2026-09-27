import CollatzReversedRealTriangularZero
import CollatzReversedRealTriangularSubunit
import CollatzReversedRealTriangularUnit
import CollatzReversedRealTriangularExpanding

namespace CollatzResearch.RealTriangular

open Matrix CollatzCertificate RealAffine

theorem strict_upper_triangular_contradiction
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (ha0 : A.matrix 1 0=0) (hb0 : B.matrix 1 0=0) (he0 : E.matrix 1 0=0)
    (hf0 : F.matrix 1 0=0) (hg0 : G.matrix 1 0=0) : False := by
  rcases eq_or_lt_of_le (hF.1 0 0) with hfzero | hfpos
  · exact RealTriangularZero.strict_upper_zero_middle_diagonal_contradiction
      A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict
      ha0 hb0 he0 hf0 hg0 hfzero.symm
  · obtain ⟨hab,hef,hgf,ha1,_hfpos,hfle⟩ :=
      RealTriangularPositive.positive_active_diagonal_values A B C D E F G i₀ 0 1
        (by decide) hA hB hC hD hE hF hG h hstrict ha0 hb0 he0 hf0 hg0 hfpos
    rcases eq_or_lt_of_le ha1 with haunit | haexp
    · have ha : A.matrix 0 0=1 := haunit.symm
      have hb : B.matrix 0 0=1 := hab.symm.trans ha
      have hf1 : F.matrix 0 0≤1 := hfle.trans_eq ha
      rcases eq_or_lt_of_le hf1 with hfunit | hfsub
      · exact RealTriangularUnit.upper_unit_first_diagonals_exclude_strict
          A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict
          ha hb (hef.trans hfunit) hfunit (hgf.trans hfunit) ha0 hb0 he0 hf0 hg0
      · have hd := RealTriangularContracting.strict_upper_second_diagonal_lt_one
          A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict ha0 hb0
        exact RealTriangularSubunit.strict_upper_unit_subunit_ternary_contradiction
          A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict
          ha ha0 he0 hd (hef.trans_lt hfsub)
    · exact RealTriangularExpanding.strict_upper_expanding_active_diagonal_contradiction
        A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict
        ha0 hb0 he0 hf0 hg0 hfpos haexp

end CollatzResearch.RealTriangular

#print axioms CollatzResearch.RealTriangular.strict_upper_triangular_contradiction
