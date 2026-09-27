import CollatzReversedRealExpanding
import CollatzReversedRealExpandingSupport
import CollatzReversedRealUnitEigen

namespace CollatzResearch.RealAllReturns

open Matrix CollatzCertificate RealAffine

theorem strict_reversed_all_returns_contradiction
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (hreturn : ∀ i j : Fin 2, ∃ k : ℕ,
      0 < (((A.matrix+B.matrix)+(E.matrix+F.matrix+G.matrix))^k) j i) : False := by
  obtain ⟨l,m,u,hl,_hm,hml,hu,hAu,_hBu,hEu,hFu,hGu⟩ :=
    RealUnitEigen.strict_reversed_expanding_common_eigenvector_of_returns
      A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict hreturn
  obtain ⟨hAd,hBd,h01,h10⟩ :=
    RealExpandingSupport.strict_reversed_binary_support_of_returns
      A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict hreturn
  have hoff := RealExpandingPrefix.strict_binary_offset_nonzero A B D G i₀ hD hG hstrict
  obtain ⟨p,hp4,hp7,hp⟩ := RealExpandingPrefix.positive_binary_prefix_of_nonzero_offset
    A B C.offset hA hB hC.2 hAd hBd h01 h10 hoff
  obtain ⟨c,hc,hprefix⟩ := RealExpandingPrefix.positive_vector_dominates_positive_ray
    (ReversedCertificate.binaryInterp (eval A) (eval B) p C.offset) u hp hu
  exact RealExpanding.positive_prefix_expanding_contradiction A B C D E F G
    hA hB hC hE hF hG h u l m c p hu hl hml hc hAu hEu hFu hGu hp4 hp7 hprefix

end CollatzResearch.RealAllReturns

#print axioms CollatzResearch.RealAllReturns.strict_reversed_all_returns_contradiction
