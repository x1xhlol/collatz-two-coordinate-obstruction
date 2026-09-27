import FullTwoFlip
import FullTwoNormalize

namespace CollatzResearch.FullTwo

open Matrix CollatzCertificate

theorem comp_identity (X : Aff2) : X.comp identity = X := by
  apply affine_ext <;> simp [identity, Affine.comp]

theorem normalize_forward (A B C D E F G : Aff2)
    (hA : Upper A) (hB : Upper B) (hG : Upper G)
    (hC : Admissible C) (h : ForwardWeak A B C D E F G) :
    ForwardWeak A B (outerBoundary C) (innerBoundary D) E F G := by
  have hc : 0 < C.matrix 0 0 := lt_of_lt_of_le zero_lt_one hC.2
  constructor
  · have hh : (A.comp D).Weak (identity.comp D) := by simpa only [identity_comp] using h.ad
    simpa only [identity_comp] using normalize_inner_weak D A identity hA identity_upper hh
  · exact normalize_inner_weak D B G hB hG h.bd
  · exact h.ae
  · exact h.af
  · exact h.ag
  · exact h.be
  · exact h.bf
  · exact h.bg
  · exact normalize_outer_weak C E B hc h.ce
  · exact normalize_outer_weak C F (A.comp A) hc h.cf
  · exact normalize_outer_weak C G (A.comp B) hc h.cg

theorem denormalize_forward_gaps (A B C D E F G : Aff2)
    (hA : Upper A) (hB : Upper B) (hG : Upper G) (hC : Admissible C)
    (h : ForwardGapsZero A B (outerBoundary C) (innerBoundary D) E F G) :
    ForwardGapsZero A B C D E F G := by
  have hc : 0 < C.matrix 0 0 := lt_of_lt_of_le zero_lt_one hC.2
  constructor
  · have hh : (A.comp (innerBoundary D)).offset 0 =
        (identity.comp (innerBoundary D)).offset 0 := by simpa only [identity_comp] using h.ad
    simpa only [identity_comp] using normalize_inner_gap_back D A identity hA identity_upper hh
  · exact normalize_inner_gap_back D B G hB hG h.bd
  · exact h.ae
  · exact h.af
  · exact h.ag
  · exact h.be
  · exact h.bf
  · exact h.bg
  · exact normalize_outer_gap_back C E B hc h.ce
  · exact normalize_outer_gap_back C F (A.comp A) hc h.cf
  · exact normalize_outer_gap_back C G (A.comp B) hc h.cg

theorem normalize_reversed (A B C D E F G : Aff2)
    (hA : Upper A) (hB : Upper B) (hE : Upper E) (hF : Upper F) (hG : Upper G)
    (hD : Admissible D) (h : ReversedRealWeak A B C D E F G) :
    ReversedRealWeak A B (innerBoundary C) (outerBoundary D) E F G := by
  have hd : 0 < D.matrix 0 0 := lt_of_lt_of_le zero_lt_one hD.2
  constructor
  · have hh : (D.comp A).Weak (D.comp identity) := by simpa only [comp_identity] using h.da
    simpa only [comp_identity] using normalize_outer_weak D A identity hd hh
  · exact normalize_outer_weak D B G hd h.db
  · exact h.ea
  · exact h.fa
  · exact h.ga
  · exact h.eb
  · exact h.fb
  · exact h.gb
  · exact normalize_inner_weak C E B hE hB h.ec
  · have hh : (F.comp C).Weak ((A.comp A).comp C) := by simpa only [comp_assoc] using h.fc
    simpa only [comp_assoc] using normalize_inner_weak C F (A.comp A) hF (upper_comp A A hA hA) hh
  · have hh : (G.comp C).Weak ((B.comp A).comp C) := by simpa only [comp_assoc] using h.gc
    simpa only [comp_assoc] using normalize_inner_weak C G (B.comp A) hG (upper_comp B A hB hA) hh

theorem denormalize_reversed_gaps (A B C D E F G : Aff2)
    (hA : Upper A) (hB : Upper B) (hE : Upper E) (hF : Upper F) (hG : Upper G)
    (hD : Admissible D)
    (h : ReversedGapsZero A B (innerBoundary C) (outerBoundary D) E F G) :
    ReversedGapsZero A B C D E F G := by
  have hd : 0 < D.matrix 0 0 := lt_of_lt_of_le zero_lt_one hD.2
  constructor
  · have hh : ((outerBoundary D).comp A).offset 0 = ((outerBoundary D).comp identity).offset 0 :=
      by simpa only [comp_identity] using h.da
    simpa only [comp_identity] using normalize_outer_gap_back D A identity hd hh
  · exact normalize_outer_gap_back D B G hd h.db
  · exact h.ea
  · exact h.fa
  · exact h.ga
  · exact h.eb
  · exact h.fb
  · exact h.gb
  · exact normalize_inner_gap_back C E B hE hB h.ec
  · have hh : (F.comp (innerBoundary C)).offset 0 = ((A.comp A).comp (innerBoundary C)).offset 0 :=
      by simpa only [comp_assoc] using h.fc
    simpa only [comp_assoc] using normalize_inner_gap_back C F (A.comp A) hF (upper_comp A A hA hA) hh
  · have hh : (G.comp (innerBoundary C)).offset 0 = ((B.comp A).comp (innerBoundary C)).offset 0 :=
      by simpa only [comp_assoc] using h.gc
    simpa only [comp_assoc] using normalize_inner_gap_back C G (B.comp A) hG (upper_comp B A hB hA) hh

theorem flip_forward_gaps_back (A B C D E F G : Aff2)
    (hA : Upper A) (hB : Upper B) (hC : Upper C) (hD : Upper D)
    (hE : Upper E) (hF : Upper F) (hG : Upper G)
    (h : ForwardGapsZero (flip A) (flip B) (flip C) (flip D) (flip E) (flip F) (flip G)) :
    ReversedGapsZero A B C D E F G := by
  have heq (X Y : Aff2) (hx : Upper X) (hy : Upper Y) :
      ((flip Y).comp (flip X)).offset 0 = (X.comp Y).offset 0 := by
    rw [← flip_comp X Y hx hy, flip_offset]
  constructor
  · simpa only [heq D A hD hA, flip_offset] using h.ad
  · simpa only [heq D B hD hB, heq D G hD hG] using h.bd
  · simpa only [heq E A hE hA, heq A E hA hE] using h.ae
  · simpa only [heq F A hF hA, heq B E hB hE] using h.af
  · simpa only [heq G A hG hA, heq A F hA hF] using h.ag
  · simpa only [heq E B hE hB, heq B F hB hF] using h.be
  · simpa only [heq F B hF hB, heq A G hA hG] using h.bf
  · simpa only [heq G B hG hB, heq B G hB hG] using h.bg
  · simpa only [heq E C hE hC, heq B C hB hC] using h.ce
  · have hh := h.cf
    rw [← flip_comp A A hA hA] at hh
    simpa only [heq F C hF hC, heq (A.comp A) C (upper_comp A A hA hA) hC, comp_assoc] using hh
  · have hh := h.cg
    rw [← flip_comp B A hB hA] at hh
    simpa only [heq G C hG hC, heq (B.comp A) C (upper_comp B A hB hA) hC, comp_assoc] using hh

end CollatzResearch.FullTwo

#print axioms CollatzResearch.FullTwo.comp_identity
#print axioms CollatzResearch.FullTwo.normalize_forward
#print axioms CollatzResearch.FullTwo.denormalize_forward_gaps
#print axioms CollatzResearch.FullTwo.normalize_reversed
#print axioms CollatzResearch.FullTwo.denormalize_reversed_gaps
#print axioms CollatzResearch.FullTwo.flip_forward_gaps_back
