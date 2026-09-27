import FullTwoUpperTransfer
import FullTwoUpper

namespace CollatzResearch.FullTwo

open CollatzCertificate

theorem upper_forward_gaps_zero (A B C D E F G : Aff2)
    (hA : Admissible A) (hB : Admissible B) (hC : Admissible C) (hD : Admissible D)
    (hE : Admissible E) (hF : Admissible F) (hG : Admissible G)
    (uA : Upper A) (uB : Upper B) (uE : Upper E) (uF : Upper F) (uG : Upper G)
    (w : ForwardWeak A B C D E F G) : ForwardGapsZero A B C D E F G := by
  have wn := normalize_forward A B C D E F G uA uB uG hC w
  have wd := toUpperData_weak A B C D E F G hA hB hC hD hE hF hG uA uB uE uF uG wn
  have wz := FullTwoUpper.zero_gaps (toUpperData A B C D E F G) wd
  exact denormalize_forward_gaps A B C D E F G uA uB uG hC
    (toUpperData_gaps A B C D E F G uA uB uE uF uG wz)

theorem flip_admissible (X : Aff2) (hX : Admissible X) : Admissible (flip X) :=
  ⟨flip_nonnegative X hX.1, by simp [flip,upper]⟩

theorem upper_reversed_gaps_zero (A B C D E F G : Aff2)
    (hA : Admissible A) (hB : Admissible B) (hC : Admissible C) (hD : Admissible D)
    (hE : Admissible E) (hF : Admissible F) (hG : Admissible G)
    (uA : Upper A) (uB : Upper B) (uE : Upper E) (uF : Upper F) (uG : Upper G)
    (w : ReversedRealWeak A B C D E F G) : ReversedGapsZero A B C D E F G := by
  have wn := normalize_reversed A B C D E F G uA uB uE uF uG hD w
  have wf := flip_reversed_weak A B (innerBoundary C) (outerBoundary D) E F G
    uA uB (innerBoundary_upper C) (outerBoundary_upper D) uE uF uG wn
  have wz := upper_forward_gaps_zero
    (flip A) (flip B) (flip (innerBoundary C)) (flip (outerBoundary D)) (flip E) (flip F) (flip G)
    (flip_admissible A hA) (flip_admissible B hB)
    (flip_admissible (innerBoundary C) (innerBoundary_admissible C hC))
    (flip_admissible (outerBoundary D) (outerBoundary_admissible D hD))
    (flip_admissible E hE) (flip_admissible F hF) (flip_admissible G hG)
    (flip_upper A) (flip_upper B) (flip_upper E) (flip_upper F) (flip_upper G) wf
  have wb := flip_forward_gaps_back A B (innerBoundary C) (outerBoundary D) E F G
    uA uB (innerBoundary_upper C) (outerBoundary_upper D) uE uF uG wz
  exact denormalize_reversed_gaps A B C D E F G uA uB uE uF uG hD wb

end CollatzResearch.FullTwo

#print axioms CollatzResearch.FullTwo.upper_forward_gaps_zero
#print axioms CollatzResearch.FullTwo.flip_admissible
#print axioms CollatzResearch.FullTwo.upper_reversed_gaps_zero
