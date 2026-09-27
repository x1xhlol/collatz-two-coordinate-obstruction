import FullTwoBasic

namespace CollatzResearch.FullTwo

open Matrix CollatzCertificate

set_option linter.unusedSimpArgs false

theorem comp_assoc (X Y Z : Aff2) : (X.comp Y).comp Z = X.comp (Y.comp Z) := by
  apply affine_ext
  · exact Matrix.mul_assoc _ _ _
  · simp [Affine.comp, mulVec_add, mulVec_mulVec, add_assoc]

theorem upper_comp (X Y : Aff2) (hX : Upper X) (hY : Upper Y) :
    Upper (X.comp Y) := by
  rcases hX with ⟨hx, hx'⟩
  rcases hY with ⟨hy, hy'⟩
  simp [Upper, Affine.comp, Matrix.mul_apply, Fin.sum_univ_two, hx, hx', hy, hy']

def flip (X : Aff2) : Aff2 :=
  upper (X.offset 1) (X.matrix 1 1) (X.offset 0) (X.matrix 0 1)

theorem flip_upper (X : Aff2) : Upper (flip X) := by
  simp [flip, upper, Upper]

theorem flip_nonnegative (X : Aff2) (hX : X.Nonnegative) : (flip X).Nonnegative := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [flip, upper]
    · exact hX.2 1
    · exact hX.1 1 1
  · intro i
    fin_cases i <;> simp [flip, upper]
    · exact hX.2 0
    · exact hX.1 0 1

theorem flip_comp (X Y : Aff2) (hX : Upper X) (hY : Upper Y) :
    flip (X.comp Y) = (flip Y).comp (flip X) := by
  rw [eq_upper X hX, eq_upper Y hY]
  apply affine_ext
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [flip, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Pi.add_apply, one_mul, zero_mul, zero_add, add_zero] <;> ring
  · ext i
    fin_cases i <;>
      simp only [flip, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Pi.add_apply, one_mul, zero_mul, zero_add, add_zero] <;> ring

theorem flip_weak (X Y : Aff2) (h : X.Weak Y) : (flip X).Weak (flip Y) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [flip, upper]
    · exact h.2 1
    · exact h.1 1 1
  · intro i
    fin_cases i <;> simp [flip, upper]
    · exact h.2 0
    · exact h.1 0 1

theorem flip_offset (X : Aff2) : (flip X).offset 0 = X.offset 0 := rfl

theorem flip_reversed_weak (A B C D E F G : Aff2)
    (hA : Upper A) (hB : Upper B) (hC : Upper C) (hD : Upper D)
    (hE : Upper E) (hF : Upper F) (hG : Upper G)
    (h : ReversedRealWeak A B C D E F G) :
    ForwardWeak (flip A) (flip B) (flip C) (flip D) (flip E) (flip F) (flip G) := by
  constructor
  · simpa [flip_comp D A hD hA] using flip_weak _ _ h.da
  · simpa [flip_comp D B hD hB, flip_comp D G hD hG] using flip_weak _ _ h.db
  · simpa [flip_comp E A hE hA, flip_comp A E hA hE] using flip_weak _ _ h.ea
  · simpa [flip_comp F A hF hA, flip_comp B E hB hE] using flip_weak _ _ h.fa
  · simpa [flip_comp G A hG hA, flip_comp A F hA hF] using flip_weak _ _ h.ga
  · simpa [flip_comp E B hE hB, flip_comp B F hB hF] using flip_weak _ _ h.eb
  · simpa [flip_comp F B hF hB, flip_comp A G hA hG] using flip_weak _ _ h.fb
  · simpa [flip_comp G B hG hB, flip_comp B G hB hG] using flip_weak _ _ h.gb
  · simpa [flip_comp E C hE hC, flip_comp B C hB hC] using flip_weak _ _ h.ec
  · simpa [flip_comp F C hF hC, flip_comp A (A.comp C) hA (upper_comp A C hA hC),
      flip_comp A C hA hC, comp_assoc] using flip_weak _ _ h.fc
  · simpa [flip_comp G C hG hC, flip_comp B (A.comp C) hB (upper_comp A C hA hC),
      flip_comp A C hA hC, comp_assoc] using flip_weak _ _ h.gc

end CollatzResearch.FullTwo

#print axioms CollatzResearch.FullTwo.comp_assoc
#print axioms CollatzResearch.FullTwo.upper_comp
#print axioms CollatzResearch.FullTwo.flip_upper
#print axioms CollatzResearch.FullTwo.flip_nonnegative
#print axioms CollatzResearch.FullTwo.flip_comp
#print axioms CollatzResearch.FullTwo.flip_weak
#print axioms CollatzResearch.FullTwo.flip_offset
#print axioms CollatzResearch.FullTwo.flip_reversed_weak
