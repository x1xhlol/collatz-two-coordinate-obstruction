import CollatzReversedRealNonsingularEigen

namespace CollatzResearch.RealExpandingPrefix

open Matrix CollatzCertificate RealAffine ReversedCertificate

theorem strict_binary_offset_nonzero
    (A B D G : Affine (Fin 2)) (i₀ : Fin 2)
    (hD : D.Nonnegative) (hG : G.Nonnegative)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) :
    A.offset ≠ 0 ∨ B.offset ≠ 0 := by
  by_cases ha : A.offset=0
  · right
    intro hb
    rcases hstrict with hs | hs
    · change D.offset i₀ < D.matrix i₀ ⬝ᵥ A.offset+D.offset i₀ at hs
      simp only [ha,dotProduct_zero,zero_add,lt_self_iff_false] at hs
    · have hn := dotProduct_nonneg_of_nonneg (fun j => hD.1 i₀ j) hG.2
      change D.matrix i₀ ⬝ᵥ G.offset+D.offset i₀ <
        D.matrix i₀ ⬝ᵥ B.offset+D.offset i₀ at hs
      rw [hb,dotProduct_zero,zero_add] at hs
      linarith only [hs,hn]
  · exact Or.inl ha

theorem eval_nonzero_of_offset_nonzero (A : Affine (Fin 2)) (x : Vec (Fin 2))
    (hA : A.Nonnegative) (hx : 0 ≤ x) (ha : A.offset ≠ 0) : eval A x ≠ 0 := by
  intro hz
  have hh := eval_monotone hA.1 hx
  have hb : A.offset ≤ eval A x := by simpa only [eval,mulVec_zero,zero_add] using hh
  apply ha
  funext i
  have hi := hb i
  rw [hz] at hi
  exact le_antisymm hi (hA.2 i)

theorem positive_image_of_positive_column (A : Affine (Fin 2)) (x : Vec (Fin 2))
    (hA : A.Nonnegative) (hx : 0 ≤ x) (j : Fin 2) (hj : 0 < x j)
    (hc : ∀ i, 0 < A.matrix i j) : ∀ i, 0 < eval A x i := by
  intro i
  have hp : 0 < A.matrix i ⬝ᵥ x :=
    (Finset.sum_pos_iff_of_nonneg (fun k _ => mul_nonneg (hA.1 i k) (hx k))).mpr
      ⟨j,Finset.mem_univ j,mul_pos (hc i) hj⟩
  exact add_pos_of_pos_of_nonneg hp (hA.2 i)

theorem positive_binary_extension (A B : Affine (Fin 2)) (x : Vec (Fin 2))
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hx : 0 ≤ x) (hne : x ≠ 0)
    (hAd : ∀ i, 0 < A.matrix i i) (hBd : ∀ i, 0 < B.matrix i i)
    (h01 : 0 < (A.matrix+B.matrix) 0 1)
    (h10 : 0 < (A.matrix+B.matrix) 1 0) :
    (∀ i, 0 < eval A x i) ∨ (∀ i, 0 < eval B x i) := by
  obtain ⟨j,hj⟩ : ∃ j, 0 < x j := by
    by_contra hn
    push_neg at hn
    apply hne
    funext j
    exact le_antisymm (hn j) (hx j)
  fin_cases j
  · by_cases hp : 0 < A.matrix 1 0
    · left
      apply positive_image_of_positive_column A x hA hx 0 hj
      intro i
      fin_cases i
      · exact hAd 0
      · exact hp
    · right
      have hpB : 0 < B.matrix 1 0 := by
        change 0 < A.matrix 1 0+B.matrix 1 0 at h10
        linarith only [h10,hp]
      apply positive_image_of_positive_column B x hB hx 0 hj
      intro i
      fin_cases i
      · exact hBd 0
      · exact hpB
  · by_cases hp : 0 < A.matrix 0 1
    · left
      apply positive_image_of_positive_column A x hA hx 1 hj
      intro i
      fin_cases i
      · exact hp
      · exact hAd 1
    · right
      have hpB : 0 < B.matrix 0 1 := by
        change 0 < A.matrix 0 1+B.matrix 0 1 at h01
        linarith only [h01,hp]
      apply positive_image_of_positive_column B x hB hx 1 hj
      intro i
      fin_cases i
      · exact hpB
      · exact hBd 1

theorem positive_binary_prefix_of_nonzero_offset (A B : Affine (Fin 2)) (γ : Vec (Fin 2))
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hγ : 0 ≤ γ)
    (hAd : ∀ i, 0 < A.matrix i i) (hBd : ∀ i, 0 < B.matrix i i)
    (h01 : 0 < (A.matrix+B.matrix) 0 1)
    (h10 : 0 < (A.matrix+B.matrix) 1 0)
    (hne : A.offset ≠ 0 ∨ B.offset ≠ 0) :
    ∃ m : ℕ, 4 ≤ m ∧ m ≤ 7 ∧ ∀ i, 0 < ReversedCertificate.binaryInterp (eval A) (eval B) m γ i := by
  rcases hne with ha | hb
  · have hx := eval_nonnegative hA hγ
    have hxne := eval_nonzero_of_offset_nonzero A γ hA hγ ha
    rcases positive_binary_extension A B (eval A γ) hA hB hx hxne hAd hBd h01 h10
      with hpos | hpos
    · refine ⟨4,by decide,by decide,?_⟩
      simpa [ReversedCertificate.binaryInterp] using hpos
    · refine ⟨5,by decide,by decide,?_⟩
      simpa [ReversedCertificate.binaryInterp] using hpos
  · have hx := eval_nonnegative hB hγ
    have hxne := eval_nonzero_of_offset_nonzero B γ hB hγ hb
    rcases positive_binary_extension A B (eval B γ) hA hB hx hxne hAd hBd h01 h10
      with hpos | hpos
    · refine ⟨6,by decide,by decide,?_⟩
      simpa [ReversedCertificate.binaryInterp] using hpos
    · refine ⟨7,by decide,by decide,?_⟩
      simpa [ReversedCertificate.binaryInterp] using hpos

theorem positive_vector_dominates_positive_ray (x u : Vec (Fin 2))
    (hx : ∀ i, 0 < x i) (hu : ∀ i, 0 < u i) : ∃ c : ℝ, 0 < c ∧ c • u ≤ x := by
  let c := min (x 0/u 0) (x 1/u 1)
  refine ⟨c,lt_min (div_pos (hx 0) (hu 0)) (div_pos (hx 1) (hu 1)),?_⟩
  intro i
  fin_cases i
  · exact (le_div_iff₀ (hu 0)).mp (min_le_left _ _)
  · exact (le_div_iff₀ (hu 1)).mp (min_le_right _ _)

end CollatzResearch.RealExpandingPrefix

#print axioms CollatzResearch.RealExpandingPrefix.strict_binary_offset_nonzero
#print axioms CollatzResearch.RealExpandingPrefix.eval_nonzero_of_offset_nonzero
#print axioms CollatzResearch.RealExpandingPrefix.positive_image_of_positive_column
#print axioms CollatzResearch.RealExpandingPrefix.positive_binary_extension
#print axioms CollatzResearch.RealExpandingPrefix.positive_binary_prefix_of_nonzero_offset
#print axioms CollatzResearch.RealExpandingPrefix.positive_vector_dominates_positive_ray
