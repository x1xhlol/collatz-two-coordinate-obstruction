import CollatzReversedRealExpandingGrowth

namespace CollatzResearch.RealTriangularPrefix

open Matrix CollatzCertificate RealAffine

set_option maxHeartbeats 1000000

theorem positive_first_image_of_positive_entry (A : Affine (Fin 2)) (x : Vec (Fin 2))
    (hA : A.Nonnegative) (hx : 0≤x) (j : Fin 2) (hj : 0<x j)
    (hentry : 0<A.matrix 0 j) : 0<eval A x 0 := by
  have hp : 0<A.matrix 0 ⬝ᵥ x :=
    (Finset.sum_pos_iff_of_nonneg (fun k _ => mul_nonneg (hA.1 0 k) (hx k))).mpr
      ⟨j,Finset.mem_univ j,mul_pos hentry hj⟩
  exact add_pos_of_pos_of_nonneg hp (hA.2 0)

theorem positive_first_binary_extension (A B : Affine (Fin 2)) (x : Vec (Fin 2))
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hx : 0≤x) (hne : x≠0)
    (hA00 : 0<A.matrix 0 0) (hcross : 0<A.matrix 0 1+B.matrix 0 1) :
    0<eval A x 0 ∨ 0<eval B x 0 := by
  obtain ⟨j,hj⟩ : ∃ j, 0<x j := by
    by_contra hn
    push_neg at hn
    apply hne
    funext j
    exact le_antisymm (hn j) (hx j)
  fin_cases j
  · exact Or.inl (positive_first_image_of_positive_entry A x hA hx 0 hj hA00)
  · by_cases ha : 0<A.matrix 0 1
    · exact Or.inl (positive_first_image_of_positive_entry A x hA hx 1 hj ha)
    · have hb : 0<B.matrix 0 1 := by linarith only [ha,hcross]
      exact Or.inr (positive_first_image_of_positive_entry B x hB hx 1 hj hb)

theorem positive_first_binary_prefix_of_nonzero_offset
    (A B : Affine (Fin 2)) (γ : Vec (Fin 2))
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hγ : 0≤γ)
    (hA00 : 0<A.matrix 0 0) (hcross : 0<A.matrix 0 1+B.matrix 0 1)
    (hoff : A.offset≠0 ∨ B.offset≠0) :
    ∃ p : ℕ, 4≤p ∧ p≤7 ∧ 0≤ReversedCertificate.binaryInterp (eval A) (eval B) p γ ∧
      0<ReversedCertificate.binaryInterp (eval A) (eval B) p γ 0 := by
  rcases hoff with ha | hb
  · have hx := eval_nonnegative hA hγ
    have hxne := RealExpandingPrefix.eval_nonzero_of_offset_nonzero A γ hA hγ ha
    rcases positive_first_binary_extension A B (eval A γ) hA hB hx hxne hA00 hcross
      with hp | hp
    · refine ⟨4,by decide,by decide,?_,?_⟩
      · simpa [ReversedCertificate.binaryInterp] using eval_nonnegative hA hx
      · simpa [ReversedCertificate.binaryInterp] using hp
    · refine ⟨5,by decide,by decide,?_,?_⟩
      · simpa [ReversedCertificate.binaryInterp] using eval_nonnegative hB hx
      · simpa [ReversedCertificate.binaryInterp] using hp
  · have hx := eval_nonnegative hB hγ
    have hxne := RealExpandingPrefix.eval_nonzero_of_offset_nonzero B γ hB hγ hb
    rcases positive_first_binary_extension A B (eval B γ) hA hB hx hxne hA00 hcross
      with hp | hp
    · refine ⟨6,by decide,by decide,?_,?_⟩
      · simpa [ReversedCertificate.binaryInterp] using eval_nonnegative hA hx
      · simpa [ReversedCertificate.binaryInterp] using hp
    · refine ⟨7,by decide,by decide,?_,?_⟩
      · simpa [ReversedCertificate.binaryInterp] using eval_nonnegative hB hx
      · simpa [ReversedCertificate.binaryInterp] using hp

theorem first_coordinate_binary_prefix_lower
    (A B : Affine (Fin 2)) (γ : Vec (Fin 2)) (l c : ℝ) (p : ℕ)
    (hA : A.Nonnegative) (hp : 0<p) (hl : 0≤l) (hA00 : A.matrix 0 0=l)
    (hprefix : 0≤ReversedCertificate.binaryInterp (eval A) (eval B) p γ)
    (hc : c≤ReversedCertificate.binaryInterp (eval A) (eval B) p γ 0) (n : ℕ) :
    c*l^n≤ReversedCertificate.binaryInterp (eval A) (eval B) (p*2^n) γ 0 := by
  let z := ReversedCertificate.binaryInterp (eval A) (eval B) p γ
  have hn (k : ℕ) : 0≤(eval A)^[k] z := by
    induction k with
    | zero => exact hprefix
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact eval_nonnegative hA ih
  rw [RealExpandingGrowth.binaryInterp_times_pow_two (eval A) (eval B) p n hp γ]
  change c*l^n≤((eval A)^[n] z) 0
  induction n with
  | zero => simpa only [pow_zero,mul_one] using hc
  | succ n ih =>
    rw [Function.iterate_succ_apply',pow_succ]
    change c*(l^n*l)≤A.matrix 0 ⬝ᵥ ((eval A)^[n] z)+A.offset 0
    simp only [dotProduct,Fin.sum_univ_two,hA00]
    have hm := mul_le_mul_of_nonneg_left ih hl
    have hp := mul_nonneg (hA.1 0 1) (hn n 1)
    have ha : 0≤A.offset 0 := hA.2 0
    nlinarith only [hm,hp,ha]

end CollatzResearch.RealTriangularPrefix

#print axioms CollatzResearch.RealTriangularPrefix.positive_first_image_of_positive_entry
#print axioms CollatzResearch.RealTriangularPrefix.positive_first_binary_extension
#print axioms CollatzResearch.RealTriangularPrefix.positive_first_binary_prefix_of_nonzero_offset
#print axioms CollatzResearch.RealTriangularPrefix.first_coordinate_binary_prefix_lower
