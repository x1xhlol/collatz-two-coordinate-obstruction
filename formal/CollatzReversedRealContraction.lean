import CollatzReversedRealGrowth

namespace CollatzResearch.RealContraction

open Matrix CollatzCertificate RealAffine

variable {ι : Type*} [Fintype ι]

theorem affine_upper_box_of_positive_contraction [Nonempty ι]
    (B : Affine ι) (x v : Vec ι) (hv : ∀ i, 0 < v i)
    (hc : ∀ i, (B.matrix *ᵥ v) i < v i) :
    ∃ u : Vec ι, x ≤ u ∧ eval B u ≤ u := by
  classical
  let t : ι → ℝ := fun i => max (x i / v i) (B.offset i / (v i - (B.matrix *ᵥ v) i))
  let M := Finset.univ.sup' Finset.univ_nonempty t
  have ht (i : ι) : t i ≤ M := Finset.le_sup' t (Finset.mem_univ i)
  refine ⟨M • v, ?_, ?_⟩
  · intro i
    have hi : x i / v i ≤ M := (le_max_left _ _).trans (ht i)
    exact (div_le_iff₀ (hv i)).mp hi
  · intro i
    have hi : B.offset i / (v i - (B.matrix *ᵥ v) i) ≤ M := (le_max_right _ _).trans (ht i)
    have hb := (div_le_iff₀ (sub_pos.mpr (hc i))).mp hi
    change (B.matrix *ᵥ (M • v)) i + B.offset i ≤ (M • v) i
    rw [mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    nlinarith

theorem affine_iterates_bounded_by_postfixed
    (B : Affine ι) (hB : B.Nonnegative) (x u : Vec ι)
    (hx : x ≤ u) (hu : eval B u ≤ u) (n : ℕ) : (eval B)^[n] x ≤ u := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (eval_monotone hB.1 ih).trans hu

theorem reversed_real_excludes_postfixed_above_initial
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (u : Vec ι) (hu : C.offset ≤ u) (hpost : eval B u ≤ u) : False := by
  obtain ⟨N, hN⟩ := RealGrowth.real_reversed_word_b_growth A B C D E F G i₀
    hA hB hC hD hE hF hG h hstrict [] (eval D u i₀)
  have hg := hN N le_rfl
  have hb := eval_monotone hD.1 (affine_iterates_bounded_by_postfixed B hB C.offset u hu hpost N) i₀
  exact not_lt_of_ge hb (by simpa only [RankGrowth.wordEval] using hg)

theorem reversed_real_excludes_positive_contraction
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (v : Vec ι) (hv : ∀ i, 0 < v i) :
    ∃ i, v i ≤ (B.matrix *ᵥ v) i := by
  letI : Nonempty ι := ⟨i₀⟩
  by_contra hn
  have hc : ∀ i, (B.matrix *ᵥ v) i < v i := by
    intro i
    by_contra hi
    exact hn ⟨i, le_of_not_gt hi⟩
  obtain ⟨u, hu, hpost⟩ := affine_upper_box_of_positive_contraction B C.offset v hv hc
  exact reversed_real_excludes_postfixed_above_initial A B C D E F G i₀
    hA hB hC hD hE hF hG h hstrict u hu hpost

theorem reversed_real_second_binary_row_sum_bound
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) :
    ∃ i, 1 ≤ ∑ j, B.matrix i j := by
  obtain ⟨i, hi⟩ := reversed_real_excludes_positive_contraction A B C D E F G i₀
    hA hB hC hD hE hF hG h hstrict (fun _ => 1) (fun _ => zero_lt_one)
  exact ⟨i, by simpa only [mulVec, dotProduct, mul_one] using hi⟩

#print axioms affine_upper_box_of_positive_contraction
#print axioms affine_iterates_bounded_by_postfixed
#print axioms reversed_real_excludes_postfixed_above_initial
#print axioms reversed_real_excludes_positive_contraction
#print axioms reversed_real_second_binary_row_sum_bound

end CollatzResearch.RealContraction
