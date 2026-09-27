import CollatzReversedRealRowContraction

namespace CollatzResearch.RealCriticalReadout

open Matrix CollatzCertificate RealAffine RealMixedGrowth

variable {ι : Type*} [Fintype ι]

theorem critical_readout_offset_zero
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hF : F.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hqA : D.matrix i₀ ≤ (D.matrix i₀ ᵥ* B.matrix) ᵥ* A.matrix)
    (hqB : (D.matrix i₀ ᵥ* B.matrix) ᵥ* B.matrix = D.matrix i₀ ᵥ* B.matrix)
    (hqE : (D.matrix i₀ ᵥ* B.matrix) ᵥ* E.matrix ≤ D.matrix i₀)
    (hrF : D.matrix i₀ ᵥ* F.matrix ≤ D.matrix i₀) :
    (D.matrix i₀ ᵥ* B.matrix) ⬝ᵥ B.offset = 0 ∧
      D.matrix i₀ ⬝ᵥ G.offset = D.matrix i₀ ⬝ᵥ B.offset := by
  let r : Vec ι := D.matrix i₀
  let q : Vec ι := r ᵥ* B.matrix
  have hr : 0 ≤ r := fun j => hD.1 i₀ j
  have hq : 0 ≤ q := rowMul_nonneg hr hB.1
  have hrA : r ≤ r ᵥ* A.matrix := fun j => h.da.1 i₀ j
  have hrG : r ᵥ* G.matrix ≤ q := fun j => h.db.1 i₀ j
  have hrg : r ⬝ᵥ G.offset ≤ r ⬝ᵥ B.offset := by
    have hi := h.db.2 i₀
    change r ⬝ᵥ G.offset + D.offset i₀ ≤ r ⬝ᵥ B.offset + D.offset i₀ at hi
    linarith
  have hgc := dotProduct_le_dotProduct_of_nonneg_left h.gc.2 hr
  have hec := dotProduct_le_dotProduct_of_nonneg_left h.ec.2 hq
  have hfa := dotProduct_le_dotProduct_of_nonneg_left h.fa.2 hr
  have hga := dotProduct_le_dotProduct_of_nonneg_left h.ga.2 hr
  change r ⬝ᵥ (B.matrix *ᵥ (A.matrix *ᵥ C.offset + A.offset) + B.offset) ≤
    r ⬝ᵥ (G.matrix *ᵥ C.offset + G.offset) at hgc
  change q ⬝ᵥ (B.matrix *ᵥ C.offset + B.offset) ≤
    q ⬝ᵥ (E.matrix *ᵥ C.offset + E.offset) at hec
  change r ⬝ᵥ (B.matrix *ᵥ E.offset + B.offset) ≤
    r ⬝ᵥ (F.matrix *ᵥ A.offset + F.offset) at hfa
  change r ⬝ᵥ (A.matrix *ᵥ F.offset + A.offset) ≤
    r ⬝ᵥ (G.matrix *ᵥ A.offset + G.offset) at hga
  simp only [dotProduct_add, dotProduct_mulVec] at hgc hec hfa hga
  change r ≤ q ᵥ* A.matrix at hqA
  change q ᵥ* B.matrix = q at hqB
  change q ᵥ* E.matrix ≤ r at hqE
  change r ᵥ* F.matrix ≤ r at hrF
  change (q ᵥ* A.matrix) ⬝ᵥ C.offset + q ⬝ᵥ A.offset + r ⬝ᵥ B.offset ≤
    (r ᵥ* G.matrix) ⬝ᵥ C.offset + r ⬝ᵥ G.offset at hgc
  change q ⬝ᵥ E.offset + r ⬝ᵥ B.offset ≤
    (r ᵥ* F.matrix) ⬝ᵥ A.offset + r ⬝ᵥ F.offset at hfa
  rw [hqB] at hec
  have h1 := dotProduct_le_dotProduct_of_nonneg_right hqA hC.2
  have h2 := dotProduct_le_dotProduct_of_nonneg_right hrG hC.2
  have h3 := dotProduct_le_dotProduct_of_nonneg_right hqE hC.2
  have h4 := dotProduct_le_dotProduct_of_nonneg_right hrF hA.2
  have h5 := dotProduct_le_dotProduct_of_nonneg_right hrA hF.2
  have h6 := dotProduct_le_dotProduct_of_nonneg_right hrG hA.2
  have hn := dotProduct_nonneg_of_nonneg hq hB.2
  change q ⬝ᵥ B.offset = 0 ∧ r ⬝ᵥ G.offset = r ⬝ᵥ B.offset
  constructor <;> linarith

theorem row_nondecrease_fixed_by_positive_vector
    (M : Mat ι) (r u : Vec ι) (hu : ∀ j, 0 < u j)
    (hMu : M *ᵥ u = u) (hr : r ≤ r ᵥ* M) : r ᵥ* M = r := by
  have hz : ((r ᵥ* M) - r) ⬝ᵥ u = 0 := by
    rw [sub_dotProduct, ← dotProduct_mulVec, hMu, sub_self]
  have hn (j : ι) : 0 ≤ ((r ᵥ* M) j - r j) * u j :=
    mul_nonneg (sub_nonneg.mpr (hr j)) (hu j).le
  have he (j : ι) : ((r ᵥ* M) j - r j) * u j = 0 :=
    congrFun ((Fintype.sum_eq_zero_iff_of_nonneg hn).mp hz) j
  funext j
  exact sub_eq_zero.mp ((mul_eq_zero.mp (he j)).resolve_right (ne_of_gt (hu j)))

variable [DecidableEq ι]

theorem critical_readout_excludes_strict
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (hqA : D.matrix i₀ ≤ (D.matrix i₀ ᵥ* B.matrix) ᵥ* A.matrix)
    (hqB : (D.matrix i₀ ᵥ* B.matrix) ᵥ* B.matrix = D.matrix i₀ ᵥ* B.matrix)
    (hqE : (D.matrix i₀ ᵥ* B.matrix) ᵥ* E.matrix ≤ D.matrix i₀)
    (hrF : D.matrix i₀ ᵥ* F.matrix ≤ D.matrix i₀) : False := by
  have hz := critical_readout_offset_zero A B C D E F G i₀ hA hB hC hD hF
    h hqA hqB hqE hrF
  have hgrowth : ∀ K : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K < (D.matrix i₀ ᵥ* B.matrix) ⬝ᵥ ((eval B)^[n] C.offset) := by
    simpa only [matrixWord, affineDigit, mul_one] using
      real_reversed_mixed_row_growth A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict [.b]
  rcases RealRowContraction.unbounded_row_has_offset_or_increase B _ C.offset hB hC.2 hgrowth
    with hoff | ⟨j, hj⟩
  · exact (ne_of_gt hoff) hz.1
  · rw [hqB] at hj
    exact (lt_irrefl _ hj)

theorem critical_readout_gaps_zero
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hqA : D.matrix i₀ ≤ (D.matrix i₀ ᵥ* B.matrix) ᵥ* A.matrix)
    (hqB : (D.matrix i₀ ᵥ* B.matrix) ᵥ* B.matrix = D.matrix i₀ ᵥ* B.matrix)
    (hqE : (D.matrix i₀ ᵥ* B.matrix) ᵥ* E.matrix ≤ D.matrix i₀)
    (hrF : D.matrix i₀ ᵥ* F.matrix ≤ D.matrix i₀) :
    (D.comp A).offset i₀ = D.offset i₀ ∧
      (D.comp B).offset i₀ = (D.comp G).offset i₀ := by
  have hn := critical_readout_excludes_strict A B C D E F G i₀
    hA hB hC hD hE hF hG h
  constructor
  · apply le_antisymm _ (h.da.2 i₀)
    by_contra hp
    exact hn (Or.inl (lt_of_not_ge hp)) hqA hqB hqE hrF
  · apply le_antisymm _ (h.db.2 i₀)
    by_contra hp
    exact hn (Or.inr (lt_of_not_ge hp)) hqA hqB hqE hrF

theorem projection_readout_gaps_zero
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hrA : D.matrix i₀ ᵥ* A.matrix = D.matrix i₀)
    (hBA : B.matrix * A.matrix = A.matrix)
    (hBB : B.matrix * B.matrix = B.matrix)
    (hEA : E.matrix = A.matrix) (hFI : F.matrix = 1) :
    (D.comp A).offset i₀ = D.offset i₀ ∧
      (D.comp B).offset i₀ = (D.comp G).offset i₀ := by
  apply critical_readout_gaps_zero A B C D E F G i₀ hA hB hC hD hE hF hG h
  · rw [vecMul_vecMul, hBA, hrA]
  · rw [vecMul_vecMul, hBB]
  · rw [hEA, vecMul_vecMul, hBA, hrA]
  · rw [hFI, vecMul_one]

theorem positive_fixed_projection_gaps_zero
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (u : Vec ι) (hu : ∀ j, 0 < u j) (hAu : A.matrix *ᵥ u = u)
    (hBA : B.matrix * A.matrix = A.matrix)
    (hBB : B.matrix * B.matrix = B.matrix)
    (hEA : E.matrix = A.matrix) (hFI : F.matrix = 1) :
    (D.comp A).offset i₀ = D.offset i₀ ∧
      (D.comp B).offset i₀ = (D.comp G).offset i₀ := by
  apply projection_readout_gaps_zero A B C D E F G i₀ hA hB hC hD hE hF hG h
    (row_nondecrease_fixed_by_positive_vector A.matrix (D.matrix i₀) u hu hAu
      (fun j => h.da.1 i₀ j)) hBA hBB hEA hFI

#print axioms critical_readout_offset_zero
#print axioms row_nondecrease_fixed_by_positive_vector
#print axioms critical_readout_excludes_strict
#print axioms critical_readout_gaps_zero
#print axioms projection_readout_gaps_zero
#print axioms positive_fixed_projection_gaps_zero

end CollatzResearch.RealCriticalReadout
