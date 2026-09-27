import ReversedTwoDimensionalNonsingularEigenShape

namespace CollatzCertificate.TwoDimensionalNonsingularEigen

open Matrix FullTwoMatrix TwoDimensionalInvertibleMiddle

theorem positive_common_eigenvalue_bounds (A B G : M2)
    (r u : Vec (Fin 2)) (l m : ℝ)
    (hr : 0 ≤ r) (hrne : r ≠ 0) (hu : ∀ i, 0 < u i)
    (hda : r ≤ r ᵥ* A) (hdb : r ᵥ* G ≤ r ᵥ* B)
    (hAu : A *ᵥ u=l • u) (hBu : B *ᵥ u=l • u) (hGu : G *ᵥ u=m • u) :
    1 ≤ l ∧ m ≤ l := by
  obtain ⟨j,hj⟩ : ∃ j, 0 < r j := by
    by_contra hn
    push_neg at hn
    apply hrne
    funext j
    exact le_antisymm (hn j) (hr j)
  have hru : 0 < r ⬝ᵥ u :=
    (Finset.sum_pos_iff_of_nonneg (fun k _ => mul_nonneg (hr k) (hu k).le)).mpr
      ⟨j,Finset.mem_univ j,mul_pos hj (hu j)⟩
  have hscale := dotProduct_le_dotProduct_of_nonneg_right hda (fun k => (hu k).le)
  rw [← dotProduct_mulVec,hAu,dotProduct_smul,smul_eq_mul] at hscale
  have hternary := dotProduct_le_dotProduct_of_nonneg_right hdb (fun k => (hu k).le)
  rw [← dotProduct_mulVec,← dotProduct_mulVec,hGu,hBu,dotProduct_smul,
    dotProduct_smul,smul_eq_mul,smul_eq_mul] at hternary
  constructor <;> nlinarith only [hscale,hternary,hru]

theorem nonsingular_eigenvector_with_bounds (A B E F G : M2) (r : Vec (Fin 2))
    (h : ReversedExactSwaps A B E F G)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B)
    (hE : EntrywiseLE 0 E) (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (ha : A.det ≠ 0) (hf : F.det ≠ 0) (hne : A*B ≠ B*A)
    (hreturn : ∀ i j : Fin 2, ∃ k : ℕ, 0 < (((A+B)+(E+F+G))^k) j i)
    (hr : 0 ≤ r) (hrne : r ≠ 0)
    (hda : r ≤ r ᵥ* A) (hdb : r ᵥ* G ≤ r ᵥ* B) :
    ∃ μ κ : ℝ, ∃ u : Vec (Fin 2), 0 < μ ∧ 0 < κ ∧
      1 ≤ 2*μ ∧ 3*κ ≤ 2*μ ∧ (∀ i, 0 < u i) ∧
      A *ᵥ u=(2*μ) • u ∧ B *ᵥ u=(2*μ) • u ∧
      E *ᵥ u=(3*κ) • u ∧ F *ᵥ u=(3*κ) • u ∧ G *ᵥ u=(3*κ) • u := by
  obtain ⟨μ,κ,u,hμ,hκ,hu,hAu,hBu,hEu,hFu,hGu⟩ :=
    nonsingular_common_positive_eigenvector A B E F G h hA hB hE hF hG ha hf hne hreturn
  obtain ⟨hl,hml⟩ := positive_common_eigenvalue_bounds A B G r u (2*μ) (3*κ)
    hr hrne hu hda hdb hAu hBu hGu
  exact ⟨μ,κ,u,hμ,hκ,hl,hml,hu,hAu,hBu,hEu,hFu,hGu⟩

end CollatzCertificate.TwoDimensionalNonsingularEigen

#print axioms CollatzCertificate.TwoDimensionalNonsingularEigen.positive_common_eigenvalue_bounds
#print axioms CollatzCertificate.TwoDimensionalNonsingularEigen.nonsingular_eigenvector_with_bounds
