import ReversedReadoutEigenrow

namespace CollatzCertificate

open Matrix

local infix:50 " ≤ₘ " => EntrywiseLE

variable {n : Type*} [Fintype n]

theorem second_row_first_eigenrow_gaps
    {A B F G : Mat n} {a b e f g γ r : Vec n} {β : ℝ}
    (hA : 0 ≤ₘ A) (hB : 0 ≤ₘ B) (hF : 0 ≤ₘ F) (hG : 0 ≤ₘ G)
    (ha : 0 ≤ a) (he : 0 ≤ e) (hf : 0 ≤ f) (hγ : 0 ≤ γ)
    (hgaMatrix : A * F ≤ₘ G * A)
    (hgaOffset : A *ᵥ f + a ≤ G *ᵥ a + g)
    (hfaOffset : B *ᵥ e + b ≤ F *ᵥ a + f)
    (hgc : (B * A) *ᵥ γ + B *ᵥ a + b ≤ G *ᵥ γ + g)
    (hr : Admissible A B G b g r) (hβ : 1 ≤ β)
    (heigen : (r ᵥ* B) ᵥ* A = β • (r ᵥ* B)) :
    r ⬝ᵥ a = 0 ∧ r ⬝ᵥ (b - g) = 0 := by
  have hrow : r ᵥ* B ≤ (r ᵥ* B) ᵥ* A := by
    rw [heigen]
    intro j
    have hn := rowMul_nonneg hr.nonneg hB j
    change (0 : ℝ) ≤ (r ᵥ* B) j at hn
    change (r ᵥ* B) j ≤ β * (r ᵥ* B) j
    nlinarith
  have hg := row_order_zero_second_gap hB ha hγ hgc hr hrow
  have hb := first_gap_le_BAa hA hB hF hG ha he hf
    hgaMatrix hgaOffset hfaOffset hr hg.2 hg.1.symm
  rw [← vecMul_vecMul, heigen, smul_dotProduct, hg.2, smul_zero] at hb
  exact ⟨le_antisymm hb (dotProduct_nonneg_of_nonneg hr.nonneg ha),
    by rw [dotProduct_sub, hg.1, sub_self]⟩

theorem five_affine_rules_gaps_zero_of_second_row_first_eigenrow
    (A B C D E F G : Affine n) (i₀ : n) (β : ℝ)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative)
    (hG : G.Nonnegative)
    (hda : (D.comp A).Weak D)
    (hdb : (D.comp B).Weak (D.comp G))
    (hfa : (F.comp A).Weak (B.comp E))
    (hga : (G.comp A).Weak (A.comp F))
    (hgc : (G.comp C).Weak (B.comp (A.comp C)))
    (hβ : 1 ≤ β)
    (heigen : (D.matrix i₀ ᵥ* B.matrix) ᵥ* A.matrix = β • (D.matrix i₀ ᵥ* B.matrix)) :
    ((D.comp A).offset - D.offset) i₀ = 0 ∧
    ((D.comp B).offset - (D.comp G).offset) i₀ = 0 := by
  let r : Vec n := D.matrix i₀
  have hr : Admissible A.matrix B.matrix G.matrix B.offset G.offset r := by
    refine ⟨fun j => hD.1 i₀ j, ?_, ?_, ?_⟩
    · intro j
      exact hda.1 i₀ j
    · intro j
      exact hdb.1 i₀ j
    · have h := hdb.2 i₀
      change (D.matrix *ᵥ G.offset) i₀ + D.offset i₀ ≤
        (D.matrix *ᵥ B.offset) i₀ + D.offset i₀ at h
      exact (add_le_add_iff_right (D.offset i₀)).mp h
  have hgc' : (B.matrix * A.matrix) *ᵥ C.offset + B.matrix *ᵥ A.offset + B.offset ≤
      G.matrix *ᵥ C.offset + G.offset := by
    have h := hgc.2
    change B.matrix *ᵥ (A.matrix *ᵥ C.offset + A.offset) + B.offset ≤
      G.matrix *ᵥ C.offset + G.offset at h
    simpa only [mulVec_add, mulVec_mulVec] using h
  have h := second_row_first_eigenrow_gaps hA.1 hB.1 hF.1 hG.1
    hA.2 hE.2 hF.2 hC.2 hga.1 hga.2 hfa.2 hgc' hr hβ heigen
  constructor
  · change (r ⬝ᵥ A.offset + D.offset i₀) - D.offset i₀ = 0
    linarith [h.1]
  · change (r ⬝ᵥ B.offset + D.offset i₀) -
      (r ⬝ᵥ G.offset + D.offset i₀) = 0
    simpa only [dotProduct_sub, add_sub_add_right_eq_sub] using h.2

theorem five_affine_rules_gaps_zero_of_scalar_first_matrix [DecidableEq n]
    (A B C D E F G : Affine n) (i₀ : n) (β : ℝ)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative)
    (hG : G.Nonnegative)
    (hda : (D.comp A).Weak D)
    (hdb : (D.comp B).Weak (D.comp G))
    (hfa : (F.comp A).Weak (B.comp E))
    (hga : (G.comp A).Weak (A.comp F))
    (hgc : (G.comp C).Weak (B.comp (A.comp C)))
    (hscalar : A.matrix = β • 1) :
    ((D.comp A).offset - D.offset) i₀ = 0 ∧
    ((D.comp B).offset - (D.comp G).offset) i₀ = 0 := by
  classical
  by_cases hz : D.matrix i₀ = 0
  · change ((D.matrix i₀ ⬝ᵥ A.offset + D.offset i₀) - D.offset i₀ = 0) ∧
      ((D.matrix i₀ ⬝ᵥ B.offset + D.offset i₀) -
        (D.matrix i₀ ⬝ᵥ G.offset + D.offset i₀) = 0)
    simp [hz]
  · have hp : ∃ j, 0 < D.matrix i₀ j := by
      by_contra hn
      apply hz
      funext j
      have hle : D.matrix i₀ j ≤ 0 := by
        by_contra h
        exact hn ⟨j, lt_of_not_ge h⟩
      exact le_antisymm hle (hD.1 i₀ j)
    obtain ⟨j, hj⟩ := hp
    have hrow := hda.1 i₀ j
    change D.matrix i₀ j ≤ (D.matrix i₀ ᵥ* A.matrix) j at hrow
    rw [hscalar, vecMul_smul, vecMul_one] at hrow
    have hβ : 1 ≤ β := by
      change D.matrix i₀ j ≤ β * D.matrix i₀ j at hrow
      nlinarith
    apply five_affine_rules_gaps_zero_of_second_row_first_eigenrow A B C D E F G i₀ β
      hA hB hC hD hE hF hG hda hdb hfa hga hgc hβ
    rw [hscalar, vecMul_smul, vecMul_one]

#print axioms second_row_first_eigenrow_gaps
#print axioms five_affine_rules_gaps_zero_of_second_row_first_eigenrow
#print axioms five_affine_rules_gaps_zero_of_scalar_first_matrix

end CollatzCertificate
