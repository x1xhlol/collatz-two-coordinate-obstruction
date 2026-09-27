import ReversedBinaryPowerClosure

namespace CollatzCertificate

open Matrix

local infix:50 " ≤ₘ " => EntrywiseLE

variable {n : Type*} [Fintype n]

theorem row_order_zero_second_gap
    {A B G : Mat n} {a b g γ r : Vec n}
    (hB : 0 ≤ₘ B) (ha : 0 ≤ a) (hγ : 0 ≤ γ)
    (hgc : (B * A) *ᵥ γ + B *ᵥ a + b ≤ G *ᵥ γ + g)
    (hr : Admissible A B G b g r)
    (hrow : r ᵥ* B ≤ (r ᵥ* B) ᵥ* A) :
    r ⬝ᵥ g = r ⬝ᵥ b ∧ (r ᵥ* B) ⬝ᵥ a = 0 := by
  have h1 := dotProduct_le_dotProduct_of_nonneg_right (hr.dbMatrix.trans hrow) hγ
  have h2 := dotProduct_le_dotProduct_of_nonneg_left hgc hr.nonneg
  have h3 := dotProduct_nonneg_of_nonneg (rowMul_nonneg hr.nonneg hB) ha
  simp only [dotProduct_add, dotProduct_mulVec, vecMul_vecMul] at h1 h2
  constructor <;> linarith [hr.dbOffset]

theorem row_domination_zero_gaps
    {A B G : Mat n} {a b g γ r : Vec n} {ε : ℝ}
    (hB : 0 ≤ₘ B) (ha : 0 ≤ a) (hγ : 0 ≤ γ)
    (hgc : (B * A) *ᵥ γ + B *ᵥ a + b ≤ G *ᵥ γ + g)
    (hr : Admissible A B G b g r)
    (hrow : r ᵥ* B ≤ (r ᵥ* B) ᵥ* A)
    (hε : 0 < ε) (hdom : ε • r ≤ r ᵥ* B) :
    r ⬝ᵥ a = 0 ∧ r ⬝ᵥ (b - g) = 0 := by
  have hz := row_order_zero_second_gap hB ha hγ hgc hr hrow
  have hle := dotProduct_le_dotProduct_of_nonneg_right hdom ha
  have hn := dotProduct_nonneg_of_nonneg hr.nonneg ha
  rw [smul_dotProduct, hz.2] at hle
  constructor
  · change ε * (r ⬝ᵥ a) ≤ 0 at hle
    nlinarith
  · rw [dotProduct_sub, hz.1, sub_self]

theorem zero_second_binary_row_gaps
    {A B F G : Mat n} {a b e f g γ r : Vec n}
    (hA : 0 ≤ₘ A) (hB : 0 ≤ₘ B) (hF : 0 ≤ₘ F) (hG : 0 ≤ₘ G)
    (ha : 0 ≤ a) (he : 0 ≤ e) (hf : 0 ≤ f) (hγ : 0 ≤ γ)
    (hgaMatrix : A * F ≤ₘ G * A)
    (hgaOffset : A *ᵥ f + a ≤ G *ᵥ a + g)
    (hfaOffset : B *ᵥ e + b ≤ F *ᵥ a + f)
    (hgc : (B * A) *ᵥ γ + B *ᵥ a + b ≤ G *ᵥ γ + g)
    (hr : Admissible A B G b g r) (hz : r ᵥ* B = 0) :
    r ⬝ᵥ a = 0 ∧ r ⬝ᵥ (b - g) = 0 := by
  have hrow : r ᵥ* B ≤ (r ᵥ* B) ᵥ* A := by simp [hz]
  have hg := row_order_zero_second_gap hB ha hγ hgc hr hrow
  have hle := first_gap_le_BAa hA hB hF hG ha he hf
    hgaMatrix hgaOffset hfaOffset hr hg.2 hg.1.symm
  rw [← vecMul_vecMul, hz, zero_vecMul, zero_dotProduct] at hle
  exact ⟨le_antisymm hle (dotProduct_nonneg_of_nonneg hr.nonneg ha),
    by rw [dotProduct_sub, hg.1, sub_self]⟩

theorem second_binary_readout_eigenrow_gaps
    {A B F G : Mat n} {a b e f g γ r : Vec n} {β : ℝ}
    (hA : 0 ≤ₘ A) (hB : 0 ≤ₘ B) (hF : 0 ≤ₘ F) (hG : 0 ≤ₘ G)
    (ha : 0 ≤ a) (he : 0 ≤ e) (hf : 0 ≤ f) (hγ : 0 ≤ γ)
    (hgaMatrix : A * F ≤ₘ G * A)
    (hgaOffset : A *ᵥ f + a ≤ G *ᵥ a + g)
    (hfaOffset : B *ᵥ e + b ≤ F *ᵥ a + f)
    (hgc : (B * A) *ᵥ γ + B *ᵥ a + b ≤ G *ᵥ γ + g)
    (hr : Admissible A B G b g r) (hβ : 0 ≤ β)
    (heigen : r ᵥ* B = β • r) :
    r ⬝ᵥ a = 0 ∧ r ⬝ᵥ (b - g) = 0 := by
  rcases eq_or_lt_of_le hβ with hz | hp
  · apply zero_second_binary_row_gaps hA hB hF hG ha he hf hγ
      hgaMatrix hgaOffset hfaOffset hgc hr
    simpa [← hz] using heigen
  · have hrow : r ᵥ* B ≤ (r ᵥ* B) ᵥ* A := by
      rw [heigen, smul_vecMul]
      intro j
      exact mul_le_mul_of_nonneg_left (hr.da j) hβ
    exact row_domination_zero_gaps hB ha hγ hgc hr hrow hp (le_of_eq heigen.symm)

theorem five_affine_rules_gaps_zero_of_second_eigenrow
    (A B C D E F G : Affine n) (i₀ : n) (β : ℝ)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative)
    (hG : G.Nonnegative)
    (hda : (D.comp A).Weak D)
    (hdb : (D.comp B).Weak (D.comp G))
    (hfa : (F.comp A).Weak (B.comp E))
    (hga : (G.comp A).Weak (A.comp F))
    (hgc : (G.comp C).Weak (B.comp (A.comp C)))
    (hβ : 0 ≤ β) (heigen : D.matrix i₀ ᵥ* B.matrix = β • D.matrix i₀) :
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
  have h := second_binary_readout_eigenrow_gaps hA.1 hB.1 hF.1 hG.1
    hA.2 hE.2 hF.2 hC.2 hga.1 hga.2 hfa.2 hgc' hr hβ heigen
  constructor
  · change (r ⬝ᵥ A.offset + D.offset i₀) - D.offset i₀ = 0
    linarith [h.1]
  · change (r ⬝ᵥ B.offset + D.offset i₀) -
      (r ⬝ᵥ G.offset + D.offset i₀) = 0
    simpa only [dotProduct_sub, add_sub_add_right_eq_sub] using h.2

theorem five_affine_rules_gaps_zero_of_scalar_second_matrix [DecidableEq n]
    (A B C D E F G : Affine n) (i₀ : n) (β : ℝ)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative)
    (hG : G.Nonnegative)
    (hda : (D.comp A).Weak D)
    (hdb : (D.comp B).Weak (D.comp G))
    (hfa : (F.comp A).Weak (B.comp E))
    (hga : (G.comp A).Weak (A.comp F))
    (hgc : (G.comp C).Weak (B.comp (A.comp C)))
    (hβ : 0 ≤ β) (hscalar : B.matrix = β • 1) :
    ((D.comp A).offset - D.offset) i₀ = 0 ∧
    ((D.comp B).offset - (D.comp G).offset) i₀ = 0 := by
  apply five_affine_rules_gaps_zero_of_second_eigenrow A B C D E F G i₀ β
    hA hB hC hD hE hF hG hda hdb hfa hga hgc hβ
  rw [hscalar, vecMul_smul, vecMul_one]

#print axioms row_order_zero_second_gap
#print axioms row_domination_zero_gaps
#print axioms zero_second_binary_row_gaps
#print axioms second_binary_readout_eigenrow_gaps
#print axioms five_affine_rules_gaps_zero_of_second_eigenrow
#print axioms five_affine_rules_gaps_zero_of_scalar_second_matrix

end CollatzCertificate
