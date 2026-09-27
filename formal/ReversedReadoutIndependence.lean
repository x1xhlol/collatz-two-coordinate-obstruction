import ReversedReadoutEigenrow

namespace CollatzCertificate

open Matrix

local infix:50 " ≤ₘ " => EntrywiseLE

variable {n : Type*} [Fintype n]

theorem eigenrow_of_zero_minors (r : Vec n) (B : Mat n)
    (hr : 0 ≤ r) (hB : 0 ≤ₘ B)
    (hz : ∀ i j, r i * (r ᵥ* B) j = r j * (r ᵥ* B) i) :
    ∃ β : ℝ, 0 ≤ β ∧ r ᵥ* B = β • r := by
  classical
  by_cases hrz : r = 0
  · exact ⟨0, le_refl 0, by simp [hrz]⟩
  have hp : ∃ i, 0 < r i := by
    by_contra hn
    apply hrz
    funext i
    have hle : r i ≤ 0 := by
      by_contra h
      exact hn ⟨i, lt_of_not_ge h⟩
    exact le_antisymm hle (hr i)
  obtain ⟨i, hi⟩ := hp
  refine ⟨(r ᵥ* B) i / r i, div_nonneg (rowMul_nonneg hr hB i) hi.le, ?_⟩
  funext j
  change (r ᵥ* B) j = ((r ᵥ* B) i / r i) * r j
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (ne_of_gt hi)).2
  nlinarith [hz i j]

theorem five_affine_rules_readout_minor_nonzero
    (A B C D E F G : Affine n) (i₀ : n)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative)
    (hG : G.Nonnegative)
    (hda : (D.comp A).Weak D)
    (hdb : (D.comp B).Weak (D.comp G))
    (hfa : (F.comp A).Weak (B.comp E))
    (hga : (G.comp A).Weak (A.comp F))
    (hgc : (G.comp C).Weak (B.comp (A.comp C)))
    (hs : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) :
    ∃ i j, D.matrix i₀ i * (D.matrix i₀ ᵥ* B.matrix) j ≠
      D.matrix i₀ j * (D.matrix i₀ ᵥ* B.matrix) i := by
  classical
  by_contra hn
  have hz : ∀ i j, D.matrix i₀ i * (D.matrix i₀ ᵥ* B.matrix) j =
      D.matrix i₀ j * (D.matrix i₀ ᵥ* B.matrix) i := by
    intro i j
    by_contra h
    exact hn ⟨i, j, h⟩
  obtain ⟨β, hβ, heigen⟩ := eigenrow_of_zero_minors (D.matrix i₀) B.matrix
    (fun j => hD.1 i₀ j) hB.1 hz
  have hg := five_affine_rules_gaps_zero_of_second_eigenrow A B C D E F G i₀ β
    hA hB hC hD hE hF hG hda hdb hfa hga hgc hβ heigen
  rcases hs with ha | hb
  · have h := hg.1
    change (D.comp A).offset i₀ - D.offset i₀ = 0 at h
    linarith
  · have h := hg.2
    change (D.comp B).offset i₀ - (D.comp G).offset i₀ = 0 at h
    linarith

#print axioms eigenrow_of_zero_minors
#print axioms five_affine_rules_readout_minor_nonzero

end CollatzCertificate
