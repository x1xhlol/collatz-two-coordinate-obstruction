import FullTwoMatrixTriangular

namespace CollatzCertificate.FullTwoMatrix

open Matrix

theorem triangular_common_diagonals (A B C D E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (hA₀ : 1 ≤ A 0 0) (hB₀ : 1 ≤ B 0 0) (hF₀ : 1 ≤ F 0 0)
    (h : WeakRules A B C D E F G) (ho : Upper A B E F G ∨ Lower A B E F G) :
    A 0 0 = B 0 0 ∧ E 0 0 = F 0 0 ∧ G 0 0 = F 0 0 := by
  have hh := forward_swap_equalities_on_diagonal A B C D E F G hA hB hE hF hG h 0
  apply equal_first_diagonals (A 0 0) (B 0 0) (E 0 0) (F 0 0) (G 0 0) hA₀ hB₀ hF₀
  all_goals rcases ho with ⟨ha, hb, he, hf, hg⟩ | ⟨ha, hb, he, hf, hg⟩
  all_goals simp only [Matrix.mul_apply, Fin.sum_univ_two, ha, hb, he, hf, hg,
    zero_mul, mul_zero, add_zero] at hh
  all_goals first | exact hh.2.2.1 | exact hh.2.2.2.1 | exact hh.2.1

theorem upper_first_diagonals_one (A B C D E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hC : EntrywiseLE 0 C)
    (hD : EntrywiseLE 0 D) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (hA₀ : 1 ≤ A 0 0) (hB₀ : 1 ≤ B 0 0) (hC₀ : 1 ≤ C 0 0)
    (hD₀ : 1 ≤ D 0 0) (hF₀ : 1 ≤ F 0 0)
    (h : WeakRules A B C D E F G) (ho : Upper A B E F G) :
    A 0 0 = 1 ∧ B 0 0 = 1 ∧ E 0 0 = 1 ∧ F 0 0 = 1 ∧ G 0 0 = 1 := by
  obtain ⟨hab, hef, hgf⟩ := triangular_common_diagonals A B C D E F G
    hA hB hE hF hG hA₀ hB₀ hF₀ h (Or.inl ho)
  rcases ho with ⟨ha, hb, he, hf, hg⟩
  have hcg00 := h.cg 0 0
  have hbd00 := h.bd 0 0
  have had10 := h.ad 1 0
  have hbd10 := h.bd 1 0
  have hcg01 := h.cg 0 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, ha, hb, he, hf, hg,
    ← hab, hef, hgf, zero_mul, mul_zero, add_zero, zero_add] at hcg00 hbd00 had10 hbd10 hcg01
  obtain ⟨ht, hs⟩ := upper_scalar_diagonals_one
    (A 0 0) (F 0 0) (A 0 1) (B 0 1) (G 0 1) (A 1 1) (B 1 1) (G 1 1)
    (C 0 0) (C 0 1) (D 0 0) (D 1 0)
    hA₀ hF₀ (hA 0 1) (hB 0 1) (hB 1 1) (hG 1 1)
    hC₀ (hC 0 1) hD₀ (hD 1 0) hcg00 hbd00 had10 hbd10 hcg01
  exact ⟨ht, hab ▸ ht, hef.trans hs, hs, hgf.trans hs⟩

theorem lower_first_diagonals_one (A B C D E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hC : EntrywiseLE 0 C)
    (hD : EntrywiseLE 0 D) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (hA₀ : 1 ≤ A 0 0) (hB₀ : 1 ≤ B 0 0) (hC₀ : 1 ≤ C 0 0)
    (hD₀ : 1 ≤ D 0 0) (hF₀ : 1 ≤ F 0 0)
    (h : WeakRules A B C D E F G) (ho : Lower A B E F G) :
    A 0 0 = 1 ∧ B 0 0 = 1 ∧ E 0 0 = 1 ∧ F 0 0 = 1 ∧ G 0 0 = 1 := by
  obtain ⟨hab, hef, hgf⟩ := triangular_common_diagonals A B C D E F G
    hA hB hE hF hG hA₀ hB₀ hF₀ h (Or.inr ho)
  have hh := forward_swap_equalities_on_diagonal A B C D E F G hA hB hE hF hG h 1
  rcases ho with ⟨ha, hb, he, hf, hg⟩
  have hbd00 := h.bd 0 0
  have hce00 := h.ce 0 0
  have hcf00 := h.cf 0 0
  have hcg00 := h.cg 0 0
  have hce01 := h.ce 0 1
  have hcf01 := h.cf 0 1
  have hcg01 := h.cg 0 1
  have hbd10 := h.bd 1 0
  have hae10 := h.ae 1 0
  have hag10 := h.ag 1 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, ha, hb, he, hf, hg,
    ← hab, hef, hgf, zero_mul, mul_zero, add_zero, zero_add] at hh hbd00 hce00 hcf00 hcg00 hce01 hcf01 hcg01 hbd10 hae10 hag10
  have hcf00' : C 0 0 * (A 0 0 * A 0 0) + C 0 1 * ((A 0 0 + A 1 1) * A 1 0) ≤
      C 0 0 * F 0 0 + C 0 1 * F 1 0 := by nlinarith only [hcf00]
  obtain ⟨ht, hs⟩ := lower_scalar_diagonals_one
    (A 0 0) (F 0 0) (A 1 0) (B 1 0) (E 1 0) (F 1 0) (G 1 0)
    (A 1 1) (B 1 1) (E 1 1) (F 1 1) (G 1 1)
    (C 0 0) (C 0 1) (D 0 0) (D 1 0)
    hA₀ hF₀ (hA 1 0) (hB 1 0) (hA 1 1) (hB 1 1) (hE 1 1) (hF 1 1) (hG 1 1)
    hC₀ (hC 0 1) hD₀ (hD 1 0) hbd00 hce00 hcf00' (by simpa only [mul_comm (A 1 0) (A 0 0)] using hcg00) hce01 hcf01 hcg01
    hh.2.1 hh.2.2.1 hh.2.2.2.2.1 hbd10 hae10 hag10
  exact ⟨ht, hab ▸ ht, hef.trans hs, hs, hgf.trans hs⟩

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.upper_first_diagonals_one
#print axioms CollatzCertificate.FullTwoMatrix.lower_first_diagonals_one
