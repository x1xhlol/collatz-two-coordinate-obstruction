import FullTwoMatrixBasic

namespace CollatzCertificate.FullTwoMatrix

open Matrix

def ExactSwaps (A B E F G : M2) : Prop :=
  A * E = E * A ∧ A * F = E * B ∧ A * G = F * A ∧
  B * E = F * B ∧ B * F = G * A ∧ B * G = G * B

theorem exact_swaps_of_total_offdiagonal_positive (A B C D E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (h : WeakRules A B C D E F G)
    (h01 : 0 < ((A+B)+(E+F+G)) 0 1)
    (h10 : 0 < ((A+B)+(E+F+G)) 1 0) : ExactSwaps A B E F G := by
  let H := (A+B)+(E+F+G)
  let P := A+B
  have hH : EntrywiseLE 0 H := by
    intro i j
    exact add_nonneg (add_nonneg (hA i j) (hB i j))
      (add_nonneg (add_nonneg (hE i j) (hF i j)) (hG i j))
  have hdiff : EntrywiseLE 0 (P*H-H*P) := by
    intro i j
    change 0 ≤ (P*H-H*P) i j
    simp only [H, P, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Matrix.sub_apply]
    linarith [h.ae i j, h.af i j, h.ag i j, h.be i j, h.bf i j, h.bg i j]
  have hreturn (i j : Fin 2) : ∃ k : ℕ, 0 < (H^k) j i := by
    fin_cases i <;> fin_cases j
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simpa [H] using h10⟩
    · exact ⟨1, by simpa [H] using h01⟩
    · exact ⟨0, by simp⟩
  have hex (i j : Fin 2) :
      (A*E) i j = (E*A) i j ∧ (A*F) i j = (E*B) i j ∧
      (A*G) i j = (F*A) i j ∧ (B*E) i j = (F*B) i j ∧
      (B*F) i j = (G*A) i j ∧ (B*G) i j = (G*B) i j := by
    obtain ⟨k, hk⟩ := hreturn i j
    have hz := nonnegative_commutator_zero_at_return H P hH hdiff k i j hk
    simp only [H, P, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Matrix.sub_apply] at hz
    have h1 := h.ae i j
    have h2 := h.af i j
    have h3 := h.ag i j
    have h4 := h.be i j
    have h5 := h.bf i j
    have h6 := h.bg i j
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  exact ⟨Matrix.ext (fun i j => (hex i j).1),
    Matrix.ext (fun i j => (hex i j).2.1), Matrix.ext (fun i j => (hex i j).2.2.1),
    Matrix.ext (fun i j => (hex i j).2.2.2.1), Matrix.ext (fun i j => (hex i j).2.2.2.2.1),
    Matrix.ext (fun i j => (hex i j).2.2.2.2.2)⟩

theorem orientation_or_exact_swaps (A B C D E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (h : WeakRules A B C D E F G) :
    Upper A B E F G ∨ Lower A B E F G ∨ ExactSwaps A B E F G := by
  by_cases h10 : ((A+B)+(E+F+G)) 1 0 = 0
  · left
    simp only [Matrix.add_apply] at h10
    have h1 := hA 1 0
    have h2 := hB 1 0
    have h3 := hE 1 0
    have h4 := hF 1 0
    have h5 := hG 1 0
    change 0 ≤ A 1 0 at h1
    change 0 ≤ B 1 0 at h2
    change 0 ≤ E 1 0 at h3
    change 0 ≤ F 1 0 at h4
    change 0 ≤ G 1 0 at h5
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  by_cases h01 : ((A+B)+(E+F+G)) 0 1 = 0
  · right; left
    simp only [Matrix.add_apply] at h01
    have h1 := hA 0 1
    have h2 := hB 0 1
    have h3 := hE 0 1
    have h4 := hF 0 1
    have h5 := hG 0 1
    change 0 ≤ A 0 1 at h1
    change 0 ≤ B 0 1 at h2
    change 0 ≤ E 0 1 at h3
    change 0 ≤ F 0 1 at h4
    change 0 ≤ G 0 1 at h5
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  right; right
  apply exact_swaps_of_total_offdiagonal_positive A B C D E F G hA hB hE hF hG h
  · exact lt_of_le_of_ne (add_nonneg (add_nonneg (hA 0 1) (hB 0 1))
      (add_nonneg (add_nonneg (hE 0 1) (hF 0 1)) (hG 0 1))) (Ne.symm h01)
  · exact lt_of_le_of_ne (add_nonneg (add_nonneg (hA 1 0) (hB 1 0))
      (add_nonneg (add_nonneg (hE 1 0) (hF 1 0)) (hG 1 0))) (Ne.symm h10)

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.exact_swaps_of_total_offdiagonal_positive
#print axioms CollatzCertificate.FullTwoMatrix.orientation_or_exact_swaps
