import FullTwoMatrixFirstDiagonal
import FullTwoMatrixAggregate

namespace CollatzCertificate.FullTwoMatrix

open Matrix

structure ReversedWeakRules (A B C D E F G : M2) : Prop where
  da : EntrywiseLE D (D * A)
  db : EntrywiseLE (D * G) (D * B)
  ea : EntrywiseLE (A * E) (E * A)
  fa : EntrywiseLE (B * E) (F * A)
  ga : EntrywiseLE (A * F) (G * A)
  eb : EntrywiseLE (B * F) (E * B)
  fb : EntrywiseLE (A * G) (F * B)
  gb : EntrywiseLE (B * G) (G * B)
  ec : EntrywiseLE (B * C) (E * C)
  fc : EntrywiseLE ((A * A) * C) (F * C)
  gc : EntrywiseLE ((B * A) * C) (G * C)

theorem nonnegative_transpose (M : M2) (h : EntrywiseLE 0 M) : EntrywiseLE 0 Mᵀ :=
  fun i j => h j i

theorem reversed_rules_transpose (A B C D E F G : M2)
    (h : ReversedWeakRules A B C D E F G) : WeakRules Aᵀ Bᵀ Cᵀ Dᵀ Eᵀ Fᵀ Gᵀ := by
  constructor
  all_goals intro i j
  · simpa only [← transpose_mul, transpose_apply] using h.da j i
  · simpa only [← transpose_mul, transpose_apply] using h.db j i
  · simpa only [← transpose_mul, transpose_apply] using h.ea j i
  · simpa only [← transpose_mul, transpose_apply] using h.fa j i
  · simpa only [← transpose_mul, transpose_apply] using h.ga j i
  · simpa only [← transpose_mul, transpose_apply] using h.eb j i
  · simpa only [← transpose_mul, transpose_apply] using h.fb j i
  · simpa only [← transpose_mul, transpose_apply] using h.gb j i
  · simpa only [← transpose_mul, transpose_apply] using h.ec j i
  · simpa only [← transpose_mul, transpose_apply] using h.fc j i
  · simpa only [← transpose_mul, transpose_apply] using h.gc j i

theorem reversed_triangular_first_diagonals_one (A B C D E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hC : EntrywiseLE 0 C)
    (hD : EntrywiseLE 0 D) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (hA₀ : 1 ≤ A 0 0) (hB₀ : 1 ≤ B 0 0) (hC₀ : 1 ≤ C 0 0)
    (hD₀ : 1 ≤ D 0 0) (hF₀ : 1 ≤ F 0 0)
    (h : ReversedWeakRules A B C D E F G) (ho : Upper A B E F G ∨ Lower A B E F G) :
    A 0 0 = 1 ∧ B 0 0 = 1 ∧ E 0 0 = 1 ∧ F 0 0 = 1 ∧ G 0 0 = 1 := by
  have ht := reversed_rules_transpose A B C D E F G h
  rcases ho with hu | hl
  · exact lower_first_diagonals_one Aᵀ Bᵀ Cᵀ Dᵀ Eᵀ Fᵀ Gᵀ
      (nonnegative_transpose A hA) (nonnegative_transpose B hB) (nonnegative_transpose C hC)
      (nonnegative_transpose D hD) (nonnegative_transpose E hE)
      (nonnegative_transpose F hF) (nonnegative_transpose G hG)
      hA₀ hB₀ hC₀ hD₀ hF₀ ht hu
  · exact upper_first_diagonals_one Aᵀ Bᵀ Cᵀ Dᵀ Eᵀ Fᵀ Gᵀ
      (nonnegative_transpose A hA) (nonnegative_transpose B hB) (nonnegative_transpose C hC)
      (nonnegative_transpose D hD) (nonnegative_transpose E hE)
      (nonnegative_transpose F hF) (nonnegative_transpose G hG)
      hA₀ hB₀ hC₀ hD₀ hF₀ ht hl

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.reversed_rules_transpose
#print axioms CollatzCertificate.FullTwoMatrix.reversed_triangular_first_diagonals_one
