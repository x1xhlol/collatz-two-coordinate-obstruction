import ReversedSwapRecurrence
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

namespace CollatzCertificate.FullTwoMatrix

open Matrix

abbrev M2 := Mat (Fin 2)

structure WeakRules (A B C D E F G : M2) : Prop where
  ad : EntrywiseLE D (A * D)
  bd : EntrywiseLE (G * D) (B * D)
  ae : EntrywiseLE (E * A) (A * E)
  af : EntrywiseLE (E * B) (A * F)
  ag : EntrywiseLE (F * A) (A * G)
  be : EntrywiseLE (F * B) (B * E)
  bf : EntrywiseLE (G * A) (B * F)
  bg : EntrywiseLE (G * B) (B * G)
  ce : EntrywiseLE (C * B) (C * E)
  cf : EntrywiseLE (C * (A * A)) (C * F)
  cg : EntrywiseLE (C * (A * B)) (C * G)

def Upper (A B E F G : M2) : Prop :=
  A 1 0 = 0 ∧ B 1 0 = 0 ∧ E 1 0 = 0 ∧ F 1 0 = 0 ∧ G 1 0 = 0

def Lower (A B E F G : M2) : Prop :=
  A 0 1 = 0 ∧ B 0 1 = 0 ∧ E 0 1 = 0 ∧ F 0 1 = 0 ∧ G 0 1 = 0

theorem forward_swap_equalities_on_diagonal (A B C D E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (h : WeakRules A B C D E F G) (i : Fin 2) :
    (A * E) i i = (E * A) i i ∧ (A * F) i i = (E * B) i i ∧
    (A * G) i i = (F * A) i i ∧ (B * E) i i = (F * B) i i ∧
    (B * F) i i = (G * A) i i ∧ (B * G) i i = (G * B) i i := by
  have hn (M : M2) (hm : EntrywiseLE 0 M) : EntrywiseLE 0 Mᵀ := by
    intro j k
    exact hm k j
  have ht (M N P Q : M2) (hh : EntrywiseLE (M * N) (P * Q)) :
      EntrywiseLE (Nᵀ * Mᵀ) (Qᵀ * Pᵀ) := by
    intro j k
    simpa only [← Matrix.transpose_mul, Matrix.transpose_apply] using hh k j
  have hh := reversed_swap_equalities_on_diagonal Aᵀ Bᵀ Eᵀ Fᵀ Gᵀ
    (hn A hA) (hn B hB) (hn E hE) (hn F hF) (hn G hG)
    (ht E A A E h.ae) (ht E B A F h.af) (ht F A A G h.ag)
    (ht F B B E h.be) (ht G A B F h.bf) (ht G B B G h.bg) i
  simpa only [← Matrix.transpose_mul, Matrix.transpose_apply] using hh

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.forward_swap_equalities_on_diagonal
