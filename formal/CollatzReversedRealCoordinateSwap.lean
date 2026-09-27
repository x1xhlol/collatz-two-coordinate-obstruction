import ReversedRealCoordinateChange
import Mathlib.Tactic.FinCases

namespace CollatzResearch.RealCoordinateSwap

open Matrix CollatzCertificate

def swapMatrix : Mat (Fin 2) := !![0,1;1,0]

def swapCoordinates (X : Affine (Fin 2)) : Affine (Fin 2) :=
  coordinateChange swapMatrix swapMatrix X

def swapInput (D : Affine (Fin 2)) : Affine (Fin 2) := inputChange swapMatrix D

theorem swap_matrix_nonnegative : EntrywiseLE 0 swapMatrix := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [swapMatrix]

theorem swap_matrix_square : swapMatrix*swapMatrix=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swapMatrix,Matrix.mul_apply,Fin.sum_univ_two]

theorem swap_coordinates_entries (X : Affine (Fin 2)) :
    (swapCoordinates X).matrix 0 0=X.matrix 1 1 ∧
    (swapCoordinates X).matrix 0 1=X.matrix 1 0 ∧
    (swapCoordinates X).matrix 1 0=X.matrix 0 1 ∧
    (swapCoordinates X).matrix 1 1=X.matrix 0 0 := by
  simp [swapCoordinates,coordinateChange,swapMatrix,Matrix.mul_apply,Matrix.vecMul,
    dotProduct,Fin.sum_univ_two]

theorem swap_coordinates_nonnegative (X : Affine (Fin 2)) (hX : X.Nonnegative) :
    (swapCoordinates X).Nonnegative :=
  coordinateChange_nonnegative swapMatrix swapMatrix swap_matrix_nonnegative
    swap_matrix_nonnegative X hX

theorem swap_input_nonnegative (D : Affine (Fin 2)) (hD : D.Nonnegative) :
    (swapInput D).Nonnegative := inputChange_nonnegative swapMatrix swap_matrix_nonnegative D hD

theorem swap_coordinates_reversed_weak (A B C D E F G : Affine (Fin 2))
    (h : ReversedRealWeak A B C D E F G) :
    ReversedRealWeak (swapCoordinates A) (swapCoordinates B) (swapCoordinates C)
      (swapInput D) (swapCoordinates E) (swapCoordinates F) (swapCoordinates G) :=
  coordinateChange_reversed_weak swapMatrix swapMatrix swap_matrix_nonnegative
    swap_matrix_nonnegative swap_matrix_square A B C D E F G h

theorem swap_coordinates_strict (A B D G : Affine (Fin 2)) (i₀ : Fin 2)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) :
    (swapInput D).offset i₀ < ((swapInput D).comp (swapCoordinates A)).offset i₀ ∨
      ((swapInput D).comp (swapCoordinates G)).offset i₀ <
        ((swapInput D).comp (swapCoordinates B)).offset i₀ := by
  have ha := inputChange_comp_offset swapMatrix swapMatrix swap_matrix_square D A
  have hb := inputChange_comp_offset swapMatrix swapMatrix swap_matrix_square D B
  have hg := inputChange_comp_offset swapMatrix swapMatrix swap_matrix_square D G
  change D.offset i₀ < ((inputChange swapMatrix D).comp
      (coordinateChange swapMatrix swapMatrix A)).offset i₀ ∨
    ((inputChange swapMatrix D).comp (coordinateChange swapMatrix swapMatrix G)).offset i₀ <
      ((inputChange swapMatrix D).comp (coordinateChange swapMatrix swapMatrix B)).offset i₀
  rw [ha,hg,hb]
  exact hstrict

theorem lower_digits_swap_upper (A B E F G : Affine (Fin 2))
    (ha : A.matrix 0 1=0) (hb : B.matrix 0 1=0) (he : E.matrix 0 1=0)
    (hf : F.matrix 0 1=0) (hg : G.matrix 0 1=0) :
    (swapCoordinates A).matrix 1 0=0 ∧ (swapCoordinates B).matrix 1 0=0 ∧
      (swapCoordinates E).matrix 1 0=0 ∧ (swapCoordinates F).matrix 1 0=0 ∧
      (swapCoordinates G).matrix 1 0=0 := by
  exact ⟨(swap_coordinates_entries A).2.2.1.trans ha,
    (swap_coordinates_entries B).2.2.1.trans hb,
    (swap_coordinates_entries E).2.2.1.trans he,
    (swap_coordinates_entries F).2.2.1.trans hf,
    (swap_coordinates_entries G).2.2.1.trans hg⟩

end CollatzResearch.RealCoordinateSwap

#print axioms CollatzResearch.RealCoordinateSwap.swap_matrix_nonnegative
#print axioms CollatzResearch.RealCoordinateSwap.swap_matrix_square
#print axioms CollatzResearch.RealCoordinateSwap.swap_coordinates_entries
#print axioms CollatzResearch.RealCoordinateSwap.swap_coordinates_nonnegative
#print axioms CollatzResearch.RealCoordinateSwap.swap_input_nonnegative
#print axioms CollatzResearch.RealCoordinateSwap.swap_coordinates_reversed_weak
#print axioms CollatzResearch.RealCoordinateSwap.swap_coordinates_strict
#print axioms CollatzResearch.RealCoordinateSwap.lower_digits_swap_upper
