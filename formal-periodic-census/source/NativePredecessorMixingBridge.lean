import Erdos1135.Tao.Fourier.Prop114CanonicalAssembly
import Erdos1135Predecessor.Tao.Fourier.MixingStatement

set_option autoImplicit false

namespace CollatzCanonical.BoundedInverseSeed

theorem native_predecessor_syracPMF_eq (n : ℕ) :
    Erdos1135.Tao.syracPMF n = Erdos1135Predecessor.Tao.syracPMF n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Erdos1135.Tao.syracPMF, Erdos1135Predecessor.Tao.syracPMF, ih]
      rfl

theorem native_predecessor_fineScaleOscillation_eq (m n : ℕ) :
    Erdos1135.Tao.syracFineScaleOscillation m n =
      Erdos1135Predecessor.Tao.syracFineScaleOscillation m n := by
  unfold Erdos1135.Tao.syracFineScaleOscillation
    Erdos1135Predecessor.Tao.syracFineScaleOscillation
    Erdos1135.Tao.syracPMFMassVector Erdos1135Predecessor.Tao.syracPMFMassVector
  rw [native_predecessor_syracPMF_eq]
  rfl

theorem predecessor_mixing_each_positive_power (A : ℕ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ Erdos1135Predecessor.Tao.syracFineScaleMixingAt A C := by
  obtain ⟨C, hC, hmix⟩ := Erdos1135.Tao.taoProp114FineScaleMixing A hA
  refine ⟨C, hC, ?_⟩
  intro n m hm hmn
  rw [← native_predecessor_fineScaleOscillation_eq]
  exact hmix n m hm hmn

#print axioms native_predecessor_syracPMF_eq
#print axioms native_predecessor_fineScaleOscillation_eq
#print axioms predecessor_mixing_each_positive_power

end CollatzCanonical.BoundedInverseSeed
