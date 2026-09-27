import FullTwoMatrixNonsingularBasic
import Mathlib.Tactic.Module

namespace CollatzCertificate.FullTwoMatrix

open Matrix TwoDimensionalSwapAlgebra TwoDimensionalMiddleRank

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem binary_equal_of_scalar (A B E F G : M2)
    (h : ExactSwaps A B E F G) (ha : A.det ≠ 0) (hb : B.det ≠ 0) (he : E.det ≠ 0)
    (a : ℝ) (hs : A=a • (1 : M2)) : A=B := by
  rcases h with ⟨hae,haf,hag,hbe,hbf,hbg⟩
  have hgf : G=F := by
    apply (matrix_unit_of_det A ha).mul_left_cancel
    rw [hag,hs]
    simp [Matrix.smul_mul, Matrix.mul_smul]
  have hef : E=F := by
    apply (matrix_unit_of_det B hb).mul_left_cancel
    rw [hbe,← hgf,← hbg]
  apply (matrix_unit_of_det E he).mul_left_cancel
  rw [← hae,hef]
  simpa only [hef] using haf

theorem nonsingular_unequal_shape (A B E F G : M2)
    (h : ExactSwaps A B E F G)
    (ha : A.det ≠ 0) (hb : B.det ≠ 0) (he : E.det ≠ 0) (hg : G.det ≠ 0)
    (htA : 0 < tr A) (htB : 0 < tr B) (htE : 0 < tr E) (hne : A ≠ B) :
    ∃ μ t : ℝ, 0 < μ ∧ 0 < t ∧ tr A=3*μ ∧ A.det=2*μ^2 ∧
      A*(B-A)=μ • (B-A) ∧ (B-A)*A=(2*μ) • (B-A) ∧
      E=t • (2 • A-μ • (1 : M2)) ∧
      F=t • (A+B-μ • (1 : M2)) ∧ G=t • (2 • B-μ • (1 : M2)) := by
  have inv := nonsingular_binary_invariants A B E F G h hb he hg htA htB
  obtain ⟨hdet,htr,htAB,htN,hdN,htAN⟩ := inv
  let N := B-A
  have hn : N ≠ 0 := by
    intro hz
    exact hne (sub_eq_zero.mp hz).symm
  have hBN : B=A+N := by dsimp [N]; abel
  have hn2 : N*N=0 := by
    rw [square_trace_identity]
    change tr (B-A) • N-(B-A).det • (1 : M2)=0
    rw [htN,hdN,zero_smul,zero_smul,sub_self]
  obtain ⟨a,hAN⟩ := nilpotent_invariant_image A N hn htN hdN htAN
  let κ := tr A-a
  have hNA : N*A=κ • N := by
    have hh := polarized_trace_identity A N
    rw [htN,htAN,zero_smul,add_zero,mul_zero,sub_self,zero_smul,add_zero,hAN] at hh
    dsimp [κ]
    rw [sub_smul]
    exact eq_sub_of_add_eq' hh
  have ha0 : a ≠ 0 := by
    intro hz
    have hh : A*N=A*0 := by simpa only [hz,zero_smul,Matrix.mul_zero] using hAN
    exact hn ((matrix_unit_of_det A ha).mul_left_cancel hh)
  have hk0 : κ ≠ 0 := by
    intro hz
    have hh : N*A=0*A := by simpa only [hz,zero_smul,Matrix.zero_mul] using hNA
    exact hn ((matrix_unit_of_det A ha).mul_right_cancel hh)
  rcases centralizer_scalar_or_span A E h.1 with ⟨c,hc⟩ | ⟨x,y,hE⟩
  · exact False.elim (hne (binary_equal_of_scalar A B E F G h ha hb he c hc))
  let b := x+y*a
  let e := b/a
  let g := e*κ/a
  have hea : e*a=b := by dsimp [e]; exact div_mul_cancel₀ b ha0
  have hga : g*a=e*κ := by dsimp [g]; exact div_mul_cancel₀ (e*κ) ha0
  have hEN : E*N=b • N := by
    rw [hE,Matrix.add_mul,Matrix.smul_mul,Matrix.smul_mul,Matrix.one_mul,hAN,smul_smul]
    exact (add_smul x (y*a) N).symm
  have hNE : N*E=(x+y*κ) • N := by
    rw [hE,Matrix.mul_add,Matrix.mul_smul,Matrix.mul_smul,Matrix.mul_one,hNA,smul_smul]
    exact (add_smul x (y*κ) N).symm
  have hF : F=E+e • N := by
    apply (matrix_unit_of_det A ha).mul_left_cancel
    calc
      A*F=E*B := h.2.1
      _ = A*E+b • N := by rw [hBN,Matrix.mul_add,← h.1,hEN]
      _ = A*(E+e • N) := by
        rw [Matrix.mul_add,Matrix.mul_smul,hAN,smul_smul,hea]
  have hG : G=E+g • N := by
    apply (matrix_unit_of_det A ha).mul_left_cancel
    calc
      A*G=F*A := h.2.2.1
      _ = A*E+(e*κ) • N := by rw [hF,Matrix.add_mul,Matrix.smul_mul,hNA,smul_smul,← h.1]
      _ = A*(E+g • N) := by
        rw [Matrix.mul_add,Matrix.mul_smul,hAN,smul_smul,hga]
  have hrelation : y*(κ-a)=e*κ := by
    have hh := h.2.2.2.1
    rw [hBN,hF] at hh
    simp only [Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,hNE,hEN,hNA,hn2,smul_zero,add_zero,smul_smul,← h.1] at hh
    have hcoeff : x+y*κ=b+e*κ := by
      apply smul_left_injective ℝ hn
      apply add_left_cancel (a := A*E)
      simpa only [add_smul,add_assoc,add_comm,add_left_comm] using hh
    dsimp [b] at hcoeff
    nlinarith only [hcoeff]
  have hcomm : (g-y)*(a-κ)=0 := by
    have hh := h.2.2.2.2.2
    rw [hBN,hG] at hh
    simp only [Matrix.add_mul,Matrix.mul_add,Matrix.mul_smul,Matrix.smul_mul,
      hAN,hNA,hn2,hEN,hNE,smul_zero,smul_smul,add_zero,zero_add,← h.1] at hh
    have hc : ((g-y)*(a-κ)) • N=0 := by
      ext i j
      have hij := congrFun (congrFun hh i) j
      simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.zero_apply] at hij ⊢
      dsimp [b] at hij
      linear_combination hij
    exact (smul_eq_zero.mp hc).resolve_right hn
  have hak : a ≠ κ := by
    intro hak
    have he0 : e=0 := by rw [← hak,sub_self,mul_zero] at hrelation; exact (mul_eq_zero.mp hrelation.symm).resolve_right ha0
    have hb0 : b=0 := by simpa only [he0,zero_mul] using hea.symm
    have hh : E*N=E*0 := by simpa only [hb0,zero_smul,Matrix.mul_zero] using hEN
    exact hn ((matrix_unit_of_det E he).mul_left_cancel hh)
  have hgy : g=y := sub_eq_zero.mp ((mul_eq_zero.mp hcomm).resolve_right (sub_ne_zero.mpr hak))
  have hy0 : y ≠ 0 := by
    intro hy
    have hg0 : g=0 := hgy.trans hy
    have he0 : e=0 := by
      have hh : e*κ=0 := by simpa only [hg0,zero_mul] using hga.symm
      exact (mul_eq_zero.mp hh).resolve_right hk0
    have hb0 : b=0 := by simpa only [he0,zero_mul] using hea.symm
    have hh : E*N=E*0 := by simpa only [hb0,zero_smul,Matrix.mul_zero] using hEN
    exact hn ((matrix_unit_of_det E he).mul_left_cancel hh)
  have hka : κ=2*a := by
    have hh : y*(κ-2*a)=0 := by rw [hgy] at hga; nlinarith only [hrelation,hga]
    have hh' := (mul_eq_zero.mp hh).resolve_left hy0
    linarith only [hh']
  have htrA : tr A=3*a := by dsimp [κ] at hka; linarith only [hka]
  have hap : 0 < a := by linarith only [htA,htrA]
  have heq : e=y/2 := by
    rw [hka] at hrelation
    have hh : a*(2*e-y)=0 := by nlinarith only [hrelation]
    have hh' := (mul_eq_zero.mp hh).resolve_left ha0
    linarith only [hh']
  have hx : x=-(y*a/2) := by dsimp [b] at hea; rw [heq] at hea; nlinarith only [hea]
  have ht : 0 < y/2 := by
    rw [hE] at htE
    simp only [tr,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply_eq,mul_one] at htE
    have hh : 0 < 2*y*a := by
      simp only [tr] at htrA
      have hyt := congrArg (fun z : ℝ => y*z) htrA
      nlinarith only [htE,hyt,hx]
    have hy : 0 < y := by nlinarith only [hh,hap]
    linarith only [hy]
  have hdeta : A.det=2*a^2 := by
    have hh := congrArg (fun X : M2 => X*N) (square_trace_identity A)
    simp only [Matrix.mul_assoc,hAN,Matrix.mul_smul,hAN,Matrix.sub_mul,
      Matrix.smul_mul,Matrix.one_mul,smul_smul,htrA] at hh
    have hc : a*a=3*a*a-A.det := by
      apply smul_left_injective ℝ hn
      simpa only [sub_smul] using hh
    nlinarith only [hc]
  refine ⟨a,y/2,hap,ht,htrA,hdeta,hAN,?_,?_,?_,?_⟩
  · simpa only [hka] using hNA
  · rw [hE,hx]
    module
  · rw [hF,hE,hx,heq,hBN]
    module
  · rw [hG,hE,hx,hgy,hBN]
    module

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.binary_equal_of_scalar
#print axioms CollatzCertificate.FullTwoMatrix.nonsingular_unequal_shape
