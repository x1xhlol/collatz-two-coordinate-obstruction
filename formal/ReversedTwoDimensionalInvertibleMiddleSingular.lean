import ReversedTwoDimensionalInvertibleMiddleBasic

namespace CollatzCertificate.TwoDimensionalInvertibleMiddle

open Matrix TwoDimensionalMiddleRank FullTwoMatrix
open TwoDimensionalSwapAlgebra (tr)

set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

theorem forward_singular_binary_dichotomy (A B E F G : M2)
    (h : ExactSwaps A B E F G) (ha : A.det=0) (hb : B.det=0) (hf : F.det ≠ 0)
    (htA : 0 < tr A) (htB : 0 < tr B) (hFnonneg : EntrywiseLE 0 F) (hne : A ≠ B) :
    ∃ α : ℝ, 0 < α ∧ tr A=α ∧ tr B=α ∧
      ((A*B=α • B ∧ B*A=α • A) ∨
        ∃ β : ℝ, 0 < β ∧ A*B=α • A ∧ B*A=α • B ∧
          F=β • (1 : M2) ∧ E=(β/α) • A ∧ G=(β/α) • B) := by
  obtain ⟨htr,htAB,htN,hdN,htAN,hABF,hBAF⟩ := singular_binary_invariants A B E F G h ha hb hf htA htB
  let α := tr A
  let N := B-A
  have hα : 0 < α := htA
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hn : N ≠ 0 := by intro hz; exact hne (sub_eq_zero.mp hz).symm
  have hBN : B=A+N := by dsimp [N];abel
  have haa : A*A=α • A := by simp only [square_trace_identity,ha,zero_smul,sub_zero];rfl
  have hbb : B*B=α • B := by simp only [square_trace_identity,hb,zero_smul,sub_zero,← htr];rfl
  obtain ⟨a,hAN⟩ := nilpotent_invariant_image A N hn htN hdN htAN
  have hNA : N*A=(α-a) • N := by
    have hh := polarized_trace_identity A N
    rw [htN,htAN,zero_smul,add_zero,mul_zero,sub_self,zero_smul,add_zero,hAN] at hh
    rw [sub_smul]
    exact eq_sub_of_add_eq' hh
  have ha_cases : a=0 ∨ a=α := by
    have hh : (a*a) • N=(α*a) • N := by
      calc
        (a*a) • N = A*(A*N) := by rw [hAN,Matrix.mul_smul,hAN,smul_smul]
        _ = (A*A)*N := (Matrix.mul_assoc _ _ _).symm
        _ = (α*a) • N := by rw [haa,Matrix.smul_mul,hAN,smul_smul]
    have hs := (smul_left_injective ℝ hn) hh
    have hz : a*(a-α)=0 := by nlinarith only [hs]
    exact (mul_eq_zero.mp hz).imp_right sub_eq_zero.mp
  refine ⟨α,hα,rfl,htr.symm,?_⟩
  rcases ha_cases with ha0 | haα
  · right
    have hAN0 : A*N=0 := by simpa only [ha0,zero_smul] using hAN
    have hNA' : N*A=α • N := by simpa only [ha0,sub_zero] using hNA
    have hab : A*B=α • A := by rw [hBN,Matrix.mul_add,hAN0,add_zero,haa]
    have hba : B*A=α • B := by rw [hBN,Matrix.add_mul,hNA',haa,smul_add]
    have haf : A*F=F*A := by
      rw [hab,haa,Matrix.smul_mul,Matrix.mul_smul] at hABF
      exact (smul_right_injective _ hα0) hABF
    have hbf : B*F=F*B := by
      rw [hba,hbb,Matrix.smul_mul,Matrix.mul_smul] at hBAF
      exact (smul_right_injective _ hα0) hBAF
    obtain ⟨x,y,hF⟩ := (centralizer_scalar_or_span A F haf).resolve_left
      (singular_trace_not_scalar A ha htA)
    have hy : y=0 := by
      have hh := hbf
      rw [hF] at hh
      simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,
        Matrix.mul_one,Matrix.one_mul,hab,hba,smul_smul] at hh
      have hc : (y*α) • B=(y*α) • A := add_left_cancel hh
      have hz : y*α=0 := by
        by_contra hz
        exact hne ((smul_right_injective _ hz) hc).symm
      exact (mul_eq_zero.mp hz).resolve_right hα0
    have hfshape : F=x • (1 : M2) := by simpa only [hy,zero_smul,add_zero] using hF
    have hx0 : x ≠ 0 := by
      intro hx0
      apply hf
      simp only [hfshape,hx0,zero_smul,Matrix.det_zero]
    have hx : 0 < x := by
      have hxnonneg := hFnonneg 0 0
      change 0 ≤ F 0 0 at hxnonneg
      rw [hfshape] at hxnonneg
      simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply_eq,mul_one] at hxnonneg
      exact lt_of_le_of_ne hxnonneg (Ne.symm hx0)
    obtain ⟨u,v,hE⟩ := (centralizer_scalar_or_span A E h.1).resolve_left
      (singular_trace_not_scalar A ha htA)
    have heq : u • B+(v*α) • A=x • A := by
      have hh := h.2.1.symm
      rw [hE,hfshape] at hh
      simpa only [Matrix.mul_smul,Matrix.mul_one,Matrix.add_mul,Matrix.smul_mul,
        Matrix.one_mul,hab,smul_smul] using hh
    obtain ⟨hu,hvx⟩ := equal_trace_independence A B α u (v*α) x rfl htr.symm hα0 hne heq
    have hv : v=x/α := (eq_div_iff hα0).mpr hvx
    have hEshape : E=(x/α) • A := by simpa only [hu,hv,zero_smul,zero_add] using hE
    obtain ⟨u',v',hG⟩ := (centralizer_scalar_or_span B G h.2.2.2.2.2).resolve_left
      (singular_trace_not_scalar B hb htB)
    have hgq : u' • A+(v'*α) • B=x • B := by
      have hh := h.2.2.2.2.1.symm
      rw [hG,hfshape] at hh
      simpa only [Matrix.mul_smul,Matrix.mul_one,Matrix.add_mul,Matrix.smul_mul,
        Matrix.one_mul,hba,smul_smul] using hh
    obtain ⟨hu',hvx'⟩ := equal_trace_independence B A α u' (v'*α) x htr.symm rfl hα0 hne.symm hgq
    have hv' : v'=x/α := (eq_div_iff hα0).mpr hvx'
    have hGshape : G=(x/α) • B := by simpa only [hu',hv',zero_smul,zero_add] using hG
    exact ⟨x,hx,hab,hba,hfshape,hEshape,hGshape⟩
  · left
    constructor
    · rw [hBN,Matrix.mul_add,hAN,haα,haa,smul_add]
    · rw [hBN,Matrix.add_mul,hNA,haα,sub_self,zero_smul,add_zero,haa]

end CollatzCertificate.TwoDimensionalInvertibleMiddle

#print axioms CollatzCertificate.TwoDimensionalInvertibleMiddle.forward_singular_binary_dichotomy
