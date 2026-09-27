import FullTwoMatrixNonsingularBasic
import Mathlib.Tactic.Module

namespace CollatzCertificate.FullTwoMatrix

open Matrix TwoDimensionalSwapAlgebra TwoDimensionalMiddleRank

set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

theorem singular_trace_not_scalar (A : M2) (hd : A.det=0) (ht : 0 < tr A) :
    ¬∃ a : ℝ, A=a • (1 : M2) := by
  rintro ⟨a,ha⟩
  rw [ha] at hd ht
  simp [Matrix.det_fin_two,tr] at hd ht
  nlinarith only [hd,ht]

theorem equal_trace_independence (A B : M2) (α c d k : ℝ)
    (hA : tr A=α) (hB : tr B=α) (hα : α ≠ 0) (hne : A ≠ B)
    (h : c • B+d • A=k • A) : c=0 ∧ d=k := by
  have heq : c+d=k := by
    have hh := congrArg tr h
    simp only [tr,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] at hh hA hB
    have hz : (c+d-k)*α=0 := by
      linear_combination hh-c*hB-d*hA+k*hA
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hα)
  have hc : c • B=c • A := by
    rw [← heq,add_smul] at h
    exact add_right_cancel h
  have hc0 : c=0 := by
    by_contra hc0
    exact hne ((smul_right_injective _ hc0) hc).symm
  exact ⟨hc0,by simpa only [hc0,zero_add] using heq⟩

theorem singular_binary_invariants (A B E F G : M2)
    (h : ExactSwaps A B E F G) (ha : A.det=0) (hb : B.det=0) (hf : F.det ≠ 0)
    (htA : 0 < tr A) (htB : 0 < tr B) :
    tr A=tr B ∧ tr (A*B)=(tr A)^2 ∧ tr (B-A)=0 ∧
      (B-A).det=0 ∧ tr (A*(B-A))=0 ∧
      (A*B)*F=F*(A*A) ∧ (B*A)*F=F*(B*B) := by
  have hABF : (A*B)*F=F*(A*A) := by
    rw [Matrix.mul_assoc,h.2.2.2.2.1,← Matrix.mul_assoc,h.2.2.1,Matrix.mul_assoc]
  have hBAF : (B*A)*F=F*(B*B) := by
    rw [Matrix.mul_assoc,h.2.1,← Matrix.mul_assoc,h.2.2.2.1,Matrix.mul_assoc]
  have ht1 := trace_of_intertwining (A*B) (A*A) F hf hABF
  have ht2 := trace_of_intertwining (B*A) (B*B) F hf hBAF
  rw [tr_square,ha,mul_zero,sub_zero] at ht1
  rw [trace_product_commutes B A,tr_square,hb,mul_zero,sub_zero] at ht2
  have ht : tr A=tr B := by nlinarith only [ht1,ht2,htA,htB]
  refine ⟨ht,ht1,?_,?_,?_,hABF,hBAF⟩
  · simp only [tr,Matrix.sub_apply]
    simp only [tr] at ht
    linarith only [ht]
  · rw [det_sub_identity,ha,hb,ht1,← ht]
    ring
  · have hs : tr (A*A)=(tr A)^2 := by rw [tr_square,ha];ring
    simp only [Matrix.mul_sub,tr,Matrix.sub_apply]
    simp only [tr] at ht1 hs
    linarith only [ht1,hs]

theorem singular_binary_unequal_shape (A B E F G : M2)
    (h : ExactSwaps A B E F G) (ha : A.det=0) (hb : B.det=0) (hf : F.det ≠ 0)
    (htA : 0 < tr A) (htB : 0 < tr B) (htF : 0 < tr F) (hne : A ≠ B) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ tr A=α ∧ tr B=α ∧
      A*B=α • A ∧ B*A=α • B ∧ F=β • (1 : M2) ∧
      E=(β/α) • A ∧ G=(β/α) • B := by
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
  have hAN0 : A*N=0 := by
    rcases ha_cases with haz | haz
    · simpa only [haz,zero_smul] using hAN
    · have hab' : A*B=α • B := by rw [hBN,Matrix.mul_add,hAN,haz,haa,smul_add]
      have hba' : B*A=α • A := by rw [hBN,Matrix.add_mul,hNA,haz,sub_self,zero_smul,add_zero,haa]
      have hbf : B*F=F*A := by
        rw [hab',haa,Matrix.smul_mul,Matrix.mul_smul] at hABF
        exact (smul_right_injective _ hα0) hABF
      have haf : A*F=F*B := by
        rw [hba',hbb,Matrix.smul_mul,Matrix.mul_smul] at hBAF
        exact (smul_right_injective _ hα0) hBAF
      have hanti : F*N+N*F=0 := by
        dsimp [N]
        rw [Matrix.mul_sub,Matrix.sub_mul,← hbf,← haf]
        abel
      have htFN : tr (F*N)=0 := by
        have hh := congrArg tr hanti
        have hc := trace_product_commutes F N
        simp only [tr,Matrix.add_apply,Matrix.zero_apply,add_zero] at hh hc ⊢
        linarith only [hh,hc]
      have hp := polarized_trace_identity F N
      rw [hanti,htN,htFN,zero_smul,add_zero,mul_zero,sub_self,zero_smul,add_zero] at hp
      have hz : N=0 := (smul_eq_zero.mp hp.symm).resolve_left (ne_of_gt htF)
      exact False.elim (hn hz)
  have ha0 : a=0 := by
    have hh : a • N=(0 : ℝ) • N := by rw [← hAN,hAN0,zero_smul]
    exact (smul_left_injective ℝ hn) hh
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
  have hx : 0 < x := by simp only [hfshape,tr,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply_eq,mul_one] at htF;linarith only [htF]
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
  exact ⟨α,x,hα,hx,rfl,htr.symm,hab,hba,hfshape,hEshape,hGshape⟩

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.singular_trace_not_scalar
#print axioms CollatzCertificate.FullTwoMatrix.equal_trace_independence
#print axioms CollatzCertificate.FullTwoMatrix.singular_binary_invariants
#print axioms CollatzCertificate.FullTwoMatrix.singular_binary_unequal_shape
