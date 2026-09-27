import CollatzReversedRealTriangularPositive
import CollatzReversedRealTriangularContracting
import CollatzReversedRealExpandingPrefix

namespace CollatzResearch.RealTriangularSuperunit

open Matrix CollatzCertificate RealAffine RealOrderedTwo

set_option maxHeartbeats 1000000

theorem strict_upper_expanding_second_binary_contradiction
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (ha0 : A.matrix 1 0=0) (hb0 : B.matrix 1 0=0) (he0 : E.matrix 1 0=0)
    (hf0 : F.matrix 1 0=0) (hg0 : G.matrix 1 0=0)
    (hfpos : 0<F.matrix 0 0) (ha : 1<A.matrix 0 0) (hb : 1<B.matrix 1 1) : False := by
  obtain ⟨hab,hef,hgf,_ha1,hfpos,hfle⟩ :=
    RealTriangularPositive.positive_active_diagonal_values A B C D E F G i₀ 0 1
      (by decide) hA hB hC hD hE hF hG h hstrict ha0 hb0 he0 hf0 hg0 hfpos
  have han0 : 0≤A.offset 0 := hA.2 0
  have han1 : 0≤A.offset 1 := hA.2 1
  have hbn0 : 0≤B.offset 0 := hB.2 0
  have hbn1 : 0≤B.offset 1 := hB.2 1
  have hcn0 : 0≤C.offset 0 := hC.2 0
  have hcn1 : 0≤C.offset 1 := hC.2 1
  have hen0 : 0≤E.offset 0 := hE.2 0
  have hen1 : 0≤E.offset 1 := hE.2 1
  have hfn0 : 0≤F.offset 0 := hF.2 0
  have hfn1 : 0≤F.offset 1 := hF.2 1
  have ha11 := RealTriangularContracting.strict_upper_second_diagonal_lt_one
    A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict ha0 hb0
  obtain ⟨_hea,hfa,_hga,heb,_hfb,_hgb⟩ := reversed_swap_equalities_on_diagonal
    A.matrix B.matrix E.matrix F.matrix G.matrix hA.1 hB.1 hE.1 hF.1 hG.1
      h.ea.1 h.fa.1 h.ga.1 h.eb.1 h.fb.1 h.gb.1 1
  simp only [Matrix.mul_apply,Fin.sum_univ_two,hf0,hb0,he0,zero_mul,zero_add] at hfa heb
  have hef11 : E.matrix 1 1=F.matrix 1 1 := by nlinarith only [heb,hb]
  have hf11 : F.matrix 1 1=0 := by
    rw [hef11] at hfa
    nlinarith only [hfa,ha11,hb,hF.1 1 1]
  have he11 : E.matrix 1 1=0 := hef11.trans hf11
  have hfa1 := h.fa.2 (1 : Fin 2)
  have heb1 := h.eb.2 (1 : Fin 2)
  simp only [Affine.comp,Pi.add_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
    hf0,hb0,he0,hf11,he11,zero_mul,zero_add] at hfa1 heb1
  have hsum : E.offset 1+F.offset 1≤0 := by
    have hh : (B.matrix 1 1-1)*(E.offset 1+F.offset 1)≤0 := by
      nlinarith only [hfa1,heb1,hbn1]
    by_contra hn
    exact (not_lt_of_ge hh) (mul_pos (sub_pos.mpr hb) (lt_of_not_ge hn))
  have he1 : E.offset 1=0 := by linarith only [hsum,hen1,hfn1]
  have hf1 : F.offset 1=0 := by linarith only [hsum,hen1,hfn1]
  have hb1 : B.offset 1=0 := by rw [he1,hf1,mul_zero] at hfa1; linarith only [hfa1,hbn1]
  have hea1 := h.ea.2 (1 : Fin 2)
  have hec1 := h.ec.2 (1 : Fin 2)
  simp only [Affine.comp,Pi.add_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
    ha0,hb0,he0,he11,he1,hb1,zero_mul,mul_zero,zero_add,add_zero] at hea1 hec1
  have ha1 : A.offset 1=0 := le_antisymm hea1 (han1)
  have hc1 : C.offset 1=0 := by nlinarith only [hec1,hb,hcn1]
  have hgb0 := h.gb.2 (0 : Fin 2)
  simp only [Affine.comp,Pi.add_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
    hb1,mul_zero,add_zero,← hab,hgf] at hgb0
  have hgbound : G.offset 0≤B.offset 0 := by
    have hh : (A.matrix 0 0-1)*(G.offset 0-B.offset 0)≤0 := by
      nlinarith only [hgb0,mul_nonneg (hB.1 0 1) (hG.2 1),
        mul_nonneg (sub_nonneg.mpr hfle) (hbn0)]
    by_contra hn
    exact (not_lt_of_ge hh) (mul_pos (sub_pos.mpr ha) (sub_pos.mpr (lt_of_not_ge hn)))
  have hgc0 := h.gc.2 (0 : Fin 2)
  simp only [Affine.comp,Pi.add_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
    ha0,hc1,ha1,mul_zero,zero_mul,add_zero,← hab,hgf] at hgc0
  have hcoeff : 0<A.matrix 0 0*A.matrix 0 0-F.matrix 0 0 := by
    nlinarith only [ha,hfle]
  have hzero : C.offset 0=0 ∧ A.offset 0=0 := by
    have hsum0 : (A.matrix 0 0*A.matrix 0 0-F.matrix 0 0)*C.offset 0+
        A.matrix 0 0*A.offset 0≤0 := by nlinarith only [hgc0,hgbound]
    have hterm0 := mul_nonneg hcoeff.le (hcn0)
    have hterm1 := mul_nonneg (lt_trans zero_lt_one ha).le (han0)
    constructor <;> nlinarith only [hsum0,hterm0,hterm1,hcoeff,ha,hcn0,han0]
  obtain ⟨hc0,haoff0⟩ := hzero
  have hea0 := h.ea.2 (0 : Fin 2)
  simp only [Affine.comp,Pi.add_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
    ha1,haoff0,he1,mul_zero,zero_add,add_zero] at hea0
  have heoff0 : E.offset 0=0 := by nlinarith only [hea0,ha,hen0]
  have hec0 := h.ec.2 (0 : Fin 2)
  simp only [Affine.comp,Pi.add_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
    hc0,hc1,heoff0,mul_zero,zero_add,add_zero] at hec0
  have hboff0 : B.offset 0=0 := le_antisymm hec0 (hbn0)
  have hao : A.offset=0 := by funext i; fin_cases i <;> assumption
  have hbo : B.offset=0 := by funext i; fin_cases i <;> assumption
  rcases RealExpandingPrefix.strict_binary_offset_nonzero A B D G i₀ hD hG hstrict
    with hh | hh
  · exact hh hao
  · exact hh hbo

end CollatzResearch.RealTriangularSuperunit

#print axioms CollatzResearch.RealTriangularSuperunit.strict_upper_expanding_second_binary_contradiction
