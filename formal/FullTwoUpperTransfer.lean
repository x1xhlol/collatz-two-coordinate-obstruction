import FullTwoBoundaryTransfer
import FullTwoUpperBasic

namespace CollatzResearch.FullTwo

open Matrix CollatzCertificate

set_option linter.unusedSimpArgs false

noncomputable def toUpperData (A B C D E F G : Aff2) : FullTwoUpper.Data where
  za := A.matrix 1 1
  zb := B.matrix 1 1
  ze := E.matrix 1 1
  zf := F.matrix 1 1
  zg := G.matrix 1 1
  qa := A.matrix 0 1
  qb := B.matrix 0 1
  qe := E.matrix 0 1
  qf := F.matrix 0 1
  qg := G.matrix 0 1
  ha := A.offset 0
  hb := B.offset 0
  he := E.offset 0
  hf := F.offset 0
  hg := G.offset 0
  ka := A.offset 1
  kb := B.offset 1
  ke := E.offset 1
  kf := F.offset 1
  kg := G.offset 1
  kap := C.matrix 0 1 / C.matrix 0 0
  tau := D.offset 1

theorem toUpperData_weak (A B C D E F G : Aff2)
    (hA : Admissible A) (hB : Admissible B) (hC : Admissible C) (hD : Admissible D)
    (hE : Admissible E) (hF : Admissible F) (hG : Admissible G)
    (uA : Upper A) (uB : Upper B) (uE : Upper E) (uF : Upper F) (uG : Upper G)
    (w : ForwardWeak A B (outerBoundary C) (innerBoundary D) E F G) :
    FullTwoUpper.Weak (toUpperData A B C D E F G) := by
  constructor
  · exact hA.1.1 1 1
  · exact hB.1.1 1 1
  · exact hE.1.1 1 1
  · exact hF.1.1 1 1
  · exact hG.1.1 1 1
  · exact hA.1.1 0 1
  · exact hB.1.1 0 1
  · exact hE.1.1 0 1
  · exact hF.1.1 0 1
  · exact hG.1.1 0 1
  · exact hA.1.2 0
  · exact hB.1.2 0
  · exact hE.1.2 0
  · exact hF.1.2 0
  · exact hG.1.2 0
  · exact hA.1.2 1
  · exact hB.1.2 1
  · exact hE.1.2 1
  · exact hF.1.2 1
  · exact hG.1.2 1
  · exact div_nonneg (hC.1.1 0 1) (hC.1.1 0 0)
  · exact hD.1.2 1
  · have hh := w.af.1 1 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.ag.1 1 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.be.1 1 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.bf.1 1 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.ae.1 0 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.af.1 0 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.ag.1 0 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.be.1 0 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.bf.1 0 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.bg.1 0 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.ae.2 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.af.2 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.ag.2 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.be.2 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.bf.2 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.bg.2 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.ae.2 0
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.af.2 0
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.ag.2 0
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.be.2 0
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.bf.2 0
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.bg.2 0
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.ad.2 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.bd.2 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.ad.2 0
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.bd.2 0
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.ce.1 0 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.cf.1 0 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.cg.1 0 1
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.ce.2 0
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.cf.2 0
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.cg.2 0
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]

theorem toUpperData_gaps (A B C D E F G : Aff2)
    (uA : Upper A) (uB : Upper B) (uE : Upper E) (uF : Upper F) (uG : Upper G)
    (w : FullTwoUpper.ZeroGaps (toUpperData A B C D E F G)) :
    ForwardGapsZero A B (outerBoundary C) (innerBoundary D) E F G := by
  constructor
  · have hh := w.ad
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.bd
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.ae
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.af
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.ag
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.be
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.bf
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.bg
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.ce
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.cf
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]
  · have hh := w.cg
    simp only [toUpperData, outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, uA.1, uA.2, uB.1, uB.2, uE.1, uE.2, uF.1, uF.2, uG.1, uG.2] at hh ⊢
    nlinarith only [hh]

end CollatzResearch.FullTwo

#print axioms CollatzResearch.FullTwo.toUpperData_weak
#print axioms CollatzResearch.FullTwo.toUpperData_gaps
