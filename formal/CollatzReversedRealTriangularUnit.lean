import CollatzReversedRealTriangularReadout
import FullTwoCoordinate

namespace CollatzResearch.RealTriangularUnit

open Matrix CollatzCertificate RealAffine

theorem upper_unit_first_diagonals_exclude_strict
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (ha1 : A.matrix 0 0=1) (hb1 : B.matrix 0 0=1) (he1 : E.matrix 0 0=1)
    (hf1 : F.matrix 0 0=1) (hg1 : G.matrix 0 0=1)
    (ha0 : A.matrix 1 0=0) (hb0 : B.matrix 1 0=0) (he0 : E.matrix 1 0=0)
    (hf0 : F.matrix 1 0=0) (hg0 : G.matrix 1 0=0) : False := by
  have hr := (RealTriangularReadout.strict_triangular_active_diagonal_bounds
    A B C D E F G i₀ 0 1 (by decide) hA hB hC hD hE hF hG h hstrict ha0 hb0).1
  let P : Mat (Fin 2) := !![1,0;0,0]
  let C' : Affine (Fin 2) := ⟨P,C.offset⟩
  let k : ℝ := (D.matrix i₀ 0)⁻¹
  let D' := normalizedReadout D i₀ 0 k
  have hk : 0 < k := inv_pos.mpr hr
  have hP (X : Affine (Fin 2)) (hx1 : X.matrix 0 0=1) (hx0 : X.matrix 1 0=0) :
      X.matrix*P=P := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P,Matrix.mul_apply,Fin.sum_univ_two,hx1,hx0]
  have hAP := hP A ha1 ha0
  have hBP := hP B hb1 hb0
  have hEP := hP E he1 he0
  have hFP := hP F hf1 hf0
  have hGP := hP G hg1 hg0
  have hC' : FullTwo.Admissible C' := by
    refine ⟨⟨?_,hC.2⟩,?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;> norm_num [C',P]
    · norm_num [C',P]
  have hD' : FullTwo.Admissible D' := by
    refine ⟨normalized_readout_nonnegative hD i₀ 0 hk.le,?_⟩
    change 1 ≤ (D.matrix i₀ 0)⁻¹*D.matrix i₀ 0
    rw [inv_mul_cancel₀ (ne_of_gt hr)]
  have h' : ReversedRealWeak A B C' D' E F G := by
    refine ⟨normalized_readout_preserves_da hA hD h.da i₀ 0 hk.le,
      normalized_readout_preserves_db h.db i₀ 0 hk.le,
      h.ea,h.fa,h.ga,h.eb,h.fb,h.gb,?_,?_,?_⟩
    · refine ⟨?_,h.ec.2⟩
      change EntrywiseLE (B.matrix*P) (E.matrix*P)
      rw [hBP,hEP]
      exact fun _ _ => le_rfl
    · refine ⟨?_,h.fc.2⟩
      change EntrywiseLE (A.matrix*(A.matrix*P)) (F.matrix*P)
      rw [hAP,hAP,hFP]
      exact fun _ _ => le_rfl
    · refine ⟨?_,h.gc.2⟩
      change EntrywiseLE (B.matrix*(A.matrix*P)) (G.matrix*P)
      rw [hAP,hBP,hGP]
      exact fun _ _ => le_rfl
  have hz := FullTwo.reversed_all_gaps_zero A B C' D' E F G
    ⟨hA,by rw [ha1]⟩ ⟨hB,by rw [hb1]⟩ hC' hD'
    ⟨hE,by rw [he1]⟩ ⟨hF,by rw [hf1]⟩ ⟨hG,by rw [hg1]⟩ h'
  have hda := normalized_readout_gap_da A D i₀ 0 k
  have hdb := normalized_readout_gap_db B D G i₀ 0 k
  change (D'.comp A).offset 0-D'.offset 0=
    k*((D.comp A).offset i₀-D.offset i₀) at hda
  change (D'.comp B).offset 0-(D'.comp G).offset 0=
    k*((D.comp B).offset i₀-(D.comp G).offset i₀) at hdb
  rw [hz.da,sub_self] at hda
  rw [hz.db,sub_self] at hdb
  have hda0 := (mul_eq_zero.mp hda.symm).resolve_left (ne_of_gt hk)
  have hdb0 := (mul_eq_zero.mp hdb.symm).resolve_left (ne_of_gt hk)
  rcases hstrict with hs | hs <;> linarith only [hs,hda0,hdb0]

end CollatzResearch.RealTriangularUnit

#print axioms CollatzResearch.RealTriangularUnit.upper_unit_first_diagonals_exclude_strict
