import CollatzReversedRealTriangularZeroBasic

namespace CollatzResearch.RealTriangularSubunit

open Matrix CollatzCertificate RealAffine

set_option maxHeartbeats 1000000

theorem upper_unit_stationary_row (A E : Mat (Fin 2))
    (hA : EntrywiseLE 0 A) (hA00 : A 0 0=1) (hA10 : A 1 0=0)
    (hE10 : E 1 0=0) (hd : A 1 1<1) (hAE : EntrywiseLE (A*E) (E*A)) :
    ∃ w : Vec (Fin 2), 0≤w ∧ w 0=1 ∧ w ᵥ* A=w ∧ w ᵥ* E≤E 0 0 • w := by
  let z := A 0 1/(1-A 1 1)
  let w : Vec (Fin 2) := ![1,z]
  have hden : 0<1-A 1 1 := sub_pos.mpr hd
  have hz : 0≤z := div_nonneg (hA 0 1) hden.le
  have heq : z*(1-A 1 1)=A 0 1 := div_mul_cancel₀ _ (ne_of_gt hden)
  refine ⟨w,?_,rfl,?_,?_⟩
  · intro i
    fin_cases i
    · exact zero_le_one
    · exact hz
  · funext i
    simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    fin_cases i
    · change 1*A 0 0+z*A 1 0=1
      rw [hA00,hA10]
      ring
    · change 1*A 0 1+z*A 1 1=z
      nlinarith only [heq]
  · intro i
    simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two,Pi.smul_apply,smul_eq_mul]
    fin_cases i
    · change 1*E 0 0+z*E 1 0≤E 0 0*1
      rw [hE10]
      ring_nf
      exact le_rfl
    · change 1*E 0 1+z*E 1 1≤E 0 0*z
      have hea := hAE 0 1
      simp only [Matrix.mul_apply,Fin.sum_univ_two,hA00,one_mul] at hea
      apply (mul_le_mul_iff_left₀ hden).mp
      calc
        (1*E 0 1+z*E 1 1)*(1-A 1 1)=
            E 0 1*(1-A 1 1)+E 1 1*(z*(1-A 1 1)) := by ring
        _=E 0 1*(1-A 1 1)+E 1 1*A 0 1 := by rw [heq]
        _≤E 0 0*A 0 1 := by nlinarith only [hea]
        _=(E 0 0*z)*(1-A 1 1) := by rw [mul_assoc,heq]

theorem stationary_first_row_bounds_upper_orbit (A : Affine (Fin 2))
    (γ q w : Vec (Fin 2)) (hA : A.Nonnegative) (hγ : 0≤γ) (hq : 0≤q)
    (hw : 0≤w) (hw0 : w 0=1) (hwA : w ᵥ* A.matrix=w)
    (hwa : w ⬝ᵥ A.offset=0) (hA10 : A.matrix 1 0=0) (hd : A.matrix 1 1<1) :
    ∃ L : ℝ, ∀ n : ℕ, q ⬝ᵥ ((eval A)^[n] γ)≤L := by
  let v : Vec (Fin 2) := ![0,1]
  have hv : 0≤v := by intro i; fin_cases i <;> norm_num [v]
  have hvA : v ᵥ* A.matrix=A.matrix 1 1 • v := by
    funext i
    simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two,Pi.smul_apply,smul_eq_mul]
    fin_cases i
    · change 0*A.matrix 0 0+1*A.matrix 1 0=A.matrix 1 1*0
      rw [hA10]
      ring
    · change 0*A.matrix 0 1+1*A.matrix 1 1=A.matrix 1 1*1
      ring
  obtain ⟨L,hL⟩ := RealAbovePowers.contracting_eigenrow_iterates_bounded
    A v γ (A.matrix 1 1) hv hγ hA.2 (hA.1 1 1) hd hvA
  have hfixed (n : ℕ) : w ⬝ᵥ ((eval A)^[n] γ)=w ⬝ᵥ γ := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      change w ⬝ᵥ (A.matrix *ᵥ ((eval A)^[n] γ)+A.offset)=w ⬝ᵥ γ
      rw [dotProduct_add,dotProduct_mulVec,hwA,hwa,add_zero,ih]
  have hn (n : ℕ) : 0≤(eval A)^[n] γ := by
    induction n with
    | zero => exact hγ
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact eval_nonnegative hA ih
  refine ⟨q 0*(w ⬝ᵥ γ)+q 1*L,?_⟩
  intro n
  have hb := hL n
  have hf := hfixed n
  simp only [dotProduct,Fin.sum_univ_two] at hb hf ⊢
  change 0*((eval A)^[n] γ) 0+1*((eval A)^[n] γ) 1≤L at hb
  rw [hw0] at hf
  have hp := mul_nonneg (hw 1) (hn n 1)
  have hfirst : ((eval A)^[n] γ) 0≤w 0*γ 0+w 1*γ 1 := by
    rw [hw0]
    nlinarith only [hf,hp]
  have hm0 := mul_le_mul_of_nonneg_left hfirst (hq 0)
  have hm1 := mul_le_mul_of_nonneg_left hb (hq 1)
  nlinarith only [hm0,hm1]

theorem strict_upper_unit_subunit_ternary_contradiction
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (hA00 : A.matrix 0 0=1) (hA10 : A.matrix 1 0=0)
    (hE10 : E.matrix 1 0=0) (hd : A.matrix 1 1<1) (he : E.matrix 0 0<1) : False := by
  obtain ⟨w,hw,hw0,hwA,hwE⟩ := upper_unit_stationary_row A.matrix E.matrix
    hA.1 hA00 hA10 hE10 hd h.ea.1
  have hswap : A.matrix *ᵥ E.offset+A.offset≤E.matrix *ᵥ A.offset+E.offset := h.ea.2
  have hs := dotProduct_le_dotProduct_of_nonneg_left hswap hw
  have hb := dotProduct_le_dotProduct_of_nonneg_right hwE hA.2
  have hn := dotProduct_nonneg_of_nonneg hw hA.2
  simp only [dotProduct_add,dotProduct_mulVec,hwA] at hs
  rw [smul_dotProduct] at hb
  change (w ᵥ* E.matrix) ⬝ᵥ A.offset≤E.matrix 0 0*(w ⬝ᵥ A.offset) at hb
  have hwa : w ⬝ᵥ A.offset=0 := by nlinarith only [hs,hb,hn,he]
  obtain ⟨L,hL⟩ := stationary_first_row_bounds_upper_orbit A C.offset
    (D.matrix i₀ ᵥ* B.matrix) w hA hC.2
    (rowMul_nonneg (fun i => hD.1 i₀ i) hB.1) hw hw0 hwA hwa hA10 hd
  obtain ⟨N,hN⟩ := RealAbovePowers.real_reversed_b_a_row_growth
    A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict L
  exact (not_lt_of_ge (hL N)) (hN N le_rfl)

end CollatzResearch.RealTriangularSubunit

#print axioms CollatzResearch.RealTriangularSubunit.upper_unit_stationary_row
#print axioms CollatzResearch.RealTriangularSubunit.stationary_first_row_bounds_upper_orbit
#print axioms CollatzResearch.RealTriangularSubunit.strict_upper_unit_subunit_ternary_contradiction
