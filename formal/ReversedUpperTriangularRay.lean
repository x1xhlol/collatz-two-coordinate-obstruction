import CollatzReversedRealExpandingGrowth

namespace CollatzResearch.ReversedUpperTriangularRay

open Matrix CollatzCertificate RealAffine

theorem common_positive_upper_ray
    (E F G : Mat (Fin 2)) (l : ℝ) (hl : 1<l)
    (hE : EntrywiseLE 0 E) (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (he0 : E 1 0=0) (hf0 : F 1 0=0) (hg0 : G 1 0=0)
    (he00 : E 0 0≤l) (hf00 : F 0 0≤l) (hg00 : G 0 0≤l)
    (he11 : E 1 1≤l) (hf11 : F 1 1≤l) (hg11 : G 1 1≤l) :
    ∃ (u : Vec (Fin 2)) (L : ℝ), (∀ i, 0<u i) ∧ u 0=1 ∧ 1≤L ∧ L^2<l^3 ∧
      E *ᵥ u≤L • u ∧ F *ᵥ u≤L • u ∧ G *ᵥ u≤L • u := by
  have he01 : 0≤E 0 1 := hE 0 1
  have hf01 : 0≤F 0 1 := hF 0 1
  have hg01 : 0≤G 0 1 := hG 0 1
  let L := (3*l-1)/2
  have hLl : l<L := by dsimp [L]; linarith only [hl]
  have hL : 1≤L := (lt_trans hl hLl).le
  have hrate : L^2<l^3 := by
    have hp := mul_pos (sq_pos_of_pos (sub_pos.mpr hl)) (show 0<4*l-1 by linarith only [hl])
    dsimp [L]
    nlinarith only [hp]
  let d := 1+E 0 1+F 0 1+G 0 1
  have hd : 0<d := by dsimp [d]; linarith only [he01,hf01,hg01]
  let t := (L-l)/d
  have ht : 0<t := div_pos (sub_pos.mpr hLl) hd
  have hdt : d*t=L-l := by dsimp [t]; field_simp
  let u : Vec (Fin 2) := ![1,t]
  have hu : ∀ i, 0<u i := by intro i; fin_cases i; exact zero_lt_one; exact ht
  have hbound (T : Mat (Fin 2)) (hT0 : T 1 0=0)
      (hT00 : T 0 0≤l) (hT11 : T 1 1≤l) (hTd : T 0 1≤d) : T *ᵥ u≤L • u := by
    intro i
    fin_cases i
    · have hh := mul_le_mul_of_nonneg_right hTd ht.le
      change T 0 ⬝ᵥ u≤L*u 0
      simp only [dotProduct,Fin.sum_univ_two,u,Fin.isValue,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_fin_one,mul_one]
      linarith only [hh,hdt,hT00]
    · change T 1 ⬝ᵥ u≤L*u 1
      simp only [dotProduct,Fin.sum_univ_two,u,Fin.isValue,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_fin_one,hT0,zero_mul,zero_add]
      exact mul_le_mul_of_nonneg_right (le_trans hT11 hLl.le) ht.le
  refine ⟨u,L,hu,rfl,hL,hrate,?_,?_,?_⟩
  · apply hbound E he0 he00 he11
    dsimp [d]
    linarith only [hf01,hg01]
  · apply hbound F hf0 hf00 hf11
    dsimp [d]
    linarith only [he01,hg01]
  · apply hbound G hg0 hg00 hg11
    dsimp [d]
    linarith only [he01,hf01]

end CollatzResearch.ReversedUpperTriangularRay

#print axioms CollatzResearch.ReversedUpperTriangularRay.common_positive_upper_ray
