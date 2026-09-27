import CollatzReversedRealScaledProjection

namespace CollatzResearch.RealProjectionAlgebra

open Matrix CollatzCertificate RealAffine RealScaledProjection

theorem expanding_projection_scalar_offsets_zero
    (l m x y a sa b sb g sg e f : ℝ)
    (hl : 1 < l) (hm : 0 ≤ m) (hml : m ≤ l)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) (hsa : 0 ≤ sa)
    (hb : 0 ≤ b) (hsb : 0 ≤ sb)
    (hea : l * e + a ≤ m * a + e)
    (hec : l * y + b ≤ m * x + e)
    (hgc : l ^ 2 * x + l * sa + sb ≤ m * y + sg)
    (hfc : l ^ 2 * x + (l + 1) * a ≤ m * x + f)
    (hga : l * f + a ≤ m * sa + g)
    (hfb : l * g + a ≤ m * b + f)
    (hgb : l * sg + sb ≤ m * sb + sg) : a = 0 ∧ b = 0 ∧ x = 0 := by
  have hl0 : 0 < l := lt_trans zero_lt_one hl
  have he : e ≤ a := by
    apply le_of_mul_le_mul_left (a := l - 1) _ (sub_pos.mpr hl)
    nlinarith only [hea, mul_nonneg (sub_nonneg.mpr hml) ha]
  have hg : sg ≤ sb := by
    apply le_of_mul_le_mul_left (a := l - 1) _ (sub_pos.mpr hl)
    nlinarith only [hgb, mul_nonneg (sub_nonneg.mpr hml) hsb]
  have hec' : l * y + b ≤ m * x + a := by linarith only [hec, he]
  have hl2 : 0 < l ^ 2 - 1 := by nlinarith only [hl, sq_nonneg (l - 1)]
  have hquad : 0 ≤ l ^ 2 - m := by nlinarith only [hl, hml, sq_nonneg (l - 1)]
  have hcubic : 0 < l ^ 3 - m ^ 2 := by
    have h1 := mul_nonneg (sub_nonneg.mpr hml) (add_nonneg hl0.le hm)
    have h2 := mul_pos (pow_pos hl0 2) (sub_pos.mpr hl)
    nlinarith only [h1, h2]
  have hxcoeff : 0 < (l ^ 2 - 1) * (l ^ 2 - m) + (l ^ 3 - m ^ 2) :=
    add_pos_of_nonneg_of_pos (mul_nonneg hl2.le hquad) hcubic
  have hacoeff : 0 < l ^ 2 * (l + 1) - m := by
    have hi := mul_pos hl2 (show 0 < l + 1 by linarith only [hl])
    nlinarith only [hi, hml]
  have hsum : ((l ^ 2 - 1) * (l ^ 2 - m) + (l ^ 3 - m ^ 2)) * x +
      (l ^ 2 * (l + 1) - m) * a + l * (l - m) * sa + l * (sb - sg) ≤ 0 := by
    linear_combination m * hec' + l * hgc + l * hga + hfb + (l ^ 2 - 1) * hfc
  have hn1 := mul_nonneg hxcoeff.le hx
  have hn2 := mul_nonneg hacoeff.le ha
  have hn3 := mul_nonneg (mul_nonneg hl0.le (sub_nonneg.mpr hml)) hsa
  have hn4 := mul_nonneg hl0.le (sub_nonneg.mpr hg)
  have hax : a = 0 := by
    have hz : (l ^ 2 * (l + 1) - m) * a = 0 := by
      linarith only [hsum, hn1, hn2, hn3, hn4]
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hacoeff)
  have hxx : x = 0 := by
    have hz : ((l ^ 2 - 1) * (l ^ 2 - m) + (l ^ 3 - m ^ 2)) * x = 0 := by
      linarith only [hsum, hn1, hn2, hn3, hn4]
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hxcoeff)
  refine ⟨hax, ?_, hxx⟩
  rw [hax, hxx, mul_zero, add_zero] at hec'
  linarith only [hec', mul_nonneg hl0.le hy, hb]

variable {ι : Type*} [Fintype ι]

theorem expanding_projection_row_offsets_zero
    (A B C D E F G : Affine ι) (p s : Vec ι) (l m : ℝ)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hp : 0 ≤ p) (hs : 0 ≤ s) (hl : 1 < l) (hm : 0 ≤ m) (hml : m ≤ l)
    (hpA : p ᵥ* A.matrix = l • p) (hpB : p ᵥ* B.matrix = l • s)
    (hsA : s ᵥ* A.matrix = l • p) (hsB : s ᵥ* B.matrix = l • s)
    (hpE : p ᵥ* E.matrix = m • p) (hpF : p ᵥ* F.matrix = m • p)
    (hpG : p ᵥ* G.matrix = m • s) (hsG : s ᵥ* G.matrix = m • s) :
    p ⬝ᵥ A.offset = 0 ∧ p ⬝ᵥ B.offset = 0 ∧ p ⬝ᵥ C.offset = 0 := by
  have hea := dotProduct_le_dotProduct_of_nonneg_left h.ea.2 hp
  have hec := dotProduct_le_dotProduct_of_nonneg_left h.ec.2 hp
  have hgc := dotProduct_le_dotProduct_of_nonneg_left h.gc.2 hs
  have hfc := dotProduct_le_dotProduct_of_nonneg_left h.fc.2 hp
  have hga := dotProduct_le_dotProduct_of_nonneg_left h.ga.2 hp
  have hfb := dotProduct_le_dotProduct_of_nonneg_left h.fb.2 hp
  have hgb := dotProduct_le_dotProduct_of_nonneg_left h.gb.2 hs
  change p ⬝ᵥ (A.matrix *ᵥ E.offset + A.offset) ≤
    p ⬝ᵥ (E.matrix *ᵥ A.offset + E.offset) at hea
  change p ⬝ᵥ (B.matrix *ᵥ C.offset + B.offset) ≤
    p ⬝ᵥ (E.matrix *ᵥ C.offset + E.offset) at hec
  change s ⬝ᵥ (B.matrix *ᵥ (A.matrix *ᵥ C.offset + A.offset) + B.offset) ≤
    s ⬝ᵥ (G.matrix *ᵥ C.offset + G.offset) at hgc
  change p ⬝ᵥ (A.matrix *ᵥ (A.matrix *ᵥ C.offset + A.offset) + A.offset) ≤
    p ⬝ᵥ (F.matrix *ᵥ C.offset + F.offset) at hfc
  change p ⬝ᵥ (A.matrix *ᵥ F.offset + A.offset) ≤
    p ⬝ᵥ (G.matrix *ᵥ A.offset + G.offset) at hga
  change p ⬝ᵥ (A.matrix *ᵥ G.offset + A.offset) ≤
    p ⬝ᵥ (F.matrix *ᵥ B.offset + F.offset) at hfb
  change s ⬝ᵥ (B.matrix *ᵥ G.offset + B.offset) ≤
    s ⬝ᵥ (G.matrix *ᵥ B.offset + G.offset) at hgb
  simp only [dotProduct_add, dotProduct_mulVec, hpA, hpB, hsA, hsB,
    hpE, hpF, hpG, hsG, smul_vecMul, smul_dotProduct, smul_eq_mul]
    at hea hec hgc hfc hga hfb hgb
  have hgc' : l ^ 2 * (p ⬝ᵥ C.offset) + l * (s ⬝ᵥ A.offset) + s ⬝ᵥ B.offset ≤
      m * (s ⬝ᵥ C.offset) + s ⬝ᵥ G.offset := by nlinarith only [hgc]
  have hfc' : l ^ 2 * (p ⬝ᵥ C.offset) + (l + 1) * (p ⬝ᵥ A.offset) ≤
      m * (p ⬝ᵥ C.offset) + p ⬝ᵥ F.offset := by nlinarith only [hfc]
  exact expanding_projection_scalar_offsets_zero l m (p ⬝ᵥ C.offset) (s ⬝ᵥ C.offset)
    (p ⬝ᵥ A.offset) (s ⬝ᵥ A.offset) (p ⬝ᵥ B.offset) (s ⬝ᵥ B.offset)
    (p ⬝ᵥ G.offset) (s ⬝ᵥ G.offset) (p ⬝ᵥ E.offset) (p ⬝ᵥ F.offset)
    hl hm hml (dotProduct_nonneg_of_nonneg hp hC.2) (dotProduct_nonneg_of_nonneg hs hC.2)
    (dotProduct_nonneg_of_nonneg hp hA.2) (dotProduct_nonneg_of_nonneg hs hA.2)
    (dotProduct_nonneg_of_nonneg hp hB.2) (dotProduct_nonneg_of_nonneg hs hB.2)
    hea hec hgc' hfc' hga hfb hgb

variable [DecidableEq ι]

theorem expanding_binary_projection_gaps_zero
    (A B C D E F G : Affine ι) (i₀ : ι) (l t : ℝ)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hl : 1 < l) (hm : 0 ≤ t * l) (hml : t * l ≤ l)
    (hAA : A.matrix * A.matrix = l • A.matrix)
    (hAB : A.matrix * B.matrix = l • B.matrix)
    (hBA : B.matrix * A.matrix = l • A.matrix)
    (hBB : B.matrix * B.matrix = l • B.matrix)
    (hEA : E.matrix = t • A.matrix)
    (hFI : F.matrix = (t * l) • (1 : Mat ι)) (hGB : G.matrix = t • B.matrix) :
    (D.comp A).offset i₀ = D.offset i₀ ∧
      (D.comp B).offset i₀ = (D.comp G).offset i₀ := by
  let r : Vec ι := D.matrix i₀
  let p := r ᵥ* A.matrix
  let s := r ᵥ* B.matrix
  have hr : 0 ≤ r := fun j => hD.1 i₀ j
  have hp : 0 ≤ p := rowMul_nonneg hr hA.1
  have hs : 0 ≤ s := rowMul_nonneg hr hB.1
  have hpA : p ᵥ* A.matrix = l • p := by
    dsimp [p]
    rw [vecMul_vecMul, hAA, vecMul_smul]
  have hpB : p ᵥ* B.matrix = l • s := by
    dsimp [p, s]
    rw [vecMul_vecMul, hAB, vecMul_smul]
  have hsA : s ᵥ* A.matrix = l • p := by
    dsimp [s, p]
    rw [vecMul_vecMul, hBA, vecMul_smul]
  have hsB : s ᵥ* B.matrix = l • s := by
    dsimp [s]
    rw [vecMul_vecMul, hBB, vecMul_smul]
  have hpE : p ᵥ* E.matrix = (t * l) • p := by
    rw [hEA, vecMul_smul, hpA, smul_smul]
  have hpF : p ᵥ* F.matrix = (t * l) • p := by
    rw [hFI, vecMul_smul, vecMul_one]
  have hpG : p ᵥ* G.matrix = (t * l) • s := by
    rw [hGB, vecMul_smul, hpB, smul_smul]
  have hsG : s ᵥ* G.matrix = (t * l) • s := by
    rw [hGB, vecMul_smul, hsB, smul_smul]
  obtain ⟨hpa, hpb, _⟩ := expanding_projection_row_offsets_zero A B C D E F G p s l (t * l)
    hA hB hC h hp hs hl hm hml hpA hpB hsA hsB hpE hpF hpG hsG
  have hrp : r ≤ p := fun j => h.da.1 i₀ j
  have hra : r ⬝ᵥ A.offset = 0 := by
    have hi := dotProduct_le_dotProduct_of_nonneg_right hrp hA.2
    exact le_antisymm (by linarith only [hi, hpa]) (dotProduct_nonneg_of_nonneg hr hA.2)
  have hrb : r ⬝ᵥ B.offset = 0 := by
    have hi := dotProduct_le_dotProduct_of_nonneg_right hrp hB.2
    exact le_antisymm (by linarith only [hi, hpb]) (dotProduct_nonneg_of_nonneg hr hB.2)
  have hrg : r ⬝ᵥ G.offset = 0 := by
    have hi := h.db.2 i₀
    change r ⬝ᵥ G.offset + D.offset i₀ ≤ r ⬝ᵥ B.offset + D.offset i₀ at hi
    exact le_antisymm (by linarith only [hi, hrb]) (dotProduct_nonneg_of_nonneg hr hG.2)
  change r ⬝ᵥ A.offset + D.offset i₀ = D.offset i₀ ∧
    r ⬝ᵥ B.offset + D.offset i₀ = r ⬝ᵥ G.offset + D.offset i₀
  simp only [hra, hrb, hrg, zero_add, and_self]

theorem positive_binary_projection_gaps_zero
    (A B C D E F G : Affine ι) (i₀ : ι) (l t : ℝ)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hAA : A.matrix * A.matrix = l • A.matrix)
    (hAB : A.matrix * B.matrix = l • B.matrix)
    (hBA : B.matrix * A.matrix = l • A.matrix)
    (hBB : B.matrix * B.matrix = l • B.matrix)
    (hEA : E.matrix = t • A.matrix)
    (hFI : F.matrix = (t * l) • (1 : Mat ι)) (hGB : G.matrix = t • B.matrix)
    (u : Vec ι) (hu : ∀ j, 0 < u j) (hAu : A.matrix *ᵥ u = l • u) :
    (D.comp A).offset i₀ = D.offset i₀ ∧
      (D.comp B).offset i₀ = (D.comp G).offset i₀ := by
  let r : Vec ι := D.matrix i₀
  have hr : 0 ≤ r := fun j => hD.1 i₀ j
  by_cases hpos : ∃ j, 0 < r j
  · obtain ⟨j, hj⟩ := hpos
    have hru : 0 < r ⬝ᵥ u :=
      (Finset.sum_pos_iff_of_nonneg (fun k _ => mul_nonneg (hr k) (hu k).le)).mpr
        ⟨j, Finset.mem_univ j, mul_pos hj (hu j)⟩
    have hda : r ≤ r ᵥ* A.matrix := fun k => h.da.1 i₀ k
    have hscale := dotProduct_le_dotProduct_of_nonneg_right hda (fun k => (hu k).le)
    rw [← dotProduct_mulVec, hAu, dotProduct_smul, smul_eq_mul] at hscale
    have hl : 1 ≤ l := by nlinarith only [hscale, hru]
    have hl0 : 0 < l := lt_of_lt_of_le zero_lt_one hl
    have hBu : B.matrix *ᵥ u = l • u := by
      have hi := congrArg (fun M : Mat ι => M *ᵥ u) hBA
      dsimp only at hi
      rw [← mulVec_mulVec, hAu, mulVec_smul, smul_mulVec, hAu] at hi
      funext k
      have hk := congrFun hi k
      change l * (B.matrix *ᵥ u) k = l * (l * u k) at hk
      change (B.matrix *ᵥ u) k = l * u k
      nlinarith only [hk, hl0]
    have hdb : r ᵥ* G.matrix ≤ r ᵥ* B.matrix := fun k => h.db.1 i₀ k
    have hμ := dotProduct_le_dotProduct_of_nonneg_right hdb (fun k => (hu k).le)
    rw [← dotProduct_mulVec, ← dotProduct_mulVec, hGB, smul_mulVec, hBu,
      smul_smul, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hμ
    have hml : t * l ≤ l := by nlinarith only [hμ, hru]
    have hm : 0 ≤ t * l := by
      have hi := hF.1 i₀ i₀
      rw [hFI] at hi
      simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one] using hi
    by_cases hlex : 1 < l
    · exact expanding_binary_projection_gaps_zero A B C D E F G i₀ l t
        hA hB hC hD hG h hlex hm hml hAA hAB hBA hBB hEA hFI hGB
    · have hl1 : l = 1 := le_antisymm (le_of_not_gt hlex) hl
      subst l
      simp only [one_smul, mul_one] at hBA hBB hFI hAu
      have hrA : r ᵥ* A.matrix = r :=
        RealCriticalReadout.row_nondecrease_fixed_by_positive_vector A.matrix r u hu hAu hda
      apply scaled_readout_gaps_zero A B C D E F G i₀ (r ᵥ* B.matrix) 1 t
        hA hB hC hD hE hF hG h
      · simpa only [one_smul] using hrA
      · simp only [r, one_smul]
      · simpa only [vecMul_vecMul, hBA, one_smul] using hrA
      · simp only [vecMul_vecMul, hBB, one_smul]
      · rw [hFI, vecMul_smul, vecMul_one]
      · rw [hGB, vecMul_smul]
      · rw [hEA, vecMul_smul, vecMul_vecMul, hBA, hrA]
  · have hrz : r = 0 := funext (fun j =>
      le_antisymm (not_lt.mp ((not_exists.mp hpos) j)) (hr j))
    change r ⬝ᵥ A.offset + D.offset i₀ = D.offset i₀ ∧
      r ⬝ᵥ B.offset + D.offset i₀ = r ⬝ᵥ G.offset + D.offset i₀
    simp only [hrz, zero_dotProduct, zero_add, and_self]

#print axioms expanding_projection_scalar_offsets_zero
#print axioms expanding_projection_row_offsets_zero
#print axioms expanding_binary_projection_gaps_zero
#print axioms positive_binary_projection_gaps_zero

end CollatzResearch.RealProjectionAlgebra
